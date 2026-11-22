#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""pack.py — 整包交接阵列（质控交接包）。

以 SQLite 落盘存储阵列包，支持：

  publish(root, req, A, R, L, B) -> (包号, 摘要)
      A = {id: (高, 宽, 块高, 块宽)}            正整数尺寸
      R = {id: (标量表, 引用表)}                标量表 {(行,列): int}，引用表 {(行,列): 引用}
      L = {绝对路径: id}                        别名保身份，路径无祖先冲突
      B = 单遍乱序迭代 (id, 块行, 块列, 整数矩阵) 零基块位齐全唯一，边块截短，拒布尔
      引用为 None、("a"/"r", id) 或 ("s", 数组id, 零基坐标列)；允许前向与成环。
      同请求同逻辑内容复领原回执；同请求异内容拒绝。

  export(root, id, path) -> 摘要
      导出自足包（引用传递闭包），断源可开。

  open(path[, id]) -> 只读件
      验结构及摘要。只读件方法：
        get(path)            -> (id, (高, 宽, 块高, 块宽))
        read(ref)            -> None | 目标id | 坐标升序去重值流
        check(ref, lo, hi)   -> (计数, 和, 最小, 最大, 均在整数闭区间)

错误约定：坏件或坏参 ValueError；缺包 KeyError；来源及写入异常原抛。
失败不产生新回执，也不留下可开残件。整阵不物化，块级落盘、按需重扫。
"""

from __future__ import annotations

import hashlib
import json
import os
import sqlite3
import sys
import tempfile
import urllib.parse

__all__ = ["publish", "export", "open"]

_builtin_open = open  # 业务接口 open 定义之前留存内置 open（自测写坏件用）

_FORMAT = "pointwise-pack"
_VERSION = "1"
_REGISTRY = "registry.sqlite"
_PKGDIR = "packages"

_SCHEMA = """
CREATE TABLE meta (key TEXT PRIMARY KEY, value TEXT);
CREATE TABLE arrays (id_key TEXT PRIMARY KEY, h INTEGER, w INTEGER, bh INTEGER, bw INTEGER);
CREATE TABLE aliases (path TEXT PRIMARY KEY, id_key TEXT NOT NULL);
CREATE TABLE scalars (id_key TEXT NOT NULL, r INTEGER NOT NULL, c INTEGER NOT NULL,
                      v TEXT NOT NULL, PRIMARY KEY (id_key, r, c));
CREATE TABLE refs (id_key TEXT NOT NULL, r INTEGER NOT NULL, c INTEGER NOT NULL,
                   kind TEXT NOT NULL, target TEXT, coords TEXT,
                   PRIMARY KEY (id_key, r, c));
CREATE TABLE blocks (id_key TEXT NOT NULL, br INTEGER NOT NULL, bc INTEGER NOT NULL,
                     rows TEXT NOT NULL, PRIMARY KEY (id_key, br, bc));
"""

_REGISTRY_SCHEMA = """
CREATE TABLE IF NOT EXISTS packages (digest TEXT PRIMARY KEY, pkg_no INTEGER UNIQUE, filename TEXT);
CREATE TABLE IF NOT EXISTS requests (req TEXT PRIMARY KEY, digest TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS arrays_index (id_key TEXT NOT NULL, digest TEXT NOT NULL);
"""


# ---------------------------------------------------------------- 基础校验

def _is_int(x):
    return isinstance(x, int) and not isinstance(x, bool)


def _check_id(i):
    if isinstance(i, bool) or not isinstance(i, (str, int)):
        raise ValueError("id 须为 str 或 int（拒布尔）: %r" % (i,))
    return i


def _id_key(i):
    # 可逆且类型可辨的键编码（"1" 与 1 不同键）
    return json.dumps(i, ensure_ascii=False)


def _key_id(k):
    return json.loads(k)


def _req_key(req):
    if isinstance(req, bool) or not isinstance(req, (str, int)):
        raise ValueError("req 须为 str 或 int（拒布尔）: %r" % (req,))
    return _id_key(req)


def _norm_path(p):
    if not isinstance(p, str) or not p:
        raise ValueError("路径须为非空字符串: %r" % (p,))
    n = os.path.normpath(p)
    if not os.path.isabs(n):
        raise ValueError("路径须为绝对路径: %r" % (p,))
    return n


def _check_coord(coord, h, w):
    if isinstance(coord, (str, bytes)) or not isinstance(coord, (list, tuple)) or len(coord) != 2:
        raise ValueError("坐标须为 (行, 列): %r" % (coord,))
    r, c = coord
    if not _is_int(r) or not _is_int(c):
        raise ValueError("坐标须为整数（拒布尔）: %r" % (coord,))
    if not (0 <= r < h and 0 <= c < w):
        raise ValueError("坐标越界: %r（阵列 %dx%d）" % (coord, h, w))
    return (r, c)


def _canon_ref(ref, arrays):
    """校验并规范化引用；arrays 为 {id: (h,w,bh,bw)}。允许前向与成环。"""
    if ref is None:
        return None
    if isinstance(ref, (str, bytes)) or not isinstance(ref, (list, tuple)):
        raise ValueError("引用须为 None、('a'/'r', id) 或 ('s', id, 坐标列): %r" % (ref,))
    if len(ref) == 2 and ref[0] in ("a", "r"):
        target = _check_id(ref[1])
        if target not in arrays:
            raise ValueError("引用目标不存在: %r" % (target,))
        return (ref[0], target)
    if len(ref) == 3 and ref[0] == "s":
        target = _check_id(ref[1])
        if target not in arrays:
            raise ValueError("引用目标不存在: %r" % (target,))
        coords = ref[2]
        if isinstance(coords, (str, bytes)) or not isinstance(coords, (list, tuple)):
            raise ValueError("坐标列须为序列: %r" % (coords,))
        h, w = arrays[target][0], arrays[target][1]
        canon = sorted(set(_check_coord(cd, h, w) for cd in coords))
        return ("s", target, tuple(canon))
    raise ValueError("引用须为 None、('a'/'r', id) 或 ('s', id, 坐标列): %r" % (ref,))


def _validate_A(A):
    if not isinstance(A, dict):
        raise ValueError("A 须为 {id: (高,宽,块高,块宽)} 字典")
    arrays = {}
    for i, d in A.items():
        _check_id(i)
        if isinstance(d, (str, bytes)) or not isinstance(d, (list, tuple)) or len(d) != 4:
            raise ValueError("阵列定义须为 (高,宽,块高,块宽): %r" % (d,))
        h, w, bh, bw = d
        if not all(_is_int(x) and x > 0 for x in (h, w, bh, bw)):
            raise ValueError("尺寸须为正整数（拒布尔）: %r" % (d,))
        arrays[i] = (h, w, bh, bw)
    return arrays


def _validate_L(L, arrays):
    if L is None:
        return {}
    if not isinstance(L, dict):
        raise ValueError("L 须为 {绝对路径: id} 字典")
    m = {}
    for p, i in L.items():
        np = _norm_path(p)
        _check_id(i)
        if i not in arrays:
            raise ValueError("别名指向未知 id: %r" % (i,))
        if np in m:
            if m[np] != i:
                raise ValueError("路径绑定冲突: %r" % (p,))
            continue
        m[np] = i
    paths = sorted(m)
    for a, p in enumerate(paths):
        prefix = p if p == os.sep else p.rstrip(os.sep) + os.sep
        for q in paths[a + 1:]:
            if q.startswith(prefix):
                raise ValueError("路径祖先冲突: %r 与 %r" % (p, q))
    return m


def _validate_R(R, arrays):
    if R is None:
        return {}
    if not isinstance(R, dict):
        raise ValueError("R 须为 {id: (标量表, 引用表)} 字典")
    out = {}
    for i, pair in R.items():
        _check_id(i)
        if i not in arrays:
            raise ValueError("R 含未知 id: %r" % (i,))
        if isinstance(pair, (str, bytes)) or not isinstance(pair, (list, tuple)) or len(pair) != 2:
            raise ValueError("R 项须为 (标量表, 引用表): %r" % (pair,))
        scalars, refs = pair
        h, w = arrays[i][0], arrays[i][1]
        smap = {}
        if scalars is not None:
            if not isinstance(scalars, dict):
                raise ValueError("标量表须为 {(行,列): 整数}: %r" % (scalars,))
            for coord, v in scalars.items():
                rc = _check_coord(coord, h, w)
                if not _is_int(v):
                    raise ValueError("标量须为整数（拒布尔）: %r" % (v,))
                smap[rc] = v
        rmap = {}
        if refs is not None:
            if not isinstance(refs, dict):
                raise ValueError("引用表须为 {(行,列): 引用}: %r" % (refs,))
            for coord, ref in refs.items():
                rc = _check_coord(coord, h, w)
                rmap[rc] = _canon_ref(ref, arrays)
        if set(smap) & set(rmap):
            raise ValueError("同一格既为标量又为引用: %r" % (i,))
        if smap or rmap:
            out[i] = (smap, rmap)
    return out


def _validate_matrix(m, er, ec):
    if isinstance(m, (str, bytes)) or not isinstance(m, (list, tuple)):
        raise ValueError("块须为整数矩阵")
    if len(m) != er:
        raise ValueError("块行数不符：期望 %d，实得 %d" % (er, len(m)))
    out = []
    for row in m:
        if isinstance(row, (str, bytes)) or not isinstance(row, (list, tuple)):
            raise ValueError("块行须为整数序列")
        if len(row) != ec:
            raise ValueError("块列数不符：期望 %d，实得 %d" % (ec, len(row)))
        for v in row:
            if not _is_int(v):
                raise ValueError("块元素须为整数（拒布尔）: %r" % (v,))
        out.append([int(v) for v in row])
    return out


# ---------------------------------------------------------------- 摘要

class _Hasher:
    def __init__(self):
        self._h = hashlib.sha256()

    def feed(self, *fields):
        self._h.update(json.dumps(fields, ensure_ascii=False, separators=(",", ":")).encode("utf-8"))
        self._h.update(b"\n")

    def hexdigest(self):
        return self._h.hexdigest()


def _decode_ref(kind, target_key, coords_json):
    if kind == "n":
        return None
    if kind in ("a", "r"):
        return (kind, _key_id(target_key))
    if kind == "s":
        return ("s", _key_id(target_key), tuple(tuple(x) for x in json.loads(coords_json)))
    raise ValueError("坏件：未知引用类别 %r" % (kind,))


def _compute_digest(db):
    hs = _Hasher()
    hs.feed(_FORMAT, 1)
    for ik, h, w, bh, bw in db.execute("SELECT id_key,h,w,bh,bw FROM arrays ORDER BY id_key"):
        hs.feed("array", _key_id(ik), h, w, bh, bw)
    for path, ik in db.execute("SELECT path,id_key FROM aliases ORDER BY path"):
        hs.feed("alias", path, _key_id(ik))
    for ik, r, c, v in db.execute("SELECT id_key,r,c,v FROM scalars ORDER BY id_key,r,c"):
        hs.feed("scalar", _key_id(ik), r, c, int(v))
    for ik, r, c, kind, tk, cj in db.execute(
            "SELECT id_key,r,c,kind,target,coords FROM refs ORDER BY id_key,r,c"):
        hs.feed("ref", _key_id(ik), r, c, _decode_ref(kind, tk, cj))
    for ik, br, bc, rows_json in db.execute(
            "SELECT id_key,br,bc,rows FROM blocks ORDER BY id_key,br,bc"):
        hs.feed("block", _key_id(ik), br, bc)
        for row in json.loads(rows_json):
            hs.feed("row", row)
    return "sha256:" + hs.hexdigest()


# ---------------------------------------------------------------- 包构建

def _init_package(db):
    db.executescript(_SCHEMA)
    db.execute("INSERT INTO meta(key,value) VALUES('format',?)", (_FORMAT,))
    db.execute("INSERT INTO meta(key,value) VALUES('version',?)", (_VERSION,))


def _fill_static(db, arrays, aliases, overlays):
    db.executemany("INSERT INTO arrays VALUES(?,?,?,?,?)",
                   [(_id_key(i), h, w, bh, bw) for i, (h, w, bh, bw) in arrays.items()])
    db.executemany("INSERT INTO aliases VALUES(?,?)",
                   [(p, _id_key(i)) for p, i in aliases.items()])
    for i, (smap, rmap) in overlays.items():
        ik = _id_key(i)
        db.executemany("INSERT INTO scalars VALUES(?,?,?,?)",
                       [(ik, r, c, str(v)) for (r, c), v in smap.items()])
        rows = []
        for (r, c), ref in rmap.items():
            if ref is None:
                rows.append((ik, r, c, "n", None, None))
            elif ref[0] in ("a", "r"):
                rows.append((ik, r, c, ref[0], _id_key(ref[1]), None))
            else:
                rows.append((ik, r, c, "s", _id_key(ref[1]),
                             json.dumps([[cr, cc] for cr, cc in ref[2]])))
        db.executemany("INSERT INTO refs VALUES(?,?,?,?,?,?)", rows)


def _ingest_B(db, B, arrays):
    try:
        it = iter(B)
    except TypeError:
        raise ValueError("B 须为可迭代对象")
    counts = {i: 0 for i in arrays}
    for item in it:  # 来源异常原抛
        try:
            i, br, bc, m = item
        except (TypeError, ValueError):
            raise ValueError("B 项须为 (id, 块行, 块列, 整数矩阵): %r" % (item,))
        _check_id(i)
        if i not in arrays:
            raise ValueError("块指向未知 id: %r" % (i,))
        h, w, bh, bw = arrays[i]
        gr = -(-h // bh)
        gc = -(-w // bw)
        if not _is_int(br) or not _is_int(bc) or not (0 <= br < gr and 0 <= bc < gc):
            raise ValueError("块位越界: (%r, %r)，块网格 %dx%d" % (br, bc, gr, gc))
        er = min(bh, h - br * bh)
        ec = min(bw, w - bc * bw)
        rows = _validate_matrix(m, er, ec)
        try:
            db.execute("INSERT INTO blocks VALUES(?,?,?,?)",
                       (_id_key(i), br, bc, json.dumps(rows)))
        except sqlite3.IntegrityError:
            raise ValueError("块位重复: (%r, %d, %d)" % (i, br, bc))
        counts[i] += 1
    for i, (h, w, bh, bw) in arrays.items():
        want = (-(-h // bh)) * (-(-w // bw))
        if counts[i] != want:
            raise ValueError("阵列 %r 块位不齐全：期望 %d，实得 %d" % (i, want, counts[i]))


def _open_registry(root):
    reg = sqlite3.connect(os.path.join(root, _REGISTRY))
    reg.isolation_level = None  # 手动事务，避免隐式 BEGIN 干扰
    reg.executescript(_REGISTRY_SCHEMA)
    return reg


# ---------------------------------------------------------------- publish

def publish(root, req, A, R, L, B):
    """发布整包阵列，返回 (包号, 摘要)。同请求同逻辑内容复领，异绑拒绝。"""
    if not isinstance(root, (str, os.PathLike)):
        raise ValueError("root 须为路径: %r" % (root,))
    root = os.fspath(root)
    req_k = _req_key(req)
    arrays = _validate_A(A)
    aliases = _validate_L(L, arrays)
    overlays = _validate_R(R, arrays)

    pkgdir = os.path.join(root, _PKGDIR)
    os.makedirs(pkgdir, exist_ok=True)  # 写入异常原抛

    fd, tmp = tempfile.mkstemp(prefix=".build-", suffix=".pack", dir=pkgdir)
    os.close(fd)
    try:
        db = sqlite3.connect(tmp)
        try:
            _init_package(db)
            _fill_static(db, arrays, aliases, overlays)
            _ingest_B(db, B, arrays)
            digest = _compute_digest(db)
            db.execute("INSERT INTO meta(key,value) VALUES('digest',?)", (digest,))
            db.commit()
        finally:
            db.close()
    except Exception:
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise

    reg = _open_registry(root)
    try:
        reg.execute("BEGIN IMMEDIATE")
        try:
            row = reg.execute("SELECT digest FROM requests WHERE req=?", (req_k,)).fetchone()
            if row is not None:
                if row[0] != digest:
                    raise ValueError("请求已绑定不同逻辑内容，拒绝异绑")
                pkg_no = reg.execute("SELECT pkg_no FROM packages WHERE digest=?",
                                     (digest,)).fetchone()[0]
                os.unlink(tmp)  # 复领：内容已在库
                reg.execute("COMMIT")
                return (pkg_no, digest)
            row = reg.execute("SELECT pkg_no FROM packages WHERE digest=?", (digest,)).fetchone()
            if row is not None:
                pkg_no = row[0]
                os.unlink(tmp)  # 同逻辑内容已有包
            else:
                pkg_no = reg.execute(
                    "SELECT COALESCE(MAX(pkg_no),0)+1 FROM packages").fetchone()[0]
                final = os.path.join(pkgdir, "pack-%d-%s.pack" % (pkg_no, digest[7:23]))
                db = sqlite3.connect(tmp)
                try:
                    db.execute("INSERT INTO meta(key,value) VALUES('pkg_no',?)", (str(pkg_no),))
                    db.commit()
                finally:
                    db.close()
                os.replace(tmp, final)  # 写入异常原抛
                try:
                    reg.execute("INSERT INTO packages VALUES(?,?,?)",
                                (digest, pkg_no, os.path.basename(final)))
                    reg.executemany("INSERT INTO arrays_index VALUES(?,?)",
                                    [(_id_key(i), digest) for i in arrays])
                except Exception:
                    try:
                        os.unlink(final)
                    except OSError:
                        pass
                    raise
            reg.execute("INSERT INTO requests VALUES(?,?)", (req_k, digest))
            reg.execute("COMMIT")
        except Exception:
            reg.execute("ROLLBACK")
            raise
    finally:
        reg.close()
    return (pkg_no, digest)


# ---------------------------------------------------------------- 包校验（open）

def _validate_db(db):
    tables = {r[0] for r in db.execute("SELECT name FROM sqlite_master WHERE type='table'")}
    if not {"meta", "arrays", "aliases", "scalars", "refs", "blocks"} <= tables:
        raise ValueError("坏件：结构缺失")
    meta = dict(db.execute("SELECT key,value FROM meta"))
    if meta.get("format") != _FORMAT or meta.get("version") != _VERSION or "digest" not in meta:
        raise ValueError("坏件：清单缺失或不匹配")

    arrays = {}
    for ik, h, w, bh, bw in db.execute("SELECT id_key,h,w,bh,bw FROM arrays"):
        i = _key_id(ik)  # JSONDecodeError 属 ValueError
        _check_id(i)
        if not all(_is_int(x) and x > 0 for x in (h, w, bh, bw)):
            raise ValueError("坏件：尺寸非法")
        arrays[i] = (h, w, bh, bw)

    amap = {}
    for p, ik in db.execute("SELECT path,id_key FROM aliases"):
        if not isinstance(p, str) or not os.path.isabs(os.path.normpath(p)):
            raise ValueError("坏件：别名路径非法")
        i = _key_id(ik)
        if i not in arrays:
            raise ValueError("坏件：别名指向未知 id")
        if p in amap and amap[p] != i:
            raise ValueError("坏件：别名冲突")
        amap[p] = i
    paths = sorted(amap)
    for a, p in enumerate(paths):
        prefix = p if p == os.sep else p.rstrip(os.sep) + os.sep
        for q in paths[a + 1:]:
            if q.startswith(prefix):
                raise ValueError("坏件：路径祖先冲突")

    for ik, r, c, v in db.execute("SELECT id_key,r,c,v FROM scalars"):
        i = _key_id(ik)
        if i not in arrays:
            raise ValueError("坏件：标量指向未知 id")
        _check_coord((r, c), arrays[i][0], arrays[i][1])
        try:
            int(v)
        except (TypeError, ValueError):
            raise ValueError("坏件：标量非法")

    for ik, r, c, kind, tk, cj in db.execute("SELECT id_key,r,c,kind,target,coords FROM refs"):
        i = _key_id(ik)
        if i not in arrays:
            raise ValueError("坏件：引用指向未知 id")
        _check_coord((r, c), arrays[i][0], arrays[i][1])
        if kind not in ("n", "a", "r", "s"):
            raise ValueError("坏件：引用类别非法")
        if kind in ("a", "r", "s"):
            t = _key_id(tk)
            if t not in arrays:
                raise ValueError("坏件：引用目标缺失")
            if kind == "s":
                try:
                    coords = json.loads(cj)
                except (TypeError, ValueError):
                    raise ValueError("坏件：引用坐标列非法")
                if not isinstance(coords, list):
                    raise ValueError("坏件：引用坐标列非法")
                for cd in coords:
                    _check_coord(cd, arrays[t][0], arrays[t][1])

    if db.execute("SELECT 1 FROM scalars s JOIN refs f "
                  "ON s.id_key=f.id_key AND s.r=f.r AND s.c=f.c LIMIT 1").fetchone():
        raise ValueError("坏件：同格既为标量又为引用")

    counts = {}
    for ik, br, bc, rows_json in db.execute("SELECT id_key,br,bc,rows FROM blocks"):
        i = _key_id(ik)
        if i not in arrays:
            raise ValueError("坏件：块指向未知 id")
        h, w, bh, bw = arrays[i]
        gr = -(-h // bh)
        gc = -(-w // bw)
        if not _is_int(br) or not _is_int(bc) or not (0 <= br < gr and 0 <= bc < gc):
            raise ValueError("坏件：块位越界")
        try:
            rows = json.loads(rows_json)
        except (TypeError, ValueError):
            raise ValueError("坏件：块数据非法")
        _validate_matrix(rows, min(bh, h - br * bh), min(bw, w - bc * bw))
        counts[i] = counts.get(i, 0) + 1
    for i, (h, w, bh, bw) in arrays.items():
        want = (-(-h // bh)) * (-(-w // bw))
        if counts.get(i, 0) != want:
            raise ValueError("坏件：阵列 %r 块位不齐全" % (i,))

    if _compute_digest(db) != meta["digest"]:
        raise ValueError("坏件：摘要不匹配")
    return arrays, amap


class _Handle:
    """open() 返回的只读件。"""

    def __init__(self, db, path, arrays, amap):
        self._db = db
        self.path = path
        self._defs = arrays
        self._aliases = amap
        row = db.execute("SELECT value FROM meta WHERE key='digest'").fetchone()
        self.digest = row[0] if row else None

    # -- 只读件接口 --

    def get(self, path):
        """按别名路径取 (id, (高,宽,块高,块宽))。"""
        np = _norm_path(path)
        if np not in self._aliases:
            raise KeyError(path)
        i = self._aliases[np]
        return (i, self._defs[i])

    def read(self, ref):
        """读引用：None -> None；('a'/'r', id) -> 目标id；
        ('s', id, 坐标列) -> 坐标升序去重值流（生成器）。"""
        canon = self._validate_ref_arg(ref)
        if canon is None:
            return None
        if canon[0] in ("a", "r"):
            return canon[1]
        return self._stream_cells(canon[1], canon[2])

    def check(self, ref, lo, hi):
        """统计引用值流：(计数, 和, 最小, 最大, 均在 [lo,hi] 整数闭区间)。
        空区零计数零和、空极值(None)、通过。"""
        if not _is_int(lo) or not _is_int(hi):
            raise ValueError("lo/hi 须为整数（拒布尔）")
        if lo > hi:
            raise ValueError("lo 不可大于 hi")
        canon = self._validate_ref_arg(ref)
        if canon is None:
            values = iter(())
        elif canon[0] in ("a", "r"):
            values = self._scan_array(canon[1])
        else:
            values = self._stream_cells(canon[1], canon[2])
        count = 0
        total = 0
        mn = None
        mx = None
        ok = True
        for v in values:
            count += 1
            if _is_int(v):
                total += v
                mn = v if mn is None or v < mn else mn
                mx = v if mx is None or v > mx else mx
                if not (lo <= v <= hi):
                    ok = False
            else:
                ok = False
        return (count, total, mn, mx, ok)

    def close(self):
        self._db.close()

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        self.close()
        return False

    # -- 内部 --

    def _validate_ref_arg(self, ref):
        if ref is None:
            return None
        if isinstance(ref, (str, bytes)) or not isinstance(ref, (list, tuple)):
            raise ValueError("引用须为 None、('a'/'r', id) 或 ('s', id, 坐标列): %r" % (ref,))
        if len(ref) == 2 and ref[0] in ("a", "r"):
            target = _check_id(ref[1])
            if target not in self._defs:
                raise KeyError(ref[1])
            return (ref[0], target)
        if len(ref) == 3 and ref[0] == "s":
            target = _check_id(ref[1])
            if target not in self._defs:
                raise KeyError(ref[1])
            coords = ref[2]
            if isinstance(coords, (str, bytes)) or not isinstance(coords, (list, tuple)):
                raise ValueError("坐标列须为序列: %r" % (coords,))
            h, w = self._defs[target][0], self._defs[target][1]
            canon = sorted(set(_check_coord(cd, h, w) for cd in coords))
            return ("s", target, tuple(canon))
        raise ValueError("引用须为 None、('a'/'r', id) 或 ('s', id, 坐标列): %r" % (ref,))

    def _overlay(self, ik, r, c):
        row = self._db.execute("SELECT kind,target,coords FROM refs WHERE id_key=? AND r=? AND c=?",
                               (ik, r, c)).fetchone()
        if row is not None:
            return _decode_ref(row[0], row[1], row[2])
        row = self._db.execute("SELECT v FROM scalars WHERE id_key=? AND r=? AND c=?",
                               (ik, r, c)).fetchone()
        if row is not None:
            return int(row[0])
        return _MISSING

    def _block(self, ik, br, bc):
        row = self._db.execute("SELECT rows FROM blocks WHERE id_key=? AND br=? AND bc=?",
                               (ik, br, bc)).fetchone()
        if row is None:
            raise ValueError("坏件：块缺失 (%d, %d)" % (br, bc))
        return json.loads(row[0])

    def _stream_cells(self, i, coords):
        ik = _id_key(i)
        bh, bw = self._defs[i][2], self._defs[i][3]
        cache_key = None
        cache_rows = None
        for (r, c) in coords:
            v = self._overlay(ik, r, c)
            if v is _MISSING:
                key = (r // bh, c // bw)
                if key != cache_key:
                    cache_key = key
                    cache_rows = self._block(ik, key[0], key[1])
                v = cache_rows[r % bh][c % bw]
            yield v

    def _scan_array(self, i):
        ik = _id_key(i)
        h, w, bh, bw = self._defs[i]
        for br, bc, rows_json in self._db.execute(
                "SELECT br,bc,rows FROM blocks WHERE id_key=? ORDER BY br,bc", (ik,)):
            rows = json.loads(rows_json)
            r0 = br * bh
            c0 = bc * bw
            r1 = r0 + len(rows)
            c1 = c0 + (len(rows[0]) if rows else 0)
            overlay = {}
            for r, c, kind, tk, cj in self._db.execute(
                    "SELECT r,c,kind,target,coords FROM refs "
                    "WHERE id_key=? AND r>=? AND r<? AND c>=? AND c<?",
                    (ik, r0, r1, c0, c1)):
                overlay[(r, c)] = _decode_ref(kind, tk, cj)
            for r, c, v in self._db.execute(
                    "SELECT r,c,v FROM scalars "
                    "WHERE id_key=? AND r>=? AND r<? AND c>=? AND c<?",
                    (ik, r0, r1, c0, c1)):
                overlay[(r, c)] = int(v)
            for di, row in enumerate(rows):
                for dj, v in enumerate(row):
                    yield overlay.get((r0 + di, c0 + dj), v)


class _Missing:
    pass


_MISSING = _Missing()


def open(path, id=None):
    """打开包文件，验结构及摘要，返回只读件。缺包 KeyError，坏件 ValueError。"""
    if not isinstance(path, (str, os.PathLike)):
        raise ValueError("path 须为路径: %r" % (path,))
    p = os.fspath(path)
    if id is not None:
        _check_id(id)
    if not os.path.isfile(p):
        raise KeyError(p)
    uri = "file:%s?mode=ro" % urllib.parse.quote(os.path.abspath(p))
    try:
        db = sqlite3.connect(uri, uri=True)
    except sqlite3.Error:
        raise ValueError("坏件：无法打开 %r" % (p,))
    try:
        try:
            qc = db.execute("PRAGMA quick_check").fetchone()
        except sqlite3.DatabaseError:
            raise ValueError("坏件：非有效包文件 %r" % (p,))
        if qc is None or qc[0] != "ok":
            raise ValueError("坏件：完整性检查未过 %r" % (p,))
        try:
            arrays, amap = _validate_db(db)
        except sqlite3.DatabaseError:
            raise ValueError("坏件：结构读取失败 %r" % (p,))
    except Exception:
        db.close()
        raise
    if id is not None and id not in arrays:
        db.close()
        raise KeyError(id)
    return _Handle(db, p, arrays, amap)


# ---------------------------------------------------------------- export

def export(root, id, path):
    """从 root 库导出含 id 引用闭包的自足包到 path，返回摘要。缺包 KeyError。"""
    if not isinstance(root, (str, os.PathLike)):
        raise ValueError("root 须为路径: %r" % (root,))
    if not isinstance(path, (str, os.PathLike)):
        raise ValueError("path 须为路径: %r" % (path,))
    _check_id(id)
    root = os.fspath(root)
    p = os.fspath(path)
    ik = _id_key(id)

    reg_path = os.path.join(root, _REGISTRY)
    if not os.path.isfile(reg_path):
        raise KeyError(id)
    try:
        reg = sqlite3.connect("file:%s?mode=ro" % urllib.parse.quote(os.path.abspath(reg_path)),
                              uri=True)
    except sqlite3.Error:
        raise ValueError("坏件：库登记不可读")
    try:
        row = reg.execute(
            "SELECT a.digest, p.pkg_no, p.filename FROM arrays_index a "
            "JOIN packages p ON p.digest = a.digest "
            "WHERE a.id_key = ? ORDER BY p.pkg_no DESC LIMIT 1", (ik,)).fetchone()
    except sqlite3.DatabaseError:
        reg.close()
        raise ValueError("坏件：库登记不可读")
    reg.close()
    if row is None:
        raise KeyError(id)
    src_path = os.path.join(root, _PKGDIR, row[2])

    src = open(src_path)  # 验结构及摘要；缺包 KeyError、坏件 ValueError
    try:
        # 引用传递闭包
        included = set()
        stack = [id]
        while stack:
            x = stack.pop()
            if x in included:
                continue
            included.add(x)
            xk = _id_key(x)
            for (kind, tk, cj) in src._db.execute(
                    "SELECT kind,target,coords FROM refs WHERE id_key=?", (xk,)):
                if kind in ("a", "r", "s"):
                    t = _key_id(tk)
                    if t not in included:
                        stack.append(t)

        out_dir = os.path.dirname(os.path.abspath(p))
        os.makedirs(out_dir, exist_ok=True)  # 写入异常原抛
        fd, tmp = tempfile.mkstemp(prefix=".export-", suffix=".pack", dir=out_dir)
        os.close(fd)
        try:
            db = sqlite3.connect(tmp)
            try:
                _init_package(db)
                keys = sorted((_id_key(x) for x in included))
                db.executemany(
                    "INSERT INTO arrays VALUES(?,?,?,?,?)",
                    [tuple(r) for k in keys for r in src._db.execute(
                        "SELECT id_key,h,w,bh,bw FROM arrays WHERE id_key=?", (k,))])
                db.executemany(
                    "INSERT INTO aliases VALUES(?,?)",
                    [tuple(r) for k in keys for r in src._db.execute(
                        "SELECT path,id_key FROM aliases WHERE id_key=?", (k,))])
                db.executemany(
                    "INSERT INTO scalars VALUES(?,?,?,?)",
                    [tuple(r) for k in keys for r in src._db.execute(
                        "SELECT id_key,r,c,v FROM scalars WHERE id_key=?", (k,))])
                db.executemany(
                    "INSERT INTO refs VALUES(?,?,?,?,?,?)",
                    [tuple(r) for k in keys for r in src._db.execute(
                        "SELECT id_key,r,c,kind,target,coords FROM refs WHERE id_key=?", (k,))])
                for k in keys:  # 块级流式拷贝，不整阵物化
                    for br, bc, rows_json in src._db.execute(
                            "SELECT br,bc,rows FROM blocks WHERE id_key=? ORDER BY br,bc", (k,)):
                        db.execute("INSERT INTO blocks VALUES(?,?,?,?)", (k, br, bc, rows_json))
                digest = _compute_digest(db)
                db.execute("INSERT INTO meta(key,value) VALUES('digest',?)", (digest,))
                db.commit()
            finally:
                db.close()
            os.replace(tmp, p)  # 写入异常原抛
        except Exception:
            try:
                os.unlink(tmp)
            except OSError:
                pass
            raise
    finally:
        src.close()
    return digest


# ---------------------------------------------------------------- CLI：setup / verify / demo

def _expect(exc, fn, *args, **kw):
    try:
        fn(*args, **kw)
    except exc:
        return
    raise AssertionError("应抛 %s: %s" % (exc.__name__, getattr(fn, "__name__", fn)))


def _selftest():
    import shutil

    tmp = tempfile.mkdtemp(prefix="pack-verify-")
    try:
        store = os.path.join(tmp, "store")
        A = {"m": (2, 3, 1, 2), "n": (2, 2, 1, 1), "z": (1, 1, 1, 1)}
        R = {
            "n": ({(0, 0): 7},
                  {(0, 1): None, (1, 0): ("a", "z"), (1, 1): ("s", "m", [(1, 2), (0, 1), (1, 2)])}),
            "z": ({}, {(0, 0): ("r", "n")}),  # n->z->n 成环，允许
        }
        L = {"/data/main": "m", "/alias/main": "m", "/data/other": "n"}

        def B():
            yield ("m", 0, 0, [[1, 2]])
            yield ("m", 0, 1, [[3]])
            yield ("m", 1, 1, [[6]])      # 乱序
            yield ("m", 1, 0, [[4, 5]])
            yield ("n", 0, 0, [[1]])
            yield ("n", 0, 1, [[2]])
            yield ("n", 1, 0, [[3]])
            yield ("n", 1, 1, [[4]])
            yield ("z", 0, 0, [[9]])

        no1, d1 = publish(store, "req-1", A, R, L, B())
        assert no1 == 1 and isinstance(d1, str) and d1.startswith("sha256:"), (no1, d1)

        # 同请求同逻辑内容复领
        assert publish(store, "req-1", A, R, L, B()) == (no1, d1)
        # 异请求同逻辑内容亦复领同一回执
        assert publish(store, "req-2", A, R, L, B()) == (no1, d1)
        # 同请求异绑拒绝（内容合法但不同）
        def B_bad():
            yield ("m", 0, 0, [[9, 9]])
            yield ("m", 0, 1, [[3]])
            yield ("m", 1, 0, [[4, 5]])
            yield ("m", 1, 1, [[6]])
            yield ("n", 0, 0, [[1]])
            yield ("n", 0, 1, [[2]])
            yield ("n", 1, 0, [[3]])
            yield ("n", 1, 1, [[4]])
            yield ("z", 0, 0, [[9]])
        _expect(ValueError, publish, store, "req-1", A, R, L, B_bad())
        # 新内容得新包号
        A3 = dict(A)
        A3["w"] = (1, 1, 1, 1)
        def B3():
            yield from B()
            yield ("w", 0, 0, [[5]])
        no3, _ = publish(store, "req-3", A3, R, L, B3())
        assert no3 == 2, no3

        pkgdir = os.path.join(store, _PKGDIR)
        pkg1 = [os.path.join(pkgdir, f) for f in os.listdir(pkgdir) if f.startswith("pack-1-")][0]

        h = open(pkg1)
        try:
            assert h.get("/data/main") == ("m", (2, 3, 1, 2))
            assert h.get("/alias/main") == ("m", (2, 3, 1, 2))  # 别名保身份
            assert h.read(None) is None
            assert h.read(("a", "m")) == "m"
            assert h.read(("r", "n")) == "n"
            # 题面用例：[[1,2,3],[4,5,6]] 切 1x2 块，[(1,2),(0,1),(1,2)] 读 [2,6]
            assert list(h.read(("s", "m", [(1, 2), (0, 1), (1, 2)]))) == [2, 6]
            assert h.check(("a", "m"), 0, 10) == (6, 21, 1, 6, True)
            assert h.check(("a", "m"), 0, 5) == (6, 21, 1, 6, False)
            assert h.check(None, 0, 1) == (0, 0, None, None, True)
            assert h.check(("s", "m", []), 0, 1) == (0, 0, None, None, True)
            # 标量覆盖块值；引用格原样读出
            assert list(h.read(("s", "n", [(0, 0)]))) == [7]
            vals = list(h.read(("s", "n", [(0, 1), (1, 0), (1, 1)])))
            assert vals[0] is None and vals[1] == ("a", "z")
            assert vals[2] == ("s", "m", ((0, 1), (1, 2))), vals
            c = h.check(("s", "n", [(0, 0), (0, 1)]), 0, 100)
            assert c[0] == 2 and c[1] == 7 and c[2] == 7 and c[3] == 7 and c[4] is False, c
            # 缺包 / 坏参
            _expect(KeyError, h.get, "/nope")
            _expect(ValueError, h.get, "relative/path")
            _expect(KeyError, h.read, ("a", "nope"))
            _expect(ValueError, h.read, "x")
            _expect(ValueError, h.read, ("s", "m", [(9, 9)]))
            _expect(ValueError, h.check, ("a", "m"), 5, 1)
            _expect(ValueError, h.check, ("a", "m"), True, 1)
        finally:
            h.close()
        _expect(KeyError, open, pkg1, "nope")
        _expect(KeyError, open, os.path.join(tmp, "missing.pack"))

        # 坏件：篡改内容 -> 摘要不匹配
        import shutil as _sh
        tampered = os.path.join(tmp, "tampered.pack")
        _sh.copyfile(pkg1, tampered)
        db = sqlite3.connect(tampered)
        db.execute("UPDATE blocks SET rows='[[8,8]]' WHERE id_key='\"m\"' AND br=0 AND bc=0")
        db.commit()
        db.close()
        _expect(ValueError, open, tampered)
        # 坏件：截断
        broken = os.path.join(tmp, "broken.pack")
        with _builtin_open(broken, "wb") as f:
            f.write(b"not a package")
        _expect(ValueError, open, broken)

        # 坏参：拒布尔、缺块、重块、越界、错型、祖先冲突、同格双表
        def B_bool():
            yield from B()
        bb = B_bool()
        next(bb)
        def B_bool2():
            yield ("m", 0, 0, [[True, 2]])
            yield from bb
        _expect(ValueError, publish, store, "req-bool", A, R, L, B_bool2())
        _expect(ValueError, publish, store, "req-dim", {"m": (0, 3, 1, 2)}, None, None,
                iter(()))
        _expect(ValueError, publish, store, "req-dim2", {"m": (2, 3, True, 2)}, None, None,
                iter(()))
        _expect(ValueError, publish, store, "req-miss", A, None, None,
                iter([("m", 0, 0, [[1, 2]])]))
        _expect(ValueError, publish, store, "req-dup", {"m": (1, 2, 1, 1)}, None, None,
                iter([("m", 0, 0, [[1]]), ("m", 0, 0, [[2]]), ("m", 0, 1, [[3]])]))
        _expect(ValueError, publish, store, "req-oob", {"m": (1, 1, 1, 1)}, None, None,
                iter([("m", 0, 1, [[1]])]))
        _expect(ValueError, publish, store, "req-shape", {"m": (1, 2, 1, 1)}, None, None,
                iter([("m", 0, 0, [[1, 2]]), ("m", 0, 1, [[3]])]))
        _expect(ValueError, publish, store, "req-anc", {"m": (1, 1, 1, 1)}, None,
                {"/a": "m", "/a/b": "m"}, iter([("m", 0, 0, [[1]])]))
        _expect(ValueError, publish, store, "req-rel", {"m": (1, 1, 1, 1)}, None,
                {"rel/path": "m"}, iter([("m", 0, 0, [[1]])]))
        _expect(ValueError, publish, store, "req-both", {"m": (1, 1, 1, 1)},
                {"m": ({(0, 0): 1}, {(0, 0): None})}, None, iter([("m", 0, 0, [[1]])]))
        _expect(ValueError, publish, store, "req-reft", {"m": (1, 1, 1, 1)},
                {"m": (None, {(0, 0): ("a", "nope")})}, None, iter([("m", 0, 0, [[1]])]))
        _expect(ValueError, publish, store, "req-refc", {"m": (1, 1, 1, 1)},
                {"m": (None, {(0, 0): ("s", "m", [(5, 5)])})}, None, iter([("m", 0, 0, [[1]])]))
        _expect(ValueError, publish, store, "req-refty", {"m": (1, 1, 1, 1)},
                {"m": (None, {(0, 0): 42})}, None, iter([("m", 0, 0, [[1]])]))
        _expect(ValueError, publish, store, "req-sbool", {"m": (1, 1, 1, 1)},
                {"m": ({(0, 0): False}, None)}, None, iter([("m", 0, 0, [[1]])]))

        # 失败无新回执、无可开残件
        before = set(os.listdir(pkgdir))
        _expect(ValueError, publish, store, "req-fail", A, None, None,
                iter([("m", 0, 0, [[1, 2]])]))
        assert set(os.listdir(pkgdir)) == before, os.listdir(pkgdir)
        reg = sqlite3.connect(os.path.join(store, _REGISTRY))
        n_req = reg.execute("SELECT COUNT(*) FROM requests").fetchone()[0]
        reg.close()
        assert n_req == 3, n_req  # req-1/2/3；复领不新增，失败不留回执

        # export：自足、断源可开
        exp1 = os.path.join(tmp, "only-m.pack")
        dexp = export(store, "m", exp1)
        assert isinstance(dexp, str) and dexp.startswith("sha256:")
        exp2 = os.path.join(tmp, "closure.pack")
        export(store, "n", exp2)
        _expect(KeyError, export, store, "nope", os.path.join(tmp, "x.pack"))
        failed_export = os.path.join(tmp, "sub", "x.pack")
        _expect(KeyError, export, store, "nope", failed_export)
        assert not os.path.exists(failed_export)

        shutil.rmtree(store)  # 断源
        h1 = open(exp1)
        try:
            assert h1.get("/data/main") == ("m", (2, 3, 1, 2))
            assert list(h1.read(("s", "m", [(1, 2), (0, 1), (1, 2)]))) == [2, 6]
            assert h1.check(("a", "m"), 0, 10) == (6, 21, 1, 6, True)
            _expect(KeyError, h1.get, "/data/other")  # 未随包导出
        finally:
            h1.close()
        h2 = open(exp2)
        try:
            # n 的闭包含 z、m（成环亦可自足）
            assert list(h2.read(("s", "n", [(0, 0)]))) == [7]
            assert h2.read(("a", "z")) == "z"
            assert h2.check(("a", "m"), 0, 10) == (6, 21, 1, 6, True)
            assert h2.get("/alias/main") == ("m", (2, 3, 1, 2))
        finally:
            h2.close()
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def _demo():
    import shutil

    tmp = tempfile.mkdtemp(prefix="pack-demo-")
    store = os.path.join(tmp, "store")
    print("[demo] 质控整包交接：发布 -> 导出 -> 断源 -> 核验")
    A = {"raw": (2, 3, 1, 2), "clean": (2, 2, 1, 1)}
    R = {"clean": ({(0, 0): 100},
                   {(0, 1): ("a", "raw"), (1, 1): ("s", "raw", [(1, 2), (0, 1), (1, 2)])})}
    L = {"/qc/raw": "raw", "/qc/clean": "clean", "/handover/clean": "clean"}

    def B():
        yield ("raw", 0, 0, [[1, 2]])
        yield ("raw", 0, 1, [[3]])
        yield ("raw", 1, 0, [[4, 5]])
        yield ("raw", 1, 1, [[6]])
        yield ("clean", 0, 0, [[5]])
        yield ("clean", 0, 1, [[6]])
        yield ("clean", 1, 0, [[7]])
        yield ("clean", 1, 1, [[8]])

    no, digest = publish(store, "handover-2026-11", A, R, L, B())
    print("[demo] 发布回执：包号=%d 摘要=%s" % (no, digest))
    again = publish(store, "handover-2026-11", A, R, L, B())
    print("[demo] 同请求同内容复领：%s（回执一致）" % (again == (no, digest)))

    handover = os.path.join(tmp, "handover.pack")
    d2 = export(store, "clean", handover)
    print("[demo] 导出自足包：%s（摘要 %s）" % (handover, d2[:23] + "..."))

    shutil.rmtree(store)  # 断源：来源库整体移除
    print("[demo] 已断源：来源库 %s 已删除" % store)

    h = open(handover)
    try:
        got = h.get("/handover/clean")
        vals = list(h.read(("s", "raw", [(1, 2), (0, 1), (1, 2)])))
        stats = h.check(("a", "raw"), 0, 100)
        overlay = list(h.read(("s", "clean", [(0, 0), (0, 1), (1, 1)])))
        print("[demo] 断源后 get('/handover/clean') -> %r" % (got,))
        print("[demo] 断源后 read(('s','raw',[(1,2),(0,1),(1,2)])) -> %r" % (vals,))
        print("[demo] 断源后 check(('a','raw'),0,100) -> %r" % (stats,))
        print("[demo] 断源后 clean 覆盖格读出 -> %r" % (overlay,))
        assert got == ("clean", (2, 2, 1, 1))
        assert vals == [2, 6]
        assert stats == (6, 21, 1, 6, True)
        assert overlay[0] == 100 and overlay[1] == ("a", "raw")
    finally:
        h.close()
        shutil.rmtree(tmp, ignore_errors=True)
    print("[demo] 断源核验通过")


def main(argv):
    if len(argv) < 2 or argv[1] not in ("setup", "verify", "demo"):
        sys.stderr.write("usage: python3 pack.py {setup|verify|demo}\n")
        return 2
    cmd = argv[1]
    if cmd == "setup":
        if sys.version_info < (3, 7):
            sys.stderr.write("需要 Python >= 3.7\n")
            return 1
        print("setup ok: 仅依赖标准库（sqlite3），无需安装")
        return 0
    if cmd == "verify":
        try:
            _selftest()
        except Exception as e:  # noqa: BLE001 - 统一以非零退出报告失败
            import traceback
            traceback.print_exc()
            print("verify FAILED: %r" % (e,))
            return 1
        print("verify ok")
        return 0
    _demo()
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
