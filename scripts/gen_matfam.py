#!/usr/bin/env python3
"""Find a one-parameter family of bricks for a thin shape and emit a Lean proof
that the shape is representation-infinite (via `RayCat.MatFam`).

Usage (needs sympy; run with /usr/bin/python3):
  gen_matfam.py SPEC.json NAME OUT.lean [SEED]

The family has the null root of the Euler form as dimension vector, entries in
{0, 1, -1} except one entry `t` on an arrow outside all relations. It is
accepted when the endomorphism and Hom systems have the right rank over Q, F2
and F3 and the certificates have primitive denominators that factor into
monic linear factors (and `t - s` for Hom). Certificates are emitted as
`linear_combination` steps.
"""
import json, sys, random, itertools
from fractions import Fraction as Fr

def load(path):
    s = json.load(open(path))
    V = s['verts']; A = [(a, b) for a, b, _ in s['arrows']]
    Z = set(tuple(p) for p in s.get('zero', []))
    return V, A, Z

def reach(V, A):
    R = {v: {v} for v in V}
    ch = True
    while ch:
        ch = False
        for (a, b) in A:
            for v in V:
                if a in R[v] and b not in R[v]:
                    R[v].add(b); ch = True
    return R

def paths(V, A, x, z):
    out = []
    def go(v, p):
        if v == z: out.append(p); return
        for (a, b) in A:
            if a == v: go(b, p + [(a, b)])
    go(x, [])
    return out

def le_table(V, A, Z):
    R = reach(V, A)
    return {(x, y): (y in R[x] and (x, y) not in Z) for x in V for y in V}, R

# exact linear algebra over Fractions
def rank(rows, ncols):
    M = [r[:] for r in rows]; r = 0
    for c in range(ncols):
        p = None
        for i in range(r, len(M)):
            if M[i][c] != 0: p = i; break
        if p is None: continue
        M[r], M[p] = M[p], M[r]
        inv = 1 / M[r][c]
        M[r] = [v * inv for v in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]; M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        r += 1
    return r

def nullity(rows, n): return n - rank(rows, n)

def euler_radical(V, le):
    n = len(V); idx = {v: i for i, v in enumerate(V)}
    # Cartan C[x][y] = le x y ; Euler form matrix E = C^{-1}
    C = [[Fr(1 if le[(V[i], V[j])] else 0) for j in range(n)] for i in range(n)]
    # invert
    M = [C[i][:] + [Fr(1 if i == j else 0) for j in range(n)] for i in range(n)]
    for c in range(n):
        p = next(i for i in range(c, n) if M[i][c] != 0)
        M[c], M[p] = M[p], M[c]
        iv = 1 / M[c][c]; M[c] = [v * iv for v in M[c]]
        for i in range(n):
            if i != c and M[i][c] != 0:
                f = M[i][c]; M[i] = [a - f * b for a, b in zip(M[i], M[c])]
    Ci = [row[n:] for row in M]
    S = [[Ci[i][j] + Ci[j][i] for j in range(n)] for i in range(n)]
    return S

def kernel(S):
    n = len(S); M = [r[:] for r in S]; piv = []; r = 0
    for c in range(n):
        p = next((i for i in range(r, n) if M[i][c] != 0), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]; iv = 1 / M[r][c]; M[r] = [v * iv for v in M[r]]
        for i in range(n):
            if i != r and M[i][c] != 0:
                f = M[i][c]; M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        piv.append(c); r += 1
    free = [c for c in range(n) if c not in piv]
    basis = []
    for f in free:
        v = [Fr(0)] * n; v[f] = Fr(1)
        for i, c in enumerate(piv): v[c] = -M[i][f]
        basis.append(v)
    return basis

# ---------- representation search ----------
def matmul(X, Y):
    n, m, p = len(X), len(Y), (len(Y[0]) if Y else 0)
    return [[sum((X[i][k] * Y[k][j] for k in range(m)), Fr(0)) for j in range(p)] for i in range(n)]

def ident(n): return [[Fr(1 if i == j else 0) for j in range(n)] for i in range(n)]
def zeros(r, c): return [[Fr(0)] * c for _ in range(r)]

class Shape:
    def __init__(s, path, dims=None):
        s.V, s.A, s.Z = load(path)
        s.le, s.R = le_table(s.V, s.A, s.Z)
        if dims is None:
            K = kernel(euler_radical(s.V, s.le))[0]
            if any(x < 0 for x in K): K = [-x for x in K]
            from math import lcm
            L = 1
            for x in K: L = lcm(L, x.denominator)
            dims = [int(x * L) for x in K]
        s.d = dict(zip(s.V, dims))
        # constraints: for each reachable (x,z), x != z: all paths
        s.cons = []
        for x in s.V:
            for z in s.V:
                if x == z or z not in s.R[x]: continue
                ps = paths(s.V, s.A, x, z)
                good = [p for p in ps if s.nonzero_path(p)]
                bad = [p for p in ps if not s.nonzero_path(p)]
                for p in bad: s.cons.append(('zero', p, None))
                for p in good[1:]: s.cons.append(('eq', p, good[0]))
    def nonzero_path(s, p):
        vs = [p[0][0]] + [b for (_, b) in p]
        return all(s.le[(vs[i], vs[j])] for i in range(len(vs)) for j in range(i + 1, len(vs)))
    def prod(s, M, p):
        x = p[0][0]; P = ident(s.d[x])
        for a in p: P = matmul(M[a], P)
        return P
    def check(s, M):
        for kind, p, q in s.cons:
            P = s.prod(M, p)
            Q = zeros(len(P), len(P[0]) if P else 0) if kind == 'zero' else s.prod(M, q)
            if P != Q: return False
        return True

def solve_affine(eqs, n):
    # eqs: list of (coeffs list len n, rhs); return (particular, nullbasis) or None
    M = [list(c) + [r] for c, r in eqs]; piv = []; r = 0
    for c in range(n):
        p = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]; iv = 1 / M[r][c]; M[r] = [v * iv for v in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]; M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        piv.append(c); r += 1
    for i in range(r, len(M)):
        if M[i][n] != 0: return None
    part = [Fr(0)] * n
    for i, c in enumerate(piv): part[c] = M[i][n]
    free = [c for c in range(n) if c not in piv]
    basis = []
    for f in free:
        v = [Fr(0)] * n; v[f] = Fr(1)
        for i, c in enumerate(piv): v[c] = -M[i][f]
        basis.append(v)
    return part, basis

def search(s, order, rng, rngvals=(-1, 0, 1, 1, 2)):
    M = {}
    for i, a in enumerate(order):
        r, c = s.d[a[1]], s.d[a[0]]
        n = r * c
        # constraints fully inside chosen arrows and involving a
        chosen = set(order[:i + 1])
        rel = [k for k in s.cons if a in k[1] + (k[2] or []) and set(k[1] + (k[2] or [])) <= chosen]
        if not rel:
            M[a] = [[Fr(rng.choice(rngvals)) for _ in range(c)] for _ in range(r)]
            continue
        # linear in entries of M[a]: evaluate with basis matrices
        def evalc(X):
            M2 = dict(M); M2[a] = X
            out = []
            for kind, p, q in rel:
                P = s.prod(M2, p)
                Q = zeros(len(P), len(P[0])) if kind == 'zero' else s.prod(M2, q)
                out += [P[ii][jj] - Q[ii][jj] for ii in range(len(P)) for jj in range(len(P[0]))]
            return out
        base = evalc(zeros(r, c))
        cols = []
        for e in range(n):
            X = zeros(r, c); X[e // c][e % c] = Fr(1)
            v = evalc(X); cols.append([vi - bi for vi, bi in zip(v, base)])
        eqs = [([cols[e][k] for e in range(n)], -base[k]) for k in range(len(base))]
        sol = solve_affine(eqs, n)
        if sol is None: return None
        part, basis = sol
        x = part[:]
        for b in basis:
            co = rng.choice(rngvals)
            x = [xi + co * bi for xi, bi in zip(x, b)]
        M[a] = [[x[ii * c + jj] for jj in range(c)] for ii in range(r)]
    return M

def end_eqs(s, M1, M2):
    # unknowns G_v (d_v x d_v); equations G_y M1_a - M2_a G_x = 0
    idx = {}; n = 0
    for v in s.V:
        for i in range(s.d[v]):
            for j in range(s.d[v]):
                idx[(v, i, j)] = n; n += 1
    rows = []
    for a in s.A:
        x, y = a
        for i in range(s.d[y]):
            for j in range(s.d[x]):
                row = [Fr(0)] * n
                for k in range(s.d[y]): row[idx[(y, i, k)]] += M1[a][k][j]
                for k in range(s.d[x]): row[idx[(x, k, j)]] -= M2[a][i][k]
                rows.append(row)
    return rows, n, idx

def subst(M, a, i, j, val):
    M2 = {b: [r[:] for r in M[b]] for b in M}
    M2[a][i][j] = Fr(val)
    return M2

def good_family(s, M, a, i, j, ts=(2, 3, 5, 7, 11)):
    reps = {t: subst(M, a, i, j, t) for t in ts}
    for t in ts:
        if not s.check(reps[t]): return False
        rows, n, _ = end_eqs(s, reps[t], reps[t])
        if nullity(rows, n) != 1: return False
    for t in ts[:3]:
        for u in ts[:3]:
            if t != u:
                rows, n, _ = end_eqs(s, reps[t], reps[u])
                if nullity(rows, n) != 0: return False
    return True

def simplify(s, M, a, i, j, rng, passes=3):
    entries = [(b, r, c) for b in s.A for r in range(len(M[b])) for c in range(len(M[b][0])) if (b, r, c) != (a, i, j)]
    for _ in range(passes):
        rng.shuffle(entries)
        changed = False
        for (b, r, c) in entries:
            cur = M[b][r][c]
            for v in (0, 1, -1):
                if cur == v: break
                M2 = {x: [row[:] for row in M[x]] for x in M}; M2[b][r][c] = Fr(v)
                if s.check(subst(M2, a, i, j, 2)) and good_family(s, M2, a, i, j):
                    M = M2; changed = True; break
        if not changed: break
    return M

def find_family(path, seed=1, trials=400):
    s = Shape(path)
    rng = random.Random(seed)
    free = [a for a in s.A if not any(a in k[1] + (k[2] or []) for k in s.cons)]
    for trial in range(trials):
        order = s.A[:]; rng.shuffle(order)
        M = search(s, order, rng)
        if M is None or not s.check(M): continue
        rows, n, idx = end_eqs(s, M, M)
        if nullity(rows, n) != 1: continue
        for a in free:
            for i in range(s.d[a[1]]):
                for j in range(s.d[a[0]]):
                    if good_family(s, M, a, i, j):
                        M = simplify(s, M, a, i, j, rng)
                        return s, M, (a, i, j)
    return s, None, None

def show(s, M, par):
    a, i, j = par
    for b in s.A:
        rows = [['t' if (b, r, c) == (a, i, j) else str(M[b][r][c]) for c in range(len(M[b][0]))] for r in range(len(M[b]))]
        print(' ', b, rows)

def unit_entries(M):
    return all(x in (-1, 0, 1) for b in M for r in M[b] for x in r)

def find_family01(path, seed=1, trials=3000):
    s = Shape(path)
    rng = random.Random(seed)
    free = [a for a in s.A if not any(a in k[1] + (k[2] or []) for k in s.cons)]
    for trial in range(trials):
        order = s.A[:]; rng.shuffle(order)
        M = search(s, order, rng, rngvals=(-1, 0, 1, 1, 0))
        if M is None or not unit_entries(M) or not s.check(M): continue
        rows, n, idx = end_eqs(s, M, M)
        if nullity(rows, n) != 1: continue
        for a in free:
            for i in range(s.d[a[1]]):
                for j in range(s.d[a[0]]):
                    if good_family(s, M, a, i, j):
                        M = simplify(s, M, a, i, j, rng)
                        return s, M, (a, i, j), trial
    return s, None, None, trials


# ---------- certificates ----------
import sympy as sp
from sympy.polys.matrices import DomainMatrix

tt, ss = sp.symbols('t s')

def sym_rep(sh, M, par, sym):
    a, i, j = par
    return {b: [[sym if (b, r, c) == (a, i, j) else sp.Integer(int(M[b][r][c]))
                 for c in range(len(M[b][0]))] for r in range(len(M[b]))] for b in sh.A}

def eq_rows(sh, M1, M2, K, unk):
    n = len(unk); pos = {u: k for k, u in enumerate(unk)}
    rows = []; labels = []
    for a in sh.A:
        x, y = a
        for i in range(sh.d[y]):
            for j in range(sh.d[x]):
                row = [K.zero] * n
                for k in range(sh.d[y]): row[pos[(y, i, k)]] += K.convert(M1[a][k][j])
                for k in range(sh.d[x]): row[pos[(x, k, j)]] -= K.convert(M2[a][i][k])
                if any(v != K.zero for v in row):
                    rows.append(row); labels.append((a, i, j))
    return rows, labels

def rref_track(rows, n, K):
    m = len(rows)
    aug = [rows[r] + [K.one if c == r else K.zero for c in range(m)] for r in range(m)]
    R, piv = DomainMatrix(aug, (m, n + m), K).rref()
    return R.to_Matrix(), piv

def rank_over(sh, M1, M2, K, unk):
    rows, _ = eq_rows(sh, M1, M2, K, unk)
    if not rows: return 0
    _, piv = DomainMatrix(rows, (len(rows), len(unk)), K).rref()
    return len(piv)

def lin_factors(expr, var):
    """Factor a polynomial in ZZ[var] into monic linear factors; None if impossible."""
    c, fl = sp.factor_list(sp.expand(expr), var)
    if c not in (1, -1): return None
    out = []
    for f, m in fl:
        P = sp.Poly(f, var)
        if P.degree() != 1 or P.LC() not in (1, -1): return None
        if P.LC() == -1: f = -f
        out.append((sp.expand(f), m))
    return out

def accept(sh, M, par):
    vs = sh.V
    x0 = vs[0]
    unk_e = [(v, i, j) for v in vs for i in range(sh.d[v]) for j in range(sh.d[v]) if (v, i, j) != (x0, 0, 0)] + [(x0, 0, 0)]
    ones = [v for v in vs if sh.d[v] == 1]
    x1 = ones[0] if ones else vs[0]
    unk_h = [(v, i, j) for v in vs for i in range(sh.d[v]) for j in range(sh.d[v]) if (v, i, j) != (x1, 0, 0)] + [(x1, 0, 0)]
    n = len(unk_e)
    for p in (2, 3):
        K = sp.GF(p).frac_field(tt)
        R1 = sym_rep(sh, M, par, tt)
        if rank_over(sh, R1, R1, K, unk_e) != n - 1: return None
        K2 = sp.GF(p).frac_field(tt, ss)
        if rank_over(sh, R1, sym_rep(sh, M, par, ss), K2, unk_h) != n: return None
    # End certificates over Q(t)
    K = sp.QQ.frac_field(tt)
    R1 = sym_rep(sh, M, par, tt)
    rows, labels = eq_rows(sh, R1, R1, K, unk_e)
    Rm, piv = rref_track(rows, n, K)
    m = len(rows)
    if len([q for q in piv if q < n]) != n - 1: return None
    endc = {}
    bad = {}
    for r, q in enumerate(piv):
        if q >= n: break
        u = unk_e[q]
        # row: u + coef * c = sum lam_e e ; check coef
        coef = Rm[r, n - 1]
        target = 1 if u[1] == u[2] else 0
        if sp.simplify(coef + target) != 0: return None
        lams = [sp.together(Rm[r, n + e]) for e in range(m)]
        den = sp.Integer(1)
        for l in lams:
            if l != 0: den = sp.lcm(den, sp.denom(l))
        den = sp.factor(den)
        fl = lin_factors(den, tt)
        if fl is None: return None
        D = sp.Integer(1)
        for f, mult in fl:
            D *= f ** mult
            bad[f] = max(bad.get(f, 0), 1)
        cs = [(e, sp.expand(sp.cancel(lams[e] * D))) for e in range(m) if lams[e] != 0]
        for _, c in cs:
            if any(not co.is_integer for co in sp.Poly(c, tt).coeffs()): return None
        endc[u] = (sp.expand(D), target, cs)
    # Hom certificate over Q(t, s)
    K2 = sp.QQ.frac_field(tt, ss)
    R2 = sym_rep(sh, M, par, ss)
    hrows, hlabels = eq_rows(sh, R1, R2, K2, unk_h)
    Rh, hpiv = rref_track(hrows, n, K2)
    hm = len(hrows)
    if len([q for q in hpiv if q < n]) != n: return None
    r = n - 1
    if hpiv[r] != n - 1: return None
    lams = [sp.together(Rh[r, n + e]) for e in range(hm)]
    den = sp.Integer(1)
    for l in lams:
        if l != 0: den = sp.lcm(den, sp.denom(l))
    c, fl = sp.factor_list(sp.expand(den), tt, ss)
    if c not in (1, -1): return None
    hfac = []
    for f, mult in fl:
        f = sp.expand(f)
        if sp.expand(f - (tt - ss)) == 0 or sp.expand(f + (tt - ss)) == 0:
            hfac.append(('ts', tt - ss, mult)); continue
        fs = f.free_symbols
        if fs == {tt}:
            g = lin_factors(f, tt)
            if g is None: return None
            for (h, mm) in g: hfac.append(('t', h, mult * mm)); bad[h] = 1
        elif fs == {ss}:
            g = lin_factors(f.subs(ss, tt), tt)
            if g is None: return None
            for (h, mm) in g: hfac.append(('s', h.subs(tt, ss), mult * mm)); bad[h] = 1
        else:
            return None
    D = sp.Integer(1)
    for _, f, mult in hfac: D *= f ** mult
    hcs = [(e, sp.expand(sp.cancel(lams[e] * D))) for e in range(hm) if lams[e] != 0]
    for _, cc in hcs:
        if any(not co.is_integer for co in sp.Poly(cc, tt, ss).coeffs()): return None
    return dict(x0=x0, x1=x1, endc=endc, labels=labels, hlabels=hlabels, hcert=(D, hfac, hcs), bad=bad)

def find_accepted(path, seed=1, trials=4000):
    s = Shape(path)
    rng = random.Random(seed)
    free = [a for a in s.A if not any(a in k[1] + (k[2] or []) for k in s.cons)]
    tried = 0
    for trial in range(trials):
        order = s.A[:]; rng.shuffle(order)
        M = search(s, order, rng, rngvals=(-1, 0, 1, 1, 0))
        if M is None or not unit_entries(M) or not s.check(M): continue
        rows, n, idx = end_eqs(s, M, M)
        if nullity(rows, n) != 1: continue
        for a in free:
            for i in range(s.d[a[1]]):
                for j in range(s.d[a[0]]):
                    if good_family(s, M, a, i, j):
                        M2 = simplify(s, M, a, i, j, rng)
                        if not unit_entries(M2): continue
                        tried += 1
                        res = accept(s, M2, (a, i, j))
                        if res is not None:
                            return s, M2, (a, i, j), res
                        if tried > 40: return s, None, None, None
    return s, None, None, None

# ---------- Lean emission ----------
SIMPSET = ("fam, MatFam.mk', Mf, dim, Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, "
           "Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_succ, "
           "Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_one, Fin.succ_zero_eq_one, "
           "Fin.succ_one_eq_two, Fin.reduceSucc, Matrix.cons_val, mul_zero, mul_one, zero_mul, one_mul, "
           "add_zero, zero_add, neg_mul, mul_neg, neg_zero")

def lean_poly(e):
    e = sp.expand(e)
    return str(e).replace('**', '^')

def lean_mat(rows):
    return '!![' + '; '.join(', '.join(lean_poly(x) for x in r) for r in rows) + ']'

def all_mats(sh, R1):
    """Matrices for all comparable pairs (product along a nonzero path)."""
    out = {}
    for x in sh.V:
        for y in sh.V:
            if x == y or not sh.le[(x, y)]: continue
            p = next(p for p in paths(sh.V, sh.A, x, y) if sh.nonzero_path(p))
            P = sp.eye(sh.d[x])
            for a in p: P = sp.Matrix(R1[a]) * P
            out[(x, y)] = [[sp.expand(P[i, j]) for j in range(P.shape[1])] for i in range(P.shape[0])]
    return out

def factor_str(f, var='t'):
    return '(' + lean_poly(f).replace('t', var) + ')'

def emit(sh, M, par, res, N, out, doc):
    q = lambda v: f'{N}.{v}'
    R1 = sym_rep(sh, M, par, tt)
    mats = all_mats(sh, R1)
    L = []
    L.append('module\n')
    L.append('public import LargeIndecomposable.Cleaving.Basic.MatFam')
    L.append(f'public import LargeIndecomposable.Cleaving.Shapes.Shape{N}\n')
    L.append('/-!')
    L.append(f'# `{N}` is representation-infinite\n')
    L.append(doc)
    L.append('A one-parameter family of bricks of dimension the null root of the Euler')
    L.append('form, with integral certificates for "endomorphisms are scalars" and "maps')
    L.append('between different members vanish at one vertex".\n')
    L.append('Generated by `scripts/gen_matfam.py`.')
    L.append('-/\n')
    L.append('@[expose] public section\n')
    L.append('set_option autoImplicit false')
    L.append('set_option linter.unusedSimpArgs false')
    L.append('set_option linter.unnecessarySeqFocus false')
    L.append('set_option maxHeartbeats 0\n')
    L.append('noncomputable section\n')
    L.append('namespace LargeIndecomposable\n')
    L.append('open CategoryTheory Limits RayQuiver Polynomial\n')
    L.append('namespace RayCat\n')
    L.append(f'namespace {N}\n')
    L.append('variable {k : Type*} [Field k]\n')
    L.append('/-- The dimension vector. -/')
    L.append(f'abbrev dim : {N} → ℕ')
    for v in sh.V: L.append(f'  | .{v} => {sh.d[v]}')
    L.append('')
    L.append('/-- The matrices of the member `t`. -/')
    L.append(f'def Mf (t : k) : ∀ u v : {N}, Matrix (Fin (dim v)) (Fin (dim u)) k')
    for x in sh.V:
        for y in sh.V:
            if x == y: L.append(f'  | .{x}, .{y} => 1')
            elif (x, y) in mats: L.append(f'  | .{x}, .{y} => {lean_mat(mats[(x, y)])}')
            else: L.append(f'  | .{x}, .{y} => 0')
    L.append('')
    bad = list(res['bad'].keys())
    def poly_term(f):
        c = sp.Poly(f, tt).all_coeffs()[-1]
        if c == 0: return 'X'
        if c > 0: return f'(X + C {c})'
        return f'(X - C {-c})'
    def monic_term(f):
        c = sp.Poly(f, tt).all_coeffs()[-1]
        if c == 0: return 'monic_X'
        if c > 0: return f'(monic_X_add_C {c})'
        return f'(monic_X_sub_C {-c})'
    L.append('/-- The excluded parameters. -/')
    if bad:
        L.append('def bad : Polynomial k := ' + ' * '.join(poly_term(f) for f in bad) + '\n')
        mon = monic_term(bad[0])
        for f in bad[1:]: mon = f'({mon}.mul {monic_term(f)})'
    else:
        L.append('def bad : Polynomial k := 1\n')
        mon = 'monic_one'
    L.append('/-- The family. -/')
    L.append(f'abbrev fam : MatFam {N}.thin k {{t : k // bad.eval t ≠ 0}} :=')
    L.append('  MatFam.mk\' dim (fun t ↦ Mf t.1) (fun t u ↦ by cases u <;> simp only [Mf]) (by')
    L.append('    rintro ⟨t, -⟩ u v w h1 h2 h3 h4')
    L.append('    cases u <;> cases v <;> cases w <;>')
    L.append('      first')
    L.append('      | exact absurd rfl h1')
    L.append('      | exact absurd rfl h2')
    L.append('      | exact absurd h3 (by decide)')
    L.append('      | exact absurd h4 (by decide)')
    L.append('      | (split_ifs with hn <;>')
    L.append('          first')
    L.append('          | exact absurd hn (by decide)')
    L.append('          | (ext i j; fin_cases i <;> fin_cases j <;>')
    L.append('              simp [Mf, dim, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring)))\n')
    # main theorem
    L.append(f'/-- **`{N}` is representation-infinite.** -/')
    L.append('theorem not_isRepresentationFinite [Infinite k] :')
    L.append(f'    ¬Statement.IsRepresentationFinite (Linearization (ThinCat {N}.thin) k) := by')
    L.append(f'  have hbad : (bad : Polynomial k) ≠ 0 := {mon}.ne_zero')
    L.append('  have := infinite_nonroot bad hbad')
    x0, x1 = res['x0'], res['x1']
    L.append(f'  refine fam.not_isRepresentationFinite {q(x1)} (by show 0 < dim {q(x1)}; decide) ?_ ?_')
    # factor facts helper
    badprod = ' * '.join(factor_str(f) for f in bad) if bad else '1'
    def factor_facts(var, hyp, needed, ind):
        lines = []
        names = {}
        for idx, f in enumerate(bad):
            if f not in needed: continue
            others = [g for g in bad if g != f]
            Q = ' * '.join(factor_str(g, var) for g in others) if others else '1'
            nm = f'hf{var}{idx}'
            names[f] = nm
            lines.append(f'{ind}have {nm} : {factor_str(f, var)} ≠ 0 := fun h ↦ {hyp} (by linear_combination ({Q}) * h)')
        return lines, names
    # ---- End part
    L.append('  · rintro ⟨t, ht⟩ G hG')
    if bad:
        L.append('    simp only [bad, eval_mul, eval_X, eval_add, eval_sub, eval_C] at ht')
    needed = set()
    for u, (D, target, cs) in res['endc'].items():
        for f in bad:
            if sp.rem(sp.Poly(D, tt), sp.Poly(f, tt)).is_zero and D != 1: needed.add(f)
    fl, fnames = factor_facts('t', 'ht', needed, '    ')
    L += fl
    dnames = {}
    for u, (D, target, cs) in res['endc'].items():
        key = sp.srepr(D)
        if key in dnames: continue
        nm = f'hD{len(dnames)}'
        dnames[key] = nm
        if D == 1:
            L.append(f'    have {nm} : (1 : k) ≠ 0 := one_ne_zero')
        else:
            fl2 = lin_factors(D, tt)
            Ds = ' * '.join(f'{factor_str(f)} ^ {m}' for f, m in fl2)
            facts = ', '.join(fnames[f] for f, m in fl2)
            L.append(f'    have {nm} : {Ds} ≠ 0 := by apply_rules [mul_ne_zero, pow_ne_zero, {facts}]')
    labels = res['labels']
    for k_, (a, i, j) in enumerate(labels):
        x, y = a
        L.append(f'    have e{k_} := congrFun (congrFun (hG {q(x)} {q(y)} (by decide)) ({i} : Fin {sh.d[y]})) ({j} : Fin {sh.d[x]})')
    L.append(f'    simp only [{SIMPSET}] at ' + ' '.join(f'e{k_}' for k_ in range(len(labels))))
    c_str = f'G {q(x0)} (0 : Fin {sh.d[x0]}) (0 : Fin {sh.d[x0]})'
    def Dstr(D):
        if D == 1: return '1'
        return ' * '.join(f'{factor_str(f)} ^ {m}' for f, m in lin_factors(D, tt))
    gnames = {}
    for v in sh.V:
        dv = sh.d[v]
        for i in range(dv):
            for j in range(dv):
                u = (v, i, j)
                nm = f'g_{len(gnames)}'
                gnames[u] = nm
                head = f'    have {nm} : G {q(v)} ({i} : Fin {dv}) ({j} : Fin {dv}) = ({c_str} • (1 : Matrix (Fin {dv}) (Fin {dv}) k)) {i} {j} := by'
                L.append(head)
                if u == (x0, 0, 0):
                    L.append('      rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]')
                    continue
                D, target, cs = res['endc'][u]
                comb = ' + '.join(f'({lean_poly(c)}) * e{e}' for e, c in cs) if cs else '0'
                hD = dnames[sp.srepr(D)]
                if i == j:
                    L.append('      rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]')
                    L.append(f'      exact eq_of_mul_sub_eq_zero {hD} (by linear_combination {comb})')
                else:
                    L.append('      rw [Matrix.smul_apply, Matrix.one_apply_ne (by decide), smul_zero]')
                    L.append(f'      exact eq_zero_of_mul_eq_zero {hD} (by linear_combination {comb})')
    L.append(f'    refine ⟨{c_str}, fun v ↦ ?_⟩')
    L.append('    match v with')
    for v in sh.V:
        dv = sh.d[v]
        gl = ', '.join(gnames[(v, i, j)] for i in range(dv) for j in range(dv))
        L.append(f'    | .{v} => exact Matrix.ext fun (i j : Fin {dv}) ↦ by fin_cases i <;> fin_cases j; exacts [{gl}]')
    # ---- Hom part
    D, hfac, hcs = res['hcert']
    L.append('  · rintro ⟨t, ht⟩ ⟨s, hs⟩ G hG hne')
    if bad:
        L.append('    simp only [bad, eval_mul, eval_X, eval_add, eval_sub, eval_C] at ht hs')
    L.append('    have hts : t - s ≠ 0 := sub_ne_zero.2 fun h ↦ hne (Subtype.ext h)')
    need_t = set(); need_s = set()
    for kind, f, m in hfac:
        if kind == 't': need_t.add(sp.expand(f))
        if kind == 's': need_s.add(sp.expand(f.subs(ss, tt)))
    fl, fnt = factor_facts('t', 'ht', need_t, '    '); L += fl
    fl, fns = factor_facts('s', 'hs', need_s, '    '); L += fl
    parts = []; facts = ['hts']
    for kind, f, m in hfac:
        if kind == 'ts': parts.append(f'(t - s) ^ {m}')
        elif kind == 't':
            parts.append(f'{factor_str(f)} ^ {m}'); facts.append(fnt[sp.expand(f)])
        else:
            g = sp.expand(f.subs(ss, tt)); parts.append(f'{factor_str(g, "s")} ^ {m}'); facts.append(fns[g])
    Ds = ' * '.join(parts) if parts else '1'
    L.append(f'    have hD : {Ds} ≠ 0 := by apply_rules [mul_ne_zero, pow_ne_zero, {", ".join(facts)}]')
    for k_, (a, i, j) in enumerate(res['hlabels']):
        x, y = a
        L.append(f'    have h{k_} := congrFun (congrFun (hG {q(x)} {q(y)} (by decide)) ({i} : Fin {sh.d[y]})) ({j} : Fin {sh.d[x]})')
    L.append(f'    simp only [{SIMPSET}] at ' + ' '.join(f'h{k_}' for k_ in range(len(res['hlabels']))))
    comb = ' + '.join(f'({lean_poly(c)}) * h{e}' for e, c in hcs)
    d1 = sh.d[x1]
    L.append(f'    have g : {Ds} * G {q(x1)} (0 : Fin {d1}) (0 : Fin {d1}) = 0 := by linear_combination {comb}')
    L.append(f'    exact Matrix.ext fun (i j : Fin {d1}) ↦ by fin_cases i; fin_cases j; exact eq_zero_of_mul_eq_zero hD g\n')
    L.append(f'end {N}\n')
    L.append('end RayCat\n')
    L.append('end LargeIndecomposable')
    open(out, 'w').write('\n'.join(L) + '\n')

if __name__ == '__main__':
    spec, N, out = sys.argv[1], sys.argv[2], sys.argv[3]
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    doc = json.load(open(spec)).get('doc', '')
    sh, M, par, res = find_accepted(spec, seed=seed)
    if M is None:
        print('no accepted family'); sys.exit(1)
    show(sh, M, par)
    emit(sh, M, par, res, N, out, doc + '\n')
    print('wrote', out)
