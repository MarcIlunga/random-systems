#!/usr/bin/env python3
"""ADVERSARIAL REVIEW PROBE (review-only).

Slice `empirical` — exact q-query total-variation distance of XoP over Z_N for LARGE N,
via a closed-form count, versus `sopEps N q`.

For q distinct queries the transcript law depends only on the answer differences
d = (d_2..d_q); the realizing-permutation-pair count is  N * M(d) * ((N-q)!)^2  with
  M(d) = #{(t_2..t_q) : 0,t_2..t_q distinct and 0, d_2+t_2, .., d_q+t_q distinct}.
This makes N up to ~1000 reachable at q=3 and ~30 at q=4/5, which is what settles the
question the small-N data cannot: whether the true distance scales like q^1.5/N^1.5
(which would eventually CROSS sopEps ~ q^3/3N^2) or like c_q/N^2 (which does not).
It scales like c_q/N^2.  No crossing.

Values are validated against the fully adaptive enumeration in
review/slice-empirical.brute-force-adaptive.py for N <= 9.

Run:  uv run --with numpy python3 review/slice-empirical.exact-tv-large-N.py
"""
import numpy as np
from fractions import Fraction as F
import itertools, sys

def tv_q(N, q):
    """exact TV of the q-query (distinct, non-adaptive) transcript for G = Z_N.
       P(y) depends only on d=(d_2..d_q); N_q = N * M(d) with
       M(d) = #{(t_2..t_q): 0,t_2..t_q distinct and 0,d_2+t_2,..,d_q+t_q distinct}."""
    m = q-1
    grids = np.meshgrid(*[np.arange(N)]*m, indexing='ij')
    T = np.stack([g.ravel() for g in grids])           # (m, N^m)
    # t-side distinctness (independent of d): 0,t_2..t_q all distinct
    ok_t = np.ones(T.shape[1], dtype=bool)
    for i in range(m):
        ok_t &= (T[i] != 0)
        for j in range(i+1, m):
            ok_t &= (T[i] != T[j])
    desc = 1
    for i in range(q): desc *= (N-i)
    tot = F(0)
    Nq = N**q
    for d in itertools.product(range(N), repeat=m):
        Bv = [(T[i] + d[i]) % N for i in range(m)]
        ok = ok_t.copy()
        for i in range(m):
            ok &= (Bv[i] != 0)
            for j in range(i+1, m):
                ok &= (Bv[i] != Bv[j])
        M = int(ok.sum())
        p = F(N*M, desc*desc)
        tot += N * abs(p - F(1, Nq))
    return tot/2

def eps(N,q):
    s = F(0)
    for k in range(q):
        den = (N-k)**2
        if den == 0: continue
        s += F(k*k, den)
    return min(F(1), s)

# sanity: reproduce known values
for N in [5,6,7]:
    print("check q=3", N, tv_q(N,3), "  q=4", tv_q(N,4))

print()
print(f"{'N':>5} {'q':>2} {'true TV':>16} {'eps(N,q)':>16} {'true/eps':>9} {'true*N^2':>10} {'true*N^1.5':>11} holds")
for q in [2,3,4]:
    for N in [8,10,12,16,20,24,28]:
        t = tv_q(N,q); e = eps(N,q); tf=float(t)
        print(f"{N:>5} {q:>2} {tf:>16.9f} {float(e):>16.9f} {tf/float(e):>9.4f} {tf*N*N:>10.4f} {tf*N**1.5:>11.4f} {t<=e}")
    print()
