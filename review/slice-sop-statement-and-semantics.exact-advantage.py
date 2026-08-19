#!/usr/bin/env python3
"""ADVERSARIAL REVIEW PROBE (review-only).

Exact maximal distinguishing advantage of XoP over Z_N with q queries, versus `sopEps N q`.

Why the non-adaptive total-variation distance is EXACT here: both `sopReal` and `sopIdeal`
are invariant under arbitrary relabelling of the query inputs ((pi1.s, pi2.s) is uniform for
any bijection s), so the law of the answer vector depends only on the repeat-pattern of the
query list; repeated queries return the same answer on both sides and carry no information.
Hence the optimal distinguisher is non-adaptive on q distinct inputs, and TV between the two
answer-vector laws IS the maximal advantage.

Run:  uv run python3 review/slice-sop-statement-and-semantics.exact-advantage.py
"""
from itertools import permutations
from fractions import Fraction
from collections import Counter


def true_tv(N, q):
    inj = list(permutations(range(N), q))          # injective q-tuples
    M = len(inj)
    cnt = Counter()
    for u in inj:
        for v in inj:
            cnt[tuple((a + b) % N for a, b in zip(u, v))] += 1
    tot = M * M
    unif = Fraction(1, N ** q)
    tv = Fraction(0)
    for _a, c in cnt.items():
        p = Fraction(c, tot)
        if p > unif:
            tv += p - unif
    return tv


def sopEps(N, q):
    s = Fraction(0)
    for k in range(q):
        d = N - k
        if d == 0:                                  # Lean: division by zero is 0
            continue
        s += Fraction(k * k, d * d)
    return min(Fraction(1), s)


print(f"{'N':>3} {'q':>2} {'exact max advantage':>22} {'sopEps':>12} {'ratio':>8}")
for N in range(2, 9):
    for q in range(2, min(5, N + 1)):
        t = true_tv(N, q)
        e = sopEps(N, q)
        ratio = float(e / t) if t else float('inf')
        print(f"{N:>3} {q:>2} {float(t):>22.8f} {float(e):>12.8f} {ratio:>8.2f}")
        assert t <= e, (N, q, t, e)

print()
print("module-docstring tightness claim: true distance at q=2 is 1/(N(N-1)),")
print("sopEps N 2 = 1/(N-1)^2, ratio N/(N-1):")
for N in range(2, 10):
    t, e = true_tv(N, 2), sopEps(N, 2)
    assert t == Fraction(1, N * (N - 1))
    assert e == min(Fraction(1), Fraction(1, (N - 1) ** 2))
    print(f"  N={N}: true={t}  sopEps={e}")
print("BOTH CONFIRMED.")
