#!/usr/bin/env python3
"""ADVERSARIAL REVIEW PROBE (review-only).

Slice `empirical` — the TRUE maximal q-query distinguishing advantage of XoP, computed by
independent enumeration, over an arbitrary finite abelian group given as a product of cyclic
factors.  Nothing from the Lean development is used.

The recursion is over ADAPTIVE strategies (the next query may depend on all previous
answers), so it does not assume the folklore "non-adaptive is WLOG" reduction:
  V(h,0)  = max(0, P_ideal(h) - P_real(h))
  V(h,d)  = max( V(h,0), max_{x not in h} sum_y V(h+(x,y), d-1) )
V([],q) is then exactly  sup_D ( Pr^{D,ideal}[1] - Pr^{D,real}[1] ),  which is the signed
supremum `RandomSystems.CR18.maxAdvantage` denotes.

Covers Z4 vs Z2xZ2, Z8 vs Z4xZ2 vs Z2^3, Z9 vs Z3xZ3 — because `sopEps` depends on the
GROUP ORDER only, so a group-structure dependence in the truth would break the theorem.

Run:  uv run python3 review/slice-empirical.brute-force-adaptive.py
"""
from fractions import Fraction as F
import sys, itertools
sys.setrecursionlimit(100000)

def make_group(exps):
    """abelian group as product of Z_{e} ; elements indexed 0..N-1 via mixed radix"""
    N = 1
    for e in exps: N *= e
    def dec(i):
        out=[]
        for e in exps:
            out.append(i % e); i //= e
        return out
    def enc(v):
        i=0; m=1
        for k,e in enumerate(exps):
            i += (v[k]%e)*m; m*=e
        return i
    add = [[enc([dec(a)[k]+dec(b)[k] for k in range(len(exps))]) for b in range(N)] for a in range(N)]
    sub = [[enc([dec(a)[k]-dec(b)[k] for k in range(len(exps))]) for b in range(N)] for a in range(N)]
    return N, add, sub

def analyse(exps, qmax):
    N, add, sub = make_group(exps)
    def descfact(d):
        r=1
        for i in range(d): r*=(N-i)
        return r
    memo_real={}
    def count_inj(h):
        d=len(h); ys=[y for (_,y) in h]; cnt=0
        def rec(i, ua, ub):
            nonlocal cnt
            if i==d: cnt+=1; return
            for a in range(N):
                if a in ua: continue
                b = sub[ys[i]][a]
                if b in ub: continue
                rec(i+1, ua|{a}, ub|{b})
        rec(0,frozenset(),frozenset())
        return cnt
    def P_real(h):
        k=tuple(sorted(h))
        if k not in memo_real:
            memo_real[k]=F(count_inj(h), descfact(len(h))**2)
        return memo_real[k]
    memoV={}
    def V(h,d):
        key=(tuple(sorted(h)),d)
        if key in memoV: return memoV[key]
        best = max(F(0), F(1,N**len(h)) - P_real(h))
        if d>0:
            used={x for (x,_) in h}
            for x in range(N):
                if x in used: continue
                s=sum(V(h+[(x,y)],d-1) for y in range(N))
                if s>best: best=s
        memoV[key]=best
        return best
    return N, [(q,V([],q)) for q in range(qmax+1)]

def eps_of(N,q):
    s=F(0)
    for k in range(q):
        den=(N-k)**2
        if den==0: continue
        s+=F(k*k,den)
    return min(F(1),s)

for exps,qmax in [((4,),4), ((2,2),4), ((8,),3), ((4,2),3), ((2,2,2),3), ((9,),3), ((3,3),3), ((6,),4)]:
    N,res = analyse(exps,qmax)
    name = "Z"+"xZ".join(str(e) for e in exps) if len(exps)>1 else f"Z{exps[0]}"
    for (q,adv) in res:
        e=eps_of(N,q)
        flag = "" if adv<=e else "   <<<<< VIOLATION"
        print(f"{name:>10} (N={N}) q={q}: true={str(adv):>14} ({float(adv):.6f})  eps={str(e):>12} ({float(e):.6f}) holds={adv<=e}{flag}")
    print()
