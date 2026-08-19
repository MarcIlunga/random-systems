# Posterior-kernel CE checkpoint

**Status:** paused on 2026-08-06. This is a mathematical checkpoint, not a
finished SequenceHash theorem.

For a fixed occupied profile `C` with `c = |C|`, stored answers `w_z`,
multiplicities `r_y = #{z in C : w_z = y}`, and support size
`d = #{y : r_y > 0}`, the real one-step law is

$$
P(z,y)=
\begin{cases}
1/N,&z\in C,\ y=w_z,\\
1/N^2,&z\notin C,\\
0,&\text{otherwise}.
\end{cases}
$$

There is a balanced ideal extension with uniform `Z`- and `Y`-marginals.
For `0 < c` and `d < N`, put, for `z in C` and `t = w_z`,

$$
Q(z,t)=\frac{c}{N^2r_t},
\qquad
Q(z,y)=\frac{Nr_t-c}{N^2r_t(N-d)}\quad(y\notin\operatorname{supp}r),
$$

put `Q(z,y)=0` on the other occupied cells, and put `Q(z,y)=1/N^2`
for `z notin C`. For `c=0`, or for the boundary `d=N` (which forces
`c=N` and `r_y=1`), take `Q=P`. Row and column sums are both `1/N`.

Its exact distance from `P` is

$$
\delta(P,Q)=\frac{c(N-d)}{N^2}
=\delta(P_Y,U_Y).
$$

The equality to the marginal distance proves local optimality by data
processing, even among ideal extensions required to keep both marginals
uniform. The positive common sublaw is `min(P,Q)`: all unoccupied cells are
retained, and an occupied matching cell `(z,w_z)` is retained with mass
`c/(N^2 r_{w_z})`. On the real side this is thinning by
`c/(N r_{w_z})`; on the ideal side it discards precisely the occupied cells
whose answer is absent from the profile.

## Causal obstruction

This fixed-profile optimum is not, by itself, an online monotone CE game when
the construction answer is visible before a pending profile grows. Fix that
answer as `y`. After `c` pending answers, let `m_c` be the number equal to
`y`. Against the independent ideal tape, the likelihood ratio of the visible
prefix is

$$
L_c=\frac{N-c}{N}+m_c.
$$

When `m_c=0`, the fixed-profile common part thins ideal mass by the factor
`(N-c)/N`. If the next pending answer equals `y`, then `m_{c+1}=1` and the
fixed-profile ideal common-part factor becomes `1`. A monotone bad event
cannot restore the mass discarded at the previous prefix. Equivalently, the
family of terminal common measures `min(P_c,Q_c)` is not prefix-nested.

Consequently, the balanced kernel is immediately sound when the whole
occupied profile predates the activation at which the hidden endpoint is
sampled, and future outer sites are harmless once that endpoint is exposed
and linked. It does **not** yet replace the existing descriptor loss in the
opposite temporal order. A global improvement requires a different nested
common sublaw, a horizon-dependent construction with a justified causal
realization, or an additional invariant. Worst-case dependence on `c` alone
cannot improve the old coefficient because `d=1` attains
`c(N-1)/N^2`.

Terminology: this is a positive conditional-equivalence/game construction.
It does not select PDS representatives and it is not a coupling. A symmetric
pair of monitored games gives equal unnormalized pre-winning transcript
masses; CR18 one-sided conditional equivalence is a separate factorization
statement and should only be claimed after its conditional-law identity is
proved.
