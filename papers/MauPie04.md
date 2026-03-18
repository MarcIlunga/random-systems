# Composition of Random Systems: When Two Weak Make One Strong

Ueli Maurer and Krzysztof Pietrzak

ETH Zürich Department of Computer Science {maurer,pietrzak}@inf.ethz.ch

Abstract. A new technique for proving the adaptive indistinguishability of two systems, each composed of some component systems, is presented, using only the fact that corresponding component systems are non-adaptively indistinguishable. The main tool is the definition of a special monotone condition for a random system $\mathbf { F }$ , relative to another random system $\mathbf { G }$ , whose probability of occurring for a given distinguisher $\mathbf { D }$ is closely related to the distinguishing advantage $\varepsilon$ of $\mathbf { D }$ for $\mathbf { F }$ and $\mathbf { G }$ , namely it is lower and upper bounded by $\varepsilon$ and $\begin{array} { r } { \varepsilon ( 1 + \ln { \frac { 1 } { \varepsilon } } ) } \end{array}$ , respectively.

A concrete instantiation of this result shows that the cascade of two random permutations (with the second one inverted) is indistinguishable from a uniform random permutation by adaptive distinguishers which may query the system from both sides, assuming the components' security only against non-adaptive one-sided distinguishers.

As applications we provide some results in various fields as almost $k$ -wise independent probability spaces, decorrelation theory and computational indistinguishability (i.e., pseudo-randomness).

# 1 Introduction

# 1.1 Random Systems and the Distinguishing Problem

The statistical distance $\delta$ of two random variables $A$ and $B$ has a natural interpretation: The success probability of an optimal distinguisher in telling apart the two random variables $A$ and $B$ is $( 1 + \delta ) / 2$ .

It is much more intricate to deal with the indistinguishability of random systems1 which take inputs $X _ { 1 } , X _ { 2 } , \ldots$ and generate, for each new input $X _ { i }$ , an output $Y _ { i }$ which depends probabilistically on the inputs and outputs seen so far. As always, we consider a distinguisher $\mathbf { D }$ which may interactively query a random system and, after some number $k$ of queries, outputs a decision bit. For two random systems $\mathbf { F }$ and $\mathbf { G }$ and a distinguisher $\mathbf { D }$ one considers the two random experiments where $\mathbf { D }$ queries $\mathbf { F }$ and where $\mathbf { D }$ queries $\mathbf { G }$ , respectively, for some $k \geq 1$ queries. The advantage of $\mathbf { D }$ in distinguishing $\mathbf { F }$ and $\mathbf { G }$ is defined as difference of the probabilities of $\mathbf { D }$ outputting 1, in both random experiments.

Usually one is interested in the indistinguishability of a random system from some perfect random system with respect to any distinguisher from some general class of distinguishers (e.g. the class of all adaptive or the class of all non-adaptive distinguishers). In this work we will consider the problem of whether one can compose two or more random systems to obtain a new system whose security is superior to the security of any of its components. This is best illustrated by an example.

# 1.2 Composition of Random Systems: An Example

Let $\mathbf { E }$ (and likewise $\mathbf { F }$ ) be a random permutation2 where the advantage of any non-adaptive distinguisher³ for $\mathbf { E }$ and a uniform random permutation (URP) $\mathbf { P }$ is at most $\varepsilon _ { k }$ (where $k$ is the number of queries). We can build a new random permutation $\mathbf { E } \circ \mathbf { F }$ by using $\mathbf { E }$ and $\mathbf { F }$ in a cascade (see Figure 1). Intuitively, this construction should be even "closer" to $\mathbf { P }$ than $\mathbf { E }$ or $\mathbf { F }$ individually. Indeed, $\mathbf { E } \circ \mathbf { F }$ is $2 \varepsilon _ { k } ^ { 2 }$ i.e., the distinguishing advantages are multiplied. The same statement holds if we replace (both occurrences) of non-adaptive with adaptive in the above [8].

If $\mathbf { E }$ and $\mathbf { F }$ are secure against non-adaptive distinguishers, can we say something about the adaptive security of $\mathbf { E } \circ \mathbf { F } ?$ The intuition here is that adaptivity cannot help too much as the output of $\mathbf { E }$ in the cascade is obscured by $\mathbf { F }$ and the input to $\mathbf { F }$ is randomized by the leading $\mathbf { E }$ . This intuition is indeed correct. We will prove that if the non-adaptive security of $\mathbf { E }$ and $\mathbf { F }$ is $\varepsilon _ { k }$ , then $\mathbf { E } \circ \mathbf { F }$ has adaptive security $\textstyle 2 \varepsilon _ { k } { \bigl ( } 1 + \ln { \frac { 1 } { \varepsilon _ { k } } } { \bigr ) }$ . A lower bound of $\varOmega ( \varepsilon _ { k } )$ for this advantage can easily be shown, in contrast to the above stated $O ( \varepsilon _ { k } ^ { 2 } )$ when only non-adaptive security is required. This leaves us (as an open problem) a gap on the order of $\ln { \frac { 1 } { \varepsilon _ { k } } }$ between the upper and lower bound.

# 1.3 From Indistinguishability to Monotone Conditions and Back

The framework of [3] is based on the concept of monotone conditions defined for a random system. Intuitively, after each query to the system, such a condition can either be satisfied or can fail to be satisfied. Monotonicity means that once the condition has failed, it is never satisfied in the future. For example, such a condition could be that at a certain point internally in the system, for example at the input to a component, no collision has occurred. This no-collision condition is obviously monotone.

Consider two random systems $\mathbf { F }$ and $\mathbf { G }$ with compatible input and output alphabets. In this paper we will consider a monotone condition $\mathcal { A }$ for $\mathbf { F }$ , denoted $\mathbf { F } ^ { \bar { \mathcal { A } } }$ , su that ory fi ipuoutput behaviur, the probabily th $\mathbf { F }$ shows this behaviour and the condition occurs is upper bounded by the probability that $\mathbf { G }$ shows this behaviour. This will be denoted as $\mathbf { F } ^ { A } \preceq \mathbf { G }$ . Lemma 6 shows that if $\mathbf { F } ^ { A } \preceq \mathbf { G }$ , then for any distinguisher, its advantage in distinguishing $\mathbf { F }$ from $\mathbf { G }$ is upper bounded by the probability that it can make the condition $\mathcal { A }$ fail in $\mathbf { F }$

One can intuitively think of such a monotone condition as a lamp placed on the system which goes on as soon as the condition fails. More radically, one could think of failure of the condition as a trigger for the system to explode. If the failure of a condition in a system $\mathbf { F }$ is interpreted as such a visible effect, then distinguishing $\mathbf { F }$ from another system $\mathbf { G }$ (without such a trigger) is trivial, provided the trigger event occurs, i.e., the condition fails.

In very many indistinguishability proofs in the literature, such monotone conditions lie at the core of the argument, although this is sometimes obscured in complicated arguments. In [3] it is shown how complex systems with several internal subsystems, each with a monotone condition, can be analysed. However, if one only knows that the two systems are $\varepsilon$ -indistinguishable from a URF, without knowing a corresponding condition, then the technique of [3] fails. A main goal of this paper is therefore to define a special monotone condition $\mathcal { A }$ (called the maximum condition) for a random system $\mathbf { F }$ , relative to a system $\mathbf { G }$ , such that $\mathbf { F } ^ { A } \preceq \mathbf { G }$ and such that its probability $\rho$ of not occurring (for any distinguisher $\mathbf { D }$ ) is closely related to the distinguishing advantage $\varepsilon$ of $\mathbf { F }$ and $\mathbf { G }$ (for D). More precisely, we provide two lemmas (Lemma 6 mentioned before and Lemma 9) which show that $\begin{array} { r } { \varepsilon \le \rho \le \varepsilon ( 1 + \ln \frac { 1 } { \varepsilon } ) } \end{array}$ . This allows to prove the indistinguishability of two systems consisting of subsystems, knowing only that the subsystems are indistinguishable from a certain ideal system, but using the powerful framework based on monotone conditions.

Continuing the example of Section 1.2, let us discuss intuitively how this maximum condition allows to upper bound the adaptive security $\varepsilon _ { k }$ of $\mathbf { E } \circ \mathbf { F }$ assuming that the non-adaptive security of $\mathbf { E }$ (and likewise of $\mathbf { F }$ ) is at least $\gamma _ { k }$ (the $k$ refers to the number of queries the distinguisher is allowed to make). Let $\mathcal { A }$ be the maximum condition for $\mathbf { E }$ relative to a URP $\mathbf { P }$ , and let $\boldsymbol { B }$ be the maximum condition for $\mathbf { F }$ relative to $\mathbf { P }$ . One can show (using Lemma 6) that $\varepsilon _ { k } \ \leq \ \alpha _ { k }$ , where $\alpha _ { k }$ is an upper bound on the maximal success probability of any adaptive distinguisher in making either $\mathcal { A }$ or $\boldsymbol { B }$ fail when querying $\mathbf { E } ^ { A } \circ \mathbf { F } ^ { B }$ . Then using $\mathbf { E } ^ { \mathcal { A } } \preceq \bar { \mathbf { P } }$ and $\mathbf { F } ^ { B } \preceq \mathbf { P }$ one can show that this probability is at most the success probability of any adaptive distinguisher in making $\mathcal { A }$ fail in $\mathbf { E } ^ { A } \circ \mathbf { P }$ plus the probability of making $\boldsymbol { B }$ fail in $\mathbf { P } \circ \mathbf { F } ^ { B }$ . But in $\mathbf { E } ^ { A } \circ \mathbf { P }$ (and likewise in $\mathbf { P } \circ \mathbf { F } ^ { B } )$ adaptive strategies cannot be better than non-adaptive ones in making $\mathcal { A }$ fail as the output of $\bar { \mathbf { E } } ^ { A } \circ \mathbf { P }$ is completely independent of the output of the internal system $\mathbf { E }$ on which $\mathcal { A }$ is defined. So $\varepsilon _ { k } \ \leq \ 2 \beta _ { k }$ where $\beta _ { k }$ is an upper bound on the probability of any non-adaptive distinguisher in making $\mathcal { A }$ fail in $\mathbf { E }$ (and likewise $\boldsymbol { B }$ in $\mathbf { F }$ . As $\mathcal { A }$ and $\boldsymbol { B }$ are maximum conditions we now obtain (from Lemma 9) $\begin{array} { r } { \beta _ { k } \le \gamma _ { k } \big ( 1 + \ln \frac { 1 } { \gamma _ { k } } \big ) } \end{array}$ and thus $\begin{array} { r } { \varepsilon _ { k } \le 2 \gamma _ { k } \bigl ( 1 + \ln \frac { 1 } { \gamma _ { k } } \bigr ) } \end{array}$ .

# 1.4 Outline of the Paper

In Section 2 the definitions of random systems, monotone conditions, the < relation and of distinguishers are given. In Section 3 first the maximum condition for two random systems is defined. Then we lower and upper bound (Lemmas 6 and 9) the success probability of a distinguisher in making the maximum condition fail (as described in Section 1.3).

As an application of our framework, in Section 4 we provide two theorems bounding the adaptive security of two systems (parallel execution and XOR of random functions and cascades of permutations) in terms of the non-adaptive security of the component systems. We also give an application for each of the theorems, the first is about $\mathrm { k \Omega }$ -wise independent sample spaces, the second about the cascade of random involutions. Section 5 discusses some more implications of the results. Section 6 states some open problems.

# 1.5 Notation

We denote sets by capital calligraphic letters $( \mathrm { e . g . } \chi )$ and the corresponding capital letter $X$ denotes a random variable taking values in $\mathcal { X }$ Concrete values for $X$ are usually denoted by the corresponding small letter $x$ .For a set $\mathcal { X }$ we denote by $\mathcal { X } ^ { k }$ the set of ordered $\mathrm { k \Omega }$ -tuples of elements from $\mathcal { X }$ . $X ^ { k } = ( X _ { 1 } , X _ { 2 } , \ldots , X _ { k } )$ denotes a random variable taking values in $\mathcal { X } ^ { k }$ and a concrete value is usually denoted by $x ^ { k } = ( x _ { 1 } , x _ { 2 } , \ldots , x _ { k } )$ .

Because we will consider different random experiments where the same random variables appear, we extend the standard notation for probabilities and expectations (e.g. $\mathsf { P } _ { V } ( v ) , \mathsf { P } _ { V | W } ( v , w ) , \mathsf { E } [ V ] )$ by explicitly writing the considered random experiment $\mathcal { E }$ as a superscript, e.g. $\mathsf { P } _ { V } ^ { \mathcal { E } } ( v ) , \mathsf { P } _ { V | W } ^ { \mathcal { E } } ( v , w )$ and $\mathsf E ^ { \mathcal E } [ V ]$ . Equality of distributions means equality for all arguments, e.g.

$$
\mathsf { P } _ { V } ^ { \mathcal { E } _ { 1 } } = \mathsf { P } _ { V } ^ { \mathcal { E } _ { 2 } } \iff \forall v \in \mathcal { V } : \mathsf { P } _ { V } ^ { \mathcal { E } _ { 1 } } ( v ) = \mathsf { P } _ { V } ^ { \mathcal { E } _ { 2 } } ( v ) .
$$

We sometimes use the notation $\mathsf { P } _ { \xi } ^ { \mathcal { E } }$ instead of $\mathsf { P } ^ { \mathcal { E } } ( \xi )$ to denote the probability of the event $\xi$ .

# 2 Random Systems, Conditions and Distinguishers

# 2.1 Random Systems

Many cryptographic systems correspond to a probabilistic, possibly stateful (but often stateless) system which takes inputs $X _ { 1 } , X _ { 2 } , \ldots$ and generates, for each new input $X _ { i }$ , an output $Y _ { i }$ which depends probabilistically on $X _ { i }$ and the internal state.

In communication theory, a memoryless (i.e., stateless) communication channel with input $X$ and output $Y$ is modelled by a conditional probability distribution $P _ { Y \mid X }$ . In other words, $P _ { Y \mid X }$ precisely captures the input-output behaviour of the channel, and it is unnecessary to consider the internals of the channel. In the same spirit, a possibly stateful and probabilistic system $\mathbf { F }$ that takes inputs $X _ { 1 } , X _ { 2 } , \ldots$ and generates an output $Y _ { i }$ for each new input $X _ { i }$ is modelled as a so-called random system [3], defined as a sequence of conditional probability distributions PYi|X1...Xi ,Y1..Yi−1.

Defunitiion 1 An $( \mathcal { X } , \mathcal { Y } )$ $\mathbf { F }$ a ly infmic se ad $\mathsf { P } _ { Y _ { i } | X ^ { i } Y ^ { i } - 1 } ^ { \mathbf { F } }$ $i \geq 1$ $\mathbf { F }$ $\mathbf { G }$ $\mathbf { F } \equiv \mathbf { G }$   
i.e., if $\mathsf { P } _ { Y _ { i } | X ^ { i } Y ^ { i - 1 } } ^ { \mathbf { F } } = \mathsf { P } _ { Y _ { i } | X ^ { i } Y ^ { i - 1 } } ^ { \mathbf { G } }$ for  all $i \geq 1$

The sequence $\mathsf { P } _ { Y _ { i } | X ^ { i } Y ^ { i } - 1 } ^ { \mathbf { F } }$ for $i \geq 1$ also defines the sequence $\mathsf { P } _ { Y ^ { i } | X ^ { i } } ^ { \mathbf { F } }$ by

$$
{ \mathsf { P } } _ { Y ^ { i } \mid X ^ { i } } ^ { \mathbf { F } } = \prod _ { j = 1 } ^ { i } { \mathsf { P } } _ { Y _ { j } \mid X ^ { j } Y ^ { j } - 1 } ^ { \mathbf { F } } ,
$$

and vice versa by

$$
\mathsf { P } _ { Y _ { i } | X ^ { i } Y ^ { i - 1 } } ^ { \mathbf { F } } = \frac { \mathsf { P } _ { Y ^ { i } | X ^ { i } } ^ { \mathbf { F } } } { \mathsf { P } _ { Y ^ { i - 1 } | X ^ { i - 1 } } ^ { \mathbf { F } } } .
$$

As special classes of random systems we will consider random functions and random permutations, which are stateless random systems.

Definition 2 A random function $\mathcal { X }  \mathcal { V }$ (random permutation on $\mathcal { X }$ ) is a random variable which takes as values functions $\mathcal X  \mathcal y$ (permutations on $\mathcal { X }$ . Throughout the paper the symbols $\mathcal { R }$ and $\mathcal { P }$ are used for the set of all random functions and the set of all random permutations respectively.

A uniform random function $( U R F ) { \bf R } : { \mathcal { X } }  { \mathcal { Y } }$ (A uniform random permutation $\left( U R P \right) \mathbf { P }$ on $\mathcal { X }$ ) is a random function with uniform distribution over all functions from $\mathcal { X }$ to $\boldsymbol { \ y }$ (permutations on $\mathcal { X }$ ). Throughout the paper, the symbols $\mathbf { R }$ and $\mathbf { P }$ are used exclusively for the systems defined above.

# 2.2 Monotone Conditions

The concept of monotone conditions for random systems was introduced in [3]. A monotone condition $\mathcal { A }$ for a random-system $\mathbf { F }$ is a sequence $a _ { 0 } , a _ { 1 } , a _ { 2 } , \dots .$ of events, where $a _ { 0 }$ is the certain event and where $a _ { i }$ $\left( \overline { { a } } _ { i } \right)$ denotes the event that the condition is satisfied (failed) after the $i$ 'th query to $\mathbf { F }$ has been processed. As described above, monotone means that once the condition has failed, it can never hold again (i.e., $a _ { i } \Rightarrow a _ { i - 1 }$ ). A natural example of a monotone condition is a no-collision condition. As we are not interested in the behaviour of a random system after the condition has failed, and in fact this behaviour need in general not be defined, the definition below specifies the probability distribution of $Y _ { i }$ , given $X ^ { i }$ and $Y ^ { i - 1 }$ , only together with the event $a _ { i }$ , and conditioned on $a _ { i - 1 }$ . More formally, a random system with a monotone condition is defined like a random system, but the (conditional) probability distributions generally do not sum to 1. We use the term "partial" to denote such distributions which are not actually probability distributions.

Definition 3 An $( \mathcal { X } , \mathcal { Y } )$ -random system $\mathbf { F }$ with a monotone condition $\mathcal { A }$ , denoted $\mathbf { F } ^ { A }$ , is an infinite sequence of partial conditional probability distributions ${ \mathsf { P } } _ { a _ { i } Y _ { i } | X ^ { i } Y ^ { i - 1 } a _ { i - 1 } } ^ { \mathbf { F } ^ { A } }$ for $i \geq 1$ .

For any $x ^ { i }$ and $y ^ { i - 1 }$ we have

$$
\mathsf { P } _ { a _ { i } | X ^ { i } Y ^ { i - 1 } a _ { i - 1 } } ^ { \mathbf { F } ^ { A } } ( x ^ { i } , y ^ { i - 1 } ) = \sum _ { y _ { i } \in \mathcal { Y } } \mathsf { P } _ { a _ { i } Y _ { i } | X ^ { i } Y ^ { i - 1 } a _ { i - 1 } } ^ { \mathbf { F } ^ { A } } ( y _ { i } , x ^ { i } , y ^ { i - 1 } ) \le 1 .
$$

The sequence PFA $\mathsf { P } _ { a _ { i } Y _ { i } | X ^ { i } Y ^ { i - 1 } a _ { i - 1 } } ^ { \mathbf { F } ^ { A } }$ fo i ≥ 1 aso defines the quenc Y  y

$$
{ \mathsf { P } } _ { a _ { i } Y ^ { i } | X ^ { i } } ^ { \mathbf { F } ^ { A } } = \prod _ { j = 1 } ^ { i } { \mathsf { P } } _ { a _ { j } Y _ { j } | X ^ { j } Y ^ { j - 1 } a _ { j - 1 } } ^ { \mathbf { F } ^ { A } } ,
$$

and vice versa.

Definition 4 We introduce a partial order $\preceq$ on input-output compatible random systems with monotone conditions, as follows:

$$
\mathbf { F } ^ { \mathcal { A } } \preceq \mathbf { G } ^ { \mathcal { B } } \iff \forall i \geq 1 : \ \mathsf { P } _ { a _ { i } Y ^ { i } | X ^ { i } } ^ { \mathbf { F } ^ { \mathcal { A } } } \leq \mathsf { P } _ { b _ { i } Y ^ { i } | X ^ { i } } ^ { \mathbf { G } ^ { \mathcal { B } } } .
$$

In other words, $\mathbf { F } ^ { A } \preceq \mathbf { G } ^ { B }$ if for all $i \geq 1$ and all $x ^ { i } \in \mathcal { X } ^ { i }$ , $y ^ { i } \in \mathcal { V } ^ { i }$ , the probability that $\mathbf { F } ^ { A }$ outputs $y ^ { i }$ on input $x ^ { i }$ and the condition $\mathcal { A }$ holds is at most the probability that $\mathbf { G } ^ { B }$ will output $y ^ { i }$ on input $x ^ { i }$ and the condition $\boldsymbol { B }$ holds. We also define $\mathbf { F } ^ { A } \preceq \mathbf { G }$ (here one may think of $\mathbf { G }$ having a condition which never fails):

$$
\mathbf { F } ^ { \mathcal { A } } \preceq \mathbf { G } \iff \forall i \geq 1 \colon \mathsf { P } _ { a _ { i } Y ^ { i } | X ^ { i } } ^ { \mathbf { F } ^ { \mathcal { A } } } \leq \mathsf { P } _ { Y ^ { i } | X ^ { i } } ^ { \mathbf { G } } .
$$

# 2.3 Distinguishers and Their Advantage

Definition 5 A distinguisher for an $( \mathcal { X } , \mathcal { Y } )$ -random systems is a $( \boldsymbol { \mathcal { V } } , \boldsymbol { \mathcal { X } } )$ -random system $\mathbf { D }$ which can interactively query $( \mathcal { X } , \mathcal { Y } )$ -random systems and finally outputs a bit.4 For an $( \mathcal { X } , \mathcal { Y } )$ -random system $\mathbf { F }$ we denote by $\mathbf { D } { \bigcirc } \mathbf { F }$ the random experiment where $\mathbf { D }$ interactively queries $\mathbf { F }$ .

This definition refers to adaptive distinguishers. A non-adaptive distinguisher must fix all inputs $X _ { 1 } , \ldots , X _ { k }$ before seeing the outputs $Y _ { 1 } , \dots , Y _ { k }$ .

For the case of random permutations, we will consider mono-directional and bidirectional distinguishers (the latter only in the adaptive version). A bidirectional distinguisher can query the system from both sides.

Definition 6 The advantage of $\mathbf { D }$ in distinguishing $\mathbf { F }$ from $\mathbf { G }$ , after $k$ queries, denoted $\varDelta _ { k } ^ { \mathrm { { D } } } ( { \bf { F } } , { \bf { G } } )$ , is the absolute value of the difference of the probability of $\mathbf { D }$ outputting 1 in the two random experiments $\mathbf { D } { \bigcirc } \mathbf { F }$ and $\mathbf { D } { \odot } \mathbf { G }$ .

Assuming without loss of generality that, after the query phase, $\mathbf { D }$ makes the optimal decision based on $X ^ { k }$ and $Y ^ { k }$ , we have5

$$
\varDelta _ { k } ^ { \mathbf { D } } ( \mathbf { F } , \mathbf { G } ) = \frac { 1 } { 2 } \sum _ { \chi ^ { k } \times \mathcal { Y } ^ { k } } \left| \mathsf { P } _ { X ^ { k } Y ^ { k } } ^ { \mathbf { D } \odot \mathbf { F } } - \mathsf { P } _ { X ^ { k } Y ^ { k } } ^ { \mathbf { D } \odot \mathbf { G } } \right| .
$$

We denote the advantages of the best adaptive and the best non-adaptive distinguisher as follows:

$$
\varDelta _ { k } ( \mathbf { F } , \mathbf { G } ) \overset { \mathrm { d e f } } { = } \operatorname* { m a x } _ { \mathbf { D } } \varDelta _ { k } ^ { \mathbf { D } } \left( \mathbf { F } , \mathbf { G } \right)
$$

and

$$
\begin{array} { r l } & { \delta _ { k } \big ( \mathbf { F } , \mathbf { G } \big ) \overset { \scriptscriptstyle { \mathrm { d e f } } } { = } \underset { \mathrm { n o n - a d a p t i v e ~ } \mathbf { D } } { \mathrm { m a x } } \varDelta _ { k } ^ { \mathbf { D } } \big ( \mathbf { F } , \mathbf { G } \big ) } \\ & { \qquad = \underset { x ^ { k } \in \mathcal { X } ^ { k } } { \mathrm { m a x } } \frac { 1 } { 2 } \underset { y ^ { k } \in \mathcal { Y } ^ { k } } { \sum } \bigg | \mathsf { P } _ { Y ^ { k } \mid X ^ { k } } ^ { \mathbf { F } } \big ( y ^ { k } , x ^ { k } \big ) - \mathsf { P } _ { Y ^ { k } \mid X ^ { k } } ^ { \mathbf { G } } \big ( y ^ { k } , x ^ { k } \big ) \bigg | . } \end{array}
$$

Definition 7 For a random system $\mathbf { F } ^ { A }$ with a monotone condition, we let

$$
\nu _ { k } ^ { \mathbf { D } } ( \mathbf { F } , \overline { { a } } _ { k } ) \stackrel { \mathrm { d e f } } { = } 1 - \mathsf { P } _ { a _ { k } } ^ { \mathbf { D } \diamond \mathbf { F } }
$$

be the probability that $\mathbf { D }$ makes the condition fail with at most $k$ queries. Furthermore, let

$$
\nu _ { k } ( \mathbf { F } , \overline { { a } } _ { k } ) \overset { \mathrm { d e f } } { = } \operatorname* { m a x } _ { \mathbf { D } } ~ \nu _ { k } ^ { \mathbf { D } } ( \mathbf { F } , \overline { { a } } _ { k } )
$$

be the maximal probability in provoking $\overline { { a } } _ { k }$ using any adaptive $\mathbf { D }$ , and analogously for non-adaptive $\mathbf { D }$ :

$$
\mu _ { k } \big ( \mathbf { F } , \overline { { a } } _ { k } \big ) \ { \stackrel { \mathrm { d e f } } { = } } \ \operatorname* { m a x } _ { \mathrm { n o n - a d a p t i v e } \ \mathbf { D } } \nu _ { k } ^ { \mathbf { D } } \big ( \mathbf { F } , \overline { { a } } _ { k } \big ) .
$$

# 2.4 Random Systems as Components in Random Experiments

In this section we propose two lemmas which we will need several times in the $\mathcal { E } ( \mathbf { F } )$ where a raandon system $\mathbf { F }$ $\mathsf { P } _ { Y _ { i } | X ^ { i } Y ^ { i - 1 } } ^ { \mathbf { F } }$   
$\mathcal { E } ( \cdot )$ ync isuions $\mathsf { P } _ { X _ { i } | X ^ { i - 1 } Y ^ { i - 1 } } ^ { \mathcal { E } ( \cdot ) }$ .6 Here $\mathcal { E } ( \cdot )$ sends a query   
$X _ { 1 }$ to $\mathbf { F }$ which answers with $Y _ { 1 }$ , then $\mathcal { E } ( \cdot )$ sends a query $X _ { 2 }$ and so on. So after   
$k$ queries this random experiment defines a random variable $X ^ { k } Y ^ { k }$ .

Lemma 1 For $\mathcal { E } ( . )$ as just defined

$$
\mathsf { P } _ { X ^ { k } Y ^ { k } } ^ { \mathcal { E } ( \mathbf { F } ) } = \mathsf { P } _ { X ^ { k } | Y ^ { k } - 1 } ^ { \mathcal { E } ( \cdot ) } \mathsf { P } _ { Y ^ { k } | X ^ { k } } ^ { \mathbf { F } } .
$$

Proof: This follows directly from the definition of this random experiment:

$$
\mathsf { P } _ { X ^ { k } Y ^ { k } } ^ { \mathcal { E } ( \mathbf { F } ) } = \prod _ { j = 1 } ^ { k } \mathsf { P } _ { X _ { j } | X ^ { j - 1 } Y ^ { j - 1 } } ^ { \mathcal { E } ( \cdot ) } \mathsf { P } _ { Y _ { j } | X ^ { j } Y ^ { j - 1 } } ^ { \mathbf { F } } = \mathsf { P } _ { X ^ { k } | Y ^ { k - 1 } } ^ { \mathcal { E } ( \cdot ) } \mathsf { P } _ { Y ^ { k } | X ^ { k } } ^ { \mathbf { F } } .
$$

For example for the random experiment $\mathbf { D } { \odot } \mathbf { F }$ (see Definition 5) we have

$$
\mathsf { P } _ { X ^ { i } Y ^ { i } } ^ { \bf D \diamond F } = \mathsf { P } _ { X ^ { i } | Y ^ { i - 1 } } ^ { \bf D } \mathsf { P } _ { Y ^ { i } | X ^ { i } } ^ { \bf F } .
$$

For $\mathcal { E } ( \cdot )$ as just defined we can also consider the random experiment $\mathcal { E } ( \mathbf { F } ^ { A } )$ .7 It is straight-forward to prove the following lemma.

Lemma 2 For $\mathcal { E } ( \cdot )$ as above let $\tau$ be any event defined on $\mathcal { E } ( \cdot )$ . Let $a _ { \tau }$ be the event that the condition $\mathcal { A }$ holds at the timepoint where $\tau$ occurs. If $\mathbf { F } ^ { A } \preceq \mathbf { G }$ then

$$
\mathsf { P } _ { \tau \wedge a _ { \tau } } ^ { \mathcal { E } ( \mathbf { F } ^ { A } ) } \le \mathsf { P } _ { \tau } ^ { \mathcal { E } ( \mathbf { G } ) }
$$

# 3 The Maximum Condition

Definition 8 For two $( \mathcal { X } , \mathcal { Y } )$ -random systems $\mathbf { F }$ and $\mathbf { G } , \mathbf { F }$ with the maximum condition (relative to $\mathbf { G }$ ) is the random system with monotone condition $\mathbf { F } ^ { A }$ defined by

$$
\mathsf { P } _ { a _ { i } | X ^ { i } Y ^ { i } } ^ { \mathbf { F } ^ { A } } = \operatorname* { m i n } _ { 1 \leq j \leq i } * \left\{ \frac { \mathsf { P } _ { Y ^ { j } | X ^ { j } } ^ { \mathbf { G } } } { \mathsf { P } _ { Y ^ { j } | X ^ { j } } ^ { \mathbf { F } } } \right\}
$$

and

$$
\mathsf { P } _ { a _ { i } Y ^ { i } | X ^ { i } } ^ { \mathbf { F } ^ { A } } = \mathsf { P } _ { Y ^ { i } | X ^ { i } } ^ { \mathbf { F } } \mathsf { P } _ { a _ { i } | X ^ { i } Y ^ { i } } ^ { \mathbf { F } ^ { A } }
$$

for $i \geq 1$ , where $\operatorname* { m i n } ^ { * }$ means that the constant 1 is included among the terms to be minimised over, i.e., a $\operatorname* { m i n } ^ { * }$ expression is always upper bounded by 1. We denote the maximum condition for $\mathbf { F }$ and $\mathbf { G }$ by $\mathbf { F } \downarrow \mathbf { G }$ and often give it a short name (e.g. $\begin{array} { r } { A : = \mathbf { F } \downarrow \mathbf { G } } \end{array}$ .

The term "maximum condition" is motivated by the following lemma.

Lemma 3 For $\boldsymbol { \mathcal { A } } : = \mathbf { F } \downarrow \mathbf { G }$ ,

$$
\mathbf { F } ^ { A } \preceq \mathbf { G } .
$$

Moreover, for all $\mathbf { F } ^ { B }$ ,

$$
\mathbf { F } ^ { B } \preceq \mathbf { G } \implies \mathbf { F } ^ { B } \preceq \mathbf { F } ^ { A } .
$$

Proof: We first observe that the condition is monotone, because of the minimisation which implies P $\mathsf { P } _ { a _ { i } | Y ^ { i } X ^ { i } } ^ { \mathbf { F } ^ { \mathcal { A } } } \le \mathsf { P } _ { a _ { i - 1 } | Y ^ { i - 1 } X ^ { i - 1 } } ^ { \mathbf { F } ^ { \mathcal { A } } }$ ii−−1 To prove F  G, observe that pFA $\mathsf { P } _ { a _ { i } | Y ^ { i } X ^ { i } } ^ { \mathbf { F } ^ { A } } \le \mathsf { P } _ { Y ^ { i } | X ^ { i } } ^ { \mathbf { G } } / \mathsf { P } _ { Y ^ { i } | X ^ { i } } ^ { \mathbf { F } }$ implies pFA $\mathsf { P } _ { a _ { i } Y ^ { i } | X ^ { i } } ^ { \mathbf { F } ^ { A } } = \mathsf { P } _ { Y ^ { i } | X ^ { i } } ^ { \mathbf { F } } \mathsf { P } _ { a _ { i } | X ^ { i } Y ^ { i } } ^ { \mathbf { F } ^ { A } } \le \mathsf { P } _ { Y ^ { i } | X ^ { i } } ^ { \mathbf { G } }$

To see that $\mathbf { F } ^ { B } \preceq \mathbf { G }$ implies $\mathbf { F } ^ { B } \preceq \mathbf { F } ^ { A }$ , note that for the maximum condition A the distribution PFA has everywhere the largst possible vaue till satifying both requirements. So for any $\mathbf { F } ^ { B } \preceq \mathbf { G }$ we have $\mathsf { P } _ { b _ { i } | Y ^ { i } X ^ { i } } ^ { \mathbf { F } ^ { B } } \le \mathsf { P } _ { a _ { i } | Y ^ { i } X ^ { i } } ^ { \mathbf { F } ^ { A } }$ aiYii and thus $\mathbf { F } ^ { B } \preceq \mathbf { F } ^ { A }$ . □

For the remainder of this section, let $\mathbf { F }$ and $\mathbf { G }$ be any $( \mathcal { X } , \mathcal { Y } )$ -random systems. For each $i \geq 0$ we define the function $\lambda _ { i } ^ { \mathbf { F } , \mathbf { G } } : \mathcal { X } ^ { i } \times \mathcal { Y } ^ { i }  [ 0 , 1 ]$ as

$$
\lambda _ { i } ^ { \mathbf { F } , \mathbf { G } } ( x ^ { i } , y ^ { i } ) \overset { \mathrm { d e f } } { = } \operatorname* { m a x } \left\{ \frac { \mathsf { P } _ { Y ^ { i } | X ^ { i } } ^ { \mathbf { F } } ( y ^ { i } , x ^ { i } ) - \mathsf { P } _ { Y ^ { i } | X ^ { i } } ^ { \mathbf { G } } ( y ^ { i } , x ^ { i } ) } { \mathsf { P } _ { Y ^ { i } | X ^ { i } } ^ { \mathbf { F } } ( y ^ { i } , x ^ { i } ) } , 0 \right\} .
$$

In a random experiment where the random_variables $X ^ { i }$ and $Y ^ { i }$ are defined we can consider the random variables $Z _ { i }$ and $\widetilde { Z } _ { i }$ defined as

$$
Z _ { i } \stackrel { \mathrm { d e f } } { = } \lambda _ { i } ^ { \mathbf { F } , \mathbf { G } } ( X ^ { i } , Y ^ { i } ) \mathrm { a n d } \tilde { Z } _ { i } \stackrel { \mathrm { d e f } } { = } \operatorname* { m a x } _ { 0 \leq j \leq i } Z _ { j } .
$$

The next two lemmas state that the expectation of these random variables in the random experiment $\mathbf { D } { \odot } \mathbf { F }$ are the distinguishing advantage of $\mathbf { D }$ for $\mathbf { F }$ and $\mathbf { G }$ and the probability that $\mathbf { D }$ provokes the maximum condition for $\mathbf { F }$ (relative to $\mathbf { G }$ ) to fail, respectively.

# Lemma 4

$$
\varDelta _ { k } ^ { \mathrm { D } } ( \mathbf { F } , \mathbf { G } ) = \mathsf { E } ^ { \mathbf { D } \diamond \mathbf { F } } [ Z _ { k } ] .
$$

Proof:

$$
\begin{array} { l } { { \displaystyle { \varDelta } _ { k } ^ { \mathbf { D } } ( { \mathbf { F } } , { \mathbb G } ) = \frac { 1 } { 2 } \sum _ { { \boldsymbol \chi } ^ { \star } \times { \mathbf { y } } ^ { k } } | { \mathbf { P } } _ { { \boldsymbol \chi } ^ { \hat { \boldsymbol \nu } \gamma _ { k } } } ^ { \mathbf { D } \cdot \mathbf { Q } { \mathbf { F } } } - { \mathbf { P } } _ { { \boldsymbol \chi } ^ { \hat { \boldsymbol \nu } \cdot } \hat { \boldsymbol \nu } ^ { k } } ^ { \mathbf { D } \cdot \mathbf { G } } | } } \\ { ~ = ~ \sum _ { { \boldsymbol \chi } ^ { \star } \times { \mathbf { y } } ^ { k } } \operatorname* { m a x } \{ \mathbf { P } _ { { \boldsymbol \chi } ^ { \hat { \boldsymbol \kappa } } \cdot { \mathbf { F } } ^ { k } } ^ { \mathbf { D } \cdot \mathbf { F } } - \mathbf { P } _ { { \boldsymbol \chi } ^ { \hat { \boldsymbol \kappa } } \cdot { \mathbf { F } } ^ { k } } ^ { \mathbf { D } \cdot \mathbf { G } } ,  } \\ { ~ = ~ \sum _ { { \boldsymbol \chi } ^ { \star } \times { \mathbf { y } } ^ { k } } \mathbf { P } _ { { \boldsymbol \chi } ^ { k } \mid { \boldsymbol \gamma } ^ { k - 1 } } ^ { \mathbf { D } } \operatorname* { m a x } \{ \mathbf { P } _ { { \boldsymbol \chi } ^ { k } \mid { \boldsymbol \chi } ^ { k } } ^ { \mathbf { F } } - \mathbf { P } _ { { \boldsymbol \chi } ^ { k } \mid { \boldsymbol \chi } ^ { k } } ^ { \mathbf { G } } , 0 \} } \\  ~ = ~ \sum _ { { \boldsymbol \chi } ^ { \star } \times { \mathbf { y } } ^ { k } } \mathbf { P } _ { { \boldsymbol \chi } ^ { \hat { \boldsymbol \kappa } } \cdot { \mathbf { F } } ^ { \mathbf { m a x } } } ^ { \mathbf { D } \cdot \mathbf { F } } \operatorname* { m a x } \{ \frac  \mathbf { P } _ { { \boldsymbol \chi } ^ { k } \mid { \boldsymbol \chi } ^ { k } } ^ { \mathbf { F } } - \mathbf { P } _  \end{array}
$$

Lemma 5 For $\boldsymbol { \mathcal { A } } : = \mathbf { F } \downarrow \mathbf { G }$ ,

$$
\nu _ { k } ^ { \mathbf { D } } ( \mathbf { F } ^ { A } , \overline { { a } } _ { k } ) = \mathsf { E } ^ { \mathbf { D } \diamond \mathbf { F } } [ \widetilde { Z } _ { k } ] .
$$

Proof:

$$
\begin{array} { r l } { \nu _ { k } ^ { \mathbf { D } } \left( \mathbf { F } ^ { A } , \bar { \alpha } _ { k } \right) = 1 - } & { \displaystyle \sum _ { \lambda ^ { \mathbf { k } } \times \mathbf { Y } ^ { k } } \mathsf { P } _ { a _ { \mathbf { k } } \times \mathbf { Y } ^ { k } } ^ { \mathbf { D O P S } } } \\ { = } & { \displaystyle \sum _ { \lambda ^ { \mathbf { k } } \times \mathbf { Y } ^ { k } } \mathsf { P } _ { \lambda ^ { \mathbf { k } } \mathbf { Y } ^ { k } } ^ { \mathbf { D O P } } \left( 1 - \mathsf { P } _ { a _ { \mathbf { k } } \times \mathbf { Y } ^ { k } } ^ { A } \right) } \\ & { = \displaystyle \sum _ { \lambda ^ { \mathbf { k } } \times \mathbf { y } ^ { k } } \mathsf { P } _ { \lambda ^ { \mathbf { k } } \mathbf { Y } ^ { k } } ^ { \mathbf { D O P } } \left( 1 - \operatorname* { m i n } ^ { \circ } \left\{ \frac { \mathsf { P C } _ { \mathbf { Y } ^ { k } | X ^ { \circ } } ^ { \mathbf { G } } } { \mathsf { P } _ { \mathbf { Y } ^ { k } | X ^ { \circ } } ^ { \mathbf { G } } } \right\} \right) } \\ & { = \displaystyle \sum _ { \lambda ^ { \mathbf { k } } \times \mathbf { y } ^ { k } } \mathsf { P } _ { \lambda ^ { \mathbf { k } } \mathbf { Y } ^ { k } } ^ { \mathbf { D O P } } \left( 1 - \operatorname* { m i n } ^ { \circ } \left\{ \frac { \mathsf { P } _ { \mathbf { Y } ^ { k } | X ^ { \circ } } ^ { \mathbf { G } } } { \mathsf { P } _ { \mathbf { Y } ^ { k } | X ^ { \circ } } ^ { \mathbf { G } } } \right\} \right) } \\ &  = \displaystyle \sum _ { \lambda ^ { \mathbf { k } } \times \mathbf { y } ^ { \mathbf { k } } } \mathsf { P } _ { \lambda ^ { \mathbf { k } } \mathbf { Y } ^ { k } } ^ { \mathbf { D O P } } \displaystyle \frac { \mathsf { m } _ { \mathbf { k } } ^ { \mathbf { a } } \mathbf { x } ^ { \mathsf { a } } }  \end{array}
$$

Here max\* means that the constant 0 is included among the terms to be minimised over, i.e., a max\* expression is always non-negative. □

Lemma 6 If $\mathbf { F } ^ { A } \preceq \mathbf { G }$ , then

$$
\varDelta _ { k } ^ { \mathbf { D } } ( \mathbf { F } , \mathbf { G } ) \leq \nu _ { k } ^ { \mathbf { D } } ( \mathbf { F } ^ { \mathcal { A } } , \overline { { { a } } } _ { k } ) .
$$

Proof: Let $\boldsymbol { B } : = \mathbf { F } \downarrow \mathbf { G }$ . Using the Lemmas 4 and 5 we get

$$
\begin{array} { r l } & { \Delta _ { k } ^ { \mathbf { D } } \left( \mathbf { F } , \mathbf { G } \right) = { \sf E } ^ { \mathbf { D } \diamond \mathbf { F } } [ Z _ { k } ] } \\ & { \qquad \leq { \sf E } ^ { \mathbf { D } \diamond \mathbf { F } } [ \widetilde { Z } _ { k } ] } \\ & { \qquad = \nu _ { k } ^ { \mathbf { D } } \left( \mathbf { F } ^ { \mathcal { B } } , \overline { { b } } _ { k } \right) } \\ & { \qquad \leq \nu _ { k } ^ { \mathbf { D } } \left( \mathbf { F } ^ { \mathcal { A } } , \overline { { a } } _ { k } \right) . } \end{array}
$$

The last step is easily verified using $\mathbf { F } ^ { A } \preceq \mathbf { F } ^ { B }$ , which follows from Lemma 3.

Definition 9 A sequence of random variables $V _ { 0 } , V _ { 1 } , \ldots ,$ is a sub-martingale if for all $i \geq 0$

$$
\mathsf { E } [ V _ { i + 1 } | V _ { 0 } , \ldots , V _ { i } ] \geq V _ { i } .
$$

The proofs of the Lemmas 7 and 8 below can be found in Appendix A.

Lemma 7 Let $V _ { 0 } , V _ { 1 } , \ldots$ be a sub-martingale where $0 \leq V _ { i } \leq 1$ for all $i$ , and let $\widetilde { V } _ { n } \ { \stackrel { \mathrm { d e f } } { = } } \ \operatorname* { m a x } _ { 0 \leq j \leq n } V _ { j }$ .Then

$$
\mathsf { E } [ \widetilde { V } _ { n } ] \leq \mathsf { E } [ V _ { n } ] \cdot ( 1 - \ln ( \mathsf { E } [ V _ { n } ] ) ) .
$$

Lemma 8 The sequence $Z _ { 0 } , Z _ { 1 } , \ldots$ as defined in (2) is a sub-martingale sequence in the random experiment $\mathbf { D } { \bigcirc } \mathbf { F }$ , i.e.,

$$
\forall i \geq 0 : { \mathsf { E } } ^ { \mathbf { D } \diamond \mathbf { F } } [ Z _ { i + 1 } | Z _ { 0 , \cdot \cdot \cdot , Z _ { i } } ] \geq Z _ { i } .
$$

![](images/fbb59793fecf8e2cd2ea4d4a429f6f8eaadfa1fc955af5e9d501cf6537a66046.jpg)  
Fig. 1. The random systems $\mathbf { E } \star \mathbf { F }$ (left) and $\mathbf { E } \circ \mathbf { F }$ (right).

Lemma 9 For $\boldsymbol { \mathcal { A } } : = \mathbf { F } \downarrow \mathbf { G }$ ,

$$
\nu _ { k } ^ { \mathbf { D } } \big ( \mathbf { F } ^ { \mathcal { A } } , \overline { { \boldsymbol { a } } } _ { k } \big ) \leq \varDelta _ { k } ^ { \mathbf { D } } \big ( \mathbf { F } , \mathbf { G } \big ) \big ( 1 - \ln \big ( \varDelta _ { k } ^ { \mathbf { D } } \big ( \mathbf { F } , \mathbf { G } \big ) \big ) \big ) .
$$

Proof: Using Lemmas 8 and 7 we get

$$
\begin{array} { r } { \mathsf { E } ^ { \mathbf { D } \diamond \mathbf { F } } [ \widetilde { Z } _ { k } ] \leq \mathsf { E } ^ { \mathbf { D } \diamond \mathbf { F } } [ Z _ { k } ] \cdot \left( 1 - \ln \left( \mathsf { E } ^ { \mathbf { D } \diamond \mathbf { F } } [ Z _ { k } ] \right) \right) . } \end{array}
$$

Now one can apply the Lemmas 4 and 5.

# 4 Stronger Security by Composition

Definition 10 A composition operator $\bowtie$ for a class of random systems $\mathcal { Q }$ is a binary operator ${ \mathcal { Q } } \times { \mathcal { Q } } \to { \mathcal { Q } }$ which, given two random systems $\mathbf { E } , \mathbf { F } \in \mathcal { Q }$ . defines how to combine $\mathbf { E }$ and $\mathbf { F }$ into a random system $\mathbf { E } \bowtie \mathbf { F } \in \mathcal { Q }$ where, on any invocation of $\mathbf { E } \bowtie \mathbf { F }$ , the internal random systems $\mathbf { E }$ and $\mathbf { F }$ are invoked once. In this paper we will consider the two composition operators $\star$ and $^ \circ$ described below.

Let $\mathbf { E } , \mathbf { F } \in \mathcal { R }$ be random functions $\mathcal { X }  \mathcal { V }$ (see Definition 2) and let $\star$ denote some group operation on $\boldsymbol { \ y }$ . We denote by ${ \mathbf { E } } \star { \mathbf { F } } \in { \mathcal { R } }$ the random function defined by applying the input to $\mathbf { E }$ and $\mathbf { F }$ and then applying $\star$ to the outputs (see Figure 1, left).   
Let $\mathbf { E } , \mathbf { F } \in \mathcal { P }$ be random permutations over $\mathcal { X }$ (see Definition 2). We denote by $\mathbf { E } \circ \mathbf { F } \in \mathcal { P }$ the random permutation defined by applying the input to $\mathbf { E }$ and $\mathbf { F }$ to the output of $\mathbf { E }$ (see Figure 1, right).

Lemma 10 Consider a class $\mathcal { Q }$ of random systems and a composition operator $\bowtie$ on $\mathcal { Q }$ . If there is a random system $\mathbf { I } \in \mathcal { Q }$ such that for all $\mathbf { F } \in { \mathcal { Q } }$ the following two conditions are satisfied

$$
\nu _ { k } ( \mathbf { E } ^ { \boldsymbol { A } } \bowtie \mathbf { I } , \overline { { \boldsymbol { a } } } _ { k } ) = \mu _ { k } ( \mathbf { E } ^ { \boldsymbol { A } } \bowtie \mathbf { I } , \overline { { \boldsymbol { a } } } _ { k } ) \quad \mathrm { a n d } \quad \nu _ { k } ( \mathbf { I } \bowtie \mathbf { F } ^ { \mathcal { B } } , \overline { { \boldsymbol { b } } } _ { k } ) = \mu _ { k } ( \mathbf { I } \bowtie \mathbf { F } ^ { \mathcal { B } } , \overline { { \boldsymbol { b } } } _ { k } ) \stackrel { \mathfrak { g } } { \mathrm { \Sigma } }
$$

Then for any $\mathbf { E } , \mathbf { F } \in \mathcal { Q }$ and any $k \geq 1$ we have

$$
\delta _ { k } ( \mathbf { E } , \mathbf { I } ) \leq \varepsilon \quad \wedge \quad \delta _ { k } ( \mathbf { F } , \mathbf { I } ) \leq \varepsilon \quad \Longrightarrow \quad \varDelta _ { k } ( \mathbf { E } \bowtie \mathbf { F } , \mathbf { I } ) \leq 2 \varepsilon ( 1 + \ln \frac { 1 } { \varepsilon } ) .
$$

Proof: Let $\boldsymbol { \mathcal { A } } \left( \boldsymbol { B } \right)$ be the maximum condition for $\textbf { E } ( \mathbf { F } )$ , relative to $\mathbf { I }$ ,i.e.,

$$
{ \mathcal { A } } : = \mathbf { E } \downarrow \mathbf { I } \qquad { \mathrm { a n d } } \qquad B : = \mathbf { F } \downarrow \mathbf { I } .
$$

Now we have (here $b _ { \overline { { a } } }$ ,and likewise $a _ { \overline { { b } } }$ , denote the event that at any timepoint where the condition $\boldsymbol { B }$ holds, also the condition $\mathcal { A }$ holds)

$$
\begin{array} { r l } & { \mathcal { \Delta } _ { k } ( \mathbf { E } \boxtimes \mathbf { F } , \mathbf { I } ) = \mathcal { \Delta } _ { k } ( \mathbf { E } \boxtimes \mathbf { F } , \mathbf { I } \boxtimes \mathbf { I } ) } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad } \\ &  \quad \quad \quad \quad \quad \end{array}
$$

The first step above follows from the first condition in the statement of the lemma. As for the second step, let $( \mathbf { E } \bowtie \mathbf { F } ) ^ { \mathcal { M } }$ be given by the partial distributions

$$
\forall i \ : \ \mathsf { P } _ { m _ { i } Y ^ { i } \mid X ^ { i } } ^ { ( \mathbf { E } \bowtie \mathbf { F } ) ^ { \mathcal { M } } } : = \mathsf { P } _ { a _ { i } \wedge b _ { i } Y ^ { i } \mid X ^ { i } } ^ { \mathbf { E } ^ { A } \bowtie \mathbf { F } ^ { \mathcal { B } } } .
$$

Here $( \mathbf { E } \bowtie \mathbf { F } ) ^ { \mathcal { M } } \preceq \mathbf { I } \bowtie \mathbf { I }$ (which follows from $\mathbf { E } ^ { A } \preceq \mathbf { I }$ and $\mathbf { F } ^ { B } \preceq \mathbf { I } )$ and we can apply Lemma 6 as $( \mathbf { E } \bowtie \mathbf { F } ) ^ { \mathcal { M } } \leq \nu _ { k } ( \mathbf { E } ^ { \mathcal { A } } \bowtie \mathbf { F } ^ { \mathcal { B } } , \overline { { \boldsymbol { m } } } _ { k } ) = \nu _ { k } ( \mathbf { E } ^ { \mathcal { A } } \bowtie \mathbf { F } ^ { \mathcal { B } } , \overline { { \boldsymbol { a } } } _ { k } \vee $ $\overline { { b } } _ { k } \mathrm { ~ , ~ }$ ). The third step uses the union bound. Note that $\overline { { a } } _ { k } \wedge b _ { \overline { { a } } _ { k } }$ is the event that the $\mathcal { A }$ -condition fails before the $\boldsymbol { B }$ -condition fails. The fourth step follows from Lemma 2. The fifth step follows by the second condition in the statement of the lemma. The sixth step follows as a non-adaptive distinguisher which queries $\mathbf { E } ^ { A }$ (and likewise $\mathbf { F } ^ { B }$ ) can simply "simulate" the system $\mathbf { \bar { E } } ^ { \mathcal { A } } \rtimes \mathbf { I } \ ( \mathbf { I } \ \bowtie \ \mathbf { \bar { F } } ^ { \mathcal { B } } )$ .9 The seventh step follows from Lemma 9, and the final step from the assumption of the lemma. □

Theorem 1 For random functions $\mathbf { E } , \mathbf { F } \in \mathcal { R }$ and $\star \ \mathrm { a s }$ in Definition 10,

$$
\delta _ { k } ( \mathbf { E } , \mathbf { R } ) \leq \varepsilon \quad \wedge \quad \delta _ { k } ( \mathbf { F } , \mathbf { R } ) \leq \varepsilon \quad \Longrightarrow \quad \varDelta _ { k } ( \mathbf { E } \star \mathbf { F } , \mathbf { R } ) \leq 2 \varepsilon \left( 1 + \ln \frac { 1 } { \varepsilon } \right) .
$$

Proof: The Theorem follows from Lemma 10 by setting $\mathbf { I }  \mathbf { R } , { \mathcal { Q } }  { \mathcal { R } }$ and $\bowtie  \star$ . We only have to verify that the two points required by Lemma 10 are satisfied. As for the first point, $\mathbf { R } \star \mathbf { R } \equiv \mathbf { R }$ clearly holds. For the second point, note that the output of $\mathbf { E } ^ { A } \star \mathbf { R }$ is independent of the output of the internal system $\mathbf { E } ^ { A }$ on which our event is defined. So seeing the output cannot help in making the condition fail and we have $\nu _ { k } ( \mathbf { E } ^ { \mathcal { A } } \star \mathbf { R } , { \overline { { a } } } _ { k } ) = { \bar { \mu _ { k } } } ( \mathbf { E } ^ { \mathcal { A } } \star \mathbf { R } , { \overline { { a } } } _ { k } )$ . By symmetry, also $\nu _ { k } \big ( \mathbf { R } \star \mathbf { F } ^ { \mathcal { B } } , \overline { { b } } _ { k } \big ) = \mu _ { k } \big ( \mathbf { R } \star \mathbf { F } ^ { \mathcal { B } } , \overline { { b } } _ { k } \big )$ holds. □

As an application for this theorem one can consider an adaptive version of almost $k$ -wise independent distributions (see [5], and [1] for simpler constructions). These are distributions over $\{ 0 , 1 \} ^ { n }$ such that the bits at any $k$ fixed positions are close (say some $\varepsilon > 0$ far away) to uniform.

It is natural to consider an adaptive version of $\varepsilon$ almost $k$ -wise independence where the positions can be chosen adaptively by a distinguisher.

Definition 11 A distribution over $\{ 0 , 1 \} ^ { n }$ is adaptively $\varepsilon$ -almost $k$ -wise independent if even an adaptive distinguisher, selecting the $k$ positions adaptively, cannot distinguish the $k$ bits from uniformly random with advantage more than $\varepsilon$ .

Corollary 1. The distribution over $\{ 0 , 1 \} ^ { n }$ defined by XOR-ing two $\varepsilon$ -almost $k$ -wise independent distributions is adaptively $\begin{array} { r } { 2 \varepsilon ( 1 + \ln { \frac { 1 } { \varepsilon } } ) } \end{array}$ -almost $k$ -wise independent.

The following theorem is inspired by Lemma 3 from [4]. We use the notation of [3] to denote bidirectional random permutations. If $\mathbf { F }$ is a random permutation, then $\langle \mathbf { F } \rangle$ is like $\mathbf { F }$ , but it can be queried from both sides. The distinguisher can thus also issue a direction bit, in addition to the query, to indicate from which side it is supposed to be applied as input.

Theorem 2 For two random permutations $\mathbf { E } , \mathbf { F } \in \mathcal { P }$ and $^ \circ$ as in Definition 10,

$$
\delta _ { k } ( \mathbf { E } , \mathbf { P } ) \leq \varepsilon \quad \wedge \quad \delta _ { k } ( \mathbf { F } , \mathbf { P } ) \leq \varepsilon \quad \Longrightarrow \quad \varDelta _ { k } ( \mathbf { E } \circ \mathbf { F } , \mathbf { P } ) \leq 2 \varepsilon \left( 1 + \ln \frac { 1 } { \varepsilon } \right) .
$$

If we take the inverse $\mathbf { F } ^ { - 1 }$ of $\mathbf { F }$ as the second element in the cascade, we additionally obtain security against bidirectional distinguishers:

$$
\begin{array} { r } { \delta _ { k } ( { \mathbf E } , { \mathbf P } ) \le \varepsilon \quad \wedge \quad \delta _ { k } ( { \mathbf F } , { \mathbf P } ) \le \varepsilon \quad \Longrightarrow \quad \varDelta _ { k } ( \langle { \mathbf E } \circ { \mathbf F } ^ { - 1 } \rangle , \langle { \mathbf P } \rangle ) \le 2 \varepsilon \left( 1 + \ln \frac { 1 } { \varepsilon } \right) . } \end{array}
$$

Proof: The first statement of the theorem follows from Lemma 10 by setting $\mathcal { Q }  \mathcal { P }$ , $\textbf { I }  \textbf { P }$ and $\sqcap  \mathrm { ~ o ~ }$ . For the second statement we must set $\mathcal { Q }  \mathcal { P }$ $\mathbf { I }  \langle \mathbf { P } \rangle$ and $\bowtie$ to be the mapping ${ \bf E } , { \bf F }  \langle { \bf E } \circ { \bf F } ^ { - 1 } \rangle$ .

We will only prove the (slightly more involved) second statement of the theorem. Note that this statement is somewhat stronger than a direct application of Lemma 10 would imply: the precondition is $\delta _ { k } ( \mathbf { E } , \mathbf { P } ) \leq \varepsilon \wedge \delta _ { k } ( \mathbf { F } , \mathbf { P } ) \leq \varepsilon$ ,and not $\delta _ { k } \bigl ( \langle \mathbf { E } \rangle , \langle \mathbf { P } \rangle \bigr ) \leq \varepsilon \wedge \delta _ { k } \bigl ( \langle \mathbf { F } \rangle , \langle \mathbf { P } \rangle \bigr ) \leq \varepsilon$ as one would expect (we will come back to that point later).

We must verify that the two points required by Lemma 10 are satisfied. As for the first point, $\left. \mathbf { P } \circ \mathbf { P } ^ { - 1 } \right. \equiv \left. \mathbf { P } \right.$ clearly holds. For the second point, note that in $\langle \mathbf { E } ^ { \mathcal { A } _ { \circ } } \circ \mathbf { P } ^ { - 1 } \rangle$ a query from the $\mathbf { P } ^ { - 1 }$ side results in a random value on the input and output of $\mathbf { E } ^ { A }$ . Thus a query from this side can be replaced by a random query from the $\mathbf { E } ^ { A }$ side without changing the probability of an event defined on $\mathbf { E } ^ { \mathcal { A } }$ , and we have $\nu _ { k } \bigl ( \bigl \langle \mathbf { E } ^ { \mathcal { A } } \circ \mathbf { P } ^ { - 1 } \bigr \rangle , \overline { { \boldsymbol { a } } } _ { k } \bigr ) = \nu _ { k } \bigl ( \mathbf { E } ^ { \mathcal { A } } \circ \mathbf { P } ^ { - 1 } , \overline { { \boldsymbol { a } } } _ { k } \bigr )$ . Now the output of $\mathbf { E } ^ { A } \circ \mathbf { P } ^ { - 1 }$ is completely independent of the output of the internal system $\mathbf { E } ^ { A }$ . So adaptive strategies cannot help in provoking an event defined on $\mathbf { E } ^ { \mathcal { A } }$ , i.e., $\nu _ { k } \big ( \mathbf { E } ^ { \mathcal { A } } \circ \mathbf { P } ^ { - 1 } , \overline { { \boldsymbol { a } } } _ { k } \big ) = \mu _ { k } \big ( \mathbf { E } ^ { \mathcal { A } } \circ \mathbf { P } ^ { - 1 } , \overline { { \boldsymbol { a } } } _ { k } \big )$ . We have shown that $\nu _ { k } \big ( \langle \mathbf { E } ^ { \mathcal { A } } \circ \mathbf { P } ^ { - 1 } \rangle , \overline { { a } } _ { k } \big ) =$ $\mu _ { k } \left( \mathbf { E } ^ { \mathcal { A } } \circ \mathbf { P } ^ { - 1 } , \overline { { a } } _ { k } \right)$ , and by symmetry we get $\nu _ { k } \big ( \langle \mathbf { P } \circ \mathbf { \scriptscriptstyle ( F } ^ { \mathcal { B } } ) ^ { - 1 } \rangle , \overline { { \boldsymbol a } } _ { k } \big ) = \mu _ { k } \big ( \mathbf { F } ^ { \mathcal { B } } \circ$ $\mathbf { P } ^ { - 1 } , \overline { { a } } _ { k } )$ . This is more than what is actually required by the second condition of Lemma 9. An inspection of the proof of the lemma shows that with this we also get a stronger statement (as mentioned before). □

As an application of this theorem, consider the cascade of two uniform random involutions over $\mathcal { X }$ . An involution is a permutation which is its own inverse, and a uniform random involution (URI) on $\mathcal { X }$ is a permutation selected at random from the set of all involutions on $\mathcal { X }$ . A URI I is non-adaptively indistinguishable from a URP $\mathbf { P }$ (the advantage is very small even for a large number of queries, actually $O ( \sqrt { | \mathcal { X } | } )$ queries are required to achieve a constant advantage), but an adaptive distinguisher can easily distinguish I from $\mathbf { P }$ simply by using any query $X _ { 1 }$ , setting $X _ { 2 }    : = Y _ { 1 }$ , and checking whether $Y _ { 2 } = X _ { 1 }$ . For a URI, this condition is always satisfied, whereas for a URP, it is satisfied only with exponentially small probability. We get the following corollary from Theorem 2

Corollary 1 Any adaptive bidirectional distinguisher must make in the order of $\sqrt { | \mathcal { X } | }$ queries to achieve a constant distinguishing advantage for a cascade of two uniform random involutions over $\mathcal { X }$ and a uniform random permutation over $\mathcal { X }$ .

# 5 Discussion

We discuss a few implications of the results of this paper.

# 5.1 Pseudorandomness

As discussed in [3], essentially all proofs of computational indistinguishability of random systems consist basically of an information-theoretic indistinguishability proof. The results of this paper therefore have direct applications to computational settings. For example, in order to design a bidirectionally secure pseudorandom permutation (i.e., a block cipher secure against a combined chosenmessage and chosen-ciphertext attack) from any pseudorandom function, it suffices to design an only non-adaptively secure random permutation $\mathbf { F }$ from a random function, then to replace the random function by a pseudorandom function, and to apply the construction twice with one of them inverted. More generally, this paper allows for new constructions of quasi-random systems, as discussed in [3].

# 5.2 Generalizing Indistinguishability Theory

This paper proposes two generalisations of the framework of [3], where the following technique to bound the indistinguishability $\varDelta _ { k } ( \mathbf { F } , \mathbf { G } )$ of two random systems $\mathbf { F }$ and $\mathbf { G }$ is used:

- Find conditions $\mathcal { A }$ and $\boldsymbol { B }$ such that $\mathbf { F } ^ { A } \equiv \mathbf { G } ^ { B }$ , which is defined as

$$
\mathbf { F } ^ { A } \equiv \mathbf { G } ^ { B } \Longleftrightarrow \forall i \geq 1 : \quad \mathsf { P } _ { a _ { i } Y _ { i } | X ^ { i } Y ^ { i - 1 } a _ { i - 1 } } ^ { \mathbf { F } ^ { A } } = \mathsf { P } _ { b _ { i } Y _ { i } | X ^ { i } Y ^ { i - 1 } b _ { i - 1 } } ^ { \mathbf { G } ^ { B } } .
$$

- Prove an upper bound on $\nu _ { k } ( \mathbf { F } ^ { \mathcal { A } } , \overline { { a } } _ { k } )$ , the success probability of any distinguisher in making the condition fail with $k$ queries. Now (by Lemma 7 from [3]) $\varDelta _ { k } ( \mathbf { F } , \mathbf { G } ) \leq \nu _ { k } ( \mathbf { F } ^ { \mathcal { A } } , \overline { { { a } } } _ { k } )$ and we are done.

The first generalisation is that by Lemma 6 we may replace the requirement $\mathbf { F } ^ { A } \equiv \mathbf { G } ^ { B }$ with the weaker requirement $\mathbf { F } ^ { A } \preceq \mathbf { G }$ and the second point still holds. As $\mathbf { F } ^ { A } \equiv \mathbf { G } ^ { B }$ implies $\mathbf { F } ^ { A } \preceq \mathbf { G }$ but $\mathbf { F } ^ { A } \preceq \mathbf { G }$ does not imply the existence of $\boldsymbol { B }$ such that $\mathbf { F } ^ { A } \equiv \mathbf { G } ^ { B }$ , this requirement is strictly weaker.

The second generalisation is that, due to Lemma 9, one can go from indistinguishability to monotone conditions: If $\varDelta _ { k } ( \mathbf { F } , \mathbf { G } ) \leq \varepsilon$ , then there always exists a monotone condition (i.e. the maximum condition for $\mathbf { F }$ and $\mathbf { G }$ ) $\mathcal { A }$ such that $\mathbf { F } ^ { A } \preceq \mathbf { G }$ and $\begin{array} { r } { \nu _ { k } ( \mathbf { F } ^ { \mathcal { A } } , \overline { { a } } _ { k } ) \le \varepsilon ( 1 + \ln \frac { 1 } { \varepsilon } ) } \end{array}$ .So using the above framework (with $\mathbf { F } ^ { A } \preceq \mathbf { G }$ instead of $\mathbf { F } ^ { A } \equiv \mathbf { G } ^ { B }$ in the first step) does not inherently restrict the set of provable statements.

This is in sharp contrast to the original $\mathbf { F } ^ { A } \equiv \mathbf { G } ^ { B }$ requirement, as there are, for any $\varepsilon > 0$ , random systems $\mathbf { F }$ and $\mathbf { G }$ where (for some $k$ , or rather some range for $k$ ) $\varDelta _ { k } ( \mathbf { F } , \mathbf { G } ) \leq \varepsilon$ ,but for any conditions $\mathcal { A }$ and $\boldsymbol { B }$ which satisfy $\mathbf { F } ^ { A } \equiv \mathbf { G } ^ { B }$ we have $\nu _ { k } ( \mathbf { F } ^ { \mathcal { A } } , \overline { { a } } _ { k } ) \geq 1 - \varepsilon$ For such systems this framework (with the original $\mathbf { F } ^ { A } \equiv \mathbf { G } ^ { B }$ requirement in the first step) is not applicable.

As an example for such systems, let the first be a source of uniform random bits and the second be a source where each bit is not completely uniform but has some small bias $\alpha$ . Here $\varDelta _ { k } ( \mathbf { F } , \mathbf { G } ) \approx \sqrt { k } \alpha$ (see [6]) and $\nu _ { k } ( \overset { \cdot } { \mathbf { F } } ^ { A } , \overline { { a } } _ { k } ) \approx 1 -$ $( 1 - \alpha ) ^ { k / 2 } \approx \alpha k / 2$ .Thus choosing $\alpha$ small and $k$ large enough we can achieve any $\varepsilon > 0$ as described.

# 5.3 Decorrelation Theory

Decorrelation theory was introduced by Vaudenay as a tool to prove security of block ciphers against $d$ -iterated attacks, this class of attacks includes linear and differential cryptanalysis. Loosely speaking, in a $d$ -iterated attack a distinguisher, which tries to distinguish the block cipher from a uniform random permutation, is limited to look at blocks of at most $d$ queries at the same time. Decorrelation theory is based on different matrix norms. We refer to [7] for the definition of these norms and note that

For a random permutation $\mathbf { E }$ over $\mathcal { M }$ let $[ E ] ^ { d }$ denote the $\mathcal { M } ^ { d } \times \mathcal { M } ^ { d }$ matrix where the $( x ^ { d } , y ^ { d } ) \in \mathcal { M } ^ { d } \times \mathcal { M } ^ { d }$ entry of $[ E ] ^ { d }$ is $\mathsf { P } _ { Y ^ { d } | X ^ { d } } ^ { \mathbf { E } } ( x ^ { d } , y ^ { d } )$ Now let $D$ be a distance over the matrix space $\mathbb { R } ^ { \mathcal { M } ^ { d } \times \mathcal { M } ^ { d } }$ . The d-wise decorrelation bias of the permutation $E$ is the distance ( $C ^ { * }$ denotes the distribution of the uniform random permutation)

$$
\mathrm { D e c P } _ { D } ^ { d } ( E ) = D ( [ E ] ^ { d } , [ C ^ { * } ] ^ { d } ) .
$$

In the above definition the distance $D$ can be replaced by a matrix norm. The matrix norms considered are denoted $| | { \bf \sigma } \cdot | | _ { \infty } , | | { \bf \sigma } \cdot | | _ { a }$ and $| | \mathbf { \partial } \cdot | | _ { s }$ . These norms have a natural interpretation as they are exactly twice the advantage of the best (non-adaptive, adaptive or bidirectional) distinguisher making at most $d$ queries in distinguishing $\mathbf { E }$ from a URP, i.e. (note that here the first terms are in our notation)

$$
\begin{array} { r c l c l } { { \delta _ { d } ( { \bf E } , { \bf P } ) } } & { { = } } & { { { \displaystyle \frac { 1 } { 2 } | | [ E ] ^ { d } - [ C ^ { * } ] ^ { d } | | _ { \infty } } } } & { { = } } & { { { \displaystyle \frac { 1 } { 2 } \mathrm { D e c } { \bf P } _ { \infty } ^ { d } ( E ) } } } \\ { { { \cal A } _ { d } ( { \bf E } , { \bf P } ) } } & { { = } } & { { { \displaystyle \frac { 1 } { 2 } | | [ E ] ^ { d } - [ C ^ { * } ] ^ { d } | | _ { a } } } } & { { = } } & { { { \displaystyle \frac { 1 } { 2 } \mathrm { D e c } { \bf P } _ { a } ^ { d } ( E ) } } } \\ { { { \cal A } _ { d } ( \langle { \bf E } \rangle , \langle { \bf P } \rangle ) } } & { { = } } & { { { \displaystyle \frac { 1 } { 2 } | | [ E ] ^ { d } - [ C ^ { * } ] ^ { d } | | _ { s } } } } & { { = } } & { { { \displaystyle \frac { 1 } { 2 } \mathrm { D e c } { \bf P } _ { s } ^ { d } ( E ) } } } \end{array}
$$

The main theorem of [7] states that if a block cipher has small $2 d \cdot$ wise $( | | \cdot |$ $| | _ { \infty } , | | \cdot | | _ { a }$ or $| | \cdot | | _ { s } )$ decorrelation bias it is secure against any $d$ -iterated attack performed by any (non-adaptive, adaptive or bidirectional) distinguisher.

We can plug in (3), (4) and (5) directly into Theorem 1 and get the first nontrivial relations known among this norms.

# Corollary 2

$$
\begin{array} { r l } & { \mathrm { D e c P } _ { \infty } ^ { d } ( E ) \leq \varepsilon \ \wedge \ \mathrm { D e c P } _ { \infty } ^ { d } ( F ) \leq \varepsilon \ \Rightarrow \ \mathrm { D e c P } _ { a } ^ { d } ( E \circ F ) \leq 2 \varepsilon \left( 1 + \ln \frac { 2 } { \varepsilon } \right) } \\ & { } \\ & { \mathrm { D e c P } _ { \infty } ^ { d } ( E ) \leq \varepsilon \ \wedge \ \mathrm { D e c P } _ { \infty } ^ { d } ( F ) \leq \varepsilon \ \Rightarrow \ \mathrm { D e c P } _ { s } ^ { d } ( E \circ F ^ { - 1 } ) \leq 2 \varepsilon \left( 1 + \ln \frac { 2 } { \varepsilon } \right) . } \end{array}
$$

The second statement of the corollary now implies that using a block-cipher with small $2 d$ -wise decorrelation bias in the $\infty$ norm against non-adaptive chosen plaintext $d$ -iterated attacks in a cascade (with independent keys, the second time in decrypt mode) results in a block cipher which is secure against adaptive combined chosen plaintext and ciphertext $2 d$ -iterated attacks.

# 6 Conclusions and Open Problems

It would be interesting to have a similar framework as the one proposed in this paper for the computational setting. For example, the computational analog of Theorem 2 would state that the cascade of two block-ciphers, each secure against non-adaptively chosen plaintext attacks, is secure against adaptive chosen plaintext/ciphertext adversaries.

As already mentioned in the introduction, there is a gap in the order of $\textstyle \ln { \frac { 1 } { \varepsilon } }$ between the $\begin{array} { r } { O ( \varepsilon \ln { \frac { 1 } { \varepsilon } } ) } \end{array}$ bound proven in Theorems 1 and 2 and an easy to show $\varOmega ( \varepsilon )$ lower bound for the respective terms. However, Lemmas 6 and 9 can be shown to be tight up to a (small) multiplicative constant, so we cannot hope to close this gap (i.e. showing an upper bound of $O ( \varepsilon )$ ) by improving on them. But trying to find a concrete example (of random systems) for which a matching $\begin{array} { r } { \varOmega ( \varepsilon \ln { \frac { 1 } { \varepsilon } } ) } \end{array}$ lower bound can be proven seems promising to us.

# References

1. N. Alon, O. Goldreich, J. Hastad, R. Peralta, Simple construction of almost k-wise independent random variables, Random Structures and Algorithms, vol. 3, no. 3, pp. 289304, 1992.   
2. M. Luby and C. Rackoff, How to construct pseudo-random permutations from pseudo-random functions, SIAM J. on Computing, vol. 17, no. 2, pp. 373386, 1988.   
3. U. Maurer, Indistinguishability of random systems, Advances in Cryptology - EUROCRYPT '02, Lecture Notes in Computer Science, vol. 2332, pp. 110-132, Springer-Verlag, 2002.   
4. U. Maurer and K. Pietrzak, The security of many-round Luby-Rackoff pseudorandom permutations, Advances in Cryptology - EUROCRYPT '03, Lecture Notes in Computer Science, vol. 2656, pp. 544561, Springer-Verlag, 2003.   
5. J. Naor and M. Naor, Small-bias probability spaces: Efficient constructions and applications, SIAM Journal on Computing, vol. 22, no. 4, pp. 838356, 1993.   
6. R. Renner, The Statistical Distance of Independently Repeated Experiments, Manuscript, available at http://www.crypto.ethz.ch/\~renner/publications.html   
7. S. Vaudenay, Provable security for block ciphers by decorrelation, Proceedings of STACS'98, Lecture Notes in Computer Science, vol. 1373, Springer-Verlag, pp. 249275, 1998.   
8. S. Vaudenay, Adaptive-attack norm for decorrelation and super-pseudorandomness, Proc. of $S A C ^ { \prime } g g$ , Lecture Notes in Computer Science, vol. 1758, pp. 4961, Springer-Verlag, 2000.

# A Martingales

In what follows, let ${ \widetilde { V } } _ { n } \ { \stackrel { \mathrm { d e f } } { = } } \ \operatorname* { m a x } _ { 0 \leq j \leq n } V _ { j }$ The Kolmogorov-Doob inequality.

Lemma 11 Let $V _ { 0 } , V _ { 1 } , . . .$ . be a sub-martingale sequence where the $V _ { i }$ are nonnegative. Then, for every $n$ ,

$$
\mathsf { P } [ \widetilde { V } _ { n } \ge \lambda ] \le \frac { \mathsf { E } [ V _ { n } ] } { \lambda } .
$$

Proof of Lemma 7: We restate the lemma for the reader's convenience: If $V _ { 0 } , V _ { 1 } , \ldots$ is a sub-martingale sequence where $0 \leq V _ { i } \leq 1$ for all $i$ ,then

$$
\mathsf { E } [ \widetilde { V } _ { n } ] \leq \mathsf { E } [ V _ { n } ] \cdot ( 1 - \ln ( \mathsf { E } [ V _ { n } ] ) ) .
$$

Let $\psi \left( r \right)$ denote the function

$$
\psi ( r ) \ { \stackrel { \scriptscriptstyle { \mathrm { d e f } } } { = } } \ \left\{ { \begin{array} { l l } { 1 } & { { \mathrm { i f } } \ r < \mathsf { E } [ V _ { n } ] } \\ { \mathsf { E } [ V _ { n } ] / r } & { { \mathrm { i f } } \ \mathsf { E } [ V _ { n } ] \leq r \leq 1 } \\ { 0 } & { { \mathrm { i f } } \ r > 1 } \end{array} } \right.
$$

With Lemma 11 and $0 \leq \widetilde { V } _ { n } \leq 1$ (which follows from $0 \leq V _ { i } \leq 1$ ) we see that

$$
\forall r : \mathsf { P } [ \widetilde { V } _ { n } \geq r ] \leq \psi ( r ) .
$$

So we can upper bound $\mathsf E [ \widetilde V _ { n } ]$ as

$$
\begin{array} { r l r } {  { \Xi [ \tilde { V } _ { n } ] \le - \int _ { - \infty } ^ { \infty } \psi ^ { \prime } ( r ) r d r } } \\ & { } & { = - \int _ { { \mathsf { E } } [ V _ { n } ] } ^ { 1 } ( \frac { { \bf E } [ V _ { n } ] } { r } ) ^ { \prime } r d r + { \bf E } [ V _ { n } ] } \\ & { } & { = \displaystyle \int _ { { \bf E } [ V _ { n } ] } ^ { 1 } \frac { { \bf E } [ V _ { n } ] } { r ^ { 2 } } r d r + { \bf E } [ V _ { n } ] } \\ & { } & { = - \ln ( { \bf E } [ V _ { n } ] ) \cdot { \bf E } [ V _ { n } ] + { \bf E } [ V _ { n } ] . } \end{array}
$$

ProofofLemma 8: We restate the lemma for the reader's convenience: $Z _ { 1 } , Z _ { 2 } , \dots$ as defined in (2) is a sub-martingale sequence in the random experiment $\mathbf { D } { \bigcirc } \mathbf { F }$ , i.e.,

$$
\forall i \geq 0 : \mathsf { E } ^ { \mathbf { D } \diamond \mathbf { F } } [ Z _ { i + 1 } \vert Z _ { 0 } , \ldots , Z _ { i } ] \geq Z _ { i } .
$$

Because the $Z _ { 0 } , \ldots , Z _ { i }$ are determined by $X ^ { i } Y ^ { i }$ , we can prove the (stronger) statement

$$
\forall i \geq 0 : \mathsf { E } ^ { \mathbf { D } \diamond \mathbf { F } } [ Z _ { i + 1 } \vert X ^ { i } Y ^ { i } ] \geq Z _ { i }
$$

instead. Below the sums over $\mathcal { X } \times \mathcal { Y }$ always apply to the random variables $X _ { i + 1 }$ and $Y _ { i + 1 }$ . Lemma 1 is used several times.

$$
\begin{array} { r l } &  \begin{array} { r l } & { \mathrm { E } ^ { \mathrm { i } \phi ( z ) } [ z ] _ { \infty , 1 } \leq ^ { \phi ( T ) } , } \\ & { = \displaystyle \sum _ { s = \phi } \frac { \phi _ { s } ^ { ( s + 1 ) } } { \phi _ { s } ^ { ( s + 1 ) } - \phi _ { s } ^ { ( s + 1 ) } - \phi _ { s } ^ { ( s + 1 ) } } \cdot \overbrace { \mathrm { ~ a n d s s s } \{ \frac { [ \phi _ { s } ^ { ( s + 1 ) } - \phi _ { s } ^ { ( s + 1 ) } - \phi _ { s } ^ { ( s + 1 ) } - \phi _ { s } ^ { ( s ) } ] } { \phi _ { s } ^ { ( s + 1 ) } - \phi _ { s } ^ { ( s ) } } \} } ^ { z _ { s + s } } } \\ & { = \displaystyle \sum _ { s = \phi } \frac { \phi _ { s } ^ { ( s + 1 ) } } { \phi _ { s } ^ { ( s + 1 ) } - \phi _ { s } ^ { ( s ) } - \phi _ { s } ^ { ( s ) } - \phi _ { s } ^ { ( s + 1 ) } } \cdot \overbrace { \mathrm { ~ a n d s s s } \{ \frac { [ \phi _ { s } ^ { ( s + 1 ) } - \phi _ { s } ^ { ( s + 1 ) } - \phi _ { s } ^ { ( s ) } ] } { \phi _ { s } ^ { ( s + 1 ) } + \phi _ { s } ^ { ( s ) } - \phi _ { s } ^ { ( s ) } } \} } ^ { \theta _ { s } ^ { ( s + 1 ) } } } \\ &  = \displaystyle \sum _ { s = \phi } \frac { \theta _ { s } ^ { ( s + 1 ) } } { \phi _ { s } ^ { ( s + 1 ) } - \phi _ { s } ^ { ( s ) } - \phi _ { s } ^ { ( s ) } - \phi _ { s } ^ { ( s ) } } \cdot \overbrace  \mathrm { ~ a n d s s s } \{ \frac { \theta _ { s } ^ { ( s + 1 ) } }  \phi _ { s } ^ { ( s + 1 ) } - \theta _ { s } ^ { ( s ) } - \phi _ { s } ^ { ( s ) } \ \end{array} \end{array}
$$