# Indistinguishability of Random Systems

Ueli Maurer?

ETH Zurich Department of Computer Science maurer@inf.ethz.ch

Abstract. An $( \mathcal { X } , \mathcal { Y } )$ -random system takes inputs $X _ { 1 } , X _ { 2 } , \ldots \in { \mathcal { X } }$ and generates, for each new input $X _ { i }$ , an output $Y _ { i } \in \mathcal { V }$ , depending probabilistically on $X _ { 1 } , \ldots , X _ { i }$ and $Y _ { 1 } , \dots , Y _ { i - 1 }$ . Many cryptographic systems like block ciphers, MAC-schemes, pseudo-random functions, etc., can be modeled as random systems, where in fact $Y _ { i }$ often depends only on $X _ { i }$ , i.e., the system is stateless. The security proof of such a system (e.g. a block cipher) amounts to showing that it is indistinguishable from a certain perfect system (e.g. a random permutation).

We propose a general framework for proving the indistinguishability of two random systems, based on the concept of the equivalence of two systems, conditioned on certain events. This abstraction demonstrates the common denominator among many security proofs in the literature, allows to unify, simplify, generalize, and in some cases strengthen them, and opens the door to proving new indistinguishability results.

We also propose the previously implicit concept of quasi-randomness and give an efficient construction of a quasi-random function which can be used as a building block in cryptographic systems based on pseudorandom functions.

Key words. Indistinguishability, random systems, pseudo-random functions, pseudo-random permutations, quasi-randomness, CBC-MAC.

# 1 Introduction

# 1.1 Indistinguishability

Indistinguishability of two systems, introduced by Blum and Micali [7] for defining pseudo-random bit generators, is a central concept in cryptographic security definitions and proofs. The simplest distinguisher problem is that for two random variables: The success probability (or advantage) of the optimal distinguisher is just the distance of the two probability distributions. As a slight generalization, one can define indistinguishability for infinite sequences of random variables, e.g. of a pseudo-random bit generator from a true random bit generator [7].

It is substantially more difficult to investigate the indistinguishability of two interactive random systems $\mathbf { F }$ and $\mathbf { G }$ because the distinguisher can adaptively choose its inputs (also called queries) to the system, depending on the outputs seen for previous inputs. Every distinguisher $\mathbf { D }$ defines a pair of generally very complex random experiments, one when $\mathbf { D }$ queries $\mathbf { F }$ and the other one when $\mathbf { D }$ queries $\mathbf { G }$ . A security proof requires to prove an upper bound, holding for every $\mathbf { D }$ , on the difference of the probability of some event in the corresponding two experiments. In general, this is a hard probability-theoretic problem.

![](images/0388fe2309fe133b60a28a98661afd0c5d538936b46d7d467389a60f66b0a12b.jpg)  
Fig. 1. Real system S, idealized system I, and perfect system $\mathbf { P }$ .

# 1.2 Security Proofs Based on Pseudo-Random Functions

The security of many cryptographic systems (e.g., block ciphers, message authentication codes, challenge-response protocols) is based on the assumption that a certain component (e.g. DES, IDEA, or Rijndael) used in the construction is a pseudo-random function (PRF) [8]. Such systems are proven secure, relative to this assumption, by showing that any algorithm for breaking the system can be transformed into a distinguisher for the PRF. For example, in a classic paper, Luby and Rackoff [10] showed how to construct a secure block cipher from any pseudo-random function, and Bellare et al. [2] proved the security of the CBC-MAC. The following general steps can be used to prove the security of a cryptographic system based on a pseudo-random function (cf. Fig. 1):

1. The attacker’s capabilities, i.e., the types and number of allowed queries to S are defined. Moreover, security of $\mathbf { s }$ is defined by specifying what it means for the attacker to break S, and a purely theoretical perfect system $\mathbf { P }$ is defined which is trivially secure (see examples below). 2. One considers an idealized system $\mathbf { I }$ obtained from $\mathbf { s }$ by replacing the PRF by a truly random function and proves that $\mathbf { I }$ and $\mathbf { P }$ are informationtheoretically indistinguishable: no adaptive computationally unbounded distinguisher algorithm $\mathbf { D }$ has a non-negligible advantage unless it queries the system for an infeasibly large (e.g. super-polynomial) number of queries.1 3. Hence, because $\mathbf { s }$ is computationally indistinguishable from I if the underlying function is pseudo-random, $\mathbf { s }$ is also computationally indistinguishable from $\mathbf { P }$ . Because $\mathbf { P }$ is unbreakable, there exists no breaking algorithm for $\mathbf { s }$ since it could directly be used as a distinguisher for $\mathbf { s }$ and $\mathbf { P }$ .

Example 1. For a block cipher the attacker is assumed to obtain the ciphertexts (plaintexts) for adaptively chosen plaintexts (ciphertexts). A perfect block cipher is a truly random permutation on the input space.

Example 2. For a MAC, the attacker may obtain the MAC for arbitrary adaptively chosen messages. A perfect MAC is a random oracle, i.e., a random function from $\{ 0 , 1 \} ^ { * }$ , the finite-length bit strings, to the $\it l$ -bit strings (e.g. $l = 6 4$ ).

# 1.3 A Motivating Example

The security proof [2] for the CBC-MAC (cf. Fig. 6), and several generalizations thereof, will follow as a simple consequence of our framework (see Section 6). Roughly speaking, the proof consists of the following simple steps. First, conditioned on the event that all inputs to the internal random function $\mathbf { R }$ (modeling the PRF used in an actual implementation), corresponding to a final block of a message, are distinct, the CBC-MAC behaves like a random oracle, i.e., a perfect MAC. Second, one can hence restrict attention to algorithms trying to prevent this event from occurring by any adaptive choice of the inputs. Third, since the outputs are independent of the inputs, given this event, one can restrict the analysis to non-adaptive strategies, which turn out to be easy to analyze.

# 1.4 Quasi-Randomness

The general idea behind such cryptographic constructions is to “package” a given amount of randomness such that it appears to any observer as a random system $\mathbf { s }$ which behaves essentially like a (in some sense) perfect random system $\mathbf { P }$ containing a much larger amount of randomness. If $\mathbf { s }$ is computationally indistinguishable from $\mathbf { P }$ , it is generally called pseudo-random (with respect to $\mathbf { P }$ ). Informally, we call $\mathbf { s }$ quasi-random (with respect to $\mathbf { P }$ ) if it is indistinguishable from $\mathbf { P }$ , provided only that the amount of interaction (e.g. the number of queries) is bounded, but with otherwise unbounded computational resources.

An important question, addressed in this paper, is how an efficient quasirandom system $\mathbf { s }$ of a certain type can be constructed, using as few random bits as possible, and indistinguishable from the corresponding perfect system $\mathbf { P }$ for as many queries as possible.

# 1.5 Previous Work

Many authors were intrigued by the complexity of certain security proofs in the literature, most notably [10], and have given shorter proofs for these and more general results. It is beyond the scope of this paper to discuss all of these results, but a few are mentioned below. Patarin [14, 15] developed a technique called “coefficient H method” and used it to analyze Feistel ciphers, even with more than four rounds [16]. To the best of our knowledge, the concept of conditioning events in security proofs was first made explicit in [11] and [12] where, using appropriate conditioning events, the proof for the Luby-Rackoff construction and generalizations thereof was shown to boil down to simple collision arguments (but the proof was stated only for non-adaptive distinguishers). Naor and Reingold [18] generalized the Luby-Rackoff constructions. In a sequence of papers (e.g., see [21, 22]), Vaudenay developed decorrelation theory and applied it to the design of block ciphers and the analysis of constructions like the CBC-MAC. Petrank and Rackoff [17] gave a generalized treatment of the CBC-MAC.

# 1.6 Contributions of the Paper

This paper defines the natural concept of a random system and proposes a general framework for proving the indistinguishability of two random systems $\mathbf { F }$ and $\mathbf { G }$ by identifying internal events such that, conditioned on these events, $\mathbf { F }$ and $\mathbf { G }$ are equivalent, i.e., have the identical input-output behavior.

The advantage in distinguishing $\mathbf { F }$ and $\mathbf { G }$ with $k$ queries and unbounded computing power is shown to be at most the probability of success in provoking one of these events not to occur (Lemma 7 and Theorem 1). Under a certain condition, adaptive strategies can be shown to be not more powerful than nonadaptive strategies, thus allowing to eliminate the distinguisher from the analysis (Theorem 2 and Corollary 1).

The framework is illustrated for a few application areas and by giving simple and intuitive analyses and generalizations of some classical results. Due to the high level of abstraction, one can apply the basic techniques in settings where previous proof techniques appeared to be too complex or where changing a small detail in the construction requires a complete rehash of the proof.

Moreover, in some cases one can prove stronger bounds. For instance, under certain conditions one can prove that if a construction involves several components, each indistinguishable from a certain perfect system, then the overall system is distinguishable from its perfect counterpart with probability only the product (rather than the sum or the maximum) of the maximal distinguishing probabilities of the component systems (Theorem 3).

# 1.7 Outline of the Paper

In Section 3 we introduce the concepts of a random automaton and of a random system as well as the equivalence of such systems, define monotone conditions and event sequences, and the conditional equivalence of random systems, and cascades of random systems and the invocation of a random system by another random system. In Section 4 we define the indistinguishability of random systems, prove a few general results on indistinguishability, and discuss the framework for indistinguishability proofs based on conditional equivalence as well as consequences thereof. In Section 5 we apply the framework to the construction of quasi-random functions, and in Sections 6 and 7 to the analysis and security proofs of MAC’s and pseudo-random permutations, respectively.

The treatment is often more general than necessary for proving the results in Sections 5–7. Due to space limitations, many proofs are omitted (but see [13]).

# 2 Notation and Preliminaries

Random variables and concrete values they can take on are usually denoted by capital and small letters, respectively. For a set $\boldsymbol { S }$ , an $\boldsymbol { S }$ -sequence is an infinite (or possibly finite) sequence $s = s _ { 1 } , s _ { 2 } , \ldots$ of elements of $\boldsymbol { S }$ . Prefixes of sequences (of values or random variables) are denoted by a superscript, e.g. $s ^ { k }$ denotes the finite sequence $[ s _ { 1 } , s _ { 2 } , \ldots , s _ { k } ]$ . For a list $L$ of random variables over the same alphabet, $\mathrm { d i s t } ( L )$ denotes the event that all values in $L$ are distinct. Let $p _ { \mathrm { c o l l } } ( n , k )$ denote the probability that $k$ independent random variables with uniform distribution over a set of size $n$ contain a collision, i.e., that they are not all distinct. Of course, $\begin{array} { r } { p _ { \mathrm { c o l l } } ( n , k ) = 1 - \prod _ { i = 1 } ^ { k - 1 } \left( 1 - \frac { i } { n } \right) < \frac { k ^ { 2 } } { 2 n } } \end{array}$ .

In the context of this paper one considers different random experiments, and when analyzing probabilities it is crucial to be precise about which random experiment is considered. The random experiment is usually defined by one or several defining, usually independent, random variables2. We will use these defining random variables as superscripts when denoting probabilities. For example, if $\mathbf { F }$ denotes the system under investigation and $\mathbf { D }$ the distinguisher, then $P ^ { \mathbf { D F } }$ denotes probabilities in the combined random experiment where $\mathbf { D }$ queries $\mathbf { F }$ . In contrast $P ^ { \mathbf { F } }$ denotes probabilities in the simpler random experiment involving only the selection of $\mathbf { F }$ , without even considering a distinguisher. If no superscript is used, the random experiment is clear from the context.

We use the following notation for probability distributions. If $\mathcal { A }$ and $\boldsymbol { B }$ are events and $U$ and $V$ are random variables with ranges $\boldsymbol { \mathcal { U } }$ and $\nu$ , respectively, then $P _ { U \mathcal { A } | V B }$ denotes the corresponding conditional probability distribution, a function ${ \mathcal { U } } \times \mathcal { V } \to \mathbf { R } ^ { + }$ . Thus $P _ { U \mathcal { A } | V B } ( u , v )$ for $u \in \mathcal { U }$ and $v \in \nu$ is well-defined (except if $P _ { V B } ( v ) = 0$ in which case it is undefined). Note that $P _ { A }$ is equivalent to $P ( A )$ . For an event $E$ , $\overline { E }$ denotes the complement of $E$ . Equality of probability distributions means equality as functions, i.e., for all arguments. This extends to the equality of conditional probability distributions, even if one of them contains additional random variables in the conditioning set, meaning that equality holds for all possible values. For example, $P _ { Y ^ { i } \mid X ^ { k } } = P _ { Y ^ { i } \mid X ^ { i } }$ for $k > i$ means that for all $x ^ { k }$ and $y ^ { i }$ , $P _ { Y ^ { i } | X ^ { k } } ( y ^ { i } , x ^ { k } ) = P _ { Y ^ { i } | X ^ { i } } ( y ^ { i } , x ^ { i } )$ .

# 3 Random Systems and Monotone Event Sequences

# 3.1 Sources, Random Automata, and Random Systems

Definitiovariables n, $\mathcal { X }$ -source aracter $\mathbf { s }$ is an infinite sequed by the sequence $\mathbf { S } = S _ { 1 } , S _ { 2 } , \ldots$ of randomonal proba$S _ { i } \in { \mathcal { X } }$ $P _ { S _ { i } | S ^ { i - 1 } } ^ { \bf S }$ |bility distributions. This also defines the distributions $\begin{array} { r } { P _ { S ^ { i } } ^ { \bf S } : = \prod _ { j = 1 } ^ { i } P _ { S _ { i } | S ^ { i - 1 } } ^ { \bf S } } \end{array}$ .

In the following we consider systems which take inputs (or queries) $X _ { 1 } , X _ { 2 } , \ldots \in { \mathcal { X } }$ and generate, for each new input $X _ { i }$ , an output $Y _ { i } \in \mathcal { V }$ . Such a system can be deterministic or probabilistic, and it can be stateless or contain internal memory. A stateless deterministic system is simply a function $\mathcal { X }  \mathcal { V }$ .

![](images/a5faa09e8a0c2d8d5758b81f9819a89302d12fadefb0e87000f64f495aa0e150.jpg)  
Fig. 2. Left: An $( \mathcal { X } , \mathcal { Y } )$ -random system $\mathbf { F }$ takes inputs $X _ { 1 } , X _ { 2 } , X _ { 3 } , . . . \in { \mathcal { X } }$ and outputs $Y _ { 1 } , Y _ { 2 } , Y _ { 3 } , . . . \in \mathcal { V }$ , where f condit $Y _ { i }$ is generated after receivingnal probability distributions $X _ { i }$ It isfor cterized. Right: $P _ { Y _ { i } | X ^ { i } Y ^ { i - 1 } } ^ { \mathbf { F } }$ $i \geq 1$ Random system $\mathbf { F }$ with a monotone event sequence $\mathcal { A } = A _ { 0 } , A _ { 1 } , A _ { 2 } , . . .$ , denoted $\mathbf { F } ^ { A }$ .

Definition 2. A random function $\mathcal { X }  \mathcal { V }$ is a random variable which takes as values functions $\mathcal { X }  \mathcal { V }$ . A deterministic system with state space $\varSigma$ is called an $( \mathcal { X } , \mathcal { Y } )$ -automaton and is described by an infinite sequence $f _ { 1 } , f _ { 2 } , \ldots$ of functions, with $f _ { i } : \mathcal { X } \times \mathcal { X }  \mathcal { Y } \times \mathcal { X }$ , where $( Y _ { i } , S _ { i } ) = f _ { i } ( X _ { i } , S _ { i - 1 } )$ , $S _ { i }$ is the state at time $i$ , and an initial state $S _ { 0 }$ is fixed. An $( \mathcal { X } , \mathcal { Y } )$ -random automaton $\mathbf { F }$ is like an automaton but $f _ { i } : \mathcal { X } \times \mathcal { X } \times \mathcal { R } \longrightarrow \mathcal { Y } \times \mathcal { X }$ (where $\mathcal { R }$ is the space of the internal randomness), together with a probability distribution over $\mathcal { R } \times \Sigma$ specifying the internal randomness and the initial state.3

A large variety of constructions and definitions in the cryptographic literature can be interpreted as random functions, including pseudo-random functions, pseudo-random permutations, and MAC schemes. We consider the more general concept of a (stateful) random system because this is just as simple and because distinguishers can also be modeled as random systems.

The observable input-output behavior of a random automaton $\mathbf { F }$ is referred to as a random system. In the following we use the terms random automaton and random system interchangeably when no confusion is possible.

Defition ition 3. Anprobability d $( \mathcal { X } , \mathcal { Y } )$ -randtions $\mathbf { F }$ r infinite.5 Two $^ 4$ sequence of condandom automata $\underline { { P } } _ { Y _ { i } | X ^ { i } Y ^ { i - 1 } } ^ { \mathbf { F } }$ $i \geq 1$ $\mathbf { F }$ $\mathbf { G }$ ${ \bf F } \equiv { \bf G }$   
system, i.e., if $P _ { Y _ { i } | X ^ { i } Y ^ { i - 1 } } ^ { \mathbf { F } } = P _ { Y _ { i } | X ^ { i } Y ^ { i - 1 } } ^ { \mathbf { G } }$ for $i \geq 1$ .6

The above definition is very general and captures systems that answer several types of queries (in which case the input set $\mathcal { X }$ is the union of the query sets) and for which the behavior depends on the index $i$ . Note that a source can be interpreted as a special type of random system for which the input is ignored, i.e., the outputs are independent of the inputs. We will often assume that the input and output alphabets of a random system are clear from the context.

Let us discuss a few special examples of random systems. Throughout, the symbols $\mathbf { B }$ , $\mathbf { R }$ , $\mathbf { P }$ , and $\mathbf { O }$ are used exclusively for the systems defined below.

Definition 4. An $( \mathcal { X } , \mathcal { Y } )$ -beacon [19] $\mathbf { B }$ is a random system (actually a source) for which $Y _ { 1 } , Y _ { 2 } , \ldots$ are independent and uniformly distributed over $_ { \mathcal { V } }$ , independent of the inputs $X _ { 1 } , X _ { 2 } , \ldots$ A uniform random function (URF) $\mathbf { R } : \mathcal { X }  \mathcal { V }$ (a uniform random permutation (URP) $\mathbf { P }$ on $\mathcal { X }$ ) is a random function with uniform distribution over all functions from $\mathcal { X }$ to $_ { \mathcal { V } }$ (permutations on $\mathcal { X }$ ). A $_ { \mathcal { V } }$ -random oracle $\mathbf { O }$ is a random function with input alphabet $\mathcal { X } = \{ 0 , 1 \} ^ { * }$ with $P _ { Y _ { i } | X _ { i } } ^ { \mathbf { U } } ( y , x ) = 1 / | y |$ for all $i \geq 1$ , $x \in \mathcal { X }$ and $y \in \mathcal { V }$ .

# 3.2 Monotone Conditions and Event Sequences

For a given $( \mathcal { X } , \mathcal { Y } )$ -random function or automaton $\mathbf { F }$ , the evaluation of $Y _ { i }$ usually requires the evaluation of some internal random variables.7 Consider the internal sequence of random variables $U _ { 1 } , U _ { 2 } , \dots$ In the sequel it is very useful to consider an internal condition defined, for each $i$ , after input $X _ { i }$ is entered. As a simple example, the condition could be $\operatorname { d i s t } ( U ^ { i } )$ , i.e., that $U _ { 1 } , \dots , U _ { i }$ are all distinct.

Such an internal condition can be modeled as a binary random variable, say $Z _ { i }$ , indicating whether the condition is satisfied ( $Z _ { i } = 1$ ) or not ( $Z _ { i } = 0$ ) after input $X _ { i }$ has been given. If $Z _ { i }$ is taken as part of the $_ i$ th output of $\mathbf { F }$ , i.e., the $\imath$ th output is the pair $( Y _ { i } , Z _ { i } )$ instead of just $Y _ { i }$ , then this corresponds to a $( \mathcal { X } , \mathcal { Y } \times \{ 0 , 1 \} )$ -random system.8 One can also define several such conditions for $\mathbf { F }$ , each corresponding to a binary random variable.

We will only consider monotone conditions, meaning that once it fails to be satisfied it remains so for all future inputs. For example, the condition $\operatorname { d i s t } ( U ^ { i } )$ is obviously monotone. If $U _ { i }$ is a vector in some vector space, another monotone condition is that $U _ { 1 } , \dots , U _ { i }$ are linearly independent.

For a random automaton $\mathbf { F }$ and a given monotone internal condition we will often be interested in $\mathbf { F }$ ’s behavior only as long as the condition is satisfied. For example, a URF behaves like a beacon as long as the inputs are distinct. We therefore consider the monotone sequence $\mathcal { A } = A _ { 0 } , A _ { 1 } , A _ { 2 } , . . .$ of events, where $A _ { i }$ is the event that the condition is satisfied (and $\overline { { A _ { i } } }$ is the complementary event) and where $A _ { 0 }$ is for convenience defined to be the certain event (cf. Fig. 2).

We will also consider two or more monotone conditions simultaneously. For two monotone event sequences (MES) $\boldsymbol { A }$ and $\boldsymbol { \beta }$ defined for $\mathbf { F }$ , $A \land B$ denotes the MES defined by $( A \land B ) _ { i } = A _ { i } \land B _ { i }$ for $i \geq 1$ , and $\mathcal { A } \lor \mathcal { B }$ is defined analogously.

Definition 5. For MESs $\mathcal { A }$ and $\boldsymbol { \mathscr { C } }$ defined for random automata $\mathbf { F }$ and $\mathbf { G }$ , $\mathbf { F }$ $\boldsymbol { A }$ nt tfor $\mathbf { G }$ with .9 $c$ , denoted $\mathbf { F } ^ { A } \equiv \mathbf { G } ^ { c }$ , if $P _ { Y _ { i } A _ { i } | X ^ { i } Y ^ { i - 1 } A _ { i - 1 } } ^ { \mathbf { F } } = P _ { Y _ { i } C _ { i } | X ^ { i } Y ^ { i - 1 } C _ { i - 1 } } ^ { \mathbf { G } }$ $i \geq 1$

We refer to later sections for examples.

Definitiotioned on 6. For a randomis equivalent to ystem , deno $\mathbf { F }$ d , $\mathcal { A } = A _ { 0 } , A _ { 1 } , A _ { 2 } , . . . , \mathbf { F }$ $\boldsymbol { A }$ $\mathbf { G }$ $\mathbf { F } | \mathcal { A } \equiv \mathbf { G }$ $P _ { Y _ { i } | X ^ { i } Y ^ { i - 1 } A _ { i } } ^ { \mathbf { F } } = P _ { Y _ { i } | X ^ { i } Y ^ { i - 1 } } ^ { \mathbf { G } }$ if for $\mathcal { A }$ $i \geq 1$ , for all arguments for which $\boldsymbol { \beta }$ are defined for $\mathbf { F }$ Yi|X, then we write $P _ { Y _ { i } | X ^ { i } Y ^ { i - 1 } A _ { i } } ^ { \mathbf { F } }$ $\mathbf { F } ^ { B } | \mathcal { A } \equiv \mathbf { G } ^ { \mathcal { C } }$ i| i i| is defined. More generally, if $P _ { Y _ { i } C _ { i } \mid X ^ { i } Y ^ { i - 1 } C _ { i - 1 } } ^ { \bf G } =$ $P _ { Y _ { i } B _ { i } | X ^ { i } Y ^ { i - 1 } B _ { i - 1 } A _ { i } } ^ { \mathbf { F } }$ for $i \geq 1$ .

Definition 7. One can adjoin an MES $\boldsymbol { \mathscr { C } }$ to a random system $\mathbf { G }$ by defining $C _ { i }$ probabilist. If an MES ally on is alrea $X ^ { i }$ and  defin $Y ^ { i }$ , i.e for by a sequence of distributions, then one can adjoin a further $P _ { C _ { i } | X ^ { i } Y ^ { i } C _ { i - 1 } } ^ { \bf G }$ $\boldsymbol { \mathscr { C } }$ $\mathbf { G }$ |MES $\mathcal { D }$ − according to a sequence $P _ { D _ { i } \left| X ^ { i } Y ^ { i } C _ { i } D _ { i - 1 } \right. } ^ { \left. { \bf G } \right. }$ of distributions.10

Lemma 1. (i) If $\mathbf { F } ^ { A } \equiv \mathbf { G } ^ { \mathcal { C } }$ , then $\mathbf { F } | \mathcal { A } \equiv \mathbf { G } | \mathcal { C } ^ { 1 1 }$ (but not vice versa). (ii) If $\mathbf { F } | \mathcal { A } \equiv \mathbf { G }$ , then $\mathbf { F } ^ { A } \equiv \mathbf { G } ^ { C }$ for some MES $\boldsymbol { \mathscr { C } }$ adjoined to $\mathbf { G }$ . ii) Mv) If y, if and $\mathbf { F } ^ { B } | \mathcal { A } \equiv \mathbf { G } ^ { \mathcal { C } }$ $\mathbf { F } ^ { A \wedge B } \equiv \mathbf { G } ^ { c \wedge \mathcal { D } }$ for for $\mathcal { D }$ .or all $\mathbf { F } | \mathcal { A } \equiv \mathbf { G } | \mathcal { C }$ $P _ { A _ { i } | X ^ { i } Y ^ { i - 1 } A _ { i - 1 } } ^ { \mathbf { F } } \leq P _ { C _ { i } | X ^ { i } Y ^ { i - 1 } C _ { i - 1 } } ^ { \mathbf { G } }$ $i \geq 1$ $x ^ { i }$ $y ^ { i - 1 }$ $\mathcal { D }$ $\mathbf { G }$ $\mathbf { F } ^ { A } \equiv \mathbf { G } ^ { \mathcal { C } \wedge \mathcal { D } }$

Proof. Claim (i) is obby defining the MES $\mathcal { D }$ ous. via $\begin{array} { l c l } { { P _ { D _ { i } | X ^ { i } Y ^ { i } C _ { i } D _ { i - 1 } } ^ { \mathbf { G } } } } & { { = } } & { { P _ { A _ { i } | X ^ { i } Y ^ { i - 1 } A _ { i - 1 } B _ { i - 1 } } ^ { \mathbf { F } } } } \end{array}$ ollows. The $P _ { Y _ { i } C _ { i } | X ^ { i } Y ^ { i - 1 } C _ { i - 1 } D _ { i - 1 } } ^ { \bf G } = P _ { Y _ { i } C _ { i } | X ^ { i } Y ^ { i - 1 } C _ { i - 1 } } ^ { \bf G }$ i| i− i− (since P GDi−1 |XiY iCi = P GDi 1 XiY i−1Ci 1 ) and P GYiC $P _ { Y _ { i } C _ { i } | X ^ { i } Y ^ { i - 1 } C _ { i - 1 } } ^ { \bf G } = P _ { Y _ { i } B _ { i } | X ^ { i } Y ^ { i - 1 } B _ { i - 1 } A _ { i } } ^ { \bf F }$ $\mathbf { F } ^ { A } \equiv \mathbf { G } ^ { \mathcal { C } }$ The proof of (iv) is omitted. ut

The following lemma states the trivial fact that given that all inputs are distinct, a random function behaves like a beacon. The proof is obvious.

Lemma 2. Let $c$ ( $\mathcal { D }$ ) be an MES defined on the inputs (outputs) of a system.

(i) $\mathbf { F } | { \mathcal { C } } \equiv \mathbf { F }$ for every random system $\mathbf { F }$ . (ii) If $\mathbf { F } ^ { A } \equiv \mathbf { G } ^ { B }$ , then $\mathbf { F } ^ { A \wedge C } \equiv \mathbf { G } ^ { B \wedge C }$ and $\mathbf { F } ^ { A \wedge \mathcal { D } } \equiv \mathbf { G } ^ { B \wedge \mathcal { D } }$ . (iii) If $C _ { i }$ implies that the first i inputs are distinct, then ${ \bf R } ^ { c } \equiv { \bf B } ^ { c }$ and $\mathbf { R } | { \mathcal { C } } \equiv \mathbf { B }$

# 3.3 Cascades and Invocations of Random Systems

Definition 8. The cascade of an $( \mathcal { X } , \mathcal { Y } )$ -random system $\mathbf { F }$ and a $( { \mathcal { V } } , { \mathcal { Z } } )$ -random system $\mathbf { G }$ , denoted FG, is the $( \mathcal { X } , \mathcal { Z } )$ -random system defined as applying $\mathbf { F }$ to the input sequence and $\mathbf { G }$ to the output of $\mathbf { F }$ (cf. Fig. 3). For MESs $\boldsymbol { A }$ and $\boldsymbol { \beta }$ defined for $\mathbf { F }$ and $\mathbf { G }$ , respectively, $\mathcal { A }$ , $\boldsymbol { B }$ , and $A \land B$ are defined naturally for $\mathbf { F G }$ .

![](images/99bbfdba16ad541a2e67a61fd9f91721b0d451c4cdc616e053ff6a78eecb9a47.jpg)

![](images/4d693b84fa396460ad93c9a25baccff490968226ac9282bede78187553365e42.jpg)  
Fig. 3. The cascade of an $( \mathcal { X } , \mathcal { Y } )$ -random system $\mathbf { F }$ and a $( { \mathcal { V } } , { \mathcal { Z } } )$ -random system $\mathbf { G }$ , denoted $\mathbf { F G }$ . For $\mathbf { F } ^ { A }$ and $\mathbf { G } ^ { B }$ , $\mathbf { F } \mathbf { G } ^ { A \wedge B }$ is defined naturally.   
Fig. 4. A random system $\mathbf { C } ( . )$ invoking an internal random system $\mathbf { F }$ , then the combined random system is $\mathbf { C } ( \mathbf { F } )$ .

Lemma 3. (i) For any source $\mathbf { S }$ and any (compatible) $\mathbf { E }$ we have $\mathbf { E S } \equiv \mathbf { S }$ .   
(ii) If $\mathbf { F } | \mathcal { A } \equiv \mathbf { G }$ , then $\mathbf { E F } | \mathcal { A } \equiv \mathbf { E G }$ for any compatible $\mathbf { E }$ .

We denote by $\mathbf { C } ( . )$ a random system that invokes an internal random system (with specified input and output alphabets). If the internal system is $\mathbf { F }$ , then the combined random system is $\mathbf { C } ( \mathbf { F } )$ (cf. Fig. 4). For the evaluation of the output $Y _ { i }$ for a given input $X _ { i }$ to $\mathbf { C } ( \mathbf { F } )$ , $\mathbf { F }$ is called zero, one, or several times, where the inputs to $\mathbf { F }$ and even the number of such inputs may depend on the state of $\mathbf { C } ( . )$ , hence on $X _ { 1 } , \ldots , X _ { i }$ . 1 2

An MES, say ${ \mathcal { C } } = C _ { 0 } , C _ { 1 } , C _ { 2 } , . . .$ , can be defined also for such a system $\mathbf { C } ( . )$ . If $\mathcal { A }$ is an MES defined for the invoked $\mathbf { F }$ , one can associate a natural corresponding MES $\ddot { \cal A } = \ddot { \cal A } _ { 0 } , \ddot { \cal A } _ { 1 } , \ddot { \cal A } _ { 2 } , \ldots$ with $\mathbf { C } ( \mathbf { F } )$ , where ${ \tilde { A } } _ { i }$ is the event that the $A$ -event occurs for $\mathbf { F }$ up to the evaluation of the $_ i$ th input to $\mathbf { C } ( \mathbf { F } )$ . If $\mathbf { F }$ is called $t$ times for each input to $\mathbf { C } ( \mathbf { F } )$ , then $\tilde { A } _ { i } = A _ { t i }$ . Let $m _ { \mathbf { C } ( . ) } ( k )$ be the maximal number of evaluations of any internal system $\mathbf { F }$ for any sequence of $k$ inputs to $\mathbf { C } ( \mathbf { F } )$ , if it is defined.

The following lemma states the simple fact that by replacing a random system by an equivalent random system, the overall behavior of a system does not change. Let $\mathbf { C } ( . )$ be any random system and let $\mathbf { F }$ and $\mathbf { G }$ be input/output compatible with $\mathbf { C } ( . )$ . Let $A , B$ , and $c$ be defined for $\mathbf { C } ( . )$ , $\mathbf { F }$ and $\mathbf { G }$ , respectively.

![](images/a8e91e29b11dc009df719d8bcc224865c01536e6c8f9766824196f44b5a5d6ba.jpg)  
Fig. 5. Distinguishing two $( \mathcal { X } , \mathcal { Y } )$ -random systems $\mathbf { F }$ and $\mathbf { G }$ by means of a distinguisher $\mathbf { D }$ . The figure shows the two random experiments under consideration.

Proof. The theorem follows directly from the fact that the probability distribution of all random variables and events occurring in $\mathbf { C } ( . ) ^ { c }$ , when including $\mathcal { A } = A _ { 0 } , A _ { 1 } , A _ { 2 } , . . .$ (or $\boldsymbol { B } = B _ { 0 } , B _ { 1 } , B _ { 2 } , . ~ . . .$ , is the product of conditional distributions defined by the random system and by $\mathbf { C } ( . )$ . The conditional distributions defined by $\mathbf { C } ( . )$ are trivially identical and those defined by $\mathbf { F } ^ { A }$ (or $\mathbf { G } ^ { B }$ ) are identical in both cases because of $\mathbf { F } ^ { A } \equiv \mathbf { G } ^ { B }$ . ut

# 4 Indistinguishability Proofs for Random Systems

# 4.1 Distinguishers for Random Systems

We consider the problem of distinguishing two $( \mathcal { X } , \mathcal { Y } )$ -random systems $\mathbf { F }$ and $\mathbf { G }$ by means of a computationally unbounded, possibly probabilistic adaptive distinguisher algorithm (or simply distinguisher) $\mathbf { D }$ asking at most $k$ queries, for some $k$ (cf. Fig. 5). The distinguisher generates $X _ { 1 }$ as an input to $\mathbf { F }$ (or $\mathbf { G }$ ), receives the output $Y _ { 1 }$ , then generates $X _ { 2 }$ , receives $Y _ { 2 }$ , etc. Finally, after receiving $Y _ { k }$ , it outputs a binary decision bit. More formally:

Definition 9. A distinguisher for $( \mathcal { X } , \mathcal { Y } )$ -random systems is a $( \mathcal { V } , \mathcal { X } )$ -random system $\mathbf { D }$ together with an initial value $X _ { 1 } \in { \mathcal { X } }$ which outputs a binary decision value after some specified number $k$ of queries to the system. Without loss of generality we can assume that $\mathbf { D }$ outputs a binary value after every query and that this sequence is monotone ( $0$ never followed by 1), i.e., we can define the MES $\mathcal { E } = E _ { 0 } , E _ { 1 } , E _ { 2 } , . . .$ where $E _ { i }$ is the event that $\mathbf { D }$ outputs 1 after the $i$ -th query. Application of $\mathbf { D }$ to a random system $\mathbf { F }$ (cf. Fig. 5) means that $X _ { 1 }$ is the first input to $\mathbf { F }$ , the $i$ -th input and output of $\mathbf { D }$ are $Y _ { i }$ and ${ \ddot { X } } _ { i }$ , respectively, and $X _ { i } : = \ddot { X } _ { i - 1 }$ for $i \geq 2$ is the $i$ -th input to $\mathbf { F }$ .

Definition 10. The maximal advantage, of any distinguisher issuing $k$ queries, for distinguishing $\mathbf { F }$ and $\mathbf { G }$ , is

$$
\begin{array} { r } { \Delta _ { k } ( { \bf F } , { \bf G } ) : = \displaystyle \operatorname* { m a x } _ { { \bf D } } \left| P ^ { { \bf D } { \bf F } } ( E _ { k } ) - P ^ { { \bf D } { \bf G } } ( E _ { k } ) \right| . } \end{array}
$$

We summarize a few simple facts used in many security proofs. The inequalities hold for any compatible random automata or random systems.

Lemma 5. (i) $\varDelta _ { k } ( \mathbf { F } , \mathbf { H } ) \leq \varDelta _ { k } ( \mathbf { F } , \mathbf { G } ) + \varDelta _ { k } ( \mathbf { G } , \mathbf { H } )$ .   
(ii) $\Delta _ { k } ( { \bf C } ( { \bf F } ) , { \bf C } ( { \bf G } ) ) \le \Delta _ { k ^ { \prime } } ( { \bf F } , { \bf G } )$ , where $k ^ { \prime } = m _ { \mathbf { C } ( . ) } ( k )$ .

(iii) $\varDelta _ { k } ( \mathbf { F } \mathbf { F } ^ { \prime } , \mathbf { G } \mathbf { G } ^ { \prime } ) \leq \varDelta _ { k } ( \mathbf { F } , \mathbf { G } ) + \varDelta _ { k } ( \mathbf { F } ^ { \prime } , \mathbf { G } ^ { \prime } )$ . (iv) (Informal.) If $\varDelta _ { k } ( \mathbf { F } , \mathbf { G } )$ is negligible in $k$ and $\mathbf { G }$ is computationally indistinguishable from $\mathbf { H }$ , then $\mathbf { F }$ is also computationally indistinguishable from $\mathbf { H }$ .

Proof. (i) follows by a simple application of the triangle inequality $| c - a | \le$ $| b - a | + | c - b |$ for any real $a , b$ , and $c$ , applied to $a = P ^ { \mathbf { D F } } ( E _ { k } )$ , $b = P ^ { \mathbf { D G } } ( E _ { k } )$ , and $c = P ^ { \bf D \bf H } ( E _ { k } )$ for any distinguisher $\mathbf { D }$ . To prove (ii), suppose for the sake of contradiction that there exists a distinguisher for $\mathbf { C } ( \mathbf { F } )$ and $\mathbf { C } ( \mathbf { G } )$ , asking at most $k$ queries, with advantage greater than $\varDelta _ { k ^ { \prime } } ( \mathbf { F } , \mathbf { G } )$ . By simulating $\mathbf { C } ( . )$ one can construct a distinguisher for $\mathbf { F }$ and $\mathbf { G }$ with the same advantage, asking at most $k ^ { \prime }$ queries. This is a contradiction. Now we prove (iii). From (ii) we have $\varDelta _ { k } ( \mathbf { F } \mathbf { F } ^ { \prime } , \mathbf { G } \mathbf { F } ^ { \prime } ) \leq \varDelta _ { k } ( \mathbf { F } , \mathbf { G } )$ and $\Delta _ { k } ( \mathbf { G } \mathbf { F } ^ { \prime } , \mathbf { G } \mathbf { G } ^ { \prime } ) \leq \varDelta _ { k } ( \mathbf { F } ^ { \prime } , \mathbf { G } ^ { \prime } )$ . Now we apply (i) to the random systems $\mathbf { F } \mathbf { F } ^ { \prime }$ , $\mathbf { G F ^ { \prime } }$ , and $\mathbf { G } \mathbf { G } ^ { \prime }$ . The proof of (iv) is omitted. ut

It is easy to see that the described view of a distinguisher $\mathbf { D }$ is equivalent to an alternative view where $\mathbf { D }$ is given access to a blackbox containing $\mathbf { F }$ or $\mathbf { G }$ with probability $\textstyle { \frac { 1 } { 2 } }$ each, where $\mathbf { D }$ must guess which of the two is the case. The best success probability with $k$ queries is $\begin{array} { r } { \frac { 1 } { 2 } + \frac { 1 } { 2 } \varDelta _ { k } ( \mathbf { F } , \mathbf { G } ) } \end{array}$ .

# 4.2 Indistinguishability Proofs Based on Conditional Equivalence

In this section we prove that if $\mathbf { F } | { \mathcal { A } } \equiv \mathbf { G }$ for some MES $\mathcal { A }$ (or if $\mathbf { F } ^ { A } \equiv \mathbf { G } ^ { B }$ ), then a distinguisger $\mathbf { D }$ for distinguishing $\mathbf { F }$ from $\mathbf { G }$ with $k$ queries (according to the view described above) must provoke the event $\overline { { A _ { k } } }$ in $\mathbf { F }$ in order to have a non-zero advantage. Informally this could be proved by assuming a genie sitting inside $\mathbf { F }$ and beeping when it sees that ${ \overline { { A } } } _ { i }$ occurs for some $_ i$ . The genie’s help can only help since it could always be ignored, and given the genie’s help, the optimal strategy would be to guess “ $\mathbf { r }$ ” if the genie beeps and to flip a fair coin between $\mathbf { F }$ and $\mathbf { G }$ otherwise. Therefore we consider distinguishers $\mathbf { D }$ that try to provoke the event $\overline { { A _ { k } } }$ .

Definition 11. For a random system $\mathbf { F }$ with MES $\boldsymbol { A }$ , let

$$
\nu ( \mathbf { F } , \overline { { A _ { k } } } ) : = \operatorname* { m a x } _ { \mathbf { D } } P ^ { \mathbf { D F } } ( \overline { { A _ { k } } } )
$$

be the maximal probability, for any adaptive strategy $\mathbf { D }$ , of provoking $\overline { { A _ { k } } }$ in $\mathbf { F }$ Moreover, let

$$
\mu ( \mathbf { F } , { \overline { { A _ { k } } } } ) : = \operatorname* { m a x } _ { x ^ { k } } P _ { A _ { k } | X ^ { k } } ^ { \mathbf { F } } ( x ^ { k } )
$$

be the maximal probability of $\overline { { A _ { k } } }$ for non-adaptive algorithms querying $\mathbf { F }$ .

and $\nu ( \mathbf { C } ( \mathbf { F } ) , \overline { { \tilde { A } _ { k } } } ) \leq \nu ( \mathbf { F } , \overline { { A _ { k ^ { \prime } } } } )$ , where $k ^ { \prime } = m _ { \mathbf { C } ( . ) } ( k )$ .   
(v) If $\boldsymbol { A }$ is defined on the inputs of $\mathbf { F }$ , then $\mu ( \mathbf { E F } , { \overline { { A _ { k } } } } ) = \mu ( \mathbf { E } , { \overline { { A _ { k } } } } )$ for any $\mathbf { E }$ .

Proof. (i) holds because the set of adaptive strategies includes the non-adaptive ones. Claim (ii) follows from $\nu ( { \bf F } , \overline { { A _ { k } } } ) = 1 - \nu ( { \bf F } , A _ { k } )$ and $\nu ( { \bf G } , \overline { { B _ { k } } } ) = 1 -$ $\nu ( \mathbf G , B _ { k } )$ , using $\nu ( { \bf F } , A _ { k } ) = \nu ( { \bf G } , B _ { k } )$ which follows from Lemma 4. Claim (iii) is a simple application of the union bound together with the fact that if different systems $\mathbf { D }$ can be used to provoke $\overline { { A _ { k } } }$ and $\overline { { B _ { k } } }$ , this can only improve the success probability. Claim (iv) follows from the fact that $\mathbf { C } ( . )$ can be used as a possible algorithm for provoking $\overline { { A _ { k } } }$ in $\mathbf { F }$ , and similarly $\mathbf { F }$ can be used as the random system in an algorithm for provoking $\overline { { B _ { k } } }$ in $\mathbf { C } ( . )$ . Claim (v) is trivial. ut

Lemma 7. If $\mathbf { F } ^ { A } \equiv \mathbf { G } ^ { B }$ , then for any (compatible) distinguisher $\mathbf { D }$ and any event $E _ { k }$ defined in $\mathbf { D }$ after $k$ queries,

$$
\big | P ^ { \mathbf { D F } } ( E _ { k } ) - P ^ { \mathbf { D G } } ( E _ { k } ) \big | \leq P ^ { \mathbf { D F } } ( \overline { { A _ { k } } } ) = P ^ { \mathbf { D G } } ( \overline { { B _ { k } } } ) .
$$

Proof. Lemma 4 gives $P ^ { \mathbf { D F } } ( E _ { k } \wedge A _ { k } ) = P ^ { \mathbf { D G } } ( E _ { k } \wedge B _ { k } ) \leq P ^ { \mathbf { D G } } ( E _ { k } )$ . Thus

$$
P ^ { \mathbf { D F } } ( E _ { k } ) = P ^ { \mathbf { D F } } ( E _ { k } \wedge A _ { k } ) + P ^ { \mathbf { D F } } ( E _ { k } \wedge \overline { { A _ { k } } } ) \leq P ^ { \mathbf { D G } } ( E _ { k } ) + P ^ { \mathbf { D F } } ( \overline { { A _ { k } } } ) .
$$

$P ^ { \mathbf { D G } } ( E _ { k } ) \ \leq \ P ^ { \mathbf { D F } } ( E _ { k } ) + P ^ { \mathbf { D G } } ( \overline { { B _ { k } } } )$ follows by symmetry, and $P ^ { \bf D F } ( \overline { { A _ { k } } } ) =$ $P ^ { \bf D G } ( \overline { { B _ { k } } } )$ follows from Lemma 4. ut

Theorem 1. (i) If $\mathbf { F } ^ { A } \equiv \mathbf { G } ^ { B }$ or $\mathbf { F } | \mathcal { A } \equiv \mathbf { G }$ , then $\varDelta _ { k } ( \mathbf { F } , \mathbf { G } ) \leq \nu ( \mathbf { F } , \overline { { \varDelta _ { k } } } )$ .   
(iii) If (ii) If $\mathbf { F } ^ { B } | \mathcal { A } \equiv \mathbf { G } ^ { \mathcal { C } }$ $\mathbf { F } | { \mathcal { A } } \equiv \mathbf { G } | { \mathcal { C } }$ , then and $\begin{array} { r } { \varDelta _ { k } ( \mathbf { F } , \mathbf { G } ) \leq \nu ( \mathbf { F } , \overline { { A _ { k } } } \vee \overline { { B _ { k } } } ) \leq \nu ( \mathbf { F } , \overline { { A _ { k } } } ) + \nu ( \mathbf { G } , \overline { { C _ { k } } } } \end{array}$ $P _ { A _ { i } | X ^ { i } Y ^ { i - 1 } A _ { i - 1 } } ^ { \bf F } \ \le \ P _ { C _ { i } | X ^ { i } Y ^ { i - 1 } C _ { i - 1 } } ^ { \bf G }$ for $i ~ \geq ~ 1$ , then ).   
$\varDelta _ { k } ( \mathbf { F } , \mathbf { G } ) \leq \nu ( \mathbf { F } , \overline { { \varDelta _ { k } } } )$ .

Proof. The first claim of (i) is a special case of Lemma 7, where $\mathbf { D }$ is the distinguisher with MES $\varepsilon$ . The second claim of (i) is a special case of (ii), which is proved as follows. According to Lemma 1 (iii) we have $\mathbf { F } ^ { A \wedge B } \equiv \mathbf { G } ^ { \mathcal { C } \wedge \mathcal { D } }$ for some MES $\mathcal { D }$ defined for $\mathbf { G }$ . Thus we can apply (i). The last inequality of (ii) follows because for any $\mathbf { D }$ , $P ^ { \mathbf { D F } } ( \overline { { A _ { k } } } \lor \overline { { B _ { k } } } ) \leq P ^ { \mathbf { D F } } ( \overline { { A _ { k } } } ) + P ^ { \mathbf { D F } } ( \overline { { B _ { k } } } | A _ { k } )$ , and since if $P ^ { \mathbf { D F } } ( \overline { { A _ { k } } } )$ and $P ^ { \bf D \bf F } ( \overline { { B _ { k } } } | A _ { k } )$ can be maximized separately by choices of $\mathbf { D }$ , this is an upper bound on $\operatorname* { m a x } _ { \mathbf { D } } P ^ { \mathbf { D F } } ( { \overline { { A _ { k } } } } \lor { \overline { { B _ { k } } } } )$ . Moreover, $\mathrm { m a x } _ { \bf D } P ^ { \bf D F } ( \overline { { B _ { k } } } | A _ { k } ) =$ $\operatorname * { m a x } _ { \mathbf { D } } P ^ { \mathbf { D G } } ( { \overline { { C _ { k } } } } ) \ = \ \nu ( \mathbf { G } , { \overline { { C _ { k } } } } )$ . To prove (iii), adjoin the MES $\mathcal { D }$ to $\mathbf { G }$ as in Lemma 1 (iv) and apply (i) of this corollary. $\boxed { \begin{array} { r l } \end{array} }$

# 4.3 Adaptive Versus Non-Adaptive Strategies

It is generally substantially easier to analyze non-adaptive as opposed to adaptive strategies, e.g. for distinguishing two random systems. The following theorem states simple and easily checkable conditions for a random system $\mathbf { F }$ with MES $\boldsymbol { A }$ which implies that no adaptive strategy for provoking $\overline { { A } } _ { k }$ is better than the best non-adaptive strategy. The optimal strategy hence selects (one of) the fixed input sequence(s) $x ^ { k }$ that minimizes P FAk Xk (xk) (or equivalently, maximizes |P FA Xk (xk)). Hence the system D (over choices of which the definition of $\nu ( \mathbf { F } , \overline { { A _ { k } } } )$ maximizes) can be eliminated from the analysis.

Theorem 2. If a random system $\mathbf { F }$ with MES $\mathcal { A }$ satisfies

$$
P _ { A _ { i } | X ^ { i } Y ^ { i - 1 } A _ { i - 1 } } ^ { \mathbf { F } } = P _ { A _ { i } | X ^ { i } A _ { i - 1 } } ^ { \mathbf { F } }
$$

for $i \geq 1$ , which holds if

$$
P _ { Y ^ { i } | X ^ { i } A _ { i } } ^ { \mathbf { F } } = P _ { Y ^ { i } | X ^ { i } } ^ { \mathbf { G } }
$$

for $i \geq 1$ , for some system $\mathbf { G }$ (actually, $\mathbf { G } \equiv \mathbf { F } | \mathcal { A } )$ , then $\nu ( \mathbf { F } , \overline { { A _ { k } } } ) = \mu ( \mathbf { F } , \overline { { A _ { k } } } )$ .

Corollary 1. (i) If $\mathcal { A }$ is defined on the inputs of $\mathbf { F }$ , then $\mathbf { F }$ satisfies $( 1 )$ . (ii) If $\mathbf { F }$ with $\mathcal { A }$ satisfy $( 1 )$ , then so does FG with $\mathcal { A }$ for any (compatible) $\mathbf { G }$ . (iii) If $\nu ( \mathbf { F } , \overline { { A _ { k } } } ) = \mu ( \mathbf { F } , \overline { { A _ { k } } } )$ , then $\nu ( \mathbf { F G } , \overline { { A _ { k } } } ) = \mu ( \mathbf { F } , \overline { { A _ { k } } } )$ for any $\mathbf { G }$ . (iv) If $A$ is defined on the inputs of $\mathbf { F }$ and $\mathbf { F } | { \mathcal { A } } \equiv \mathbf { U }$ for a source $\mathbf { U }$ , then $\nu ( \mathbf { E F } , { \overline { { A _ { k } } } } ) = \mu ( \mathbf { E } , { \overline { { A _ { k } } } } )$ for any $\mathbf { E }$ . $( \mathbf { v } )$ If $A _ { i }$ $( B _ { i } )$ is defined on the inputs (outputs) of $\mathbf { F }$ and $\mathbf { F } ^ { B } | \mathcal { A } \equiv \mathbf { U } ^ { B }$ for $a$ source $\mathbf { U }$ , then $\nu ( \mathbf { E F } , \overline { { A _ { k } } } \vee \overline { { B _ { k } } } ) \le \mu ( \mathbf { E } , \overline { { A _ { k } } } ) + \mu ( \mathbf { U } , \overline { { B _ { k } } } )$ for any $\mathbf { E }$ . (vi) If $\mathcal { A }$ is defined on the inputs of $\mathbf { F }$ and $\mathbf { F } | { \mathcal { A } } \equiv \mathbf { B }$ , then for any random system $\mathbf { C } ( . )$ such that $\mathbf { C } ( \mathbf { B } ) \equiv \mathbf { B }$ , $\nu ( \mathbf { C } ( \mathbf { F } ) , \overline { { A _ { k } } } ) = \mu ( \mathbf { C } ( \mathbf { F } ) , \overline { { A _ { k } } } )$ .

# 4.4 Exploiting Independent Events

Consider a random system $\mathbf { C } ( . , . )$ invoking two independent random systems $\mathbf { F }$ and $\mathbf { G }$ with MESs $\mathcal { A }$ and $\boldsymbol { B }$ , respectively. For each input to $\mathbf { C } ( \mathbf { F } , \mathbf { G } )$ , $\mathbf { F }$ and $\mathbf { G }$ can be called several times. For a given $k$ , let $k ^ { \prime }$ and $k ^ { \prime \prime }$ be the maximal number of invocations of $\mathbf { F }$ and $\mathbf { G }$ , respectively, for any input sequence to $\mathbf { C } ( \mathbf { F } , \mathbf { G } )$ o f length $k$ .

Theorem 3. If $\mathbf { C } ( \mathbf { F } , \mathbf { G } ) | ( \tilde { \mathcal { A } } \vee \tilde { \mathcal { B } } ) \equiv \mathbf { H }$ , then

$$
\begin{array} { r } { \varDelta _ { k } ( \mathbf { C } ( \mathbf { F } , \mathbf { G } ) , \mathbf { H } ) \leq \nu ( \mathbf { F } , \overline { { \tilde { A _ { k ^ { \prime } } } } } ) \cdot \nu ( \mathbf { G } , \overline { { \tilde { B _ { k ^ { \prime \prime } } } } } ) . } \end{array}
$$

Proof. We have

$$
\begin{array} { r l } & { \varDelta _ { k } ( { \mathbf { C } ( \mathbf { F } , \mathbf { G } ) } , \mathbf { H } ) \leq \nu ( { \mathbf { C } ( \mathbf { F } , \mathbf { G } ) } , \overline { { \tilde { \mathcal { A } _ { k ^ { \prime } } } } } \wedge \overline { { \tilde { \mathcal { B } _ { k ^ { \prime \prime } } } } } ) = \underset { { \mathbf { D } } } { \operatorname* { m a x } } P ^ { { \mathbf { D C F G } } } ( \overline { { \tilde { \mathcal { A } _ { k ^ { \prime } } } } } \wedge \overline { { \tilde { B _ { k ^ { \prime \prime } } } } } ) } \\ & { \qquad = \underset { { \mathbf { D } } } { \operatorname* { m a x } } \left( P ^ { { \mathbf { D C F G } } } ( \overline { { \tilde { \mathcal { A } _ { k ^ { \prime } } } } } ) \cdot P ^ { { \mathbf { D C F G } } } ( \overline { { \tilde { \cal B _ { k ^ { \prime \prime } } } } } | \overline { { \tilde { \mathcal { A } _ { k ^ { \prime } } } } } ) \right) } \\ & { \qquad \leq \quad \underbrace { \underset { { \mathbf { D } } } { \operatorname* { m a x } } P ^ { { \mathbf { D C F G } } } ( \overline { { \tilde { \mathcal { A } _ { k ^ { \prime } } } } } ) } _ { = \nu ( { \mathbf { C } ( \mathbf { F } , \mathbf { G } ) } , \overline { { \tilde { \mathcal { A } _ { k ^ { \prime } } } } } ) \leq \nu ( \mathbf { F } , \overline { { \tilde { \mathcal { A } _ { k ^ { \prime } } } } } ) } \cdot \underbrace { \underset { { \mathbf { D } } } { \operatorname* { m a x } } P ^ { { \mathbf { D C F G } } } ( \overline { { \tilde { \mathcal { B } _ { k ^ { \prime \prime } } } } } | \overline { { \tilde { \mathcal { A } _ { k ^ { \prime } } } } } ) } _ { \leq \nu ( \mathbf { G } , \overline { { \mathcal { B } _ { k ^ { \prime \prime } } } } ) } . } \end{array}
$$

The last inequality holds because in the expression on the last line the two maximizations over choices of $\mathbf { D }$ are independent, as opposed to the previous line. We have $\nu ( { \bf C } ( { \bf F } , { \bf G } ) , \overline { { \tilde { A _ { k ^ { \prime } } } } } ) ~ \leq ~ \nu ( { \bf F } , \overline { { \tilde { A _ { k ^ { \prime } } } } } )$ by Lemma 6 (iv) and $\operatorname* { m a x } _ { \mathbf { D } } P ^ { \mathbf { D C F G } } ( \tilde { \vec { B _ { k ^ { \prime \prime } } } } \bar { \vec { A _ { k ^ { \prime } } } } ) \leq \nu ( \mathbf { G } , \overline { { \vec { B _ { k ^ { \prime \prime } } } } } )$ because for every particular choices for $\mathbf { s }$ , $\mathbf { C }$ , and $\mathbf { F }$ , the probability of $\tilde { B _ { k ^ { \prime \prime } } }$ is at most $\nu ( \mathbf { G } , \overline { { B _ { k ^ { \prime \prime } } } } )$ , whether or not $\widetilde { A _ { k ^ { \prime } } }$ occurs for these choices. Thus the bound on $\nu ( \mathbf { G } , \tilde { B _ { k ^ { \prime \prime } } } )$ also holds on average. ut

Corollary 2. Let $\mathbf { F }$ with MES $\boldsymbol { A }$ and $\mathbf { G }$ with MES $\boldsymbol { \beta }$ be random permutations such that $\mathbf { F } | { \mathcal { A } } \equiv \mathbf { P }$ and $\mathbf { G } | \boldsymbol { B } \equiv \mathbf { P }$ . Then $\varDelta _ { k } ( \mathbf { F G } , \mathbf { P } ) \leq \nu ( \mathbf { F } , \overline { { \tilde { A _ { k ^ { \prime } } } } } ) \cdot \nu ( \mathbf { G } , \overline { { \tilde { B _ { k ^ { \prime \prime } } } } } )$ .

Proof. We have $\mathbf { F G } | ( \mathcal { A } \lor \mathcal { B } ) \equiv \mathbf { P }$ , hence Theorem 3 can be applied.15

For two $( \mathcal { X } , \mathcal { Y } )$ -random automata $\mathbf { F }$ and $\mathbf { G }$ and a group operation $\star$ on $_ { \mathcal { V } }$ , let ${ \bf F } \star { \bf G }$ denote the random automaton obtained by using $\mathbf { F }$ and $\mathbf { G }$ in parallel (with the same input) and combining the two outputs using $\star$ .

Corollary 3. If $\mathbf { F } | \mathcal { A } \equiv \mathbf { G } | \mathcal { B } \equiv \mathbf { R }$ , then $\varDelta _ { k } ( \mathbf { F } \star \mathbf { G } , \mathbf { R } ) \leq \nu ( \mathbf { F } , \overline { { \varDelta _ { k } } } ) \cdot \nu ( \mathbf { G } , \overline { { \varDelta _ { k } } } ) .$

Proof. We have $( \mathbf { F } \star \mathbf { G } ) | ( A \lor B ) \equiv \mathbf { R }$ , hence Theorem 3 can be applied.

# 5 Applications to Quasi-Random Functions

# 5.1 Quasi-Random Functions

Definition 12. For a function $d \mathbf { \Sigma } : \textbf { N } \to \mathbf { \Sigma } \mathbf { R } ^ { + }$ , a random function or random system $\mathbf { F }$ is called a $d ( k )$ -quasi-random function ( $d ( k )$ -QRF for short) if $\varDelta _ { k } ( \mathbf { F } , \mathbf { R } ) \leq d ( k )$ for $k \geq 1$ . Quasi-random permutations, beacons and oracles are defined analogously, replacing $\mathbf { R }$ by $\mathbf { P }$ , $\mathbf { B }$ , and $\mathbf { O }$ , respectively.

By concatenating, for any $w$ , $2 ^ { w }$ outputs of a $d ( k )$ -QRF $\{ 0 , 1 \} ^ { l } \to \{ 0 , 1 \} ^ { m }$ one obtains a $\tilde { d } ( k )$ -QRF $\{ 0 , 1 \} ^ { l - w }  \{ 0 , 1 \} ^ { 2 ^ { w } m }$ for $d ( k ) = d ( 2 ^ { w } k )$ , thus increasing the output size by a factor $2 ^ { w }$ at the expense of reducing the input size by $w$ bits.

The problem considered in this section is to expand the input size substantially at the sole expense of increasing $d ( k )$ moderately, i.e., to expand a given supply of random bits into a much larger supply of apparently random bits.

This general problem is important because the core of a cryptographic system based on a PRF corresponds to the construction of a quasi-random system of the same type from a URF $\mathbf { R }$ . In any such construction, $\mathbf { R }$ can be replaced by a QRF, possibly constructed recursively from smaller QRF’s, where at the lowest level the randomness is replaced by the PRF. This can for instance be used to avoid the birthday problem when collisions are a security issue (see below).

For any $d ( k )$ -QRF $\mathbf { G } : \{ 0 , 1 \} ^ { L } \to \{ 0 , 1 \} ^ { M }$ constructed from a URF $\mathbf { R }$ : $\{ 0 , 1 \} ^ { l } \to \{ 0 , 1 \} ^ { m }$ it is obvious that $d ( k )$ cannot be negligible for $k > 2 ^ { l } m / M$ , i.e., when the internal randomness is exhausted. One could achieve $d ( k ) = 0$ for up to $k \approx 2 ^ { l } m / M$ by defining $\mathbf { G }$ as the evaluation of a polynomial whose coefficients are taken from the function table of $\mathbf { R }$ , but this construction would be exponentially inefficient since the entire table of $\mathbf { R }$ must be read for each evaluation of $\mathbf { G }$ . Efficiency, i.e., the number of evaluations of $\mathbf { R }$ required for one evaluation of $\mathbf { G }$ , is an important parameter of a construction. There is a trade-off between the efficiency and the degree $d ( k )$ of indistinguishability.

# 5.2 An Efficient Construction of a Quasi-Random Function

We now propose the construction of an efficient QRF $\mathbf { C } ( \mathbf { F } ) : \{ 0 , 1 \} ^ { L }  \{ 0 , 1 \} ^ { m }$ from a QRF ${ \bf F } : \{ 0 , 1 \} ^ { l }  \{ 0 , 1 \} ^ { m }$ , for $L \gg l$ . The basic idea for the definition of $\mathbf { C } ( . )$ is to map an argument to $\mathbf { C } ( . )$ to a list of $t$ arguments for $\mathbf { F }$ and to XOR the corresponding values of $\mathbf { F }$ . In fact, we can (but need not) use the convention that if a list contains a value more than once, these values are ignored, resulting in fewer than $t$ values being XORed.

One can associate, in a natural manner, with each such set of $t$ values a characteristic vector, with at most $t$ 1-entries, in the vector space $\{ 0 , 1 \} ^ { 2 ^ { l } }$ . The described XORing operation corresponds to computing the scalar product of the characteristic vector with the function table of $\mathbf { F }$ (interpreted as a vector in $( \{ 0 , 1 \} ^ { m } ) 2 ^ { l } )$ .

Hence Lemma 11 in the Appendix implies that, given the event that these $k$ vectors (for the $k$ arguments to $\mathbf { C } ( . )$ ) are linearly independent, the construction is equivalent to a URF (and also a beacon). Therefore Theorem 1 (i) can be applied.

It only remains to find a mapping $\mathbf { H } : \{ 0 , 1 \} ^ { L } \to S$ , where $S$ is the subset of the vector space $\{ 0 , 1 \} ^ { 2 ^ { l } }$ consisting of the vectors of weight at most $t$ . The internal randomness of $\mathbf { H }$ can actually be taken from the function table of $\mathbf { F }$ (say for the $z$ highest values, where $z$ is an appropriate small number). For this to be secure, the mapping $\mathbf { H }$ must be restricted slightly to generate vectors with no 1-entry in the last $z$ coordinates.

Lemma 12 in the Appendix shows that $\mathbf { H }$ can be implemented by using a $2 t$ -wise random function $\textbf { E } : \{ 0 , 1 \} ^ { L } \times \{ 1 , . . . , t \}  \{ 0 , . . . , 2 ^ { l } - z - 1 \}$ . For an argument $x \in \{ 0 , 1 \} ^ { L }$ of $\mathbf { H }$ , ${ \bf E } ( x , i )$ for $1 \leq i \leq t$ is evaluated and the corresponding characteristic vector is formed.16 Note that the $z$ unit vectors with 1-entries in one of the top $z$ positions must also be taken into account in Lemma 12, but they are of course linearly independent of the $k$ vectors discussed above.

Hence we have outlined the proof of the following theorem.

Theorem 4. For a $d ( k )$ -QRF $\mathbf { F }$ , $\mathbf { C } ( \mathbf { F } )$ is a $\tilde { d } ( k )$ -QRF for $\begin{array} { r } { \tilde { d } ( k ) = k \left( \frac { k t } { 2 ^ { l } } \right) ^ { t } + } \end{array}$ $d ( t k + z )$ .

The term $k ( k t / 2 ^ { l } ) ^ { t }$ is very small, even for $k \gg 2 ^ { l / 2 }$ for which collisions among random values in the input space of $\mathbf { F }$ would be very probable. This was called “security beyond the birthday barrier” in $[ 1 ] ^ { 1 7 }$ Already for moderate values of $t$ , the described construction achieves a negligible ${ \ddot { d } } ( k )$ for $k \approx 2 ^ { l t / ( t + 1 ) }$ , i.e., far beyond the birthday barrier.

The above construction ideas apply in other contexts as well, for instance the use of some values of a PRF as the key of another component in a manner that does not compromise security. Note that the security of the XOR-MAC [3] and of other constructions based on linearly independent inputs (e.g. [1]) follow directly from Lemma 11 as well as a (non-adaptive) analysis of the linear independence event. For the XOR-MAC the analysis of this event is trivial.

# 6 Applications to MAC’s

A secure MAC-scheme is a PRF $\mathcal { M } \to \{ 0 , 1 \} ^ { l }$ for $\mathcal { M } = \cup _ { i = 1 } ^ { L } \{ 0 , 1 \} ^ { i }$ for some maximal message length $L$ and an appropriate security parameter $\it l$ . If $L = \infty$ , then this corresponds to a pseudo-random oracle.

A very natural construction originating in [23] and used in many later papers (e.g. see [5, 20] and the discussion and references therein) is to apply an $\epsilon$ -almost universal hash function $^ { 1 8 }$ $\mathbf { U } : \mathcal { M }  \mathcal { X }$ for some $\mathcal { X }$ to the message and to apply a PRF $\mathbf { F } : \mathcal { X } \longrightarrow \{ 0 , 1 \} ^ { l }$ to the result. Such a scheme has two keys, those of $\mathbf { U }$ and $\mathbf { F }$ , but in fact the U-key can be obtained by evaluating $\mathbf { F }$ for an appropriate number $z$ of fixed arguments, as follows easily from our framework. More precisely, $\mathbf { U } ( . )$ is a random system $^ { 1 9 }$ invoking $\mathbf { F }$ some $z$ times to set up the key of $\mathbf { U }$ and then applies it to the input. $^ { 2 0 }$ Of course, the key can be cached so that only one evaluation of $\mathbf { F }$ is needed for each input.

The security proof of such a scheme is trivial in our framework. The following theorem implies that $\mathbf { U } ( \mathbf { F } )$ is a computationally secure MAC for any PRF $\mathbf { F }$ .

Theorem 5. For a $d ( k )$ -QRF $\mathbf { F }$ , $\mathbf { U } ( \mathbf { F } )$ is a $\tilde { d } ( k )$ -QRO for $\tilde { d } ( k ) = \epsilon ( k + z ) ^ { 2 } / 2 +$ $d ( k + z )$ .

Proof. Define $A _ { i }$ as the event that all inputs to $\mathbf { F }$ are distinct, including the $z$ fixed values needed for the key setup for $\mathbf { U }$ . Lemma 5 (i) implies $\begin{array} { r } { \varDelta _ { k } ( \mathbf { U } ( \mathbf { F } ) , \mathbf { R } ) \leq \varDelta _ { k } ( \mathbf { U } ( \mathbf { F } ) , \mathbf { U } ( \mathbf { R } ) ) + \varDelta _ { k } ( \mathbf { U } ( \mathbf { R } ) , \mathbf { R } ) } \end{array}$ . Lemma 5 (ii) implies $\Delta _ { k } ( { \mathbf { U } ( \mathbf { F } ) } , { \mathbf { U } ( \mathbf { R } ) } ) \leq d ( k + z )$ . Moreover, $\mathbf { U } ( \mathbf { R } ) | \mathcal { A } \equiv \mathbf { R }$ and hence, using Theorem 1 (i), $\varDelta _ { k } ( \mathbf { U } ( \mathbf { R } ) , \mathbf { R } ) \leq \nu ( \mathbf { U } ( \mathbf { R } ) , \overline { { \varDelta _ { k } } } )$ . Using Corollary 1 (vi) together with ${ \bf R } | { \cal A } \equiv { \bf B }$ and ${ \bf U } ( { \bf B } ) \equiv { \bf B }$ gives $\nu ( \mathbf { U } ( \mathbf { R } ) , { \overline { { A _ { k } } } } ) = \mu ( \mathbf { U } ( \mathbf { R } ) , { \overline { { A _ { k } } } } )$ , hence one can restrict attention to non-adaptive strategies. Now, for any fixed input sequence to ${ \bf U } ( { \bf R } )$ , $A _ { k }$ is the union of ${ \binom { k + z } { 2 } } \ < \ ( k + z ) ^ { 2 } / 2$ collision events, each with probability at most $\epsilon$ . Application of the union bound concludes the proof. ut

As a further demonstration of the general applicability of the framework, we give a simple security proof of a generalized version of the CBC-MAC (e.g., see Fig. 6 and [2]), with which we assume the reader is familiar. We do not wish to make an $a$ priori assumption about the maximal message length, hence we need a prefix-free encoding $\sigma : \{ 0 , 1 \} ^ { * } \to \{ 0 , 1 \} ^ { * }$ of the binary strings which does not significantly expand the length. A good choice is to prepend a block encoding the length of the message, but from a theoretical viewpoint this restricts the message length and hence does not yield a true quasi-random oracle.21

![](images/4523081b632d73f080337125b450b601bfcc200d7f4955ea8163ff9f5fa2c321.jpg)  
Fig. 6. The CBC-MAC. The $( \{ 0 , 1 \} ^ { * } , \{ 0 , 1 \} ^ { l } )$ -random system $\mathbf { C } ( \mathbf { F } )$ is defined by applying some prefix-free encoding $\sigma$ to the message, then padding the result with $_ 0$ ’s to complete the last block, then applying the CBC feedback construction with a random function (or more generally a random automaton) $\mathbf { F }$ , and taking the last output (for a given message) as the MAC-value for that message.

Let $\mathbf { C } ( \mathbf { F } )$ be the $( \{ 0 , 1 \} ^ { * } , \{ 0 , 1 \} ^ { l } )$ -random system defined by applying $\sigma$ to the message, then padding with $0$ ’s to fill the last block, and then applying the CBC-MAC with a random function (or more generally a random system) $\mathbf { F }$ (cf. Fig. 6). A result similar in spirit to the following theorem was stated (without proof) independently by Petrank and Rackoff [17].

Theorem 6. If $\mathbf { F }$ is a $d ( k )$ -QRF, then $\mathbf { C } ( \mathbf { F } )$ is a ${ \ddot { d } } ( k )$ -quasi-random oracle for $\tilde { d } ( k ) = n ^ { 2 } 2 ^ { - ( l + 1 ) } + d ( n )$ , where $n$ is the total number of blocks of all $k$ messages issued by the distinguisher.

Proof. Lemma 5 (i) implies $\Delta _ { k } ( { \bf C } ( { \bf F } ) , { \bf O } ) \le \varDelta _ { k } ( { \bf C } ( { \bf F } ) , { \bf C } ( { \bf R } ) ) + \varDelta _ { k } ( { \bf C } ( { \bf R } ) , { \bf O } )$ . Lemma 5 (ii) implies $\Delta _ { k } ( { \bf C } ( { \bf F } ) , { \bf C } ( { \bf R } ) ) \le d ( n )$ . Consider the event $A _ { i }$ that all inputs to $\mathbf { F }$ are distinct, up to and including the processing of the $i$ -th message, except those inputs to $\mathbf { F }$ that are trivially equal because the prefix of the actual message processed so far is also a prefix of a previous message. Because due to $\sigma$ no (encoded) message is a prefix of another message, $A _ { i }$ implies that for a given message $x _ { i }$ the last input to $\mathbf { F }$ (for $x _ { i }$ ) is distinct from all previous inputs to $\mathbf { F }$ (for $x _ { 1 } , \ldots , x _ { i - 1 } )$ . Hence $\mathbf { C } ( \mathbf { R } ) | \mathcal { A } \equiv \mathbf { O }$ and by Theorem 1 (i) we have $\varDelta _ { k } ( { \mathbf { C } ( { \mathbf { R } } ) } , { \mathbf { O } } ) \leq \nu ( { \mathbf { C } ( { \mathbf { R } } ) } , { \varDelta _ { k } } )$ . Equation (2) is satisfied (for $\mathbf { G } = \mathbf { B }$ ) for all $i$ since $P _ { Y ^ { i } \mid X ^ { i } A _ { i } } ^ { \mathbf { C } ( \mathbf { R } ) }$ is the uniform distribution over $\{ \{ 0 , 1 \} ^ { l } \} ^ { i }$ for all input values (resulting in $A _ { i }$ being satisfied). Hence $\nu ( \mathbf { C } ( \mathbf { R } ) , \overline { { A _ { k } } } ) = \mu ( \mathbf { C } ( \mathbf { R } ) , \overline { { A _ { k } } } )$ and one can restrict attention to non-adaptive strategies, which are easy to analyse.

For any given $k$ input messages $x _ { 1 } , \ldots , x _ { k }$ of arbitrary lengths, but consisting of a total of $n$ blocks, $\overline { { A _ { k } } }$ corresponds to the event that a collision occurs among $n - w ( x ^ { k } )$ independent and uniformly random values, where $w ( x ^ { k } )$ is the total number of blocks in the messages $x _ { 1 } , \ldots , x _ { k } \in ( \{ 0 , 1 \} ^ { l } ) ^ { * }$ which belong to a prefix (say of $x _ { i }$ ) that was also the prefix of a previous message $x _ { 1 } , \ldots , x _ { i - 1 }$ (see above), i.e., $P _ { \overline { { A _ { k } } } | X ^ { k } } ^ { \mathbf { C } ( \mathbf { R } ) } ( x ^ { k } ) = p _ { \mathrm { c o l l } } ( 2 ^ { l } , n - w ( x ^ { k } ) ) \leq p _ { \mathrm { c o l l } } ( 2 ^ { l } , n ) \leq n ^ { 2 } 2 ^ { - ( l + 1 ) }$ .22 ut

# 7 Applications to the Analysis of Random Permutations

# 7.1 Random Permutations

For a random permutation $^ { 2 3 }$ $\mathbf { Q }$ , the inverse is also a random permutation and is denoted by $\mathbf { Q } ^ { - 1 }$ . Remember that $\mathbf { P }$ denotes a uniform random permutation. Let $( \mathbf { E } , \mathbf { G } )$ be any pair of (possibly dependent $^ { 2 4 }$ ) random permutations.

Lemma 8. (i) $\mathbf { E P G } \equiv \mathbf { P }$ . Moreover, if $\mathbf { Q } | { \mathcal { A } } \equiv \mathbf { P }$ , then $\mathbf { E Q G } | \mathcal { A } \equiv \mathbf { P }$ . (ii) For a MES $\boldsymbol { \mathscr { C } }$ defined on the outputs of $( \mathcal { X } , \mathcal { Y } )$ -random systems such that $C _ { i }$ implies that the first i outputs are distinct, we have R|C ≡ P|C and RC ≡ PC∧D for some MES $\mathcal { D }$ adjoined to $\mathbf { P }$ .

Proof. $\mathbf { E P G } \equiv \mathbf { P }$ is a special case of the second statement when $A _ { i }$ is the certain event for all $i$ . We have $E \mathbf { Q } G | \mathcal { A } \equiv E \mathbf { P } G$ for any two fixed permutations $E$ and $G$ because $E$ and $G$ simply correspond to relabelings of the input and output alphabets of $\mathbf { Q }$ . Hence this equivalence also holds if the pair $( E , G )$ i s a random variable. Now we prove (ii). We have $\mathbf { R } | { \mathcal { C } } \equiv \mathbf { P } | { \mathcal { C } }$ since conditioned on the output beinoutputs. Moreover, $\mathbf { R }$ $\mathbf { P }$ te completely new randomis a simple consequence of $P _ { C _ { i } | X ^ { i } Y ^ { i - 1 } C _ { i - 1 } } ^ { \mathbf { R } } \leq P _ { C _ { i } | X ^ { i } Y ^ { i - 1 } C _ { i - 1 } } ^ { \mathbf { P } }$ the fact that for a given $X ^ { i }$ with distinct values (i.e., $\mathrm { d i s t } ( X _ { 1 } , \ldots , X _ { i } ) )$ , only $Y ^ { i }$ with distinct values are consistent with $\mathbf { P }$ , whereas other values for $Y ^ { i }$ are consistent with $\mathbf { R }$ , but $C _ { i }$ cannot hold for these $Y ^ { i }$ . Now apply Lemma 1 (iv). ut

Definition 13. A pairwise independent permutation (PIP) [18] $\mathbf { Q }$ is a random permutation such that for any two inputs $x$ and $x ^ { \prime }$ , $\mathbf { Q } ( x )$ and $\mathbf { Q } ( x ^ { \prime } )$ are a completely random pair of (distinct) values.25

![](images/d215c0e50bff8c0bfcbac4e66ed7a310c8ca2d54cc8ca76839e576be9d964e93.jpg)  
Fig. 7. Left side: Notation for random systems whose inputs and outputs are pairs. $A _ { i } : = \operatorname { d i s t } ( T ^ { i } )$ and $B _ { i } : = \operatorname { d i s t } ( U ^ { i } )$ . Right side: Special case; two Feistel rounds with random systems $\mathbf { H }$ and $\mathbf { K }$ , denoted $\mathbf { M } ( \mathbf { H } , \mathbf { K } )$ .

# 7.2 Two Feistel Rounds with Random Functions

Let $\mathcal { R }$ be a set and let $\star$ be a group operation on $\mathcal { R }$ . Typically $\mathcal { R } = \{ 0 , 1 \} ^ { l }$ for some $\it l$ and $\star$ is bitwise XOR. We now consider permutations on $\mathcal { R } ^ { 2 }$ , i.e., on pairs which can be considered as “left” and “right” halves, or as high and low part when the pair is interpreted as a single element of, say, a field. For any random function ${ \bf F } : \mathcal { R } ^ { 2 }  \mathcal { R } ^ { 2 }$ we can define the following random variables (see Figure 7, left): $( S _ { i } , T _ { i } )$ is the $i$ -th input and $( U _ { i } , V _ { i } )$ are the $i$ -th output. We define two MES, $A _ { i } : = \mathrm { d i s t } ( T ^ { i } )$ and $B _ { i } : = \operatorname { d i s t } ( U ^ { \ i } )$ , used throughout Section 7.

For two random functions $\mathcal { R }  \mathcal { R }$ , $\mathbf { H }$ and $\mathbf { K }$ , let $\mathbf { M } ( \mathbf { H } , \mathbf { K } )$ be the $\mathcal { R } ^ { 2 }$ -random permutation defined by two Feistel rounds with $\mathbf { H }$ and $\mathbf { K }$ (see Figure 7, right).26 More precisely, $U _ { i } = S _ { i } \star \mathbf { H } ( T _ { i } )$ and $V _ { i } = T _ { i } \star \mathbf { K } ( U _ { i } )$ . Let ${ \bf R } : \mathcal { R } ^ { 2 }  \mathcal { R } ^ { 2 }$ be a URF, and let $\mathbf { R } ^ { \prime }$ and $\mathbf { R } ^ { \prime \prime }$ be URF’s $\mathcal { R }  \mathcal { R }$ . We have

Proof. Given $A _ { i }$ , the joint distribution of $( U _ { i } , V _ { i } )$ and $B _ { i }$ is identical for ${ \bf M } ( { \bf R } ^ { \prime } , { \bf R } ^ { \prime \prime } )$ , for $\mathbf { B }$ , and for $\mathbf { R }$ , independent of the input: $U _ { i }$ and $V _ { i }$ are independent new random values and $B _ { i }$ is determined by $U ^ { i }$ . Hence $\mathbf { M } ( \mathbf { R } ^ { \prime } , \mathbf { R } ^ { \prime \prime } ) ^ { \mathcal { A } } \equiv$ $\mathbf { B } ^ { A } \equiv \mathbf { R } ^ { A }$ and Lemma 2 (ii) gives $\mathbf { M } ( \mathbf { R } ^ { \prime } , \mathbf { R } ^ { \prime \prime } ) ^ { \mathcal { A } \wedge B } \equiv \mathbf { B } ^ { \mathcal { A } \wedge B } \equiv \mathbf { R } ^ { \mathcal { A } \wedge B }$ . The last equivalence follows from $\mathbf { R } ^ { B } \equiv \mathbf { P } ^ { B \wedge D }$ (Lemma 8 (ii)) and because $\boldsymbol { A }$ is defined on the inputs and hence Lemma 2 (ii) can be applied. ut

# 7.3 Mono-directional Luby-Rackoff and Naor-Reingold

The following theorem generalizes the one-directional Luby-Rackoff [10] and Naor-Reingold [18] results (cf. Fig. 8 left) and follows easily from our framework.

Theorem 7. Let $\mathbf { L } : = \mathbf { E M } ( \mathbf { R } ^ { \prime } , \mathbf { R } ^ { \prime \prime } )$ for some random permutation E. Then $\varDelta _ { k } ( { \mathbf { L } } , { \mathbf { P } } ) \leq \mu ( { \mathbf { E } } , \overline { { A _ { k } } } ) + p _ { \mathrm { c o l l } } ( | \mathcal { R } | , k )$ . If $\mathbf { E }$ is a PIP (Naor-Reingold) or if $\mathbf { E }$ is a Feistel round with another random function $\mathbf { R } ^ { \prime \prime \prime }$ (Luby-Rackoff), then $\varDelta _ { k } ( \mathbf { L } , \mathbf { P } ) \leq 2 \cdot p _ { \mathrm { c o l l } } ( | \mathcal { R } | , k ) < k ^ { 2 } / | \mathcal { R } |$ .

![](images/643ac42e83b07765eb23ec935733af073efebec4c88a70e9cbba6b4130d649e3.jpg)  
Fig. 8. Illustration for the one-directional (left) and bidirectional (right) Luby-Rackoff and Naor-Reingold results and generalizations thereof.

Proof. Using Lemma 9 and Lemma 4 we obtain

$$
\mathbf { L } ^ { \mathcal { A } \wedge B } \equiv \mathbf { E } \mathbf { B } ^ { \mathcal { A } \wedge B } \equiv \mathbf { E } \mathbf { P } ^ { \mathcal { A } \wedge B \wedge D }
$$

(with the events $A _ { i }$ defined internally). Lemma 8 (i) yields the first step of

$$
\varDelta _ { k } ( \mathbf { L } , \mathbf { P } ) = \varDelta _ { k } ( \mathbf { L } , \mathbf { E } \mathbf { P } ) \leq \nu ( \mathbf { L } , \overline { { A _ { k } } } \vee \overline { { B _ { k } } } ) = \nu ( \mathbf { E } \mathbf { B } , \overline { { A _ { k } } } \vee \overline { { B _ { k } } } )
$$

and the next two steps follow from (3) and Theorem 1 (i), and from (3) and Lemma 6 (ii), respectively. Now obviously (and by Corollary 1 (v)), $\nu ( \mathbf { E B } , \overline { { A _ { k } } } \lor$ ${ \overline { { B _ { k } } } } ) \le \mu ( \mathbf { E } , { \overline { { A _ { k } } } } ) + \mu ( \mathbf { B } , { \overline { { B _ { k } } } } )$ where $\mu ( { \bf B } , \overline { { B _ { k } } } ) = p _ { \mathrm { c o l l } } ( | \mathcal { R } | , k )$ . The second claim follows by a trivial analysis of a collision event among $k$ random values. $\boxed { \begin{array} { r l } \end{array} }$

Remark. Theorem 7, besides being more general, is also slightly stronger than that of [18] and [10] (see also [9]) where an additional term $k ^ { 2 } / ( | \mathcal { R } | ) ^ { 2 }$ appears on the right side. This weaker bound would in our context be obtained by proving $\varDelta _ { k } ( \mathbf { L } , \mathbf { R } ) < k ^ { 2 } / | \mathcal { R } |$ and then using $\varDelta _ { k } ( \mathbf { R } , \mathbf { P } ) \leq k ^ { 2 } / | \mathcal { R } | ^ { 2 }$ . One could also append an additional random permutation $\mathbf { G }$ , as follows directly from Corollary 1 (iii).

# 7.4 Bidirectional Permutations

Definition 14. For an $\mathcal { X }$ -random permutation $\mathbf { Q }$ , let $\langle \mathbf { Q } \rangle$ be the bidirectional permutation27 $\mathbf { Q }$ with access from both sides (i.e., one can query both $\mathbf { Q }$ and $\mathbf { Q } ^ { - 1 }$ ). More precisely, $\langle \mathbf { Q } \rangle$ is the random function $\mathcal { X } \times \{ 0 , 1 \} \to \mathcal { X }$ defined as follows:

$$
\langle \mathbf { Q } \rangle ( U _ { i } , D _ { i } ) = { \left\{ \begin{array} { l l } { \mathbf { Q } ( U _ { i } ) } & { { \mathrm { i f ~ } } D _ { i } = 0 } \\ { \mathbf { Q } ^ { - 1 } ( U _ { i } ) } & { { \mathrm { i f ~ } } D _ { i } = 1 } \end{array} \right. } .
$$

If $\mathcal { A }$ is defined for $\mathbf { Q }$ , $\boldsymbol { A }$ can also be defined naturally for $\langle \mathbf { Q } \rangle$ : Let $V _ { i } : =$ $\langle \mathbf { Q } \rangle ( U _ { i } , D _ { i } )$ , and let $X _ { i }$ and $Y _ { i }$ be the $i$ -th input and output of $\mathbf { Q }$ (i.e., if $D _ { i } ~ = ~ 0$ , then $X _ { i } ~ = ~ U _ { i }$ and $Y _ { i } ~ = ~ V _ { i }$ , and if $D _ { i } ~ = ~ 1$ , then $Y _ { i } ~ = ~ U _ { i }$ and Xi = Vi). Recall that P Q $P _ { Y _ { i } A _ { i } | X ^ { i } Y ^ { i - 1 } A _ { i - 1 } } ^ { \bf Q } = P _ { Y _ { i } | X ^ { i } Y ^ { i - 1 } A _ { i - 1 } } ^ { \bf Q } \cdot P _ { A _ { i } | X ^ { i } Y ^ { i } A _ { i - 1 } } ^ { \bf Q }$ P Ai XiY iAi 1 . Now we let P hQi $P _ { A _ { i } | X ^ { i } Y ^ { i } A _ { i - 1 } } ^ { \langle \mathbf { Q } \rangle } : = P _ { A _ { i } | X ^ { i } Y ^ { i } A _ { i - 1 } } ^ { \mathbf { Q } }$ .

Lemma 10. For any random permutatio $\mathbf { F }$ and $\mathbf { G }$ , (i) $\Delta _ { k } ( \mathbf { F } , \mathbf { G } ) \leq \varDelta _ { k } ( \mathbf { \Delta } \langle \mathbf { F } \rangle , \mathbf { \Delta } \langle \mathbf { G } \rangle )$ . 2 8 (ii) If ${ \bf F } \equiv { \bf G }$ , then ${ \bf F } ^ { - 1 } \equiv { \bf G } ^ { - 1 }$ and $\left. \mathbf { F } \right. \equiv \left. \mathbf { G } \right.$ . (iii) More generally, $\mathbf { F } ^ { A } \equiv \mathbf { G } ^ { B }$ implies $\langle \mathbf { F } \rangle ^ { A } \equiv \langle \mathbf { G } \rangle ^ { B }$ .

Proof. Claim (i) follows from the fact that being able to query from both sides can only help the distinguisher. Proof of claim (ii): the behavior of a random permutation $\mathbf { Q }$ uniquely determines the behavior of $\mathbf { Q } ^ { - 1 }$ and hence also of $\langle \mathbf { Q } \rangle$ . Claim (iii) follows because if $\mathbf { F } ^ { A } \equiv \mathbf { G } ^ { B }$ , then $P _ { A _ { i } | X ^ { i } Y ^ { i } A _ { i - 1 } } ^ { \mathbf { F } } = P _ { B _ { i } | X ^ { i } Y ^ { i } B _ { i - 1 } } ^ { \mathbf { G } }$ and thus $P _ { A _ { i } | U ^ { i } D ^ { i } V ^ { i } A _ { i - 1 } } ^ { \langle \mathbf { F } \rangle } = P _ { B _ { i } | U ^ { i } D ^ { i } V ^ { i } B _ { i - 1 } } ^ { \langle \mathbf { G } \rangle }$ . ut

The following theorem generalizes Theorem 3.2 of [18] in several ways. The proof is omitted.

Theorem 8. Let $\mathbf { L }$ be defined as $\mathbf { L } : = \mathbf { E M } ( \mathbf { R } ^ { \prime } , \mathbf { R } ^ { \prime } ) \mathbf { G } ^ { - 1 }$ (cf. Fig. 8 right).

(i) If $\mathbf { E }$ and $\mathbf { G } ^ { - 1 }$ are independent $P I P$ ’s, then $\varDelta _ { k } ( \langle \mathbf { L } \rangle , \langle \mathbf { P } \rangle ) < k ^ { 2 } / | \mathcal { R } |$ . (ii) $I f \mathbf { E }$ is a $P I P$ and ${ \bf G } = { \bf E } ^ { - 1 }$ , then $\varDelta _ { k } ( \langle \mathbf { L } \rangle , \langle \mathbf { P } \rangle ) < 4 k ^ { 2 } / | \mathcal { R } |$ . (iii) If $\mathbf { R } ^ { \prime } = \mathbf { R } ^ { \prime \prime }$ , i.e., $\mathbf { L } : = \mathbf { E M } ( \mathbf { R } ^ { \prime } , \mathbf { R } ^ { \prime } ) \mathbf { E } ^ { - 1 }$ , then $\varDelta _ { k } ( \langle \mathbf { L } \rangle , \langle \mathbf { P } \rangle ) < 8 k ^ { 2 } / | \mathcal { R } |$ . (iv) Moreover, if $\mathcal { R } = G F ( q )$ is $a$ field and $\mathbf { E }$ is also derived from $\mathbf { R } ^ { \prime }$ by a linear polynomial $a x + b$ over $G F ( q ^ { 2 } )$ with $a$ and $b$ defined by $a = ( { \bf R } ( \xi _ { 1 } ) | | { \bf R } ( \xi _ { 2 } ) )$ and $b = ( { \bf R } ( \xi _ { 3 } ) | | { \bf R } ( \xi _ { 4 } ) )$ for some fixed $\xi _ { 1 } , \xi _ { 2 } , \xi _ { 3 } , \xi _ { 4 } \in G F ( q )$ , then $\varDelta _ { k } (  { \langle { \mathbf { L } } \rangle } ,  { \langle { \mathbf { P } } \rangle } ) <$ $8 ( k + 1 ) ^ { 2 } / | \mathcal { R } | + 1 / | \mathcal { R } | ^ { 2 }$ .

# 8 Conclusions

We have described a general framework for indistinguishability proofs of the most general form of random systems. The purpose of the framework is to prove results at the most general and abstract level, and this leads to substantial simplifications in actual security proof (making them for example tractable for a textbook) and to new security proofs that before may have appeared unrealistic. It would be a pleasure to see the framework at work in future security proofs.

We suggest as an open problem to find constructions of QRF’s from QRF’s better than that of Section 5, i.e., with either higher security (degree of indistinguishability) or lower complexity (number of evaluations of $\mathbf { F }$ ), or both. It is possible that this construction is close to optimal.

# Acknowledgements

I would like to thank Thomas Holenstein, Olaf Keller, Krzysztof Pietrzak, and Renato Renner for many very helpful comments and for a careful proofreading, and Markus Stadler for discussions at an early stage of this work.

# References

1. M. Bellare, O. Goldreich, and H. Krawczyk, Stateless evaluation of pseudorandom functions: security beyond the birthday barrier, Advances in Cryptology - CRYPTO ’99, Lecture Notes in Computer Sc., vol. 1666, pp. 270–287, Springer-Verlag, 1999.   
2. M. Bellare, J. Kilian, and P. Rogaway, The security of the cipher block chaining message authentication code, Advances in Cryptology - CRYPTO ’94, Lecture Notes in Computer Science, vol. 839, pp. 341–358, Springer-Verlag, 1995.   
3. M. Bellare, J. Gu´erin, and P. Rogaway, XOR MACs: New methods for message authentication using finite pseudorandom functions, Advances in Cryptology - CRYPTO ’95, Lecture Notes in Computer Science, vol. 963, Springer-Verlag, 1994.   
4. D. J. Bernstein, How to stretch random functions: The security of protected counter sums, Journal of Cryptology, vol. 12, pp. 185–192, Springer-Verlag, 1999.   
5. J. Black, S. Halevi, H. Krawczyk, T. Krovetz, and P. Rogaway, UMAC: Fast and secure message authentication, Advances in Cryptology - CRYPTO ’99, Lecture Notes in Computer Science, vol. 1666 pp. 216–233, Springer-Verlag, 1999.   
6. R. E. Blahut, Principles and practice of information theory, Addison-Wesley Publishing Company, 1988.   
7. M. Blum and S. Micali, How to generate cryptographically strong sequences of pseudo-random bits, SIAM J. on Computing, vol. 13, no. 4, pp. 850–864, 1984.   
8. O. Goldreich, S. Goldwasser, and S. Micali, How to construct random functions, Journal of the ACM, vol. 33, no. 4, pp. 210–217, 1986.   
9. M. Luby, Pseudorandomness and Cryptographic Applications, Princeton University Press, 1996.   
10. M. Luby and C. Rackoff, How to construct pseudo-random permutations from pseudo-random functions, SIAM J. on Computing, vol. 17, no. 2, pp. 373–386, 1988.   
11. U. M. Maurer, Conditionally-perfect secrecy and a provably-secure randomized cipher, Journal of Cryptology, vol. 5, pp. 53–66, Springer-Verlag, 1992.   
12. , A simplified and generalized treatment of Luby-Rackoff pseudo-random permutation generators, Advances in Cryptology - EUROCRYPT ’92, Lecture Notes in Computer Science, vol. 658, pp. 239–255, Springer-Verlag, 1992.   
13. Extended version of this paper, see www.crypto.ethz.ch/publications/.   
14. J. Patarin, Etude des g´en´erateurs de permutations bas´es sur le Sch´ema du D.E.S., Ph. D. Thesis, INRIA, Le Chesnay, France, 1991. An extract appeared in: J. Patarin, New results on pseudorandom permutation generators based on the DES scheme, Advances in Cryptology – CRYPTO’91, J. Feigenbaum (ed.), Lecture Notes in Computer Science, Vol. 576, Springer-Verlag, pp. 301–312, 1992.   
15. —, How to construct pseudorandom permutations from a single pseudorandom function, Advances in Cryptology - EUROCRYPT ’92, R. Rueppel (ed.), Lecture Notes in Computer Science, vol. 658, pp. 256–266, Springer-Verlag, 1992.   
16. ——, About Feistel schemes with six (or more) rounds, Fast Software Encryption, Lecture Notes in Computer Science, vol. 1372, pp. 103–121, Springer-Verlag, 1998.   
17. E. Petrank and C. Rackoff, CBC MAC for real-time data sources, Journal of Cryptology, vol. 13, no. 3, pp. 315–338, 2000.   
18. M. Naor and O. Reingold, On the construction of pseudorandom permutations: Luby-Rackoff revisited, Journal of Cryptology, vol. 12, no. 1, pp. 29–66, 1999.   
19. M. O. Rabin, Transaction protection by beacons, J. Comp. Sys. Sci., vol. 27, pp. 256–267, 1983.   
20. V. Shoup, On fast and provably secure message authentication based on universal hashing, Advances in Cryptology - CRYPTO ’96, Lecture Notes in Computer Science, vol. 1109, pp. 313–328, Springer-Verlag, 1996.   
21. S. Vaudenay, Provable security for block ciphers by decorrelation, Proceedings of STACS’98, Lecture Notes in Computer Science, vol. 1373, Springer-Verlag, pp.   
249–275, 1998.   
22. ——, On provable security for conventional ciphers, in Proc. of ICISC’99, Lecture Notes in Computer Science, Springer-Verlag, 1999.   
23. M. N. Wegman and J. L. Carter, New hash functions and their use in authentication and set equality, J. of Computer and System Sciences, vol. 22, pp. 265–279, 1981.

# Appendix

Lemma 11. Let $\textbf { U } = \ \lvert U _ { 1 } , \ldots , U _ { n } \rvert$ with $U _ { i } ~ \in ~ G F ( q )$ be a vector of random variables with uniform distribution $G F ( q ) ^ { n }$ , and define the random function $\mathbf { K } :$ $G F ( q ) ^ { n } \to G F ( q )$ as the scalar product of the input vector $\mathbf { x } = [ x _ { 1 } , \ldots , x _ { n } ] \in$ $G F ( q ) ^ { n }$ and $\mathbf { U }$ ,

$$
\mathbf { K } ( \mathbf { x } ) = \langle \mathbf { x } , \mathbf { U } \rangle = \sum _ { j = 1 } ^ { n } x _ { j } U _ { j } .
$$

$T h e n \mathbf { K } ^ { A } \equiv \mathbf { R } ^ { A } \equiv \mathbf { B } ^ { A }$ with $A _ { i }$ as the event that $\mathbf { x } _ { 1 } , . . . . , \mathbf { x } _ { i }$ are linearly independent.

Proof. For a list $\mathbf { v } ^ { k } = [ \mathbf { v } _ { 1 } , \ldots , \mathbf { v } _ { k } ]$ of vectors in a finite-dimensional vector space, let $s p a n ( \mathbf { v } ^ { k } )$ denote the subspace spanned by $\mathbf { v } _ { 1 } , \ldots , \mathbf { v } _ { k }$ and let $d i m ( \mathbf { v } ^ { k } )$ denote its dimension. If $\mathbf { v } _ { 1 } , \ldots , \mathbf { v } _ { k }$ are linearly independent, then $d i m ( \mathbf { v } ^ { k } ) = k$ .

Let $T \subseteq G F ( q ) ^ { n }$ be a set of input vectors to $\mathbf { K }$ , and let $\mathbf K ( T )$ denote the corresponding list of values of $\mathbf { K }$ . We prove $^ { 2 9 }$ that $H ( \mathbf { K } ( T ) ) = d i m ( T ) r$ , where $r = \log { q }$ . This clearly implies that for any set of linearly independent vectors the corresponding function values have maximal entropy, as is to be proved. Linear dependence implies functional dependence, hence $H ( \mathbf { K } ( T ) ) = H ( \mathbf { K } ( s p a n ( T ) ) ) =$ $H ( \mathbf { K } ( s p a n ( B ) ) )$ , where $B$ is any basis of $s p a n ( T )$ and has cardinality $B =$ $d i m ( T )$ . Thus $H ( \mathbf { K } ( T ) ) \leq d i m ( T ) r$ . On the other hand, it follows from linear algebra that $T$ can be complemented by a set $T ^ { \prime }$ of size $n - d i m ( T )$ such that $T \cup T ^ { \prime }$ spans the entire space $G F ( q ) ^ { n }$ . Hence $H ( \mathbf { K } | \mathbf { K } ( T ) ) \leq ( n - d i m ( T ) ) r$ . Because $H ( \mathbf { K } ) = H ( \mathbf { K } ( T ) ) + H ( \mathbf { K } | \mathbf { K } ( T ) ) = n r$ we must have equality in the two previous inequalities. ut

Let $S _ { n } : = \{ 1 , . . . , n \}$ . The characteristic vector in $\{ 0 , 1 \} ^ { n }$ of a subset $S ^ { \prime }$ of $S _ { n }$ has a $^ { 1 }$ at position $_ i$ if and only if $i \subseteq S ^ { \prime }$ . For multi-sets or lists of elements of $S _ { n }$ , we define the characteristic vector to have a 1-entry only for those elements of $S _ { n }$ that occur exactly once.

The following lemma is the missing step in the proof of Theorem ??. The proof is straight-forward.

Lemma 12. If kt elements of $S _ { n }$ are selected $b$ -wise independently (for $b \geq 2 t$ ) and interpreted as $k$ lists of $t$ elements, $V _ { i } = [ V _ { i 1 } , \dots , V _ { i t } ]$ for $1 \leq i \leq k$ , then their characteristic vectors $W _ { 1 } , \ldots , W _ { k }$ are linearly independent with probability at least $\textstyle { 1 - k \left( { \frac { k t } { n } } \right) ^ { t } }$ .