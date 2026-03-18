# Coupling of Random Systems?

David Lanzenberger and Ueli Maurer

Department of Computer Science ETH Zurich 8092 Zurich, Switzerland   
{landavid,maurer}@inf.ethz.ch

Abstract. This paper makes three contributions. First, we present a simple theory of random systems. The main idea is to think of a probabilistic system as an equivalence class of distributions over deterministic systems. Second, we demonstrate how in this new theory, the optimal information-theoretic distinguishing advantage between two systems can be characterized merely in terms of the statistical distance of probability distributions, providing a more elementary understanding of the distance of systems. In particular, two systems that are $\epsilon$ -close in terms of the best distinguishing advantage can be understood as being equal with probability $1 - \epsilon$ , a property that holds statically, without even considering a distinguisher, let alone its interaction with the systems. Finally, we exploit this new characterization of the distinguishing advantage to prove that any threshold combiner is an amplifier for indistinguishability in the information-theoretic setting, generalizing and simplifying results from Maurer, Pietrzak, and Renner (CRYPTO 2007).

# 1 Introduction

# 1.1 Random Systems

A random system is an object of general interest in computer science and in   
particular in cryptography. Informally, a random system is an abstract object   
which operates in rounds. In the $i$ -th round, an input (or query) $X _ { i }$ is answered   
with a random output $Y _ { i }$ , and each round may (probabilistically) depend on the ous rounds. In previous work [Mau02,MPR07], a r sequence of conditional probability distributions tem (or $\mathbf { s }$ ned for $\mathrm { p } _ { Y _ { i } \mid X ^ { i } Y ^ { i } - 1 } ^ { \mathbf { S } }$ $\mathrm { p } _ { Y ^ { i } \mid X ^ { i } } ^ { \mathbf { S } } )$   
$i \geq 1$   
as it gives the probability distribution of any output $Y _ { i }$ , conditioned on the   
previous inputs $X ^ { i } = ( X _ { 1 } , \ldots , X _ { i } )$ and outputs $Y ^ { i - 1 } = ( Y _ { 1 } , \dots , Y _ { i - 1 } )$ .

For example, a uniform random function (URF) from $\mathcal { X }$ to $y$ is a random system $\mathbf { R }$ corresponding to the following behavior: Every new input $x _ { i } \in \mathcal X$ is answered with an independent uniform random value $y _ { i } \in \mathcal { V }$ and every input that was given before is answered consistently. Similarly, a uniform random permutation is a random system $\mathbf { P }$ (different from $\mathbf { R }$ ).

Many statements appearing in the cryptographic literature are about random systems (even though they are usually expressed in a specific language, for example using pseudo-code). For example, the optimal distinguishing advantage $\operatorname { A d v } ^ { \mathcal { D } } ( \mathbf { S } , \mathbf { T } )$ of a distinguisher class $\mathcal { D }$ between two systems $\mathbf { s }$ and $\mathbf { T }$ only depends on the behavior of $\mathbf { s }$ and $\mathbf { T }$ . In particular, it is independent of how $\mathbf { s }$ is implemented (in program code), whether it is a Turing Machine, or how efficient it is. For example, the well-known URP-URF switching lemma [BR06,Mau13] is a statement about the optimal information-theoretic distinguishing advantage between the two random systems $\mathbf { R }$ and $\mathbf { P }$ (see above). Clearly, the switching lemma holds irrespective of the concrete implementations of the systems $\mathbf { R }$ or $\mathbf { P }$ , e.g., whether they employ eager or lazy sampling.

# 1.2 Random Systems as Equivalence Classes

An abstract object can (usually) be represented as an equivalence class of objects from a lower abstraction layer. Perhaps surprisingly, this can give new insight about the object and also be technically useful. As an example, assume our (abstract) objects are pairs $( \mathsf { X } , \mathsf { Y } )$ of probability distributions over the same set. If we let $[ ( { \sf X } , { \sf Y } ) ]$ denote the equivalence class of all random experiments $\varepsilon$ with two arbitrarily correlated random variables $X$ and $Y$ distributed according to $\mathsf { X }$ and Y, we can express the statistical distance as follows (also known as Coupling Lemma [Ald83]):

$$
\delta ( \mathsf { X } , \mathsf { Y } ) = \operatorname* { i n f } _ { \varepsilon \in [ ( \mathsf { X } , \mathsf { Y } ) ] } \operatorname* { P r } ^ { \varepsilon } ( X \neq Y ) .
$$

Note that the statistical distance $\delta ( { \sf X } , { \sf Y } )$ is defined at the level of probability distributions, and thus does not require any joint distribution between $\mathsf { X }$ and Y (let alone a random experiment with accordingly distributed random variables). Nevertheless, the coupling interpretation provides a very intuitive and elementary understanding of the statistical distance. Moreover, it is a powerful technique that can be used to show the closeness (in statistical distance) of two probability distributions $\mathsf { X }$ and Y: one exhibits any random experiment $\varepsilon$ with cleverly correlated random variables $X$ and $Y$ (distributed according to $\mathsf { X }$ and Y) such that $\operatorname* { P r } ^ { \mathcal { E } } ( X = Y )$ is close to 1. This coupling technique has been used extensively for example to prove that certain Markov chains are rapidly mixing, i.e., they converge quickly to their stationary distribution (see for example [Ald83]).

The gist of such reasoning is to lower the level of abstraction in order to define or interpret a property, or to prove a statement in a more elementary and intuitive manner.

In this paper, we apply the outlined way of thinking to random systems. We explore a lower level of abstraction which we call probabilistic discrete systems. A probabilistic discrete system (PDS) is defined as a (probability) distribution over deterministic discrete systems (DDS). Loosely speaking, this captures the fact that for any implementation of a random system we can fix the randomness (say, the “random tape”) to obtain a deterministic system. We then observe that there exist different PDS that are observationally equivalent, i.e., their input-output behavior is equal, implying that they correspond to the same random system. Thus, we propose to think of a random system $\mathbf { s }$ as an equivalence class of PDS and write $\mathbf { S } \in \mathbf { S }$ for a PDS S that behaves like S (i.e., it is an element of the equivalence class $\mathbf { s }$ ). For example, a uniform random function $\mathbf { R }$ can be implemented by a PDS R that initially samples the complete function table and by a PDS $\mathsf { R } ^ { \prime }$ that employs lazy sampling. These are two different PDS ( $\mathsf { R } \neq \mathsf { R } ^ { \prime }$ ), but they are behaviorally equivalent and thus correspond to the same random system, i.e., ${ \sf R } \in { \bf R }$ and $\mathbf R ^ { \prime } \in \mathbf R$ (see also the later Example 5).

Many interesting properties of random systems depend on what interaction is allowed with the system. Usually, this is formalized based on the notion of environments and, in cryptography, the notion of distinguishers. Such environments are complex objects (similar to random systems) which maintain state and can ask adaptive queries. This can pose a significant challenge for example when proving indistinguishability bounds, and naturally leads to the following question:

Is it possible to express properties which classically involve environments equivalently as natural intrinsic properties of the systems themselves, i.e., without the explicit concept of an environment?

We answer this question in the positive. The key idea is to exploit the equivalence classes: we prove that the optimal information-theoretic distinguishing advantage $\operatorname { A d v } ( \mathbf { S } , \mathbf { T } )$ is equal to $\Delta ( \mathbf { S } , \mathbf { T } )$ , the infimum statistical distance $\delta ( \mathsf { S } , \mathsf { T } )$ for PDS $\mathsf { S } \in \mathbf { S }$ and ${ \mathsf { T } } \in \mathbf { T }$ . By combining this result with the above coupling interpretation of the statistical distance, we can think of the distinguishing advantage $\operatorname { A d v } ( \mathbf { R } , \mathbf { I } )$ between a real system $\mathbf { R }$ and an ideal system $\mathbf { I }$ as a failure probability of $\mathbf { R }$ i.e., the probability that $\mathbf { R }$ is not equal to $\mathbf { I }$ . This is quite surprising since being equal is a purely static property, whereas the traditional distinguishing advantage appears to be inherently dynamic.

The coupling theorem for random systems is not only of conceptual interest. It also represents a novel technique to prove indistinguishability bounds in an elementary fashion: in the core of such a proof, one only needs to bound the statistical distance of probability distributions over deterministic systems (for example by using the Coupling Method mentioned above). Usually, the fact that the distribution is over systems will be irrelevant. In particular, the interaction with the systems and the complexity of (adaptive) environments is completely avoided.

# 1.3 Security and Indistinguishability Amplification

Security amplification is a central theme of cryptography. Turning weak objects into strong objects is useful as it allows to weaken the required assumptions. Indistinguishability amplification is a special kind of security amplification, where the quantity of interest is the closeness (in terms of adaptive indistinguishability) to some idealized system. Most of the well-known constructions achieving indistinguishability amplification do this by combining many moderately close systems into a single system that is very close to its ideal form.

In this paper, we take a more general approach to indistinguishability amplification and present results that allow (for example) to combine many moderately close systems into multiple systems that are jointly very close to independent instances of their ideal form. This is useful, since many cryptographic protocols need several independent instantiations of a scheme, for example a (pseudo-)random permutation.

# 1.4 Motivating Examples for Indistinguishability Amplification

As a first motivating example, consider the following construction $\mathbf { C }$ that combines three independent random1 permutations2 $\pi _ { 1 }$ , $\pi _ { 2 }$ , and $\pi _ { 3 }$ into two random permutations by cascading (composing) them as follows:

![](images/2a376f9081e9fe312d3d5f90463feedbcfd9cc10dd9af22cdf9fe73b3ce8eed0.jpg)

If, say, the second constructed permutation is (forward-)queried with $x$ , the value $x$ is input to $\pi _ { 2 }$ and the output $x ^ { \prime } = \pi _ { 2 } ( x )$ is forwarded to $\pi _ { 3 }$ . The output of $\pi _ { 3 } ( x ^ { \prime } )$ is the response to the query $x$ .

Clearly, if any two of the three random permutations $\pi _ { i }$ are a (perfect) uniform random permutation $\mathbf { P }$ , then $( \pi _ { 1 } \circ \pi _ { 3 } , \pi _ { 2 } \circ \pi _ { 3 } )$ behaves exactly as if all three random permutations $\pi _ { i }$ are perfect uniform random permutations (i.e., it behaves as two independent uniform random permutations $( \mathbf { P } , \mathbf { P } ^ { \prime } )$ ). Thus, we call $\mathbf { C }$ a $( 2 , 3 )$ -combiner for the pairs $( \pi _ { 1 } , { \bf P } ) , ( \pi _ { 2 } , { \bf P } ) , ( \pi _ { 3 } , { \bf P } )$ .

What, however, can we say when the $\pi _ { i }$ are only $\epsilon _ { i }$ -close $^ 3$ to a uniform random permutation? A straightforward hybrid argument shows that

$$
\mathrm { A d v } ( ( \pi _ { 1 } \circ \pi _ { 3 } , \pi _ { 2 } \circ \pi _ { 3 } ) , ( { \mathbf P } , { \mathbf P } ^ { \prime } ) ) \leq \operatorname* { m i n } ( \epsilon _ { 1 } + \epsilon _ { 2 } , \epsilon _ { 1 } + \epsilon _ { 3 } , \epsilon _ { 2 } + \epsilon _ { 3 } ) ,
$$

where $\operatorname { A d v } ( \cdot , \cdot )$ denotes the optimal distinguishing advantage over all adaptive (computationally unbounded) distinguishers. Intuitively though, one might hope that if all $\epsilon _ { i }$ (as opposed to only two of them) are small, a better bound is

achievable. Ideally, this bound should be smaller than the individual $\epsilon _ { i }$ , i.e., we want to obtain indistinguishability amplification. A consequence of one of our results (Theorem 3) is that this is indeed possible. We have

$$
\mathrm { A d v } \big ( \big ( \pi _ { 1 } \circ \pi _ { 3 } , \pi _ { 2 } \circ \pi _ { 3 } \big ) , \big ( \mathbf P , \mathbf P ^ { \prime } \big ) \big ) \ \leq \ 2 \big ( \epsilon _ { 1 } \epsilon _ { 2 } + \epsilon _ { 1 } \epsilon _ { 3 } + \epsilon _ { 2 } \epsilon _ { 3 } \big ) - 3 \epsilon _ { 1 } \epsilon _ { 2 } \epsilon _ { 3 } .
$$

More generally, it is natural to ask the following question4:

How many independent random permutations that are $\epsilon ^ { \prime }$ -close to a uniform random permutation need to be combined to obtain $m$ random permutations that are (jointly) $\epsilon$ -close (for $\epsilon \ll \epsilon ^ { \prime }$ ) to $m$ independent uniform random permutations?

This question has been studied for the special case $m \ = \ 1$ (see for example [Vau98,Vau00,MPR07]), and it is known that the cascade of $n$ independent random permutations (each $\epsilon$ -close to a uniform random permutation) is $\frac { 1 } { 2 } ( 2 \epsilon ) ^ { n }$ - close to a uniform random permutation. Of course, there is a straightforward way to use such a construction for $m = 1$ multiple times in order to obtain a basic indistinguishability result for $m > 1$ : one simply partitions the $n$ independent random permutations $\pi _ { 1 } , \ldots , \pi _ { n }$ into sets of equal size and cascades the permutations in each set.

Example 1. We can construct four random permutations from 20 random permutations as follows:

![](images/54aecc3a42f586e7e768124a6395634d62fca6ae4f4778de438d98b806f93288.jpg)

If the $\pi _ { i }$ are independent and all $\epsilon$ -close (say, $2 ^ { - 1 0 }$ -close) to a uniform random permutation, Theorem 1 of [MPR07] implies that the construction above yields four random permutations that are jointly $6 4 \epsilon ^ { 5 }$ -close ( $( 2 . 3 \epsilon ) ^ { 5 }$ -close, $2 ^ { - 4 4 . 0 }$ -close) to four independent uniform random permutations.

Naturally, one might ask whether it is possible to construct four random permutations to get stronger amplification (i.e., a larger exponent) without using more random permutations. This is indeed possible, as the following example illustrates.

Example 2. Consider the following construction of four random permutations:

![](images/8af07e0cb477fe6b68f95f482926262867ba58e42f67dfe0e522add2fa044c94.jpg)

The main advantage of this construction is that it makes use of only 15 (instead of 20) random permutations. Our results imply that if the $\pi _ { i }$ are independent and $\epsilon$ -close (say, $2 ^ { - 1 0 }$ -close) to a uniform random permutation, then the constructed four random permutations are jointly $3 2 0 \epsilon ^ { 6 }$ -close ( $( 2 . 7 \epsilon ) ^ { 6 }$ -close, $2 ^ { - 5 1 . 6 }$ -close) to four independent uniform random permutations.

Instead of random permutations one can just as well combine random functions: the same constructions and bounds as in Example 1 and Example 2 apply if we replace the cascade $\circ$ with the elementwise XOR $\oplus$ . However, in this setting, we show that the additional structure of random functions can be exploited to achieve even stronger amplification than in the examples above.

Example $\mathcal { J }$ . Let $\mathbf { F } _ { 1 } , \ldots , \mathbf { F } _ { 1 0 }$ be independent random functions over a finite field $\mathbb { F }$ , and let $A$ be a $4 \times 1 0 ~ \mathrm { M D S ^ { 5 } }$ matrix over $\mathbb { F }$ . Consider the following construction of four random functions $( \mathbf { F } _ { 1 } ^ { \prime } , \mathbf { F } _ { 2 } ^ { \prime } , \mathbf { F } _ { 3 } ^ { \prime } , \mathbf { F } _ { 4 } ^ { \prime } )$ , making use of only 10 random functions (as opposed to the above constructions with 20 and 15, respectively):

![](images/bc579068a153a1ba8609aa15236cebb5b96329197e661f06d4a5eade0aaf650d.jpg)

On input $x$ to the $i$ -th constructed function $\mathbf { { F } } _ { i } ^ { \prime }$ (for $i \in \{ 1 , 2 , 3 , 4 \}$ ), all random 1to the result functions $\mathbf { F } _ { 1 } , \ldots , \mathbf { F } _ { 1 0 }$ are queried with . $x$ , and the answers $y _ { 1 } , \ldots , y _ { 1 0 }$ are combined $\begin{array} { r } { y = \sum _ { j = 1 } ^ { 1 0 } A _ { i j } \cdot y _ { j } } \end{array}$

Our results imply that if the $\mathbf { F } _ { i }$ are independent and $\epsilon$ -close (say, $2 ^ { - 1 0 }$ -close) to a uniform random function, the four random functions $( \mathbf { F } _ { 1 } ^ { \prime } , \mathbf { F } _ { 2 } ^ { \prime } , \mathbf { F } _ { 3 } ^ { \prime } , \mathbf { F } _ { 4 } ^ { \prime } )$ are jointly $7 6 8 0 \epsilon ^ { 7 }$ -close ( $( 3 . 6 \epsilon ) ^ { 7 }$ -close, $2 ^ { - 5 7 . 0 }$ -close) to four independent uniform random functions.

# 1.5 Contributions and Outline

We briefly state our main contributions in a simplified manner. In Section 3, we define deterministic discrete systems and probabilistic discrete systems together with an equivalence relation capturing the input-output behavior. Moreover, we argue that we can characterize a random system by an equivalence class of PDS.

In Section 4, we define the distance $\Delta$ for random systems as

$$
\Delta ( \mathbf { S } , \mathbf { T } ) : = \operatorname* { i n f } _ { \bar { \mathsf { T } } \in \mathbf { S } } \delta ( \mathsf { S } , \mathsf { T } ) .
$$

We then present Theorem 1, stating that for any two random systems6 $\mathbf { S }$ and $\mathbf { T }$ we have

$$
\Delta ( \mathbf { S } , \mathbf { T } ) = \operatorname { A d v } ( \mathbf { S } , \mathbf { T } ) ,
$$

and there exist PDS $\mathbf { S } \in \mathbf { S }$ and ${ \mathsf { T } } \in \mathbf { T }$ such that $\delta ( \mathsf { S } , \mathsf { T } ) = \Delta ( \mathbf { S } , \mathbf { T } )$ . By combining this result with the coupling interpretation of the statistical distance (see above), we can think in a mathematically precise sense of the distinguishing advantage $\operatorname { A d v } ( \mathbf { R } , \mathbf { I } )$ between a real system $\mathbf { R }$ and an ideal system $\mathbf { I }$ as the probability of a failure event, i.e., the probability of the event that $\mathbf { R }$ and $\mathbf { I }$ are not equal. More specifically, we phrase a coupling theorem for random systems (Theorem 2), stating that for any two random systems $\mathbf { s }$ and $\mathbf { T }$ there exist PDS $\mathbf { S } \in \mathbf { S }$ and ${ \mathsf { T } } \in \mathbf { T }$ with a joint distribution (or coupling) such that

$$
\operatorname { A d v } ( \mathbf { S } , \mathbf { T } ) = \operatorname* { P r } ( \mathbf { S } \neq \mathbf { T } ) .
$$

The coupling theorem also represents a novel technique to prove indistinguishability bounds in an elementary fashion: in the core of such a proof, one only needs to bound the statistical distance of probability distributions over deterministic systems (for example by using the Coupling Method mentioned above). Often, the fact that the distribution is over systems will be irrelevant. In particular, the interaction with the systems and the complexity of (adaptive) environments is completely avoided, as the potential failure event can be thought of as being triggered before the interaction started.

Finally, in Section 5, we demonstrate how our coupling theorem can be used to prove indistinguishability bounds. We present Theorem 3, stating that any $( k , n )$ -combiner is an amplifier for indistinguishability. A simplified variant of the bound can be expressed as follows (see Corollary 1): If $\mathsf { C }$ is a $( k , n )$ -combiner for $( \mathsf { F } _ { 1 } , \mathsf { I } _ { 1 } ) , \hdots , ( \mathsf { F } _ { n } , \mathsf { I } _ { n } )$ and $\mathrm { A d v } ( \mathsf { F } _ { i } , \mathsf { I } _ { i } ) \leq \epsilon$ for all $i \in [ n ]$ , then

$$
\operatorname { A d v } ( \mathsf C ( \mathsf F _ { 1 } , \ldots , \mathsf F _ { n } ) , \mathsf C ( \mathsf I _ { 1 } , \ldots , \mathsf I _ { n } ) ) \le \frac { 1 } { 2 } \binom { n } { k - 1 } \cdot ( 2 \epsilon ) ^ { n - k + 1 } .
$$

The indistinguishability amplification results of [MPR07] are a special case of this corollary (for $k = 1$ and $n = 2$ ).

Moreover, we demonstrate how these indistinguishability results can be instantiated by combiners transforming $n$ independent random functions (random permutations) into $m < n$ random functions (random permutations), obtaining indistinguishability amplification.

# 1.6 Related work

There exists a vast amount of literature on information-theoretic indistinguishability of various constructions, in particular for the analysis of symmetric key cryptography. Prominent examples are constructions transforming uniform random functions into uniform random permutations or vice-versa: the Luby-Rackoff construction [LR88] (or Feistel construction), similar constructions by Naor and Reingold [NR97], the truncation of a random permutation [HWKS98], and the XOR of random permutations [BI99,Luc00].

Random Systems. The characterization of random systems by their inputoutput behavior in the form of a sequence of conditional distributions $\mathrm { p } _ { Y _ { i } \mid X ^ { i } Y ^ { i - 1 } }$ (or $\mathrm { p } _ { Y ^ { i } \mid X ^ { i } }$ ) was first described in [Mau02].

Indistinguishability Proof Techniques. There exist various techniques for proving information-theoretic indistinguishability bounds. A prominent approach is to define a failure condition such that two systems are equivalent before said condition is satisfied (see also [Mau02]). Maurer, Pietrzak, and Renner proved in [MPR07] that there always exists such a failure condition that is optimal, showing that this technique allows to prove perfectly tight indistinguishability bounds. At first glance, the lemma of [MPR07] seems to be similar to our coupling theorem. While both statements are tight characterizations of the distinguishing advantage, the crucial advantage of our result is that it allows to remove the complexity of the adaptive interaction when reasoning about indistinguishability of random systems. This enables reasoning at the level of probability distributions: one can think of a failure event occurring or not before the interaction even begins. The interactive hard-core lemma shown by Tessaro [Tes11] in the computational setting allows this kind of reasoning as well, though it only holds for so-called “cc-stateless systems”.

More involved proof techniques include directly bounding the statistical distance of the transcript distributions, such as Patarin’s H-coefficient method [Pat09], and most recently, the Chi-squared method [DHT17].

Indistinguishability Amplification. Examples of previous indistinguishability amplification results are the various computational XOR lemmas, Vaudenay’s product theorem for random permutations [Vau98,Vau00], as well as the more abstract product theorem for (stateful) random systems [MPR07] (and so-called neutralizing constructions). In [MT09], some of the results of [MPR07] have been proved in the computational setting.

A different type of indistinguishability amplification is shown in [MP04,MPR07], where the amplification is with respect to the distinguisher class, lifting nonadaptive indistinguishability to adaptive indistinguishability.

# 2 Preliminaries

Notation. For $n \in \mathbb N$ , we let $[ n ]$ denote the set $\{ 1 , \ldots , n \}$ with the convention $[ 0 ] = \emptyset$ . The set of sequences (or strings) of length $n$ over the alphabet $\boldsymbol { A }$ is denoted by $\mathcal { A } ^ { n }$ . An element of $\mathcal { A } ^ { n }$ is denoted by $a ^ { n } = ( a _ { 1 } , \ldots , a _ { n } ) $ for $a _ { i } \in \mathcal A$ . The empty sequence is denoted by $\epsilon$ . The set of finite sequences over alphabet $\mathcal { A }$ is denoted by $\mathcal { A } ^ { \ast } : = \cup _ { i \in \mathbb { N } } \mathcal { A } ^ { i }$ and the set of non-empty finite sequences is denoted by $\mathcal { A } ^ { + } : = \mathcal { A } ^ { * } - \{ \epsilon \}$ . A set $A \subseteq A ^ { * }$ is prefix-closed if $( a _ { 1 } , a _ { 2 } , \dotsc , a _ { i } ) \in A$ implies $( a _ { 1 } , a _ { 2 } , \dotsc , a _ { j } ) \in A$ for any $j \le i$ . For two sequences $x ^ { i } \in \mathcal { X } ^ { i }$ and $\hat { x } ^ { j } \in \mathcal { X } ^ { j }$ , the concatenation $x ^ { \imath } | \hat { x } ^ { \jmath }$ is the sequence $( x _ { 1 } , \ldots , x _ { i } , \hat { x } _ { 1 } , \ldots , \hat { x } _ { j } ) \in \mathcal { X } ^ { i + j }$ .

A (total) function from $X$ to $Y$ is a binary relation $f \subseteq X \times Y$ such that for every $x \in X$ there exists a unique $y \in Y$ with $( x , y ) \in f$ . A partial function from $X$ to $Y$ is a total function from $X ^ { \prime }$ to $Y$ for a subset $X ^ { \prime } \subseteq X$ . The domain of a function $f$ is denoted by $\mathsf { d o m } ( f )$ . The support of a function $f : X \to Y$ with $0 \in Y$ , for example a distribution, is defined by $\mathsf { s u p p } ( f ) : = \{ x \mid x \in X , f ( x ) \neq 0 \}$ .

A multiset over $\boldsymbol { A }$ is a function $M : \mathcal { A }  \mathbb { N }$ . We represent multisets in set notation, e.g., $M = \{ ( a , 2 ) , ( b , 7 ) \}$ denotes the multiset $M$ with domain $\{ a , b \}$ , $\textstyle M ( a ) = 2$ , and $M ( b ) = 7$ . The cardinality $| M |$ of a multiset is $\sum _ { \mathbf { \lambda } _ { \mathsf { - } } \mathbf { \lambda } _ { a } \in \mathsf { d o m } ( M ) } M ( a ) \sum _ { \mathbf { \lambda } _ { \mathsf { - } } \mathbf { \lambda } _ { \mathsf { - } } }$ . The union $\cup$ , intersection $\left( ~ \right)$ , sum $^ +$ , and difference $-$ of two multisets is defined by the pointwise maximum, minimum, sum, and difference, respectively. Finally, the symmetric difference $M \triangle M ^ { \prime }$ of two multisets is defined by $M \cup M ^ { \prime } - M \cap M ^ { \prime }$ .

Throughout this paper, we use the following notion of a (finite) distribution.

Definition 1. A distribution (or measure) over $\mathcal { A }$ is a function $\mathsf { X } : \mathcal { A } \to \mathbb { R } _ { \geq 0 }$ with finite support. The weight of a distribution is defined by

$$
| \mathsf { X } | : = \sum _ { a \in \mathcal { A } } \mathsf { X } ( a ) .
$$

$A$ probability distribution is a distribution $\mathsf { X }$ with weight 1 (i.e., $| \mathsf { X } | \overset { } { = } 1$ ). Moreover, overloading the notation, we define for a distribution $\mathsf { X }$ over $\mathcal { A }$ and $A \subseteq A$

$$
\mathsf { X } ( A ) : = \sum _ { a \in A } \mathsf { X } ( a ) .
$$

In the following, we do not demand that a distribution has weight 1, i.e., we do not assume probability distributions (unless stated explicitly). This is important, as the proof of one of our main results (Theorem 1) relies on distributions of arbitrary weight.

Definition 2. The marginal distribution $\mathsf { X } _ { i }$ of a distribution $\mathsf { X }$ over $\mathcal { A } _ { 1 } \times \cdot \cdot \cdot \times \mathcal { A } _ { n }$ is defined as

$$
\mathsf X _ { i } ( a _ { i } ) = \sum _ { a ^ { \prime } \in \mathcal A _ { 1 } \times \cdots \times \mathcal A _ { n } , a _ { i } ^ { \prime } = a _ { i } } \mathsf X ( a ^ { \prime } ) .
$$

Lemma 1. Let $\mathsf { X } _ { 1 } , \ldots , \mathsf { X } _ { n }$ be distributions over $\mathcal { A } _ { 1 }$ , . . . , ${ \mathcal { A } } _ { n }$ , respectively, such that all $\mathsf { X } _ { i }$ have the same weight $p \in \mathbb { R } _ { \geq 0 }$ . Then, there exists $a$ (joint) distribution $\mathsf { X }$ over $\mathcal { A } _ { 1 } \times \cdots \times \mathcal { A } _ { n }$ with weight $p$ and marginals $\mathsf { X } _ { i }$ .

Proof. A possible choice is $\begin{array} { r } { \mathsf { X } ( a _ { 1 } , \ldots , a _ { n } ) : = p ^ { - ( n - 1 ) } \prod _ { i \in [ n ] } \mathsf X _ { i } ( a _ { i } ) . } \end{array}$

Definition 3. The statistical distance of two distributions $\mathsf { X } : \mathcal { A } \to \mathbb { R } _ { \geq 0 }$ and $\mathsf { Y } : \mathcal { A } \to \mathbb { R } _ { \geq 0 }$ is

$$
\delta ( { \mathsf X } , { \mathsf Y } ) : = \sum _ { a \in { \mathcal A } } \operatorname* { m a x } ( 0 , { \mathsf X } ( a ) - { \mathsf Y } ( a ) ) = | { \mathsf X } | - \sum _ { a \in { \mathcal A } } \operatorname* { m i n } ( { \mathsf X } ( a ) , { \mathsf Y } ( a ) ) .
$$

Note that for distributions $\mathsf { X }$ and Y of different weight, i.e., $| \mathsf { X } | \neq | \mathsf { Y } |$ , the statistical distance is not symmetric $( \delta ( { \sf X } , { \sf Y } ) \neq \delta ( { \sf Y } , { \sf X } ) )$ . Moreover, for distributions of the same weight, i.e., $| \mathsf { X } | = | \mathsf { Y } |$ , we have $\begin{array} { r } { \delta ( { \mathsf X } , { \mathsf Y } ) = \frac { 1 } { 2 } \sum _ { a \in \mathcal { A } } \vert { \mathsf X } ( a ) - { \mathsf Y } ( a ) \vert } \end{array}$ .

The following lemma, proved in Appendix A, is an immediate consequence of the definition of the statistical distance.

Lemma 2. Let $\langle \boldsymbol { A } _ { i } \rangle _ { i \in [ n ] }$ be a partition of a set $\mathcal { A }$ , and let $\mathsf { X } _ { 1 } , \ldots , \mathsf { X } _ { n }$ as well as $\mathsf { Y } _ { 1 } , \ldots , \mathsf { Y } _ { n }$ be distributions over $\mathcal { A }$ such that $\mathsf { s u p p } ( \mathsf { X } _ { i } ) \subseteq { \mathcal { A } } _ { i }$ and $\mathsf { s u p p } ( \mathsf { Y } _ { i } ) \subseteq { \mathcal { A } } _ { i }$ for all $i \in [ n ]$ . For $\begin{array} { r } { \mathsf { X } : = \sum _ { i \in [ n ] } \mathsf { X } _ { i } } \end{array}$ and $\begin{array} { r } { \mathsf { Y } : = \sum _ { i \in [ n ] } \mathsf { Y } _ { i } } \end{array}$ we have

$$
\delta ( { \sf X } , { \sf Y } ) = \sum _ { i \in [ n ] } \delta ( { \sf X } _ { i } , { \sf Y } _ { i } ) .
$$

Definition 4. For a distribution $\mathsf { X } : \mathcal { A } \to \mathbb { R } _ { \geq 0 }$ and a function $f : { \mathcal { A } }  B$ , the $f$ -transformation of $\mathsf { X }$ , denoted by $f ( { \sf X } )$ , is the distribution over $\boldsymbol { B }$ defined by7

$$
f ( \mathsf { X } ) : = \mathsf { X } \circ f ^ { - 1 } .
$$

The following lemma states that the statistical distance of two distributions cannot increase if a function $f$ is applied (to both distributions). This is wellknown for the case in which $\mathsf { X }$ and Y are probability distributions. We prove the claim in Appendix A.

Lemma 3. For two distributions $\mathsf { X }$ and Y over $\mathcal { A }$ and any total function $f$ : $A  B$ we have

$$
\delta ( { \sf X } , { \sf Y } ) \geq \delta ( f ( { \sf X } ) , f ( { \sf Y } ) ) .
$$

Lemma 4 (Coupling Lemma, Lemma 3.6 of [Ald83]). Let X, Y be probability distributions over the same set.

1. For any joint distribution of $\mathsf { X }$ and Y we have

$$
\delta ( { \sf X } , { \sf Y } ) \leq \mathrm { P r } ( { \sf X } \neq { \sf Y } ) .
$$

2. There exists a joint distribution of $\mathsf { X }$ and Y such that

$$
\delta ( { \sf X } , { \sf Y } ) = \mathrm { P r } ( { \sf X } \neq { \sf Y } ) .
$$

# 3 Discrete Random Systems

# 3.1 Deterministic Discrete Systems

A deterministic discrete $( \mathcal { X } , \mathcal { Y } )$ -system is a system with input alphabet $\mathcal { X }$ and output alphabet $_ { \mathcal { V } }$ . The system’s first output (or response) $y _ { 1 } \in \mathcal { V }$ is a function of the first input (or query) $x _ { 1 } \in \mathcal { X }$ . The second output $y _ { 2 }$ is a priori a function of the first two inputs $x _ { 1 } , x _ { 2 }$ and the first output $y _ { 1 }$ . However, since $y _ { 1 }$ is already a function of $x _ { 1 }$ , it is more minimal to define $y _ { 2 }$ as a function of the first two inputs $x ^ { 2 } = ( x _ { 1 } , x _ { 2 } ) \in \mathcal { X } ^ { 2 }$ . In general, the $i$ -th output $y _ { i } \in \mathcal { V }$ is a function of the first $_ i$ inputs $x ^ { i } \in \mathcal { X } ^ { i }$ .

Definition 5. $A$ deterministic discrete $( \mathcal { X } , \mathcal { Y } )$ -system (or $( \mathcal { X } , \mathcal { Y } )$ -DDS) is $a$ partial function

$$
s : \mathcal { X } ^ { + } \to \mathcal { Y }
$$

with prefix-closed domain. An $( \mathcal { X } , \mathcal { Y } )$ -DDS s is finite if $\mathcal { X }$ is finite and ${ \mathsf { d o m } } ( s ) \subseteq$ $\cup _ { i \leq n } \mathcal { X } ^ { i }$ for some $n \in \mathbb N$ . Moreover, we let $\mathsf { d o m } _ { 1 } ( s )$ denote the input alphabet for the first query, i.e., $\mathsf { d o m } _ { 1 } ( s ) = \mathsf { d o m } ( s ) \cap \mathcal { X } ^ { \mathrm { 1 } }$ .

A DDS is an abstraction capturing exactly the input-output behavior of a deterministic system. Thus, it is independent of any implementation details that describe how the outputs are produced. One can therefore think of a DDS as an equivalence class of more explicit implementations. For example, different programs (or Turing machines) can correspond to the same DDS. Moreover, the fact that there is state is captured canonically by letting each output depend on the previous sequence of inputs, as opposed to introducing an explicit state space.

In this paper, we restrict ourselves to finite systems. We note that the definitions and claims can be generalized to infinite systems. Alternatively, one can often interpret an infinite system as a parametrized family of finite systems.

![](images/94cd581dd4297030b84df5d37caca6b66ca27468a5213c2b01d3187762a5ff2a.jpg)  
Fig. 1. The four single-query $( \{ 0 , 1 \} , \{ 0 , 1 \} )$ -DDS zero, one, id, flip.

Example 4. Figure 1 depicts the four single-query $( \{ 0 , 1 \} , \{ 0 , 1 \} )$ -DDS zero, one, id, and flip, i.e., all total functions from $\{ 0 , 1 \}$ to $\{ 0 , 1 \}$

$$
\begin{array} { r } { \circ ( x ) : = 0 , \quad \mathsf { o n e } ( x ) : = 1 , \quad \mathsf { i d } ( x ) : = x , \quad \mathsf { f l i p } ( } \end{array}
$$

An environment is an object (similar to a DDS) that interacts with a system $s$ by producing the inputs $x _ { i }$ for $s$ and receiving the corresponding outputs $y _ { i }$ . Environments are adaptive and stateful, i.e., a produced input $x _ { i }$ is a function of all the previous outputs $y ^ { i - 1 } = ( y _ { 1 } , \dots , y _ { i - 1 } )$ . Moreover, we allow an environment to stop at any time.

Definition 6. A deterministic discrete environment for an $( \mathcal { X } , \mathcal { Y } )$ -DDS (or $( \mathcal { V } , \mathcal { X } )$ -DDE) is a partial function

$$
e : y ^ { * } \to \mathcal { X }
$$

with prefix-closed domain.

Definition 7. The transcript of a system s in environment $e$ , denoted by $\operatorname { t r } ( s , e )$ , is the sequence of pairs $( x _ { 1 } , y _ { 1 } ) , ( x _ { 2 } , y _ { 2 } ) , \ldots , ( x _ { l } , y _ { l } )$ , defined for $i \geq 1$ by

$$
x _ { i } = e ( y _ { 1 } , \ldots , y _ { i - 1 } ) a n d y _ { i } = s ( x _ { 1 } , \ldots , x _ { i } ) .
$$

We require the environment e to be compatible with $s$ , i.e., the environment must not query s outside of the system’s domain. Formally, this means that $y _ { i } =$ $s ( x _ { 1 } , \ldots , x _ { i } )$ is defined whenever $x _ { i } = e ( y _ { 1 } , . . . , y _ { i - 1 } )$ is defined. If $e ( y _ { 1 } , \dots , y _ { i - 1 } )$ is undefined (the environment stops), the transcript ends and has length $\begin{array} { r } { l = i - 1 } \end{array}$ .

# 3.2 Probabilistic Discrete Systems

We define probabilistic systems (environments) as distributions over deterministic systems (environments). Note that even though we use the term probabilistic, we do not assume that the corresponding distributions are probability distributions (i.e., they do not need to sum up to 1, unless explicitly stated).

Definition 8. $A$ probabilistic discrete $( \mathcal { X } , \mathcal { Y } )$ -system S (or $( \mathcal { X } , \mathcal { Y } )$ - $P D S$ ) is a distribution over $( \mathcal { X } , \mathcal { Y } )$ -DDS such that all DDS in the support of S have the same domain, denoted8 by dom(S). We always assume that ${ \sf S }$ is finite, i.e., $\mathcal { X }$ is finite and $\mathsf { d o m } ( \mathsf { S } ) \subseteq \cup _ { i \leq n } \chi ^ { \ i }$ for some $n \in  { \mathbb { N } }$ .

Definition 9. A probabilistic discrete environment for an $( \mathcal { X } , \mathcal { Y } )$ -PDS (or $( \mathcal { V } , \mathcal { X } )$ -PDE) is a distribution over $( { \mathcal { V } } , { \mathcal { X } } )$ -DDE.

Observe that a PDS contains all information for a system that can be executed arbitrarily many times, i.e., a system that can be rewound and then queried again on the same randomness. We consider the standard setting in which a system can only be executed once (see Definition 7). In this setting, there exist different PDS that behave identically from the perspective of any environment, i.e., they exhibit the same behavior. The following example demonstrates this.

Example $\it 5$ . Let $\vee$ be the uniform probability distribution over the set of all single-query $( \{ 0 , 1 \} , \{ 0 , 1 \} )$ -DDS $\{ \mathsf { z e r o } , \mathsf { o n e } , \mathsf { i d } , \mathsf { f } \mathsf { l i p } \}$ (see Figure 1), i.e.,

$$
\mathsf { V } : = \{ ( \mathsf { z e r o } , 1 / 4 ) , ( \mathsf { o n e } , 1 / 4 ) , ( \mathsf { i d } , 1 / 4 ) , ( \mathsf { f } \mathsf { l i p } , 1 / 4 ) \} .
$$

For any input $x \in \{ 0 , 1 \}$ , the system $\vee$ outputs a uniform random bit. Formally, the transcript distribution $\mathrm { t r } ( \mathsf { V } , e _ { x } )$ for an environment $e _ { x }$ that inputs $x \in \{ 0 , 1 \}$ (i.e., $e _ { x } ( \epsilon ) = x$ ) is

$$
\mathrm { t r } ( \mathsf { V } , e _ { x } ) = \{ ( ( x , 0 ) , 1 / 2 ) , ( ( x , 1 ) , 1 / 2 ) \} .
$$

The PDS V represents a system that samples the answers for both possible inputs $x \in \{ 0 , 1 \}$ independently (even though only one query is answered). Clearly, the exact same behavior can be implemented by sampling a uniform bit and using it for whatever query is asked, resulting in the PDS

$$
\mathsf { V } ^ { \prime } : = \{ ( \mathsf { z e r o } , 1 / 2 ) , ( \mathsf { o n e } , 1 / 2 ) , ( \mathsf { i d } , 0 ) , ( \mathsf { f } \mathsf { 1 i p } , 0 ) \} .
$$

It is easy to verify that for any $\alpha \in [ 0 , 1 / 2 ]$ , the following PDS $\mathsf { V } _ { \alpha }$ has the same behavior as $\vee$ :

$$
\mathsf { V } _ { \alpha } : = \{ ( \mathsf { z e r o } , \alpha ) , ( \mathsf { o n e } , \alpha ) , ( \mathrm { i d } , 1 / 2 - \alpha ) , ( \mathrm { f 1 i p } , 1 / 2 - \alpha ) \} .
$$

Actually, it is not difficult to show that every PDS with the behavior of $\vee$ is of the form $\mathsf { V } _ { \alpha }$ . Thus, we can think of the random system $\mathbf { V }$ (that responds for every input $x \in \{ 0 , 1 \}$ with a uniform random bit) as the equivalence class

$$
\begin{array} { r } { \mathbb { V } ] = \{ \forall _ { \alpha } \ : | \ : \alpha \in [ 0 , 1 / 2 ] \} . } \end{array}
$$

More generally, we define two PDS to be equivalent if their transcript distributions are the same in all environments. It is easy to see that considering only deterministic environments results in the same equivalence notion that is obtained when considering probabilistic environments.

Definition 10. Two $( \mathcal { X } , \mathcal { Y } )$ -PDS S and $\top$ are equivalent, denoted by ${ \mathsf { S } } \equiv { \mathsf { T } }$ , if they have the same domain and9

$\operatorname { t r } ( 5 , e ) = \operatorname { t r } ( 7 , e )$ for all compatible $( \mathcal { V } , \mathcal { X } )$ -DDE $e$ .

The equivalence class of a PDS S is denoted by [S] $| : = \{ \mathsf { S } ^ { \prime } \mid \mathsf { S } ^ { \prime } , \mathsf { S } \equiv \mathsf { S } ^ { \prime } \}$ .

The following lemma, proved in Appendix A, states that for S and $\top$ to be equivalent it suffices that the transcript distribution $\operatorname { t r } ( \mathsf { S } , e )$ is equal to $\operatorname { t r } ( { \mathsf { T } } , e )$ for all non-adaptive $_ { 1 0 }$ deterministic environments $e$ .

Lemma 5. For any two $( \mathcal { X } , \mathcal { Y } )$ -PDS S and $\top$ with the same domain we have ${ \sf S } \equiv { \sf T }$ if and only if

$\operatorname { t r } ( 5 , e ) = \operatorname { t r } ( 7 , e )$ for all compatible non-adaptive $( \mathcal { V } , \mathcal { X } )$ -DDE e.

Stated differently, an equivalence class [S] of PDS can be characterized by the transcript distributions for all non-adaptive deterministic environments. Since a non-adaptive deterministic environment is uniquely described by a sequence $x ^ { k } \in \mathcal { X } ^ { k }$ of inputs and the corresponding transcript distribution $\operatorname { t r } ( \mathsf { S } , e )$ is essentially the distribution of observed outputs under the input sequence $x ^ { k }$ , it follows immediately that an equivalence class of PDS describes exactly a random system as introduced in [Mau02] (where a characterization in the form of a sequence of conditional distributions $\mathrm { p } _ { Y _ { i } \mid X ^ { i } Y ^ { i - 1 } }$ or $\mathrm { p } _ { Y ^ { i } \mid X ^ { i } }$ was used).

Notation 1. We use bold-face font $\mathbf { s }$ to denote a random system, an equivalence class of PDS. Since the transcript distribution $\operatorname { t r } ( \mathsf { S } , e )$ does (by definition) only depend on the random system $\mathbf { s }$ and not on the concrete element $\mathbf { S } \in \mathbf { S }$ of the equivalence class, we write

$$
\operatorname { t r } ( \mathbf { S } , e )
$$

to denote the transcript distribution of the random system $\mathbf { s }$ in environment $e$

# 4 Coupling Theorem for Discrete Systems

# 4.1 Distance of Equivalence Classes and the Coupling Theorem

The optimal distinguishing advantage is widely-used in the (cryptographic) literature to quantify the distance between random systems. It can be defined as the supremum statistical distance of the transcripts under all compatible $( { \mathcal { V } } , { \mathcal { X } } )$ -DDE. In the information-theoretic setting, this is equivalent to the classical definition as the supremum difference of the probability that a (probabilistic) distinguisher outputs 1 when interacting with each system.

Definition 11. For two random $( \mathcal { X } , \mathcal { Y } )$ -systems $\mathbf { s }$ and $\mathbf { T }$ with the same domain, the optimal distinguishing advantage $\operatorname { A d v } ( \mathbf { S } , \mathbf { T } )$ is defined by

$$
\operatorname { A d v } ( \mathbf { S } , \mathbf { T } ) : = \operatorname* { s u p } _ { e } \delta ( \operatorname { t r } ( \mathbf { S } , e ) , \operatorname { t r } ( \mathbf { T } , e ) ) ,
$$

where the supremum is over all compatible $( \mathcal { V } , \mathcal { X } )$ -DDE.

Understanding a random system as an equivalence class of probabilistic discrete systems gives rise to the following distance notion $\Delta$ :

Definition 12. For two random $( \mathcal { X } , \mathcal { Y } )$ -systems $\mathbf { s }$ and $\mathbf { T }$ with the same domain we define

$$
\Delta ( \mathbf { S } , \mathbf { T } ) : = \operatorname* { i n f } _ { \bar { \mathsf { T } } \in \mathbf { S } } \delta ( \mathsf { S } , \mathsf { T } ) .
$$

Note that since there exist PDS S and ${ \mathsf S } ^ { \prime }$ that are equivalent ( ${ \mathsf { S } } \equiv { \mathsf { S } } ^ { \prime }$ ) even though $\delta ( \mathsf { S } , \mathsf { S } ^ { \prime } ) = 1$ (for example $\mathsf { V } _ { 0 }$ and $\mathsf { V } _ { 1 / 2 }$ from Example 5), taking the infimum seems to be necessary to quantify the distance of random systems in a meaningful way. We can now state the first theorem.

Theorem 1. For any two random $( \mathcal { X } , \mathcal { Y } )$ -systems $\mathbf { s }$ and $\mathbf { T }$ with the same domain we have

$$
\Delta ( \mathbf { S } , \mathbf { T } ) = \operatorname { A d v } ( \mathbf { S } , \mathbf { T } ) ,
$$

and there exist PDS $\mathbf { S } \in \mathbf { S }$ and ${ \mathsf { T } } \in \mathbf { T }$ such that $\delta ( \mathsf { S } , \mathsf { T } ) = \Delta ( \mathbf { S } , \mathbf { T } )$ .

The coupling theorem for random systems is an immediate consequence of Theorem 1 and the classical Coupling Lemma (Lemma 4).

Theorem 2 (Coupling Theorem for Random Systems). For any two random systems $\mathbf { s }$ and $\mathbf { T }$ there exist PDS $\mathsf { S } \in \mathbf { S }$ and ${ \mathsf { T } } \in \mathbf { T }$ with a joint distribution (or coupling) such that

$$
\operatorname { A d v } ( \mathbf { S } , \mathbf { T } ) = \operatorname* { P r } ( \mathbf { S } \neq \mathbf { T } ) .
$$

# 4.2 Proof of Theorem 1

The Single-Query Case. We start by proving Theorem 1 for single-query random systems. Let $\mathbf { s }$ and $\mathbf { T }$ be two single-query $( \mathcal { X } , \mathcal { Y } )$ -systems, represented by the two $( \mathcal { X } , \mathcal { Y } )$ -PDS $\mathbf { S } \in \mathbf { S }$ and ${ \mathsf { T } } \in { \mathbf { T } }$ . Observe that a single-query $( \mathcal { X } , \mathcal { Y } )$ -DDS $s$ is a function from $\mathcal { X }$ to $_ { \mathcal { V } }$ , and can thus be represented by a tuple

$$
( y _ { x _ { 1 } } , y _ { x _ { 2 } } , \dotsc , y _ { x _ { n } } ) \in { \mathcal { V } } ^ { n } , { \mathrm { ~ w h e r e ~ } } { \mathcal { X } } = \{ x _ { 1 } , \dotsc , x _ { n } \} { \mathrm { ~ a n d ~ } } s ( x _ { i } ) = y _ { x _ { i } } .
$$

Hence, we can represent S and $\top$ as distributions over $\mathcal { V } ^ { n }$ for $n = | \mathcal { X } |$ . If $\mathsf { S } _ { i }$ and $\mathsf { T } _ { i }$ are the marginal distributions of the $i$ -th index of $\mathsf { S }$ and $\top$ , respectively, then an environment that inputs the value $x _ { i } \in \mathcal X$ will observe either $\mathsf { S } _ { i }$ or $\mathsf { T } _ { i }$ . From

Definition 11 it follows that an optimal environment chooses $i$ such that $\delta ( \mathsf { S } _ { i } , \mathsf { T } _ { i } )$ is maximized, so we have

$$
\operatorname { A d v } ( \mathbf { S } , \mathbf { T } ) = \operatorname* { m a x } _ { i \in [ n ] } \delta ( \mathsf { S } _ { i } , \mathsf { T } _ { i } ) .
$$

The following lemma directly implies that there exist PDS ${ \sf S } ^ { \prime } \in \bf S$ and $\mathbf { T } ^ { \prime } \in \mathbf { T }$ such that $\delta ( \mathsf { S } ^ { \prime } , \mathsf { T } ^ { \prime } ) = \mathrm { A d v } ( \mathsf { S } , \mathbf { T } )$ . This proves Theorem 1 for single-query systems.

Lemma 6. For each $i \in [ n ]$ , let $\mathsf { X } _ { i }$ and $\mathsf { Y } _ { i }$ be distributions over $\mathbf { \mathcal { A } } _ { i }$ , such that all $\mathsf { X } _ { i }$ have the same weight $p \times \in \mathbb { R } _ { \geq 0 }$ and all $\mathsf { Y } _ { i }$ have the same weight $p \mathrm { v } \in \mathbb { R } _ { \geq 0 }$ . Then there exist (joint) distributions $\mathsf { X }$ and $\textsf { Y }$ over $\mathcal { A } _ { 1 } \times \cdots \times \mathcal { A } _ { n }$ with marginals $\mathsf { X } _ { i }$ and $\mathsf { Y } _ { i }$ , respectively, such that

$$
\delta ( \mathsf { X } , \mathsf { Y } ) = \operatorname* { m a x } _ { i \in [ n ] } \delta ( \mathsf { X } _ { i } , \mathsf { Y } _ { i } ) .
$$

Proof. As $\begin{array} { r } { \delta ( \mathsf { X } _ { i } , \mathsf { Y } _ { i } ) = p \mathsf { x } - \sum _ { a \in { \mathcal { A } } _ { i } } \operatorname* { m i n } ( \mathsf { X } _ { i } ( a ) , \mathsf { Y } _ { i } ( a ) ) } \end{array}$ , we have

$$
\operatorname* { m a x } _ { i \in [ n ] } \delta ( \mathsf { X } _ { i } , \mathsf { Y } _ { i } ) = p \mathsf { x } - \operatorname* { m i n } _ { i \in [ n ] } \sum _ { a \in \mathcal { A } _ { i } } \operatorname* { m i n } ( \mathsf { X } _ { i } ( a ) , \mathsf { Y } _ { i } ( a ) ) .
$$

Let $\begin{array} { r } { \tau : = \operatorname* { m i n } _ { i \in [ n ] } \sum _ { a \in \mathcal { A } _ { i } } \operatorname* { m i n } ( \mathsf { X } _ { i } ( a ) , \mathsf { Y } _ { i } ( a ) ) } \end{array}$ . Clearly, for every $i \in [ n ]$ , there exist distributions $\mathsf { E } _ { i }$ , $\mathsf { X } _ { i } ^ { \prime }$ , and $\mathsf { Y } _ { i } ^ { \prime }$ such that $\mathsf { E } _ { i }$ has weight $\tau$ (i.e., $| \mathsf { E } _ { i } | = \tau$ ) and

$$
{ \sf X } _ { i } = { \sf E } _ { i } + { \sf X } _ { i } ^ { \prime } \ \mathrm { a n d } \ { \sf Y } _ { i } = { \sf E } _ { i } + { \sf Y } _ { i } ^ { \prime } .
$$

By invoking Lemma 1 three times, we obtain the joint distributions $\mathsf { E } , \mathsf { X } ^ { \prime }$ , and ${ \mathsf { Y } } ^ { \prime }$ of all $\mathsf { E } _ { i }$ , $\mathsf { X } _ { i } ^ { \prime }$ , and $\mathsf { Y } _ { i } ^ { \prime }$ , respectively. We let ${ \sf X } : = \sf E + \sf X ^ { \prime }$ and $\mathsf { Y } : = \mathsf { E } + \mathsf { Y } ^ { \prime }$ . It is easy to verify that $\mathsf X$ has the marginals $\mathsf { X } _ { i }$ and Y has the marginals $\mathsf { Y } _ { i }$ . Moreover,

$$
\sum _ { \substack { v \in \mathcal { A } _ { 1 } \times \cdots \times \mathcal { A } _ { n } } } \operatorname* { m i n } ( \mathsf { X } ( v ) , \mathsf { Y } ( v ) ) \geq \sum _ { \substack { v \in \mathcal { A } _ { 1 } \times \cdots \times \mathcal { A } _ { n } } } \mathsf { E } ( v ) = | \mathsf { E } | = \tau ,
$$

which implies $\delta ( { \mathsf X } , { \mathsf Y } ) \leq p { \mathsf X } - \tau = \operatorname* { m a x } _ { i \in [ n ] } \delta ( { \mathsf X } _ { i } , { \mathsf Y } _ { i } )$ .

Finally, we have $\delta ( { \sf X } , { \sf Y } ) \geq \delta ( { \sf X } _ { i } , { \sf Y } _ { i } )$ for all $i \in [ n ]$ due to Lemma 3 and thus $\delta ( \mathsf { X } , \mathsf { Y } ) \geq \operatorname* { m a x } _ { i \in [ n ] } \delta ( \mathsf { X } _ { i } , \mathsf { Y } _ { i } )$ , concluding the proof. ut

The General Case. Before proving the general case of Theorem 1, we introduce the following notion of a successor system.

Notation $\boldsymbol { \mathcal { Z } }$ . For an $( \mathcal { X } , \mathcal { Y } )$ -DDS $s$ and any first query $x \in \mathsf { d o m } _ { 1 } ( s )$ , we let $s ^ { \uparrow x }$ denote the $( \mathcal { X } , \mathcal { Y } )$ -DDS that behaves like $s$ after the first query $x$ has been input. That is, if $s$ answers at most $q$ queries, $s ^ { \uparrow x }$ answers at most $( q - 1 )$ queries. Formally,

$$
s ^ { \uparrow x } ( \hat { x } ^ { i } ) : = s ( x | \hat { x } ^ { i } ) .
$$

Analogously, we define for a $( \mathcal { V } , \mathcal { X } )$ -DDE $e$ the successor $e ^ { \uparrow y } ( \hat { y } ^ { i } ) : = e ( y | \hat { y } ^ { i } )$ . Finally, for an $( \mathcal { X } , \mathcal { Y } )$ -PDS S, we let $\mathsf { S } ^ { \uparrow x \downarrow y }$ denote the transformation of ${ \sf S }$ with the partial function $s \mapsto s ^ { \uparrow x \downarrow y }$ (see Definition 4), where $s ^ { \uparrow x \downarrow y }$ is equal to $s ^ { \uparrow x }$ if $s ( x ) = y$ and undefined otherwise.

We stress that if ${ \sf S }$ is a probability distribution (i.e., it sums to $^ { 1 }$ ), $\mathsf { S } ^ { \uparrow x \downarrow y }$ is in general not a probability distribution anymore: the weight $\left| \mathsf { S } ^ { \uparrow x \downarrow y } \right|$ is the probability that S responds with $y$ to the query $x$ .

Proof (of Theorem 1). We prove the theorem using (arbitrary) representatives S and $\top$ of the equivalence classes, i.e., $\mathbf { s }$ and $\mathbf { T }$ correspond to [S] and [T], respectively. First, observe that $\Delta ( \mathbf { S } , \mathbf { T } ) \ge \mathrm { A d v } ( \mathbf { S } , \mathbf { T } )$ , since we have for any environment $e$ and any ${ \sf S } ^ { \prime } \in [ { \sf S } ]$ and ${ \sf T } ^ { \prime } \in [ { \sf T } ]$

$$
\delta ( \mathsf { S } ^ { \prime } , \mathsf { T } ^ { \prime } ) \geq \delta ( \operatorname { t r } ( \mathsf { S } ^ { \prime } , e ) , \operatorname { t r } ( \mathsf { T } ^ { \prime } , e ) ) = \delta ( \operatorname { t r } ( \mathsf { S } , e ) , \operatorname { t r } ( \mathsf { T } , e ) ) .
$$

The inequality is due to Lemma 3 and the equality is due to Definition 10. Thus, it only remains to prove that for all $q$ -query PDS ${ \sf S }$ and $\top$ with the same domain there exist ${ \sf S } ^ { \prime } \in [ { \sf S } ]$ and ${ \sf T } ^ { \prime } \in [ { \sf T } ]$ such that

$$
\delta ( { \sf S } ^ { \prime } , { \sf T } ^ { \prime } ) = \operatorname* { s u p } _ { e } \delta ( \operatorname { t r } ( { \sf S } , e ) , \operatorname { t r } ( { \sf T } , e ) ) .
$$

The proof of (1) is by induction over the maximal number of answered queries $q \in \mathbb N$ . If $q = 0$ , the claim follows immediately. Otherwise ( $q \geq 1$ ), let ${ { \mathcal { X } } ^ { \prime } } \subseteq { { \mathcal { X } } }$ be the input alphabet for the first query, i.e., $\mathcal { X } ^ { \prime } = \mathsf { d o m } _ { 1 } ( \mathsf { S } ) = \mathsf { d o m } _ { 1 } ( \mathsf { T } )$ . We have

$$
\begin{array} { r l } & { \underset { e } { \operatorname* { s u p } } \delta ( \mathrm { t r } ( \mathsf { S } , e ) , \mathrm { t r } ( \mathsf { T } , e ) ) = \underset { x \in \mathcal { X } ^ { \prime } } { \operatorname* { m a x } } \underset { e ( \epsilon ) = x } { \operatorname* { s u p } } \delta ( \mathrm { t r } ( \mathsf { S } , e ) , \mathrm { t r } ( \mathsf { T } , e ) ) } \\ & { \quad \quad \quad = \underset { x \in \mathcal { X } ^ { \prime } } { \operatorname* { m a x } } \underset { e ( \epsilon ) = x } { \operatorname* { s u p } } \sum _ { y \in \mathcal { Y } } \delta ( \mathrm { t r } ( \mathsf { S } ^ { \uparrow x \downarrow y } , e ^ { \uparrow y } ) , \mathrm { t r } ( \mathsf { T } ^ { \uparrow x \downarrow y } , e ^ { \uparrow y } ) ) } \\ & { \quad \quad \quad = \underset { x \in \mathcal { X } ^ { \prime } } { \operatorname* { m a x } } \underset { y \in \mathcal { Y } } { \sum } \underset { e ^ { \prime } } { \operatorname* { s u p } } \delta ( \mathrm { t r } ( \mathsf { S } ^ { \uparrow x \downarrow y } , e ^ { \prime } ) , \mathrm { t r } ( \mathsf { T } ^ { \uparrow x \downarrow y } , e ^ { \prime } ) ) . } \end{array}
$$

The second step is due to Lemma 2. In the last step, we used that the environment is adaptive: for each possible value $y \in \mathcal { V }$ , the subsequent query strategy may be chosen separately.

As $\mathsf { S } ^ { \uparrow x \downarrow y }$ and $\mathsf { T } ^ { \uparrow x \downarrow y }$ are systems answering at most $q - 1$ queries, we can invoke the induction hypothesis to obtain $\mathsf { S } _ { x y } \in [ \mathsf { S } ^ { \uparrow x \downarrow y } ]$ and $\mathsf { T } _ { x y } \in [ \mathsf { T } ^ { \uparrow x \downarrow y } ]$ for each $( x , y ) \in \mathcal { X } ^ { \prime } \times \mathcal { Y }$ such that

$$
\operatorname* { s u p } _ { e ^ { \prime } } \delta ( \mathrm { t r } ( \mathsf { S } ^ { \uparrow x \downarrow y } , e ^ { \prime } ) , \mathrm { t r } ( \mathsf { T } ^ { \uparrow x \downarrow y } , e ^ { \prime } ) ) = \delta ( \mathsf { S } _ { x y } , \mathsf { T } _ { x y } ) .
$$

For each $( x , y ) \in \mathcal { X } ^ { \prime } \times \mathcal { Y }$ , we prepend an initial query to the deterministic systems in the support of $\mathsf { S } _ { x y }$ to obtain the $q$ -query PDS $\mathsf { S } _ { x y } ^ { \prime }$ that answers the first query $x$ $\mathsf { S } _ { x y } ^ { \prime \uparrow x \downarrow y } = \mathsf { S } _ { x y }$ (deterministically) with . $\mathsf { T } _ { x y } ^ { \prime }$ is defin $y$ , that is undefined for all d analogously. This does not change the statistical $x ^ { \prime } \neq x$ as first query, and distance: we have for every $( x , y ) \in \mathcal { X } ^ { \prime } \times \mathcal { Y }$

$$
\delta ( \mathsf { S } _ { x y } , \mathsf { T } _ { x y } ) = \delta ( \mathsf { S } _ { x y } ^ { \prime } , \mathsf { T } _ { x y } ^ { \prime } ) .
$$

Next, we define the PDS $\begin{array} { r } { \mathsf { S } _ { x } ^ { \prime } : = \sum _ { y \in y } \mathsf { S } _ { x y } ^ { \prime } } \end{array}$ and $\begin{array} { r } { \mathsf T _ { x } ^ { \prime } : = \sum _ { y \in y } \mathsf T _ { x y } ^ { \prime } } \end{array}$ . We obtain via Lemma 2 that

$$
\sum _ { y \in \mathcal { V } } \delta ( \mathsf { S } _ { x y } ^ { \prime } , \mathsf { T } _ { x y } ^ { \prime } ) = \delta ( \mathsf { S } _ { x } ^ { \prime } , \mathsf { T } _ { x } ^ { \prime } ) .
$$

By Lemma 6, there exists a joint distribution11 ${ \mathsf S } ^ { \prime }$ of all $\mathsf { S } _ { x } ^ { \prime }$ and a joint distribution ${ \sf T } ^ { \prime }$ of all $\mathsf { T } _ { x } ^ { \prime }$ such that

$$
\operatorname* { m a x } _ { x \in \mathcal { X } ^ { \prime } } \delta ( \mathsf { S } _ { x } ^ { \prime } , \mathsf { T } _ { x } ^ { \prime } ) = \delta ( \mathsf { S } ^ { \prime } , \mathsf { T } ^ { \prime } ) .
$$

Finally, observe that ${ \sf S } ^ { \prime } \in [ { \sf S } ]$ and ${ \sf T } ^ { \prime } \in [ { \sf T } ]$ , which concludes the proof.

# 5 Indistinguishability Amplification from Combiners

The goal of indistinguishability amplification is to construct an object which is $\epsilon$ -close to its ideal from objects which are only $\epsilon ^ { \prime }$ -close to their ideal for $\epsilon$ much smaller than $\epsilon ^ { \prime }$ . The most basic type of this construction is to XOR two independent bits $\mathsf { B } _ { 1 }$ and $\mathsf { B } _ { 2 }$ . It is easy to verify that if $\mathsf { B } _ { 1 }$ and $\mathsf { B } _ { 2 }$ are $\epsilon _ { 1 }$ - and $\epsilon _ { 2 }$ - close (in statistical distance) to the uniform bit $\mathsf { U }$ , respectively, then $\mathsf { B } _ { 1 } \oplus \mathsf { B } _ { 2 }$ will be $2 \epsilon _ { 1 } \epsilon _ { 2 }$ -close to the uniform bit. The crucial property of the XOR construction is the following: if at least one of the bits $\mathsf { B } _ { 1 }$ or $\mathsf { B } _ { 2 }$ is perfectly uniform, then their XOR is perfectly uniform as well. This property is satisfied not only for single bits, but actually also for bitstrings (with bitwise XOR) and even for any quasigroup. Interestingly, it was shown in [MPR07] that an analogous indistinguishability amplification result to the XOR of two bits holds for constructions based on (stateful) random systems, and it is sufficient to assume only such a combiner property of a construction.

In this section, we prove that indistinguishability amplification is obtained from more general combiners. All of the above examples are special cases of such a combiner. In particular, Theorem 1 of [MPR07] is a simple corollary to our Theorem 3.

# 5.1 Constructions and Combiners

Usually (see for example [MPR07]), an $n$ -ary construction $\mathsf { C }$ is defined as a system communicating with component systems $\mathsf { S } _ { 1 } , \ldots , \mathsf { S } _ { n }$ and providing an outer communication interface. This means that ${ \mathsf { C } } ( { \mathsf { S } } _ { 1 } , \ldots , { \mathsf { S } } _ { n } )$ is a system for any (compatible) component systems $\mathsf { S } _ { 1 } , \ldots , \mathsf { S } _ { n }$ . In this paper, we use a more abstract notion of a construction, ignoring the details of the interfaces and messages. The amplification statements we make are independent of these details, and thereby simpler and stronger. Nevertheless, it may be easier for the reader to simply think of a construction $\mathsf { C }$ as a random system.

Definition 13. Let $S _ { 1 } , \ldots , S _ { n } , S _ { n + 1 }$ be sets of $( \mathcal { X } , \mathcal { Y } )$ -DDS such that for all $i \in [ n + 1 ]$ , the elements of $S _ { i }$ have the same domain. An $n$ -ary construction C is a probability distribution over functions from $S _ { 1 } \times \cdots \times S _ { n }$ to $S _ { n + 1 }$ such that for any probability distributions $\mathsf { S } _ { i }$ and ${ \mathsf { S } } _ { i } ^ { \prime }$ over $S _ { i }$ with $\mathsf { S } _ { i } \equiv \mathsf { S } _ { i } ^ { \prime }$ we have12

$$
{ \mathsf { C } } ( { \mathsf { S } } _ { 1 } , \ldots , { \mathsf { S } } _ { n } ) \equiv { \mathsf { C } } ( { \mathsf { S } } _ { 1 } ^ { \prime } , \ldots , { \mathsf { S } } _ { n } ^ { \prime } ) .
$$

In many settings (especially in cryptography), we have a pair of random systems $( \mathsf { F } , \mathsf { I } )$ , where $\mathsf { F }$ is the real system, and I is the ideal system. A combiner is a construction that combines component systems $\mathsf { S } _ { 1 } , \ldots , \mathsf { S } _ { n }$ such that only some of the component systems $\mathsf { S } _ { i }$ need to be ideal for the whole resulting system ${ \mathsf { C } } ( { \mathsf { S } } _ { 1 } , \ldots , { \mathsf { S } } _ { n } )$ to behave as if all component systems were ideal. The following definition makes this rigorous.

Definition 14. Let ${ \mathcal { A } } \subseteq \{ 0 , 1 \} ^ { n }$ be a monotone13 set. An $n$ -ary construction C is an $\boldsymbol { A }$ -combiner for $( \mathsf { F } _ { 1 } , \mathsf { I } _ { 1 } ) , \hdots , ( \mathsf { F } _ { n } , \mathsf { I } _ { n } )$ if for any choice of bits $b ^ { n } \in { \mathcal { A } }$ we have

$$
\mathsf { C } ( \langle \mathsf { F } _ { 1 } / \mathsf { I } _ { 1 } , \dots , \mathsf { F } _ { n } / \mathsf { I } _ { n } \rangle _ { b ^ { n } } ) \equiv \mathsf { C } ( \mathsf { I } _ { 1 } , \dots , \mathsf { I } _ { n } ) ,
$$

where $\langle x _ { 1 } / y _ { 1 } , \ldots , x _ { n } / y _ { n } \rangle _ { b ^ { n } } = ( z _ { 1 } , \ldots , z _ { n } )$ where $z _ { i } = x _ { i }$ if $b _ { i } = 0$ and $z _ { i } = y _ { i }$ otherwise.

A special case of an $\mathcal { A }$ -combiner is a threshold construction where the whole system behaves as if all component systems were ideal if only $k$ (arbitrary) component systems are ideal. We call such a construction a $( k , n )$ -combiner.

Definition 15. An $\mathcal { A }$ -combiner $\mathsf { C }$ is $a$ $( k , n )$ -combiner for $( \mathsf { F } _ { 1 } , \mathsf { I } _ { 1 } ) , \hdots , ( \mathsf { F } _ { n } , \mathsf { I } _ { n } )$ if $\{ b ^ { n } \mid b ^ { n } \in \{ 0 , 1 \} ^ { n } , \textstyle \sum _ { i } b _ { i } \geq k \} \subseteq { \cal A }$ .

For example, it is easy to see that for any two random functions14 $\mathsf { F } _ { 1 }$ and $\mathsf { F } _ { 2 }$ and the uniform $^ { 1 5 }$ random functions $\mathsf { R }$ and $\mathsf { R } ^ { \prime }$ on $n$ -bit strings, we have

$$
{ \sf F } _ { 1 } \oplus { \sf R } ^ { \prime } \equiv { \sf R } \oplus { \sf F } _ { 2 } \equiv { \sf R } \oplus { \sf R } ^ { \prime } \equiv { \sf R } ,
$$

where $\bigoplus$ is the binary construction that forwards every query $x _ { i }$ to both component systems and returns the bitwise XOR of both answers. Thus, $\bigoplus$ is a (deterministic) $( 1 , 2 )$ -combiner for $( \mathsf { F } _ { 1 } , \mathsf { R } )$ and $( \mathsf { F } _ { 2 } , \mathsf { R } ^ { \prime } )$ . Note that in [MPR07], a $( 1 , 2 )$ -combiner is called “neutralizing construction”.

# 5.2 Proving Indistinguishability Amplification Results

Due to the coupling theorem for random systems, we can think of the distinguishing advantage $\operatorname { A d v } ( \mathsf { F } _ { i } , \mathsf { l } _ { i } )$ as a failure probability of $\mathsf { F } _ { i }$ , i.e., the probability that $\mathsf { F } _ { i }$ is not equal to $\mathsf { I } _ { i }$ . Since an $\boldsymbol { A }$ -combiner behaves as if all component systems were ideal if the component systems described by any $a \in { \mathcal { A } }$ are ideal, one might (naively) hope that the failure probability of ${ \mathsf { C } } ( \mathsf { F } _ { 1 } , \ldots , \mathsf { F } _ { n } )$ was at most the probability that certain component systems fail, i.e.,

$$
\operatorname { A d v } ( \mathsf C ( \mathsf F _ { 1 } , \ldots , \mathsf F _ { n } ) , \mathsf C ( \mathsf I _ { 1 } , \ldots , \mathsf I _ { n } ) ) \overset { ? } { \leq } \operatorname* { P r } ( X \notin \mathcal A ) ,
$$

where $X = ( X _ { 1 } , \ldots , X _ { n } )$ for independent Bernoulli random variables $X _ { i }$ with $\operatorname* { P r } ( X _ { i } = 0 ) = \operatorname { A d v } ( \mathsf { F } _ { i } , \mathsf { l } _ { i } )$ . However, the reasoning behind this is unsound because it assumes the real system $\mathsf { F } _ { i }$ to behave ideally (as $\mathsf { I } _ { i }$ ) with probability $1 -$ $\operatorname { A d v } ( \mathsf { F } _ { i } , \mathsf { l } _ { i } )$ . This is too strong (and not true): when we condition on the event (with probability $1 - \operatorname { A d v } ( \mathsf { F } _ { i } , \mathsf { I } _ { i } ) )$ in which the real and ideal systems are equal, we also condition the ideal system, changing its original behavior.

Not only is the above reasoning unsound, the bound (2) simply does not hold, since it would for example imply that

$$
\delta ( \mathsf { B } _ { 1 } \oplus \cdots \oplus \mathsf { B } _ { n } , \mathsf { U } ) \overset { ? } { \leq } \prod _ { i = 1 } ^ { n } \delta ( \mathsf { B } _ { i } , \mathsf { U } )
$$

for independent bits $\mathsf { B } _ { i }$ and the uniform bit $\mathsf { U }$ . However, it is easy to verify that $\begin{array} { r } { \delta ( \mathsf { B } _ { 1 } \oplus \cdots \oplus \mathsf { B } _ { n } , \mathsf { U } ) = 2 ^ { n - 1 } \prod _ { i = 1 } ^ { n } \delta ( \mathsf { B } _ { i } , \mathsf { U } ) } \end{array}$ , i.e., there is an extra factor $2 ^ { n - 1 }$ .

The following technical lemma describes a general proof technique and can be used as a tool to prove indistinguishability amplification results for any $\boldsymbol { A }$ - combiner. The key idea is to consider distributions $\textsf { B }$ and $\mathsf { B } ^ { \prime }$ over ${ \mathcal { A } } \cup \{ 0 ^ { n } \}$ , inducing distributions $\mathsf { C } ( \langle \mathsf { F } _ { 1 } / \mathsf { I } _ { 1 } , \ldots , \mathsf { F } _ { n } / \mathsf { I } _ { n } \rangle _ { \mathsf { B } } )$ and $\mathsf { C } ( \langle \mathsf { F } _ { 1 } / \mathsf { I } _ { 1 } , \ldots , \mathsf { F } _ { n } / \mathsf { I } _ { n } \rangle _ { \mathsf { B } ^ { \prime } } ,$ ) (recall Definition 14 for the notation). We then use Theorem $1$ to exhibit a coupling in which systems $F _ { i }$ and $I _ { i }$ are equal with probability $1 - \operatorname { A d v } ( \mathsf { F } _ { i } , \mathsf { I } _ { i } )$ and argue that the two constructions are equal (in the coupling) unless for one of the indices $i \in [ n ]$ where $F _ { i } \neq I _ { i }$ we have $B _ { i } \neq B _ { i } ^ { \prime }$ . The proof of Theorem 3 shows how to instantiate this lemma, choosing suitable distributions $\textsf { B }$ and $\mathsf { B } ^ { \prime }$ .

Lemma 7. Let $\mathsf { C }$ be an $\mathcal { A }$ -combiner for $( \mathsf { F } _ { 1 } , \mathsf { I } _ { 1 } ) , \hdots , ( \mathsf { F } _ { n } , \mathsf { I } _ { n } )$ and let $\mathsf { B } , \mathsf { B ^ { \prime } }$ be any probability distributions over ${ \mathcal { A } } \cup \{ 0 ^ { n } \}$ such that $\mathsf { B } ( 0 ^ { n } ) > 0$ and $\mathsf { B } ^ { \prime } ( 0 ^ { n } ) = 0$ . Then,

$$
\begin{array} { r l } {  { \operatorname { A d v } ( \operatorname { C } ( \mathsf { F } _ { 1 } , \ldots , \mathsf { F } _ { n } ) , \operatorname { C } ( \mathsf { l } _ { 1 } , \ldots , \mathsf { l } _ { n } ) ) } \quad } & { } \\ & { \leq \mathsf { B } ( 0 ^ { n } ) ^ { - 1 } \cdot \displaystyle \sum _ { e \in \{ 0 , 1 \} ^ { n } } \delta ( \mathrm { b l i n d } ( \mathsf { B } , e ) , \mathrm { b l i n d } ( \mathsf { B } ^ { \prime } , e ) ) \cdot \operatorname* { P r } ( E = e ) , } \end{array}
$$

where $\mathrm { b l i n d } ( x , m )$ is the tuple derived from $x$ by removing all elements at the indices at which $m _ { i } = 0$ , and $E = ( E _ { 1 } , \dots , E _ { n } )$ for independent Bernoulli random variables $E _ { i }$ with $\operatorname* { P r } ( E _ { i } = 1 ) = \operatorname { A d v } ( \mathsf { F } _ { i } , \mathsf { I } _ { i } )$ .

Proof. By Lemma 9 (see Appendix A) we have for probability distribution $\mathsf { B } ^ { \prime \prime }$ over $\{ 0 , 1 \}$ with $\mathsf { B } ^ { \prime \prime } ( 0 ) = \mathsf { B } ( 0 ^ { n } )$

$$
\begin{array} { r l } & { \operatorname { A d v } ( \mathsf C ( \mathsf F _ { 1 } , \ldots , \mathsf F _ { n } ) , \mathsf C ( \mathsf 1 _ { 1 } , \ldots , \mathsf I _ { n } ) ) } \\ & { \quad = \mathsf B ( 0 ^ { n } ) ^ { - 1 } \cdot \operatorname { A d v } ( \langle \mathsf C ( \mathsf F _ { 1 } , \ldots , \mathsf F _ { n } ) / \mathsf C ( \mathsf I _ { 1 } , \ldots , \mathsf I _ { n } ) \rangle _ { \mathsf B ^ { \prime \prime } } , \mathsf C ( \mathsf I _ { 1 } , \ldots , \mathsf I _ { n } ) ) . } \end{array}
$$

Observe that we have $\langle { \mathsf C } ( \mathsf { F } _ { 1 } , \ldots , \mathsf { F } _ { n } ) / { \mathsf C } ( \mathsf { I } _ { 1 } , \ldots , \mathsf { I } _ { n } ) \rangle _ { \mathsf B ^ { \prime \prime } } \equiv { \mathsf C } ( \langle \mathsf { F } _ { 1 } / \mathsf { I } _ { 1 } , \ldots , \mathsf { F } _ { n } / \mathsf { I } _ { n } \rangle _ { \mathsf B } )$ and $\mathsf { C } ( \mathsf { I } _ { 1 } , \ldots , \mathsf { I } _ { n } ) \equiv \mathsf { C } ( \langle \mathsf { F } _ { 1 } / \mathsf { I } _ { 1 } , \ldots , \mathsf { F } _ { n } / \mathsf { I } _ { n } \rangle _ { \mathsf { B } ^ { \prime } } )$ , since $\mathsf { C }$ is an $\mathcal { A }$ -combiner. Thus,

$$
\begin{array} { r l } & { \mathrm { A d v } \big ( \langle \mathsf { C } ( \mathsf { F } _ { 1 } , \ldots , \mathsf { F } _ { n } ) / \mathsf { C } ( \mathsf { I } _ { 1 } , \ldots , \mathsf { I } _ { n } ) \rangle _ { \mathsf { B } ^ { \prime \prime } } , \mathsf { C } ( \mathsf { I } _ { 1 } , \ldots , \mathsf { I } _ { n } ) \big ) } \\ & { \quad = \mathrm { A d v } \big ( \mathsf { C } ( \langle \mathsf { F } _ { 1 } / \mathsf { I } _ { 1 } , \ldots , \mathsf { F } _ { n } / \mathsf { I } _ { n } \rangle _ { \mathsf { B } } ) , \mathsf { C } ( \langle \mathsf { F } _ { 1 } / \mathsf { I } _ { 1 } , \ldots , \mathsf { F } _ { n } / \mathsf { I } _ { n } \rangle _ { \mathsf { B } ^ { \prime } } ) \big ) . } \end{array}
$$

According to Theorem 1 there exist $( \mathsf { F } _ { i } ^ { \prime } , \mathsf { I } _ { i } ^ { \prime } ) \in [ \mathsf { F } _ { i } ] \times [ \mathsf { I } _ { i } ]$ for every $i \in [ n ]$ such that $\delta ( \mathsf { F } _ { i } ^ { \prime } , \mathsf { I } _ { i } ^ { \prime } ) = \mathrm { A d v } ( \mathsf { F } _ { i } , \mathsf { I } _ { i } )$ . Thus,

$$
\begin{array} { r l } & { \mathrm { A d v } \big ( \mathsf { C } ( \langle \mathsf { F } _ { 1 } / \mathsf { I } _ { 1 } , \dots , \mathsf { F } _ { n } / \mathsf { I } _ { n } \rangle _ { \mathsf { B } } ) , \mathsf { C } \big ( \langle \mathsf { F } _ { 1 } / \mathsf { I } _ { 1 } , \dots , \mathsf { F } _ { n } / \mathsf { I } _ { n } \rangle _ { \mathsf { B } ^ { \prime } } \big ) \big ) } \\ & { \quad = \mathrm { A d v } \big ( \mathsf { C } ( \langle \mathsf { F } _ { 1 } ^ { \prime } / \mathsf { I } _ { 1 } ^ { \prime } , \dots , \mathsf { F } _ { n } ^ { \prime } / \mathsf { I } _ { n } ^ { \prime } \rangle _ { \mathsf { B } } ) , \mathsf { C } \big ( \langle \mathsf { F } _ { 1 } ^ { \prime } / \mathsf { I } _ { 1 } ^ { \prime } , \dots , \mathsf { F } _ { n } ^ { \prime } / \mathsf { I } _ { n } ^ { \prime } \rangle _ { \mathsf { B } ^ { \prime } } \big ) \big ) } \\ & { \quad \le \delta \big ( \mathsf { C } ( \langle \mathsf { F } _ { 1 } ^ { \prime } / \mathsf { I } _ { 1 } ^ { \prime } , \dots , \mathsf { F } _ { n } ^ { \prime } / \mathsf { I } _ { n } ^ { \prime } \rangle _ { \mathsf { B } } ) , \mathsf { C } \big ( \langle \mathsf { F } _ { 1 } ^ { \prime } / \mathsf { I } _ { 1 } ^ { \prime } , \dots , \mathsf { F } _ { n } ^ { \prime } / \mathsf { I } _ { n } ^ { \prime } \rangle _ { \mathsf { B } ^ { \prime } } \big ) \big ) } \\ &  \quad \le \delta \big ( \langle \mathsf { F } _ { 1 } ^ { \prime } / \mathsf { I } _ { 1 } ^ { \prime } , \dots , \mathsf { F } _ { n } ^ { \prime } / \mathsf { I } _ { n } ^ { \prime } \rangle _ { \mathsf { B } } , \langle \mathsf { F } _ { 1 } ^ { \prime } / \mathsf { I } _ { 1 } ^ { \prime } , \dots , \mathsf { F } _ { n }  \end{array}
$$

where the last step is due to Lemma 3.

We exhibit a random experiment $\varepsilon$ with random variables $^ { 1 6 }$ $F _ { i } ^ { \prime } \sim \mathsf { F } _ { i } ^ { \prime } , I _ { i } ^ { \prime } \sim \mathsf { I } _ { i } ^ { \prime }$ $B \sim \mathsf { B }$ , and $B ^ { \prime } \sim \mathsf { B } ^ { \prime }$ , such that $L : = \langle F _ { 1 } ^ { \prime } / I _ { 1 } ^ { \prime } , \dots , F _ { n } ^ { \prime } / I _ { n } ^ { \prime } \rangle _ { B } \sim \langle \mathsf { F } _ { 1 } ^ { \prime } / \mathsf { I } _ { 1 } ^ { \prime } , \dots , \mathsf { F } _ { n } ^ { \prime } / \mathsf { I } _ { n } ^ { \prime } \rangle _ { \mathsf { I } }$ B and R : $= \langle F _ { 1 } ^ { \prime } / I _ { 1 } ^ { \prime } , \ldots , F _ { n } ^ { \prime } / I _ { n } ^ { \prime } \rangle _ { B ^ { \prime } } \sim \langle \mathsf { F } _ { 1 } ^ { \prime } / 1 _ { 1 } ^ { \prime } , \ldots , \mathsf { F } _ { n } ^ { \prime } / \mathsf { I } _ { n } ^ { \prime } \rangle _ { \mathsf { B } }$ 0 . Define $E _ { i } : = [ F _ { i } ^ { \prime } \neq I _ { i } ^ { \prime } ]$ and $E : = ( E _ { 1 } , \ldots , E _ { n } )$ .

Observe that the joint distribution of $F _ { i } ^ { \prime }$ and $I _ { i } ^ { \prime }$ as well as $B$ and $B ^ { \prime }$ can be chosen arbitrary (as long as the marginal distributions are respected). Let $\mathcal { C } _ { \delta } ( \cdot , \cdot )$ denote the joint distribution described in Lemma 4, and let the joint distribution of $F _ { i } ^ { \prime }$ and $I _ { i } ^ { \prime }$ be $\mathcal { C } _ { \delta } ( \mathsf { F } _ { i } ^ { \prime } , \mathsf { I } _ { i } ^ { \prime } )$ . Moreover, the joint distribution of $B$ and $B ^ { \prime }$ is chosen such that17

$$
\begin{array} { r l } & { \mathrm { P r } ^ { \mathcal { E } } ( \mathrm { b l i n d } ( B , e ) = b , \mathrm { b l i n d } ( B ^ { \prime } , e ) = b ^ { \prime } , E = e ) } \\ & { \quad = \mathcal { C } _ { \delta } ( \mathrm { b l i n d } ( \mathsf { B } , e ) , \mathrm { b l i n d } ( \mathsf { B } ^ { \prime } , e ) ) ( b , b ^ { \prime } ) \cdot \mathrm { P r } ^ { \mathcal { E } } ( E = e ) . } \end{array}
$$

Thus we have by Lemma 4

$$
\begin{array} { r l } { \displaystyle \delta ( \langle \mathsf { F } _ { 1 } ^ { \prime } / 1 _ { 1 } ^ { \prime } , \dots , \mathsf { F } _ { n } ^ { \prime } / 1 _ { n } ^ { \prime } \rangle _ { \mathsf { B } ^ { \prime } } \langle \mathsf { F } _ { 1 } ^ { \prime } / 1 _ { 1 } ^ { \prime } , \dots , \mathsf { F } _ { n } ^ { \prime } / 1 _ { n } ^ { \prime } \rangle _ { \mathsf { B } ^ { \prime } } ) } & { } \\ & { \qquad \leq \operatorname* { P r } ^ { \delta } ( L \neq R ) } \\ & { = \displaystyle \sum _ { e \in \{ 0 , 1 \} ^ { n } } \operatorname* { P r } ^ { \varepsilon } ( L \neq R , E = e ) } \\ & { = \displaystyle \sum _ { e \in \{ 0 , 1 \} ^ { n } } \operatorname* { P r } ^ { \varepsilon } ( \mathrm { b l i n d } ( B , e ) \neq \mathrm { b l i n d } ( B ^ { \prime } , e ) , E = e ) } \\ & { = \displaystyle \sum _ { e \in \{ 0 , 1 \} ^ { n } } \delta ( \mathrm { b l i n d } ( \mathsf { B } , e ) , \mathrm { b l i n d } ( \mathsf { B } ^ { \prime } , e ) ) \cdot \mathrm { P r } ^ { \varepsilon } ( E = e ) , } \end{array}
$$

which concludes the proof.

Observe that Lemma 7 by itself does not imply indistinguishability amplification for any combiner. In particular, one needs to prove the existence of suitable distributions $\textsf { B }$ and $\mathsf { B } ^ { \prime }$ such that the distance $\delta ( \mathrm { b l i n d } ( \mathsf { B } , e ) , \mathrm { b l i n d } ( \mathsf { B } ^ { \prime } , e ) )$ is small for many $e \in \{ 0 , 1 \} ^ { n }$ (ideally it is zero for all $\overline { { e } } \notin \mathcal { A }$ , where $\overline { { e } }$ is the bitwise complement of $e$ ). We show the following indistinguishability amplification theorem for all $( k , n )$ -combiners.

Theorem 3. If $\mathsf { C }$ is a $( k , n )$ -combiner for $( \mathsf { F } _ { 1 } , \mathsf { I } _ { 1 } ) , \hdots , ( \mathsf { F } _ { n } , \mathsf { I } _ { n } )$ , then

$$
\operatorname { A d v } ( C ( \mathsf { F } _ { 1 } , \ldots , \mathsf { F } _ { n } ) , C ( \mathsf { I } _ { 1 } , \ldots , \mathsf { I } _ { n } ) ) \leq \sum _ { i = n - k + 1 } ^ { n } \xi _ { i - ( n - k ) , i } \cdot \operatorname* { P r } \left( \sum _ { j \in [ n ] } E _ { j } = n - k + 1 \right) ,
$$

where

$$
\xi _ { l , m } : = \frac { 1 } { 2 } \cdot \bigg ( 1 + \sum _ { j = l } ^ { m } { \binom { m } { j } } \cdot { \binom { j - 1 } { l - 1 } } \bigg ) ,
$$

and the $E _ { i }$ are jointly independent Bernoulli random variables with $\operatorname* { P r } ( E _ { i } = 1 ) =$ $\operatorname { A d v } ( \mathsf { F } _ { i } , \mathsf { l } _ { i } )$ .

As discussed before, one might (naively) hope for threshold combiners to achieve the indistinguishability bound

$$
\operatorname { A d v } ( C ( \mathsf { F } _ { 1 } , \ldots , \mathsf { F } _ { n } ) , C ( \mathsf { I } _ { 1 } , \ldots , \mathsf { I } _ { n } ) ) \overset { ? } { \leq } \operatorname* { P r } \left( \sum _ { j \in [ n ] } E _ { j } \geq n - k + 1 \right) .
$$

This bound does not hold and thus correction factors as in Theorem 3 (i.e., the factors $\xi _ { i - ( n - k ) , i } )$ are in general unavoidable. As we have $\xi _ { 1 , 2 } = 2$ , Theorem 1 of [MPR07] is an immediate corollary of Theorem 3 (for $k = 1$ and $n = 2$ ). More generally we have $\xi _ { 1 , n } = 2 ^ { n - 1 }$ , which is tight due to the above discussed example.

Proof (of Theorem 3). For $k \geq 1$ and $n \geq k$ we represent distributions $\mathsf { B } _ { k , n } , \mathsf { B } _ { k , n } ^ { \prime }$ using multisets $A _ { k , n } , A _ { k , n } ^ { \prime }$ over ${ \mathcal { A } } \cup \{ 0 ^ { n } \}$ , with the natural understanding that $\mathsf { B } _ { k , n }$ ( $\mathbf { \Delta } _ { . } ^ { \mathsf { B ^ { \prime } } } \mathbf { \Delta } _ { k , n } ,$ ) is the probability distribution with $\mathsf { B } _ { k , n } ( a ) = A _ { k , n } ( a ) / | A _ { k , n } |$ . Let

$$
\begin{array} { r l } & { A _ { k , n } ^ { \prime } : = \underset { j \in \{ k , k + 2 , \ldots , n \} } { \bigcup } \Biggl \{ \left( b , \binom { j - 1 } { k - 1 } \right) \ \Biggl | \ b \in \{ 0 , 1 \} ^ { n } , \underset { i \in [ n ] } { \sum } b _ { i } = j \Biggr \} \quad \mathrm { a n d } } \\ & { A _ { k , n } : = \{ ( 0 ^ { n } , 1 ) \} \cup \underset { j \in \{ k + 1 , k + 3 , \ldots , n \} } { \bigcup } \Biggl \{ \left( b , \binom { j - 1 } { k - 1 } \right) \ \Biggl | \ b \in \{ 0 , 1 \} ^ { n } , \underset { i \in [ n ] } { \sum } b _ { i } = j \Biggr \} . } \end{array}
$$

For a multiset $M$ over $\{ 0 , 1 \} ^ { n }$ , let $\mathrm { b l i n d } _ { m } ( M )$ be the multiset over $\{ 0 , 1 \} ^ { n - m }$ derived from $M$ by removing the bits at $m$ fixed positions, say the first $m$ bits, for every element. We only consider multisets for which $\mathrm { b l i n d } _ { m } ( M )$ is well-defined, i.e., it does not matter at which $m$ positions the bits are removed. We prove below the following statement:

$$
\begin{array} { r l } { \forall k \geq 1 , \forall n \geq k : } & { | A _ { k , n } | = | A _ { k , n } ^ { \prime } | = \xi _ { k , n } } \\ & { \wedge \forall j \geq k : \mathrm { b l i n d } _ { j } ( A _ { k , n } ) = \mathrm { b l i n d } _ { j } ( A _ { k , n } ^ { \prime } ) } \\ & { \wedge \forall j < k : | \mathrm { b l i n d } _ { j } ( A _ { k , n } ) \triangle \mathrm { b l i n d } _ { j } ( A _ { k , n } ^ { \prime } ) | = 2 \xi _ { k - j , n - j } . } \end{array}
$$

This implies the claim via Lemma 7, since we have

$$
\begin{array} { r l } & { \mathrm { A d v } ( \mathsf { C } ( \mathsf { F } _ { 1 } , \ldots , \mathsf { F } _ { n } ) , \mathsf { C } ( \mathsf { I } _ { 1 } , \ldots , \mathsf { I } _ { n } ) ) } \\ & { \qquad \le \mathsf { B } _ { k , n } ( 0 ^ { n } ) ^ { - 1 } \cdot \displaystyle \sum _ { \epsilon \in \{ 0 , 1 \} ^ { n } } \delta ( \mathrm { b l i n d } ( \mathsf { B } _ { k , n } , e ) , \mathrm { b l i n d } ( \mathsf { B } _ { k , n } ^ { \prime } , e ) ) \cdot \mathsf { P r } ( E = e ) } \\ & { \qquad = | A _ { k , n } | \cdot \displaystyle \sum _ { i = 0 } ^ { n } \frac { | \mathrm { b l i n d } _ { n - i } ( A _ { k , n } ) \triangle \mathrm { b l i n d } _ { n - i } ( A _ { k , n } ^ { \prime } ) | } { 2 | A _ { k , n } | } \cdot \operatorname* { P r } \biggl ( \displaystyle \sum _ { j \in [ n ] } E _ { j } = i \biggr ) } \\ & { \qquad = \displaystyle \sum _ { i = n - k + 1 } ^ { n } \xi _ { i - ( n - k ) , i } \cdot \operatorname* { P r } \biggl ( \displaystyle \sum _ { j \in [ n ] } E _ { j } = i \biggr ) . } \end{array}
$$

In the second step we have used that for any two multisets $M , M ^ { \prime }$ representing probability distributions $\mathsf { M } , \mathsf { M } ^ { \prime }$ we have $\delta ( { \mathsf { M } } , { \mathsf { M } } ^ { \prime } ) = | M \triangle { M ^ { \prime } } | / ( 2 | M | )$ if $| M | =$ $\vert M ^ { \prime } \vert$ .

We prove (3) by induction over $n$ . Observe that

$$
\begin{array} { r l } & { \mathrm { b l i n d _ { 1 } } ( A _ { k , n } ^ { \prime } ) = \underset { j \in \{ k , k + 2 , \ldots , n - 1 \} } { \bigcup } \Bigg \{ \Bigg ( b , \binom { j - 1 } { k - 1 } \Bigg ) ~ \Bigg | ~ b \in \{ 0 , 1 \} ^ { n - 1 } , \underset { i \in [ n ] } { \sum } b _ { i } = j \Bigg \} } \\ & { \quad \cup \underset { j \in \{ k - 1 , k + 1 , \ldots , n - 1 \} } { \bigcup } \Bigg \{ \Bigg ( b , \binom { j } { k - 1 } \Bigg ) ~ \Bigg | ~ b \in \{ 0 , 1 \} ^ { n - 1 } , \underset { i \in [ n ] } { \sum } b _ { i } = j \Bigg \} . } \end{array}
$$

Similarly, we see that

$$
\begin{array} { r l } & { \mathrm { b l i n d _ { 1 } } ( A _ { k , n } ) = \{ ( 0 ^ { n - 1 } , 1 ) \} } \\ & { \quad \cup _ { \quad \quad \bigcup _ { j \in \{ k + 1 , k + 3 , \dots , n - 1 \} } } \Bigg \{ \Bigg ( b , \binom { j - 1 } { k - 1 } \Bigg ) ~ \Bigg | ~ b \in \{ 0 , 1 \} ^ { n - 1 } , \underset { i \in [ n ] } { \sum _ { i \in [ n ] } } b _ { i } = j \Bigg \} } \\ & { \quad \cup _ { \quad \quad j \in \{ k , k + 2 , \dots , n - 1 \} } \Bigg \{ \Bigg ( b , \binom { j } { k - 1 } \Bigg ) ~ \Bigg | ~ b \in \{ 0 , 1 \} ^ { n - 1 } , \underset { i \in [ n ] } { \sum _ { i \in [ n ] } } b _ { i } = j \Bigg \} . } \end{array}
$$

If $k = 1$ , it is easy to see that $| A _ { k , n } | = | A _ { k , n } ^ { \prime } | = \xi _ { k , n }$ , as well as $\mathrm { b l i n d } _ { 1 } ( A _ { k , n } ^ { \prime } ) =$ $\mathrm { b l i n d } _ { 1 } ( A _ { k , n } )$ and $| \mathrm { b l i n d } _ { 0 } ( A _ { k , n } ) \triangle \mathrm { b l i n d } _ { 0 } ( A _ { k , n } ^ { \prime } ) | = 2 \xi _ { k , n }$ (since $A _ { k , n }$ and $A _ { k , n } ^ { \prime }$ are disjoint). Otherwise ( $k \geq 2$ ), we use the identity $\textstyle { \binom { j } { k - 1 } } - { \binom { j - 1 } { k - 1 } } = { \binom { j - 1 } { k - 2 } }$ to obtain

$$
{ \begin{array} { r l } & { { \mathrm { b l i n d } } _ { 1 } ( A _ { k , n } ^ { \prime } ) - { \mathrm { b l i n d } } _ { 1 } ( A _ { k , n } ) \cap { \mathrm { b l i n d } } _ { 1 } ( A _ { k , n } ^ { \prime } ) } \\ & { \quad = \underset { j \in \{ k - 1 , k + 1 , \ldots , n - 1 \} } { \bigcup } \left\{ \left. \left( b , { \binom { j } { k - 2 } } \right) \ \right| b \in \{ 0 , 1 \} ^ { n - 1 } , \sum _ { i \in [ n ] } b _ { i } = j \right\} } \\ & { \quad = A _ { k - 1 , n - 1 } ^ { \prime } . } \end{array} }
$$

Analogously, we see that

$$
\begin{array} { r l } & { \mathrm { b l i n d } _ { 1 } ( A _ { k , n } ) - \mathrm { b l i n d } _ { 1 } ( A _ { k , n } ) \cap \mathrm { b l i n d } _ { 1 } ( A _ { k , n } ^ { \prime } ) } \\ & { \quad = \{ ( \boldsymbol { 0 } ^ { n - 1 } , 1 ) \} \cup \underset { j \in \{ k , k + 2 , \ldots , n - 1 \} } { \bigcup } \Bigg \{ \Bigg ( b , \binom { j - 1 } { k - 2 } \Bigg ) \Bigg | \ b \in \{ 0 , 1 \} ^ { n - 1 } , \sum _ { i \in [ n ] } b _ { i } = j \Bigg \} } \\ & { \quad = A _ { k - 1 , n - 1 } . } \end{array}
$$

As by induction hypothesis $\mathrm { b l i n d } _ { k - 1 } ( A _ { k - 1 , n - 1 } ) = \mathrm { b l i n d } _ { k - 1 } ( A _ { k - 1 , n - 1 } ^ { \prime } )$ , we have ${ \mathrm { b l i n d } } _ { k } ( A _ { k , n } ) = { \mathrm { b l i n d } } _ { k } ( A _ { k , n } ^ { \prime } )$ . Since blinding does not change the cardinality of a multiset, it follows $| A _ { k , n } | = | A _ { k , n } ^ { \prime } | = \xi _ { k , n }$ . Moreover, as $A _ { k , n }$ and $A _ { k , n } ^ { \prime }$ are disjoint we have $\vert \mathrm { b l i n d } _ { 0 } ( A _ { k , n } ) \triangle \mathrm { b l i n d } _ { 0 } ( A _ { k , n } ^ { \prime } ) \vert = 2 \xi _ { k , n }$ . Finally, for $j \geq 1$ and $j < k$ we have

$$
\begin{array} { r l } & { | \mathrm { b l i n d } _ { j } ( A _ { k , n } ) \bigtriangleup \mathrm { b l i n d } _ { j } ( A _ { k , n } ^ { \prime } ) | = | \mathrm { b l i n d } _ { j - 1 } \big ( A _ { k - 1 , n - 1 } \big ) \bigtriangleup \mathrm { b l i n d } _ { j - 1 } \big ( A _ { k - 1 , n - 1 } ^ { \prime } \big ) | } \\ & { \qquad \stackrel { \mathrm { ( I . H . ) } } { = } 2 \xi _ { ( k - 1 ) - ( j - 1 ) , ( n - 1 ) - ( j - 1 ) } = 2 \xi _ { k - j , n - j } , } \end{array}
$$

which concludes the proof.

The following corollary to Theorem 3 provides simpler (but worse) bounds.

Corollary 1. If $\mathsf { C }$ is a $( k , n )$ -combiner for $( \mathsf { F } _ { 1 } , \mathsf { I } _ { 1 } ) , \hdots , ( \mathsf { F } _ { n } , \mathsf { I } _ { n } )$ , then

$$
\begin{array} { r l r } {  { \mathrm { A d v } ( \mathsf C ( \mathsf F _ { 1 } , \ldots , \mathsf F _ { n } ) , \mathsf C ( \mathsf I _ { 1 } , \ldots , \mathsf I _ { n } ) ) \le } } \\ & { } & { 2 ^ { n - k } \displaystyle \sum _ { j = n - k + 1 } ^ { n } { \binom { j - 1 } { n - k } } \cdot \operatorname* { P r } ( \sum _ { i \in [ n ] } E _ { i } = j ) , } \end{array}
$$

where the $E _ { i }$ are jointly independent Bernoulli random variables with $\operatorname* { P r } ( E _ { i } = 1 ) = \operatorname { A d v } ( \mathsf { F } _ { i } , \mathsf { I } _ { i } )$ .

(ii) if $\mathrm { A d v } ( \mathsf { F } _ { i } , \mathsf { I } _ { i } ) \leq \epsilon$ for all $i \in [ n ]$ we have

$$
\operatorname { A d v } ( \mathsf C ( \mathsf F _ { 1 } , \ldots , \mathsf F _ { n } ) , \mathsf C ( \mathsf I _ { 1 } , \ldots , \mathsf I _ { n } ) ) \le \frac { 1 } { 2 } \binom { n } { k - 1 } \cdot ( 2 \epsilon ) ^ { n - k + 1 } .
$$

(iii) if $\mathrm { A d v } ( \mathsf { F } _ { i } , \mathsf { I } _ { i } ) \leq \epsilon$ for all $i \in [ n ]$ we have

$$
\operatorname { A d v } ( \mathsf C ( \mathsf F _ { 1 } , \dots , \mathsf F _ { n } ) , \mathsf C ( \mathsf { I } _ { 1 } , \dots , \mathsf I _ { n } ) ) \le \left( 2 e \frac { n } { n - k + 1 } \cdot \epsilon \right) ^ { n - k + 1 } .
$$

Proof. Lemma 10 in Appendix A states that $\xi _ { l , m } \leq 2 ^ { m - l } { \binom { m - 1 } { l - 1 } }$ . This immediately implies the bound $( i )$ via Theorem 3.

We use bound $( i )$ to obtain the bound (ii) as follows

$$
\begin{array} { r l } { \displaystyle \mathrm { A d v } \big ( \mathsf { C } ( \mathsf { F } _ { 1 } , \ldots , \mathsf { F } _ { n } ) , \mathsf { C } ( \mathsf { I } _ { 1 } , \ldots , \mathsf { J } _ { n } ) \big ) \leq 2 ^ { n - k } } & { \displaystyle \sum _ { j = n - k + 1 } ^ { n } \bigg ( \frac { j - 1 } { n - k } \bigg ) \cdot \mathrm { P r } \bigg ( \sum _ { i \in [ n ] } E _ { i } = j \bigg ) } \\ & { \leq 2 ^ { n - k } \displaystyle \sum _ { j = n - k + 1 } ^ { n } \bigg ( \frac { j - 1 } { n - k } \bigg ) \cdot \bigg ( \frac { n } { j } \bigg ) e ^ { j } ( 1 - \epsilon ) ^ { n - j } } \\ & { \leq 2 ^ { n - k } \displaystyle \sum _ { j = n - k + 1 } ^ { n } \bigg ( \frac { j } { n - k + 1 } \bigg ) \cdot \bigg ( \frac { n } { j } \bigg ) e ^ { j } ( 1 - \epsilon ) ^ { n - j } } \\ & { = 2 ^ { n - k } \bigg ( \displaystyle \sum _ { n = - k + 1 } ^ { n } \bigg ) \epsilon ^ { n - k + 1 } } \\ & { = \displaystyle \frac { 1 } { 2 } \bigg ( \frac { n } { n - k } \bigg ) \cdot ( 2 \epsilon ) ^ { n - k + 1 } . } \end{array}
$$

The first equality is due to the identity $\begin{array} { r } { \sum _ { j = m } ^ { n } \binom { \jmath } { m } \binom { n } { j } \epsilon ^ { j } ( 1 - \epsilon ) ^ { n - j } = \binom { n } { m } \epsilon ^ { m } } \end{array}$ . An easy proof of the identity is by considering $n$ independent Bernoulli random variables $X _ { i }$ with $\mathrm { P r } ( X _ { i } = 1 ) ~ = ~ \epsilon$ and their sum $X : = X _ { 1 } + \cdot \cdot \cdot + X _ { n }$ . The left-hand expression of the identity is simply the expected value

$$
\mathbb { E } \bigg [ \binom { X } { m } \bigg ] = \mathbb { E } \left[ \sum _ { \stackrel { I \subseteq [ n ] } { | I | = m } } \bigg [ \bigwedge _ { i \in I } ( X _ { i } = 1 ) \bigg ] \right] = \sum _ { \stackrel { I \subseteq [ n ] } { | I | = m } } \operatorname* { P r } _ { \stackrel { \left( \bigwedge _ { i \in I } ( X _ { i } = 1 ) \right) } { | I \in I } } = \binom { n } { m } \epsilon ^ { m } .
$$

Finally, bound (iii) is derived from bound (ii) via the well-known inequality $\textstyle { \binom { n } { k } } \leq ( 2 e n / k ) ^ { k }$ . ut

The bound

$$
\operatorname { A d v } ( \mathsf C ( \mathsf F _ { 1 } , \dots , \mathsf F _ { n } ) , \mathsf C ( \mathsf { I } _ { 1 } , \dots , \mathsf I _ { n } ) ) \le \left( 2 e \frac { n } { n - k + 1 } \cdot \epsilon \right) ^ { n - k + 1 }
$$

from Corollary 1 (iii) is perhaps suited best (even though it is the loosest) in order to intuitively understand the behavior of the obtained indistinguishability amplification.

On the Number of Queries. Many indistinguishability bounds are presented with a dependency on the number of queries $q$ the adversary is allowed to ask. For reasons of simplicity, we understand the number of queries as a property of a discrete system, i.e., the number of queries that a system answers. This is only a conceptual difference, and all of our results can still be used with the former perspective. For example, this means that if the indistinguishability of the component systems is for distinguishers asking up to $q$ queries, our results can be applied to the corresponding systems that answer only $q$ queries. Usually, if the component systems $\mathsf { F } _ { 1 } , \ldots , \mathsf { F } _ { n }$ answer only $q$ queries, then the overall constructed system ${ \mathsf { C } } ( \mathsf { F } _ { 1 } , \ldots , \mathsf { F } _ { n } )$ will answer only up to $q ^ { \prime }$ queries, for some $q ^ { \prime }$ depending on $q$ . As a consequence, the resulting indistinguishability bound $\operatorname { A d v } ( \mathsf { C } ( \mathsf { F } _ { 1 } , \ldots , \mathsf { F } _ { n } ) , \mathsf { C } ( \mathsf { I } _ { 1 } , \ldots , \mathsf { I } _ { n } ) )$ holds for any distinguisher asking up to $q ^ { \prime }$ queries.

# 5.3 A Simple $( k , n )$ -Combiner for Random Functions

We present a simple $( k , n )$ -combiner for arbitrary $k$ and $n \geq k$ . For a finite field $\mathbb { F }$ , let $A \in \mathbb { F } ^ { k \times n }$ be a $( k \times n )$ -matrix with $k \leq n$ , and let ${ \mathcal { A } } \subseteq \{ 0 , 1 \} ^ { n }$ be the (monotone) set containing all $v \in \{ 0 , 1 \} ^ { n }$ with $v _ { i _ { 1 } } = \cdot \cdot \cdot = v _ { i _ { k } } = 1$ for $k$ distinct indices, such that the columns $i _ { 1 } , \dots , i _ { k }$ of $A$ are linearly independent. Consider the deterministic $n$ -ary construction $\mathsf { C } : \mathbb { F } ^ { n } \to \mathbb { F } ^ { k }$ defined by18

$$
\mathsf { C } ( x _ { 1 } , \hdots , x _ { n } ) : = A \cdot ( x _ { 1 } , \hdots , x _ { n } ) ^ { \mathsf { T } } .
$$

It is easy to see that $\mathsf { C }$ is an $\boldsymbol { A }$ -combiner for $( { \mathsf { X } } _ { 1 } , { \mathsf { U } } ) , \ldots , ( { \mathsf { X } } _ { n } , { \mathsf { U } } )$ , where $\mathsf { X } _ { i }$ are arbitrary probability distributions over $\mathbb { F }$ and $\mathsf { U }$ is the uniform distribution over $\mathbb { F }$ . Moreover, if $A$ is an MDS matrix19, it is straightforward to verify using basic linear algebra that $\mathsf { C }$ is a $( k , n )$ -combiner. Assuming the field $\mathbb { F }$ has sufficiently many elements ( $| \mathbb { F } | \geq k + n )$ such a matrix is easy to construct (for example, one can take a Vandermonde matrix or a Cauchy matrix [MS77]).

The above construction can be generalized to a $( k , n )$ -combiner $C ^ { \prime }$ which combines $n$ independent random functions $\mathsf { F } _ { 1 } , \ldots , \mathsf { F } _ { n }$ (from $\mathcal { X }$ to $\mathbb { F }$ ) to $k$ random functions $\mathsf { F } _ { 1 } ^ { \prime } , \ldots , \mathsf { F } _ { k } ^ { \prime }$ as depicted in Figure 2. By the argument above, $C ^ { \prime }$ is a $( k , n )$ - combiner for $( \mathsf { F } _ { 1 } , \mathsf { R } ) , \ldots , ( \mathsf { F } _ { n } , \mathsf { R } )$ , where the $\mathsf { F } _ { i }$ are arbitrary random functions and $\mathsf { R }$ is a uniform random function (assuming $A$ is an MDS matrix).

Assuming $\mathrm { A d v } ( \mathsf { F } _ { i } , \mathsf { R } ) \leq \epsilon$ , Corollary 1 implies that

$$
\operatorname { A d v } ( ( \mathsf { F } _ { 1 } ^ { \prime } , \ldots , \mathsf { F } _ { k } ^ { \prime } ) , \mathsf { R } ^ { k } ) \leq \frac { 1 } { 2 } \binom { n } { k - 1 } ( 2 \epsilon ) ^ { n - k + 1 } ,
$$

where $\mathsf { R } ^ { k }$ are $k$ independent parallel uniform random functions.

![](images/2a30fe8329b49fb86bcabcb4f75333db60bd10c30074ca640b21b8fb0f144bc2.jpg)  
Fig. 2. Construction ${ \mathsf { C } } ^ { \prime }$ transforms the $_ { n }$ random functions $\mathsf { F } _ { 1 } , \ldots , \mathsf { F } _ { n }$ to $k$ random functions, where $k$ is the number of rows of the matrix $A$ . For an input $x \in \mathbb { F }$ to the $_ i$ -th constructed function $\mathsf { F } _ { i } ^ { \prime }$ , the output is the dot product $\textstyle \sum _ { j = 1 } ^ { n } A _ { i j } \cdot y _ { j }$ , where $y _ { i } = \mathsf F _ { i } ( x )$

# 5.4 Combining Systems Forming a Quasi-Group

We consider the setting of combining random systems forming a quasigroup $^ { 2 0 }$ with some construction $\odot$ . Examples of such systems include one- or both-sided stateless random permutations with the cascade $\circ$ , or (possibly stateful) random functions with the elementwise XOR $\bigoplus$ . Given $n$ independent such systems, the goal is to obtain $m < n$ systems that are (jointly) close to $m$ independent uniform systems. The known results from [MPR07] lead to the following straightforward construction: we partition the $n$ systems into $m$ sets of size $n / m$ , and then use the $( 1 , n / m )$ -combiner $\odot$ to combine each set into one system (see Example 1). Assuming that each component system is $\epsilon$ -close to uniform, this will yield an indistinguishability bound of21

$$
\frac { m } { 2 } ( 2 \epsilon ) ^ { n / m } .
$$

In the following, we show that by sharing a few systems among the $m$ combined sets, much stronger indistinguishability amplification is obtained, roughly squaring the above bound. As a result, only about half as many systems need to be combined in order to obtain the same indistinguishability as with the straightforward construction.

Lemma 8. Assume a set of deterministic discrete systems $\mathcal { Q }$ forming a quasigroup with the construction $\odot$ . Let ${ \mathsf { Q } } _ { 1 } , \ldots , { \mathsf { Q } } _ { n }$ be PDS over $\mathcal { Q }$ with $\mathrm { A d v } ( \mathsf { Q } _ { i } , \mathsf { U } ) \leq \epsilon$ , where $\cup$ is the uniform distribution over $\mathcal { Q }$ . Let $\langle S _ { i } \rangle _ { i \in [ m + 1 ] }$ be a partition of $[ n ]$ with $\textstyle | S _ { i } | = { \frac { n } { m + 1 } }$ for al $t ^ { 2 2 }$ $\imath$ . Then, the deterministic construction C defined by23

$$
\mathsf C ( q _ { 1 } , \hdots , q _ { n } ) : = \left( \begin{array} { l c r } { ( \odot _ { j \in S _ { 1 } } q _ { j } ) \odot \bigodot _ { j \in S _ { m + 1 } } q _ { j } } \\ { ( \odot _ { j \in S _ { 2 } } q _ { j } ) \odot \bigodot _ { j \in S _ { m + 1 } } q _ { j } } \\ { \hdots } \\ { ( \odot _ { j \in S _ { m } } q _ { j } ) \odot \bigodot _ { j \in S _ { m + 1 } } q _ { j } } \end{array} \right)
$$

satisfies

$$
\mathrm { A d v } \big ( \mathsf C ( \mathsf Q _ { 1 } , \ldots , \mathsf Q _ { n } ) , \mathsf { U } ^ { n } \big ) \le \frac { m ( m + 1 ) } 4 ( 2 \epsilon ) ^ { 2 n / ( m + 1 ) } ,
$$

where $\cup ^ { n }$ are $n$ independent parallel instances of $\mathsf { U }$ .

Proof. We rewrite $\mathsf { C }$ as the application of multiple combiners

$$
\mathsf { C } ( \mathsf { Q } _ { 1 } , \hdots , \mathsf { Q } _ { n } ) = \mathsf C _ { m , m + 1 } ^ { \prime } \Bigl ( \bigcirc _ { j \in S _ { 1 } } \mathsf Q _ { j } , \hdots , \bigcirc _ { j \in S _ { m + 1 } } \mathsf Q _ { j } \Bigr ) ,
$$

where $\mathsf { C } _ { m , m + 1 } ^ { \prime }$ is the $( m , m + 1 )$ -combiner defined by

$$
\begin{array} { r } { \mathsf { C } _ { m , m + 1 } ^ { \prime } ( q _ { 1 } , \dots , q _ { m + 1 } ) : = ( q _ { 1 } \odot q _ { m + 1 } , \dots , q _ { m } \odot q _ { m + 1 } ) . } \end{array}
$$

Since each inner argument $\big ( \bigodot _ { j \in S _ { i } } \cdot \big )$ to the construction $\mathsf { C } _ { m , m + 1 } ^ { \prime }$ in (4) is a $( 1 , n / ( m + 1 ) )$ -combiner, we have by Corollary $^ { 1 }$ for any $i \in \lfloor m + 1 \rfloor$

$$
\operatorname { A d v } \Big ( \bigcirc \cdot \bigcirc _ { j \in S _ { i } } \mathsf { Q } _ { j } , \mathsf { U } \Big ) \leq \frac { 1 } { 2 } ( 2 \epsilon ) ^ { n / ( m + 1 ) } .
$$

Again invoking Corollary $^ { 1 }$ for $c _ { m , m + 1 } ^ { \prime }$ yields

$$
\begin{array} { r l } & { \mathrm { A d v } ( \mathsf C ( \mathsf Q _ { 1 } , \ldots , \mathsf Q _ { n } ) , \mathsf U ^ { n } ) \le 2 \cdot \binom { m + 1 } { 2 } \left( \displaystyle \operatorname* { m a x } _ { i \in [ m + 1 ] } \mathrm { A d v } \left( \bigodot _ { j \in S _ { i } } \mathsf Q _ { j } , \mathsf U \right) \right) ^ { 2 } } \\ & { \qquad \le \frac { m ( m + 1 ) } { 4 } ( 2 \epsilon ) ^ { 2 n / ( m + 1 ) } . } \end{array}
$$

# 6 Conclusions and Open Problems

We presented a simple systems theory of random systems. The key insight was to interpret a random system as probability distribution over deterministic systems, and to consider equivalence classes of probabilistic systems induced by the behavior equivalence relation. We demonstrated how this perspective on random systems provides an elementary characterization of the classical distinguishing advantage and is also a useful tool to prove indistinguishability bounds.

Finally, we have shown a general indistinguishability amplification theorem for any $( k , n )$ -combiner. We demonstrated how the theorem can be instantiated to combine $n$ stateless random permutations (one- or both-sided), which are only moderately close to uniform random permutations, into $m < n$ random permutations that are jointly very close to uniform random permutations. For random functions, we have shown that even stronger indistinguishability amplification can be obtained. Several open questions remain:

(i) Any $A$ -combiner is also a $( k , n )$ -combiner for sufficiently large $k$ . In this sense, the bound of Theorem 3 applies also to any $\mathcal { A }$ -combiner. A natural question is whether significantly better indistinguishability amplification is possible for general (non-threshold) $\mathcal { A }$ -combiners. In particular, can the presented technique (Lemma 7) be used to prove such a bound? It seems that a new idea is necessary to prove such a bound, considering that the current proof strongly relies on the symmetry in the threshold case.

(ii) It is easy to see that the proved indistinguishability bound for $( k , n )$ combiners is perfectly tight for the case $k = 1$ . Is it also tight for general $k$ ? For special cases, such as $( k , n ) = ( 2 , 3 )$ , it is not too difficult to show that the presented bound is very close to tight.

(iii) We have shown how MDS matrices allow to combine $n$ independent random functions over a field to $m$ random functions. However, the same technique does not immediately apply to random permutations. The bounds shown in Lemma 8 are the first non-trivial ones in the more general setting of combining systems forming a quasigroup. It may be possible to improve substantially over said bounds, possibly also by making stronger assumptions (e.g., explicitly assuming permutations). In particular, one might hope to improve the exponent $2 n / ( m + 1 )$ .

(iv) Our treatment is in the information-theoretic setting. A natural question is whether our results can be extended to the computational setting. Under certain assumptions on the component systems, the special case of a $( 1 , n )$ -combiner was shown to provide computational indistinguishability amplification in [MT09].

(v) Can the coupling theorem be used to prove amplification results that strengthen the distinguisher class? For example, can we get more general lifting of non-adaptive indistinguishability to adaptive indistinguishability than what is shown in [MP04,MPR07]?

# References

Ald83. David Aldous. Random walks on finite groups and rapidly mixing Markov chains. In Jacques Az´ema and Marc Yor, editors, S´eminaire de Probabilit´es XVII 1981/82, pages 243–297, Berlin, Heidelberg, 1983. Springer Berlin Heidelberg.

BI99. Mihir Bellare and Russell Impagliazzo. A tool for obtaining tighter security analyses of pseudorandom function based constructions, with applications to PRP to PRF conversion. IACR Cryptology ePrint Archive, page 24, 1999.   
BR06. Mihir Bellare and Phillip Rogaway. The security of triple encryption and a framework for code-based game-playing proofs. In Proceedings of the 24th Annual International Conference on The Theory and Applications of Cryptographic Techniques, EUROCRYPT’06, page 409–426, Berlin, Heidelberg, 2006. Springer-Verlag.   
DHT17. Wei Dai, Viet Tung Hoang, and Stefano Tessaro. Information-theoretic indistinguishability via the chi-squared method. In Jonathan Katz and Hovav Shacham, editors, Advances in Cryptology – CRYPTO 2017, pages 497–523, Cham, 2017. Springer International Publishing.   
HWKS98. Chris Hall, David Wagner, John Kelsey, and Bruce Schneier. Building PRFs from PRPs. In Hugo Krawczyk, editor, Advances in Cryptology — CRYPTO ’98, pages 370–389, Berlin, Heidelberg, 1998. Springer Berlin Heidelberg.   
LR88. Michael Luby and Charles Rackoff. How to construct pseudorandom permutations from pseudorandom functions. SIAM Journal on Computing, 17(2):373–386, 1988.   
Luc00. Stefan Lucks. The sum of PRPs is a secure PRF. In Bart Preneel, editor, Advances in Cryptology — EUROCRYPT 2000, pages 470–484, Berlin, Heidelberg, 2000. Springer Berlin Heidelberg.   
Mau02. Ueli Maurer. Indistinguishability of random systems. In Lars R. Knudsen, editor, Advances in Cryptology — EUROCRYPT 2002, pages 110–132, Berlin, Heidelberg, 2002. Springer Berlin Heidelberg.   
Mau13. Ueli Maurer. Conditional equivalence of random systems and indistinguishability proofs. In 2013 IEEE International Symposium on Information Theory Proceedings (ISIT), pages 3150–3154, July 2013.   
MP04. Ueli Maurer and Krzysztof Pietrzak. Composition of random systems: When two weak make one strong. In Moni Naor, editor, Theory of Cryptography, pages 410–427, Berlin, Heidelberg, 2004. Springer Berlin Heidelberg.   
MPR07. Ueli Maurer, Krzysztof Pietrzak, and Renato Renner. Indistinguishability amplification. In Alfred Menezes, editor, Advances in Cryptology - CRYPTO 2007, pages 130–149, Berlin, Heidelberg, 2007. Springer Berlin Heidelberg.   
MS77. F. J. MacWilliams and Neil J. A. Sloane. The Theory of Error-Correcting Codes. Number 16 in North-Holland Mathematical Library. North-Holland Pub. Co., 1977.   
MT09. Ueli Maurer and Stefano Tessaro. Computational indistinguishability amplification: Tight product theorems for system composition. In Shai Halevi, editor, Advances in Cryptology — CRYPTO 2009, volume 5677 of Lecture Notes in Computer Science, pages 350–368. Springer-Verlag, August 2009.   
NR97. Moni Naor and Omer Reingold. On the construction of pseudo-random permutations: Luby-rackoff revisited (extended abstract). In Proceedings of the Twenty-Ninth Annual ACM Symposium on Theory of Computing, STOC ’97, page 189–199, New York, NY, USA, 1997. Association for Computing Machinery.   
Pat09. Jacques Patarin. The “coefficients h” technique. In Roberto Maria Avanzi, Liam Keliher, and Francesco Sica, editors, Selected Areas in Cryptography, pages 328–345, Berlin, Heidelberg, 2009. Springer Berlin Heidelberg.   
Sin64. R. Singleton. Maximum distance q-nary codes. IEEE Transactions on Information Theory, 10(2):116–118, April 1964.   
Tes11. Stefano Tessaro. Security amplification for the cascade of arbitrarily weak PRPs: Tight bounds via the interactive hardcore lemma. In Yuval Ishai, editor, Theory of Cryptography, pages 37–54, Berlin, Heidelberg, 2011. Springer Berlin Heidelberg.   
Vau98. Serge Vaudenay. Provable security for block ciphers by decorrelation. In Michel Morvan, Christoph Meinel, and Daniel Krob, editors, STACS 98, pages 249–275, Berlin, Heidelberg, 1998. Springer Berlin Heidelberg.   
Vau00. Serge Vaudenay. Adaptive-attack norm for decorrelation and superpseudorandomness. In Proceedings of the 6th Annual International Workshop on Selected Areas in Cryptography, SAC ’99, pages 49–61, London, UK, UK, 2000. Springer-Verlag.

# Appendix

A Proofs of Basic Lemmas

Proof (of Lemma 2). By the definition of the statistical distance we have

$$
\begin{array} { r l } & { \delta ( { \mathsf X } , { \mathsf Y } ) = \displaystyle \sum _ { a \in A } \operatorname* { m a x } ( 0 , { \mathsf X } ( a ) - { \mathsf Y } ( a ) ) } \\ & { \qquad = \displaystyle \sum _ { i \in [ k ] } \sum _ { a \in A _ { i } } \operatorname* { m a x } ( 0 , { \mathsf X } ( a ) - { \mathsf Y } ( a ) ) } \\ & { \qquad = \displaystyle \sum _ { i \in [ k ] } \sum _ { a \in A _ { i } } \operatorname* { m a x } ( 0 , { \mathsf X } _ { i } ( a ) - { \mathsf Y } _ { i } ( a ) ) } \\ & { \qquad = \displaystyle \sum _ { i \in [ k ] } \delta ( { \mathsf X } _ { i } , { \mathsf Y } _ { i } ) . } \end{array}
$$

Proof (of Lemma $\mathcal { B }$ ). We have

$$
\begin{array} { r l } { \delta ( f ( \mathbf { X } ) , f ( \mathbf { Y } ) ) = } & { \displaystyle \sum _ { b \in B } \operatorname* { m a x } ( 0 , f ( \mathsf { X } ) ( b ) - f ( \mathsf { Y } ) ( b ) ) } \\ & { = \displaystyle \sum _ { b \in B } \operatorname* { m a x } ( 0 , \displaystyle \sum _ { a \in f ^ { - 1 } ( b ) } \mathbf { X } ( a ) - \mathbf { Y } ( a ) ) } \\ & { \leq \displaystyle \sum _ { b \in B } \displaystyle \sum _ { a \in f ^ { - 1 } ( b ) } \operatorname* { m a x } ( 0 , \mathbf { X } ( a ) - \mathbf { Y } ( a ) ) } \\ & { = \displaystyle \sum _ { a \in A } \operatorname* { m a x } ( 0 , \mathbf { X } ( a ) - \mathbf { Y } ( a ) ) } \\ & { = \delta ( \mathbf { X } , \mathbf { Y } ) . } \end{array}
$$

In the fourth step, we used that $f$ is a total function from $\boldsymbol { A }$ to $\boldsymbol { \beta }$ .

Proof (of Lemma $\it 5$ ). It suffices to show that if we have

$\operatorname { t r } ( 5 , e ) = \operatorname { t r } ( 7 , e )$ for all compatible non-adaptive $( \mathcal { V } , \mathcal { X } )$ -DDE $e$ ,

then the same is true for all compatible $( \mathcal { V } , \mathcal { X } )$ -DDE $e$ (even adaptive ones).

Assume there exists an adaptive $( \mathcal { V } , \mathcal { X } )$ -DDE $e$ such that

$$
\operatorname { t r } ( 5 , e ) \neq \operatorname { t r } ( 7 , e ) ,
$$

implying that there exists a transcript $\hat { t } = ( \hat { x } _ { 1 } , \hat { y } _ { 1 } ) , ( \hat { x } _ { 2 } , \hat { y } _ { 2 } ) , \dots , ( \hat { x } _ { l } , \hat { y } _ { l } )$ such that $^ { 2 4 }$ $\operatorname { t r } ( { \mathsf { S } } , e ) ( { \hat { t } } ) \neq \operatorname { t r } ( { \mathsf { T } } , e ) ( { \hat { t } } )$ . Let $e ^ { \prime }$ be the environment which queries the inputs of $\hat { t }$ , i.e., $\left( \hat { x } _ { 1 } , \hat { x } _ { 2 } , \ldots , \hat { x } _ { l } \right)$ . Clearly, $e ^ { \prime }$ is non-adaptive and deterministic. Observe moreover that for any $( \mathcal { X } , \mathcal { Y } )$ -DDS $s$ and any compatible $( \mathcal { V } , \mathcal { X } )$ -DDE $\tilde { e }$ , the transcript $\operatorname { t r } ( s , { \tilde { e } } )$ is $\hat { t }$ if and only if $s ( \hat { x } ^ { i } ) = \hat { y } _ { i }$ and $\tilde { e } ( \hat { y } ^ { i - 1 } ) = \hat { x } _ { i }$ for all $i \in [ l ]$ . Since we have $e ( \hat { y } ^ { i - 1 } ) = e ^ { \prime } ( \hat { y } ^ { i - 1 } ) = \hat { x } _ { i }$ for all $i \in [ l ]$ , we obtain

$$
\begin{array} { r l } & { \mathrm { t r } ( \mathsf { S } , \mathsf { e } ^ { \prime } ) ( \hat { t } ) = \mathsf { S } ( \{ s \mid s \in \mathsf { d o m } ( \mathsf { S } ) , \forall i \in [ l ] : s ( \hat { x } ^ { i } ) = \hat { y } _ { i } \} ) = \mathrm { t r } ( \mathsf { S } , \mathsf { e } ) ( \hat { t } ) \mathrm { a n d } } \\ & { \mathrm { t r } ( \mathsf { T } , \mathsf { e } ^ { \prime } ) ( \hat { t } ) = \mathsf { T } ( \{ s \mid s \in \mathsf { d o m } ( \mathsf { T } ) , \forall i \in [ l ] : s ( \hat { x } ^ { i } ) = \hat { y } _ { i } \} ) = \mathrm { t r } ( \mathsf { T } , \mathsf { e } ) ( \hat { t } ) . } \end{array}
$$

Hence, $\operatorname { t r } ( { \mathsf { S } } , e ^ { \prime } ) ( { \hat { t } } ) \neq \operatorname { t r } ( { \mathsf { T } } , e ^ { \prime } ) ( { \hat { t } } )$ and therefore $\operatorname { t r } ( { \mathsf { S } } , e ^ { \prime } ) \neq \operatorname { t r } ( { \mathsf { T } } , e ^ { \prime } )$ , concluding the proof. ut

Lemma 9 (cf. Lemma 3 of [MPR07]). For any two compatible PDS S, T and any probability distribution $\textsf { B }$ over $\{ 0 , 1 \}$

$$
\mathrm { A d v } ( \langle \mathsf { S } / \mathsf { T } \rangle _ { \mathsf { B } } , \mathsf { T } ) = \mathsf { B } ( 0 ) \cdot \mathrm { A d v } ( \mathsf { S } , \mathsf { T } ) .
$$

Proof. Observe that

$$
\begin{array} { r l } & { \mathrm { A d v } ^ { \mathrm { D } } ( \langle \mathsf { S } / \mathsf { T } \rangle _ { \mathsf { B } } , \mathsf { T } ) = \mathrm { P r } ^ { \mathsf { D T } } ( Z = 1 ) - \mathrm { P r } ^ { \mathsf { D } ( \mathsf { S } / \mathsf { T } ) _ { \mathsf { B } } } ( Z = 1 ) } \\ & { \quad \quad \quad \quad = \mathsf { B } ( 0 ) \cdot \left( \mathrm { P r } ^ { \mathsf { D T } } ( Z = 1 ) - \mathrm { P r } ^ { \mathsf { D S } } ( Z = 1 ) \right) } \\ & { \quad \quad \quad \quad + \mathsf { B } ( 1 ) \cdot \left( \mathrm { P r } ^ { \mathsf { D T } } ( Z = 1 ) - \mathrm { P r } ^ { \mathsf { D T } } ( Z = 1 ) \right) } \\ & { \quad \quad \quad = \mathsf { B } ( 0 ) \cdot \left( \mathrm { P r } ^ { \mathsf { D T } } ( Z = 1 ) - \mathrm { P r } ^ { \mathsf { D S } } ( Z = 1 ) \right) } \\ & { \quad \quad \quad = \mathsf { B } ( 0 ) \cdot \mathrm { A d v } ^ { \mathsf { D } } ( \mathsf { S } , \mathsf { T } ) . } \end{array}
$$

Lemma 10. Let $\xi _ { l , m }$ for $l , m \in \mathbb { N } \backslash \{ 0 \}$ be defined by

$$
\xi _ { l , m } : = \frac { 1 } { 2 } \cdot \left( 1 + \sum _ { j = l } ^ { m } { \binom { m } { j } } \cdot { \binom { j - 1 } { l - 1 } } \right) .
$$

Then,

$$
\xi _ { l , m } = 2 \cdot \xi _ { l , m - 1 } + \xi _ { l - 1 , m - 1 } - 1
$$

$$
2 ^ { m - l } \cdot \binom { m - 1 } { l - 1 } \in [ \xi _ { l , m } , 2 \xi _ { l , m } - 1 ] .
$$

Proof. Consider the expression $\begin{array} { r } { t _ { l , m } : = \sum _ { j = l } ^ { m } { \binom { m } { j } } { \binom { j - 1 } { l - 1 } } . } \end{array}$ . Observe that $t _ { l , m }$ is the number of possibilities to select a first subset of $[ m ]$ with size at least $\it l$ and then selecting exactly ${ \mathit { l } } - 1$ elements (but never the smallest one) of the first subset for a second subset. Consider the element $m \in [ m ]$ . There are $t _ { l - 1 , m - 1 }$ possibilities for it to be in the second subset (and thus also in the first), and $2 t _ { l , m - 1 }$ possibilities for it not to be in the second subset (either it is in the first subset or not). Thus, we have $t _ { l , m } = 2 t _ { l , m - 1 } + t _ { l - 1 , m - 1 }$ .

We have $\xi _ { l , m } = \textstyle { \frac { 1 } { 2 } } ( 1 + t _ { l , m } )$ , and therefore

$$
\begin{array} { r l } {  { 2 \cdot \xi _ { l , m - 1 } + \xi _ { l - 1 , m - 1 } - 1 = ( 1 + t _ { l , m - 1 } ) + \frac { 1 } { 2 } ( 1 + t _ { l - 1 , m - 1 } ) - 1 } } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad } \\ &  \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array}
$$

The bound $( i i )$ can be proved by induction over $m$ . For $m = 1$ or $m = \iota$ , the claim trivially holds. For $m > 1$ and $\iota < m$ we have (using $( i )$ )

$$
\begin{array} { r l } & { \xi _ { l , m } = 2 \xi _ { l , m - 1 } + \xi _ { l - 1 , m - 1 } - 1 } \\ & { \qquad \leq 2 \cdot 2 ^ { m - 1 - l } \binom { m - 2 } { l - 1 } + 2 ^ { m - l } \binom { m - 2 } { l - 2 } } \\ & { \qquad = 2 ^ { m - l } \cdot \left( \binom { m - 2 } { l - 1 } + \binom { m - 2 } { l - 2 } \right) } \\ & { \qquad = 2 ^ { m - l } \binom { m - 1 } { l - 1 } . } \end{array}
$$

Moreover,

$$
\begin{array} { r l } & { 2 \xi _ { l , m } - 1 = 2 ( 2 \xi _ { l , m - 1 } + \xi _ { l - 1 , m - 1 } - 1 ) - 1 } \\ & { \qquad = 2 ( 2 \xi _ { l , m - 1 } - 1 ) + ( 2 \xi _ { l - 1 , m - 1 } - 1 ) } \\ & { \qquad \geq 2 \cdot 2 ^ { m - 1 - l } \binom { m - 2 } { l - 1 } + 2 ^ { m - l } \binom { m - 2 } { l - 2 } } \\ & { \qquad = 2 ^ { m - l } \cdot \bigg ( \binom { m - 2 } { l - 1 } + \binom { m - 2 } { l - 2 } \bigg ) } \\ & { \qquad = 2 ^ { m - l } \binom { m - 1 } { l - 1 } . } \end{array}
$$

This concludes the proof.