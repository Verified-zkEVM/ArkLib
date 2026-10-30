# Background

This page explains the theory that ArkLib formalizes. ArkLib's scope covers two kinds of objects,
and most succinct arguments combine them:

- information-theoretic proof systems, such as interactive oracle proofs and reductions, and the
  compilers that turn them into arguments;
- arguments and commitment schemes whose security rests on computational assumptions, such as
  discrete-logarithm and pairing assumptions, lattice assumptions such as Module-SIS, or collision
  resistance of a hash function, or on idealized models, such as a hash function modelled as a
  random oracle.

The page surveys both, with their security notions, including post-quantum and universally
composable security, which ArkLib plans to cover. It then compares ArkLib's own definition of an
interactive oracle reduction with the definitions in the literature.

It is written for cryptographers and contributors who know what an interactive proof and a SNARK
are, and who want to know which formal objects ArkLib's definitions correspond to. It is not a
status page. For what has been formalized and proved, read [ROADMAP.md](ROADMAP.md) and
[docs/design/00-current-status.md](docs/design/00-current-status.md).

ArkLib has two layers for protocols, and this page uses fixed names for them:

- the **legacy layer**, [`ArkLib/OracleReduction/`](ArkLib/OracleReduction/), which describes a
  protocol by a fixed list of rounds (`ProtocolSpec`);
- the **interaction layer**, [`ArkLib/Interaction/`](ArkLib/Interaction/), which describes a
  protocol as an interaction tree over PolyFun's polynomial functors and is meant to replace the
  legacy layer.

Citation keys such as [BCS16] refer to [Section 8](#8-references). Where the repository has a
knowledge-base page for a paper, the reference links to it.

## Contents

1. [How to use this page](#1-how-to-use-this-page)
2. [Information-theoretic proof systems](#2-information-theoretic-proof-systems)
3. [Security notions](#3-security-notions)
4. [From oracle reductions to succinct arguments](#4-from-oracle-reductions-to-succinct-arguments)
5. [Computational arguments and commitment schemes](#5-computational-arguments-and-commitment-schemes)
6. [ArkLib's oracle reductions compared with the literature](#6-arklibs-oracle-reductions-compared-with-the-literature)
7. [Related formalization efforts](#7-related-formalization-efforts)
8. [References](#8-references)

## 1. How to use this page

| If you want to know | Read |
|---|---|
| which paper introduced a model (IOP, IOPP, polynomial IOP, IOR, ...) | [Section 2](#2-information-theoretic-proof-systems) |
| how round-by-round, state-restoration and special soundness relate | [Section 3](#3-security-notions) |
| how an IOR becomes a SNARK, and where each step lives in ArkLib | [Section 4](#4-from-oracle-reductions-to-succinct-arguments) |
| what separates an argument from a proof, which security notions commitment schemes have, and what a proof in the random oracle, generic group or algebraic group model shows | [Section 5](#5-computational-arguments-and-commitment-schemes) |
| what post-quantum security in the quantum random oracle model and universal composability require, and what ArkLib plans for them | [Section 5.7](#57-post-quantum-security-in-the-quantum-random-oracle-model) and [Section 5.8](#58-universal-composability) |
| whether an ArkLib theorem about an `OracleReduction` says what a paper's theorem says | [Section 6](#6-arklibs-oracle-reductions-compared-with-the-literature) |
| how ArkLib relates to other machine-checked cryptography | [Section 7](#7-related-formalization-efforts) |

Two textbooks cover most of Sections 2 to 5 in depth. Chiesa and Yogev's *Building Cryptographic
Proofs from Hash Functions* [CY24] is the standard reference for IOPs, state-restoration soundness,
the BCS transformation, Merkle commitments in the random oracle model and Fiat–Shamir, and ArkLib's
Fiat–Shamir module follows its treatment. Thaler's *Proofs, Arguments, and Zero-Knowledge* [Tha22]
covers interactive proofs, the sum-check protocol, polynomial commitments from discrete logarithms
and pairings, and the SNARKs built from them. Ishai's two-part survey [Ish20] gives a short
account of the "information-theoretic proof system plus cryptographic compiler" methodology.

## 2. Information-theoretic proof systems

Many modern succinct arguments are built in two steps. First, one designs a protocol in an
idealized model in which the verifier has some restricted access to the prover's messages, and
proves it sound without any computational assumption. Second, a cryptographic compiler removes the
idealization. The models below differ in what the verifier may ask about a prover message, and in
what the protocol is supposed to establish. Not every argument is built this way: Section 5 covers
arguments whose soundness is computational from the start, and the commitment schemes that
compilers use.

### 2.1 Interactive proofs and probabilistically checkable proofs

An interactive proof (IP) lets a probabilistic polynomial-time verifier exchange messages with an
unbounded prover and reads each message in full [GMR89, Bab85]. The sum-check protocol [LFKN92] is
the central algebraic IP, and it remains a building block of most systems that ArkLib formalizes.

A probabilistically checkable proof (PCP) is a single static proof string that the verifier reads
at a few random locations. Babai, Fortnow, Levin and Szegedy [BFLS91] gave "transparent proofs"
that a polylogarithmic-time verifier can check given an encoded input; Babai later used the name
"holographic" for the same idea [Bab93]. The PCP theorem [AS98, ALMSS98] shows that every NP
statement has a PCP with a constant number of queries.

### 2.2 From PCPs to succinct arguments

Kilian [Kil92] observed that a PCP yields a succinct interactive argument: the prover commits to
the PCP with a Merkle tree, the verifier sends random query locations, and the prover opens those
locations with authentication paths. Micali [Mic94] removed the interaction in the random oracle
model by deriving the query locations from a hash of the commitment, in the manner of Fiat and
Shamir [FS86].

This pattern of an information-theoretic object, a commitment to each oracle, and a hash for the
verifier's randomness is the template for everything in Section 4.

### 2.3 Interactive oracle proofs

Interactive PCPs [KR08] let the prover send a PCP and then run an interactive proof about it.
Interactive oracle proofs (IOPs) generalize both IPs and PCPs. An IOP is an interactive proof in
which the verifier receives oracle access to each prover message and may query a received message
in that round or any later one. In [BCS16] the verifier sends the first message and may use private
coins. For public-coin protocols all queries can be deferred to a final phase without loss of
generality. This page generally uses a prover-message-then-challenge convention and adjusts the
first and last rounds as needed. Ben-Sasson, Chiesa and Spooner introduced IOPs [BCS16]. Independently, Reingold,
Rothblum and Rothblum [RRR16] introduced probabilistically checkable interactive proofs (PCIPs),
which [BCS16] notes are equivalent to IOPs.

[BCS16] also introduced the two notions that make IOPs useful for cryptography: a compiler from
public-coin IOPs to non-interactive arguments in the random oracle model (the BCS transformation),
and state-restoration soundness, which exactly characterizes when that compiler is sound. Both
appear again in Sections 3 and 4.

### 2.4 Proximity, holography and preprocessing

An IOP of proximity (IOPP) is an IOP in which the verifier has only oracle access to part of the
input, and soundness is required only against inputs that are far from the language. The FRI paper
[BBHR18] credits the formal introduction of IOPPs to Ben-Sasson, Chiesa, Gabizon, Riabzev and
Spooner [BCGRS17] and, independently and under the name "probabilistically checkable interactive
proofs of proximity", to [RRR16]. FRI [BBHR18], STIR [ACFY24stir] and WHIR [ACFY25] are IOPPs for
Reed–Solomon codes, and their soundness rests on proximity gaps such as [BCIKS20].

An IOP is holographic if an indexer encodes the circuit or constraint system once, and the verifier
gets oracle access to that encoding instead of reading the circuit. Fractal [COS20] defines
holographic IOPs and compiles them into preprocessing SNARGs; it credits the idea of holography to
[BFLS91] and the connection between holography and preprocessing to Marlin [CHMMVW20].

### 2.5 Algebraic oracle models

The IOP model of [BCS16] lets the verifier query individual symbols of a string. Many practical
protocols are more naturally stated with richer oracles, typically low-degree polynomials that the
verifier can evaluate at points of its choice. Each such model is designed to match one family of
commitment schemes in the compiler.

Most of these models are refinements of linear queries. In a linear PCP [IKO07] the proof is a
vector $\pi \in \mathbb{F}^m$, and each query $q \in \mathbb{F}^m$ returns the inner product
$\langle \pi, q \rangle$. A linear IOP makes the same change to an IOP: each prover message is a
vector, and the verifier makes linear queries to it [Ish20]. A point query is the linear query with
$q$ a unit vector. Evaluating a polynomial at a point is a linear query to a suitable representation
of the polynomial: to its coefficient vector, or, for a multilinear polynomial, to its values on the
Boolean hypercube. Point-query IOPs and polynomial IOPs are therefore restricted linear IOPs, which
is why [BFS20] describes polynomial IOPs as a class of algebraic linear IOPs. The weighted-sum
queries of a general $\Sigma$-IOP are not of this form: the answer $\sum_b \hat{w}(f(b), b)$ is
affine in $f$ only when $\hat{w}$ has degree less than 2 in its first argument, which is WHIR's
*linear* $\Sigma$-IOP. Linear interactive proofs (LIPs) [BCIOP13] are a different restriction: they
are interactive proofs in which the prover, honest or malicious, may only compute linear functions
of the verifier's messages. Bitansky et al. compile linear PCPs into SNARKs through LIPs. The
formalization of linear-PCP SNARKs [BM24] listed in Section 7 belongs to this line of work.

The table lists the models that ArkLib's notion of an oracle interface (Section 6.2) is meant to
subsume.

| Model | Source | What a prover oracle is | What a verifier query returns |
|---|---|---|---|
| Point-query IOP | [BCS16] | a string over an alphabet $\Sigma$ | one symbol of the string |
| Linear PCP | [IKO07] | a single vector $\pi \in \mathbb{F}^m$ | inner products $\langle \pi, q \rangle$ with verifier-chosen $q$ |
| Linear IOP | [Ish20] | a vector over $\mathbb{F}$ in each round | inner products with verifier-chosen vectors |
| Ideal linear commitment (ILC) | [BCGGHJ17] | a committed vector or matrix | linear combinations chosen by the verifier |
| Algebraic holographic proof (AHP) | [CHMMVW20] | a low-degree univariate polynomial | evaluations at verifier-chosen points |
| Polynomial IOP (PIOP) | [BFS20] | a bounded-degree polynomial | evaluations at verifier-chosen points |
| Polynomial holographic IOP (PHP) | [CFFQR21] | polynomials, with holographic index polynomials | polynomial identity checks over committed polynomials |
| Tensor IOP | [BCG20] | a vector over $\mathbb{F}$ | inner products with tensor-structured query vectors |
| $\mathcal{F}$-IOP | [ACFY25, Def. 7.1] | for oracle $j$ of round $i$, an element $f$ of a prescribed oracle set $\mathcal{O}_{i,j}$ | $F_{i,j}(f, w) \in \Sigma$ for a query $w \in \mathcal{W}_{i,j}$ |
| $\Sigma$-IOP | [ACFY25, Def. 7.2] | a multilinear polynomial | weighted sums $\sum_b \hat{w}(f(b), b)$ over the Boolean hypercube |

A few remarks on priority and naming:

- Marlin [CHMMVW20] introduces AHPs: the prover sends low-degree polynomials, the verifier queries
  their evaluations, and the result is compiled with a polynomial commitment scheme.
- The DARK paper [BFS20] calls "Polynomial IOPs" a restricted class of algebraic linear IOPs and
  remarks that examples of them date back to the first PCP [BFLS91]. It compiles any PIOP with the
  DARK polynomial commitment, and uses PLONK's protocol [GWZC19] as an example.
- Lunar [CFFQR21] introduces PHPs as "a new algebraically-flavored variant of IOPs".
- WHIR [ACFY25] defines $\mathcal{F}$-IOPs (Definition 7.1) as IOPPs with a rich class of queries,
  a specialization of the IOPs with special queries of [BCG20]. Each oracle of each round has its
  own oracle set $\mathcal{O}_{i,j}$, query set $\mathcal{W}_{i,j}$ and answer function
  $F_{i,j}$; what is shared is the answer alphabet $\Sigma$. The relation has entries $(x, y, w)$,
  and the verifier has oracle access to the input string $y$ as well as to the proof oracles. The
  definition fixes a public-coin protocol with a non-adaptive verifier and no holography. WHIR then introduces $\Sigma$-IOPs, a variant of
  multilinear polynomial IOPs whose queries are weighted sums.
- In a polynomial model the prover's messages are assumed to be polynomials of the declared degree,
  for honest and malicious provers alike; STIR's polynomial IOPPs state this restriction explicitly
  [ACFY24stir]. The compiler must then enforce the degree bound. Section 6.4 explains how ArkLib
  records this assumption.

### 2.6 From proofs to reductions

A proof ends with accept or reject. Many protocols are better described as reductions: they turn a
claim about one relation into a claim about another, and leave the new claim to a later protocol.
The sum-check protocol reduces a sum over the hypercube to one evaluation; a folding scheme reduces
two instances to one. Three papers made this view formal for the settings ArkLib cares about.

**Oracle reductions [BCGGRS19].** Ben-Sasson, Chiesa, Goldberg, Gur, Riabzev and Spooner
"formulate a new notion that we call interactive oracle reductions (in short, oracle reductions)"
(Section 2.5) to modularize the construction of linear-size IOPs. In their Definition 5.2, the
verifier makes no queries. After the interaction it outputs a list of instances together with
*virtual oracles*. A virtual oracle (Definition 5.1) is a pair of deterministic algorithms: a query
algorithm that maps a position to a list of positions in the prover's oracles, and an answer
algorithm that computes the virtual symbol from those answers. Virtual oracles are therefore
non-adaptive and have bounded locality. Soundness is a proximity condition: if the input is not in
the language, then with high probability some output virtual oracle is $\delta$-far from the
output relation. Composition uses oracle reductions of proximity (Definition 5.3). The paper
relates the definition to linear-algebraic CSPs [BCGV16].

**Reductions of knowledge [KP23].** Kothapalli and Parno define a reduction of knowledge from
$\mathcal{R}_1$ to $\mathcal{R}_2$ as a generator, a prover and a verifier. The prover maps
$(u_1, w_1)$ to $(u_2, w_2)$; the verifier maps $u_1$ to $u_2$. A reduction of knowledge must
satisfy completeness (the prover's and verifier's output statements agree and the output is in
$\mathcal{R}_2$), knowledge soundness (an expected-polynomial-time extractor recovers a witness for
$u_1$ with probability close to that of the malicious prover producing a witness for $u_2$), and
public reducibility (the output statement is a deterministic function of the input statement and
the transcript). A proof of knowledge is a reduction of knowledge to the trivial relation
$\{(\mathsf{true}, \bot)\}$. The framework comes with sequential and parallel composition
theorems. Kothapalli's thesis [Kot24] presents the definitions in this form; the folding schemes
Nova [KST22] and HyperNova [KS24] are reductions of this kind.

**Interactive oracle reductions [BMNW25].** Arc introduces the notion again, as "a notion which
extends interactive oracle proofs [BCS16; RRR16] to capture reductions" in the sense of [KP23]. In
Arc's Section 5, relations are *indexed oracle promise relations*. The instance consists of a short
instance $x$ and instance strings $\vec{y}$ that the verifier accesses as oracles. Each relation
$\mathcal{R}$ comes with a relaxed relation $\tilde{\mathcal{R}}$ in which instance strings may also
contain the symbol $\bot$. Completeness is stated for $\mathcal{R}$, while Arc's round-by-round
definitions and its compiler work with $\tilde{\mathcal{R}}$. An IOR has an indexer (so it is holographic), a
public-coin verifier with oracle access to the index string, instance strings and proof strings,
and an output instance $(x', \vec{y}')$ whose oracles are selected from the old instance oracles
and the received proof oracles (Remark 5.2). Messages that the verifier reads in full are allowed
informally (Remark 5.1). Arc also defines round-by-round soundness and knowledge for IORs
(Definitions 5.3 to 5.5) and compiles round-by-round sound IORs into non-interactive reductions
(Theorem 5.9). The compilation requires the relations to be *monotone* (Definition 5.8): restricting
the instance strings of an instance outside $L(\tilde{\mathcal{R}})$ to subsets of positions keeps
it outside, so a cheating prover gains nothing by withholding Merkle authentication paths. Arc does
not cite [BCGGRS19], which used the same name five years earlier for a related but different
definition.

Later accumulation and folding papers use the same vocabulary. An accumulation scheme [BCMS20,
BCLMS21] splits the verification of many claims into cheap updates and one final check. The
accumulation prover folds each new claim into a running accumulator, the accumulation verifier
checks each update, and a decider checks the final accumulator once. In a split accumulation scheme
the accumulator has a short instance part and a long witness part, and the accumulation verifier
reads only instance parts. Knowledge soundness asks that, when the updates were accepted and the
decider accepts the final accumulator, witnesses for the earlier claims can be extracted. A folding
step is therefore a reduction of instance–witness pairs to a new pair, not an acceptance test: the
claim it leaves is discharged only by the decider. This is why output witnesses matter in the
definitions above. WARP [BCFW25] constructs "an interactive oracle reduction of proximity that
works with any linear code" as the core of a linear-time accumulation scheme, and FICS and FACS
[BMMS26] extend the IOR framework with a knowledge notion that composes (Section 3.4).

The common core of these definitions, and the one ArkLib adopts, is this: an interactive oracle
reduction maps a statement with oracle components and a witness to a new statement with oracle
components and a new witness, the verifier accesses oracles only through queries, and soundness or
knowledge soundness is stated relative to an input relation and an output relation.

## 3. Security notions

Throughout, a reduction goes from an input relation $\mathcal{R}_{\mathsf{in}}$ to an output
relation $\mathcal{R}_{\mathsf{out}}$, with associated languages $\mathcal{L}_{\mathsf{in}}$ and
$\mathcal{L}_{\mathsf{out}}$. A proof is the special case in which the output relation is trivial
and the verifier outputs a bit.

### 3.1 Completeness, soundness and knowledge soundness

*Completeness* asks that an honest run on $(x, w) \in \mathcal{R}_{\mathsf{in}}$ produces
$(x', w') \in \mathcal{R}_{\mathsf{out}}$, except with probability $\varepsilon_{\mathsf{c}}$. For
reductions, completeness also asks that the honest prover's output statement equals the verifier's
[KP23].

*Soundness* asks that for every $x \notin \mathcal{L}_{\mathsf{in}}$ and every malicious prover,
the verifier outputs some $x' \in \mathcal{L}_{\mathsf{out}}$ with probability at most
$\varepsilon_{\mathsf{s}}$. For proximity notions, "not in the language" becomes "far from the
language" [BCGRS17, BCGGRS19].

*Knowledge soundness* asks that a prover who makes the verifier succeed must know a witness. The
definitions differ in what the extractor may access, when it is chosen, what experiment measures
it, and how much it may cost. Bellare and Goldreich [BG92] give the extractor oracle access to the
prover and bound its expected running time in terms of the prover's success probability. Kothapalli
and Parno [KP23] choose an expected-polynomial-time extractor after the adversary and ask that its
success probability be close to the probability that the malicious prover produces a witness for
the output relation; their extractors rewind the prover. A straightline extractor instead reads
only one execution: the transcript and the prover's random-oracle queries. One form for reductions,
used by ArkLib's straightline definition (Section 6.4), bounds a joint event in a single execution:
the malicious prover's output is in $\mathcal{R}_{\mathsf{out}}$ while the extractor fails to
recover a valid input witness, with probability at most $\varepsilon_{\mathsf{k}}$. These choices
matter for composition and for the Fiat–Shamir transformation.

### 3.2 Round-by-round soundness and knowledge

Canetti et al. [CCHLRRW19] introduced round-by-round (RBR) soundness to instantiate the
Fiat–Shamir transformation for multi-round protocols. RBR soundness asks for a *state function*
on partial transcripts with three properties:

- it is "doomed" (false) on the empty transcript whenever $x \notin \mathcal{L}$;
- a prover message cannot move a doomed transcript to a non-doomed one;
- if the verifier accepts a complete transcript, that transcript is not doomed.

The RBR error $\varepsilon_i$ bounds, for every doomed partial transcript ending before challenge
$i$, the probability over that challenge that the state flips to not doomed. Ordinary soundness
error is then at most $\sum_i \varepsilon_i$.

RBR knowledge soundness adds an extractor. Chiesa, Manohar and Spooner [CMS19, Def. 8.5] define it
with a polynomial-time extractor $E$: if a partial transcript is doomed but a random next challenge
undooms it with probability above $\kappa$, then $E$ applied to the instance and that partial
transcript outputs a valid witness. STIR [ACFY24stir] uses a prefix extractor
$E(x, y, \mathsf{tr})$ with a bound on its running time, where $\mathsf{tr}$ ends at the prover
message just before the fresh challenge. The SNARGs book [CY24, Def. 31.1.6] uses a
variant whose extractor receives the full sequence of prover messages. Arc [BMNW25, Def. 5.5] gives
the IOR version: its extractor also receives a transcript continuation and an output witness, but
it must succeed for every continuation, and Remark 5.6 explains that this prevents useful
dependence on the output witness.

WARP [BCFW25, Defs. 4.1 and 4.2] indexes the state by a witness instead. Its knowledge state
function $\mathsf{KState}_\delta(x, y, \mathsf{tr}, w)$ is parameterized by a proximity bound
$\delta$, keeps the same witness $w$ across prover moves, and is tied to the input relation at the
empty transcript and to the output relation at a full transcript. The RBR error of round $i$ bounds
the probability, over the fresh challenge $\rho_i$, that some witness $w$ makes the new state true
while the extractor's backward image $E(x, y, \mathsf{tr} \| \rho_i, w)$ makes the previous state
false. Each round has an explicit extraction time. Because extraction starts from a witness for the later
state, it can use the output witness. WARP shows that earlier definitions of RBR knowledge imply its
variant (Appendix C) and that its variant implies straightline state-restoration knowledge soundness
(Appendix B). Section 6.4 compares ArkLib's definition with Arc's and WARP's.

### 3.3 State-restoration soundness

In a state-restoration attack [BCS16], the malicious prover may rewind the verifier to any earlier
state and ask for a fresh challenge, up to a budget of $b$ moves, before committing to one complete
transcript. State-restoration soundness bounds its success probability. [BCS16] proves that the
BCS transformation of a public-coin IOP is sound in the random oracle model with error governed by
its state-restoration soundness, and that this characterization is tight.

The two notions are closely linked, but not with the same error. For a public-coin IOP with $k$
rounds and RBR soundness error $\varepsilon$, the SNARGs book bounds the state-restoration
soundness error against a prover with move budget $t$ by $(t + k) \cdot \varepsilon$ [CY24,
Thm. 31.2.1]. Its Theorem 31.3.1 gives the same bound from RBR knowledge soundness to straightline
state-restoration knowledge soundness. Conversely, Holmgren [Hol19] shows that a public-coin
protocol that is sound against every polynomially bounded state-restoration attack is RBR sound.
The two notions are therefore equivalent as asymptotic soundness properties for polynomially
bounded state-restoration attacks, with quantitative losses in both directions. Holmgren also
observes that neither notion is implied by the random-oracle security of the Fiat–Shamir
transformation. In practice, protocol papers prove RBR bounds and compilers consume
state-restoration bounds.

### 3.4 Special soundness

Special soundness asks for an extractor that computes a witness from a tree of accepting
transcripts with enough distinct challenges at each verifier round. A
$(k_1, \dots, k_\mu)$-special-sound protocol needs a tree with $K = \prod_i k_i$ leaves, so
extraction is efficient only while this size is polynomially bounded. Attema, Cramer and Kohl
[ACK21] give a tight analysis of knowledge extraction from multi-round special-sound protocols, and
Attema, Fehr and Klooß [AFK22] analyze the Fiat–Shamir transformation of such protocols directly,
with a loss linear in the number of random-oracle queries. Both results hold under the extraction
size and efficiency conditions they state; a non-constant number of rounds is covered only when
those conditions hold, not in general.

Attema, Fehr and Resch [AFR23] replace each threshold $k_i$ by an access structure $\Gamma_i$, which
specifies the sets of challenges for which correct answers (for a fixed first message) determine a
witness. Threshold trees are the special case in which every set of $k_i$ distinct challenges
qualifies. A $(\Gamma_1, \dots, \Gamma_\mu)$-special-sound protocol is knowledge sound when a
parameter $t_\Gamma$ that governs the extraction cost is polynomially bounded; a general access
structure does not by itself give efficient extraction. Attema, Fehr, Klooß and Resch [AFKR26]
prove the corresponding Fiat–Shamir theorem: under the same condition the transformed protocol is
knowledge sound, again with a loss linear in the number of random-oracle queries. ArkLib's
shape-generic tree special soundness (Section 6.4) parameterizes trees by a shape in a similar
spirit, but no formal equivalence with these definitions is claimed.

Fenzi, Moghaddas and Nguyen [FMN24] name coordinate-wise special soundness (CWSS), in which the
challenge set is a product and the required transcripts differ in one coordinate; they credit the
underlying extraction strategy to earlier work.

Block, Garreta, Tiwari and Zając [BGTZ25] relate these notions for IOPs, with $C_i$ the challenge
set of round $i$:

- $(k_1, \dots, k_\mu)$-special soundness implies generalized RBR soundness with errors
  $(k_i - 1)/|C_i|$ (Theorem 1.1);
- RBR knowledge soundness with errors $\varepsilon_i$ implies $(k_1, \dots, k_\mu)$-special
  soundness for $k_i = \lceil |C_i| \varepsilon_i \rceil + 1$, provided that
  $\sum_i \prod_{j \le i} k_j$ is polynomially bounded (Theorem 1.2);
- assuming $\mathsf{NP} \ne \mathsf{P}$, special soundness need not imply nontrivial RBR knowledge
  soundness: there is a $(1, \dots, 1)$-special-sound IOP whose RBR knowledge error is 1 in some
  round (Theorem 1.3).

**Trees for reductions.** For a reduction, the leaves of a transcript tree carry output instances
and witnesses, not just accepting bits. FICS and FACS [BMMS26, Section 4] build on this with
*round-by-round tree-extractability* (RBRTE) for IORs. A constrained transcript tree (their
Definition 4.1) has $a_i$ children at each node of layer $i$, joined by distinct challenges. Every
root-to-leaf path is an accepting view, and every leaf is labelled with an output instance and a
witness in the relaxed output relation. Two predicates constrain the tree:

- a *vertical predicate* on each path, which holds on the empty transcript, is unchanged by prover
  messages, and becomes false at a challenge with only negligible probability (it records that the
  prover did not get lucky);
- a *challenge predicate* on all challenges of the tree, which fails with only negligible
  probability when the challenges are sampled independently.

An IOR is RBRTE if $\prod_i a_i$ is polynomial in the instance size and a deterministic
polynomial-time extractor recovers an input witness from every such tree. The paper proves that
every RBR knowledge sound IOR is RBRTE with all $a_i = 1$ (Lemma 4.8), that RBRTE IORs compose
sequentially with tree sizes multiplying (Lemma 4.7), and that RBRTE implies rewinding
state-restoration knowledge soundness, so that the BCS-style compiler yields a non-interactive
reduction with rewinding knowledge soundness (Lemma 4.5). It takes this rewinding route because its
codes are efficiently encodable but not known to be efficiently decodable, so a straightline RBR
extractor that decodes is not available. WARP's notion (Section 3.2) is the straightline
alternative.

### 3.5 Zero knowledge

Honest-verifier zero knowledge (HVZK) asks for an efficient simulator that, given the statement,
outputs something indistinguishable from the honest verifier's view. For an IOP this view consists
of the verifier's randomness and the answers it obtains to its queries, not the entire prover
oracles [BCS16, Section 4]. Indistinguishability may be perfect, statistical or computational, and
a preservation theorem holds for the variant it states. [BCS16] shows that if the IOP is
statistical HVZK, then its BCS transformation is statistical zero knowledge. For this, BCS hides
each committed symbol by hashing it together with fresh randomness in its Merkle leaf.

In ArkLib, `ProtocolSpec.addSalt`
([`OracleReduction/Salt.lean`](ArkLib/OracleReduction/Salt.lean)) pairs each prover message with a
value of an arbitrary salt type and keeps the message's answer interface, which ignores the salt.
Using such salts for hiding requires a commitment construction, a distribution for the randomness,
and a separate zero-knowledge proof. Many zero-knowledge PIOPs instead rely on masking polynomials
together with a hiding polynomial commitment.

### 3.6 Summary of implications

All rows are information-theoretic results or results for a classical random oracle. Results in the
quantum random oracle model are discussed in Section 4.2.

| From | To | Where |
|---|---|---|
| RBR soundness with errors $\varepsilon_i$ | soundness with error $\sum_i \varepsilon_i$ | [CCHLRRW19] |
| RBR soundness with error $\varepsilon$ ($k$ rounds) | state-restoration soundness with error $(t + k) \cdot \varepsilon$ for move budget $t$ | [CY24] |
| soundness against all polynomially bounded state-restoration attacks | RBR soundness (asymptotic, with parameter losses) | [Hol19] |
| RBR knowledge soundness with error $\kappa$ ($k$ rounds) | straightline state-restoration knowledge soundness with error $(t + k) \cdot \kappa$ | [CY24] |
| RBR knowledge soundness of an IOR (WARP's variant) | straightline state-restoration knowledge soundness | [BCFW25] |
| state-restoration (knowledge) soundness of an IOP | (knowledge) soundness of its BCS transformation in the ROM | [BCS16, CY24] |
| multi-round special soundness, with polynomial-size extraction trees | knowledge soundness | [ACK21] |
| $(\Gamma_1, \dots, \Gamma_\mu)$-special soundness, with $t_\Gamma$ polynomially bounded | knowledge soundness, also after Fiat–Shamir | [AFR23, AFKR26] |
| $(k_1, \dots, k_\mu)$-special soundness | generalized RBR soundness with errors $(k_i - 1)/\lvert C_i \rvert$ | [BGTZ25] |
| RBR knowledge soundness with errors $\varepsilon_i$, if $\sum_i \prod_{j \le i} k_j$ is polynomially bounded | $(k_1, \dots, k_\mu)$-special soundness with $k_i = \lceil \lvert C_i \rvert \varepsilon_i \rceil + 1$ | [BGTZ25] |
| RBR knowledge soundness of an IOR | round-by-round tree-extractability | [BMMS26] |
| round-by-round tree-extractability | rewinding state-restoration knowledge soundness | [BMMS26] |

## 4. From oracle reductions to succinct arguments

### 4.1 Removing oracles with commitments

The BCS transformation [BCS16] replaces each prover oracle by a Merkle commitment and each verifier
query by an opening with an authentication path, and derives the verifier's challenges from a
random oracle. Replacing Merkle trees by a polynomial commitment scheme, such as KZG [KZG10], gives
the PIOP-to-SNARK compilers of Marlin [CHMMVW20], DARK [BFS20], Lunar [CFFQR21] and PLONK [GWZC19].
WHIR [ACFY25] attributes the general approach of building SNARGs from polynomial IOPs and
polynomial commitments to [CHMMVW20, BFS20].

ArkLib's design treats these as one construction. Each oracle interface (Section 6.2) is paired with
a *functional commitment* for that interface: a commitment to a message, together with an opening
argument that proves the answer to one query. The commitment-based oracle-elimination stage then:

1. replaces every oracle statement and every oracle message by a commitment;
2. replaces each verifier query by a run of the opening argument for that query, possibly batching
   several openings into one;
3. outputs an interactive reduction with no oracles.

For point-query oracles and Merkle commitments, this is the interactive commitment stage of the
BCS approach; deriving the verifier's challenges from the random oracle (Section 4.2) yields the
non-interactive BCS transformation. With a polynomial commitment and evaluation queries, the same
stage is the PIOP compiler.

This is a construction recipe, not a security theorem. Soundness, knowledge soundness, zero
knowledge, enforcement of degree bounds, and Fiat–Shamir security of the result each need their own
hypotheses on the commitment scheme, and ordinary binding is not enough in general. Marlin, for
example, compiles AHPs with an extractable polynomial commitment scheme.

For public-coin functional IOPs, the Funky compiler of Chiesa, Guan, Knabenhans and Yu [CGKY25]
preserves state-restoration soundness and state-restoration knowledge soundness. Their
Theorem 7.1 is an interactive compiler theorem. The error of the compiled argument is the error
of the functional IOP plus, for each round, the state-restoration function-binding error of the
functional commitment and a tail error of that round's query class; the reduction also pays the
query classes' solving time. The negligible-error conclusion requires the query-class and
resource conditions of [CGKY25, Corollary 7.2]. No separate extractability property is needed for
this theorem. Fiat–Shamir is a subsequent step, which turns state-restoration security into a
non-interactive argument (of knowledge) in the random oracle model. One sufficient route to
state-restoration function binding is state-restoration knowledge soundness of the opening
argument together with binding of the commitment to the whole message [CGKY25, Lemma 3.31]; this
binding notion is not the evaluation binding of Section 5.3. As a corollary, Plonk is a SNARK of
knowledge in the random oracle model under the ARSDH and SplitRSDH assumptions
[CGKY25, Corollary 1]. Zero knowledge and hiding are not treated.

The [oracle-elimination compiler design](docs/design/04-oracle-elimination-compiler.md) describes
the general construction for the interaction layer. It splits the construction into passes and
adds an explicit obligation for type-level guarantees on messages (Section 6.4). Commitment schemes
are under [`ArkLib/Commitments/`](ArkLib/Commitments/). For what is implemented, read the status
documents linked at the top of this page.

### 4.2 Removing interaction with Fiat–Shamir

The Fiat–Shamir transformation [FS86] replaces each verifier challenge by a hash of the
conversation so far. ArkLib's basic version derives the $i$-th challenge from a Fiat–Shamir oracle
applied to the input statement and all prover messages up to round $i$, following [CY24]; see
[`OracleReduction/FiatShamir/Basic.lean`](ArkLib/OracleReduction/FiatShamir/Basic.lean). In the
literature, the security of this transformation in the random oracle model follows from the
state-restoration (knowledge) soundness of the interactive protocol (Section 3.3) [BCS16, CY24].
Special-sound protocols have a separate route: [AFK22] and [AFKR26] bound the knowledge error of
the Fiat–Shamir transformation directly, with a loss linear in the number of random-oracle queries
(Section 3.4).

Deployed systems instead absorb messages into a duplex sponge and squeeze challenges from it.
Chiesa and Orrù [CO25] analyze such a transformation based on an ideal permutation, give concrete
bounds, and show that indifferentiability of the sponge alone is not enough for knowledge soundness
and zero knowledge of the resulting argument.

The results so far assume a classical random oracle. Chiesa, Manohar and Spooner [CMS19,
Thm. 8.6] analyze the BCS construction in the quantum random oracle model (QROM), in which the
attacker may query the hash function in superposition. If the IOP is RBR sound with error
$\varepsilon$, the argument has soundness error $O(t^2 \varepsilon + t^3 / 2^\lambda)$ against
attackers making at most $t - O(q \log \ell)$ quantum queries, where $q$ is the query complexity and
$\ell$ the proof length of the IOP. RBR knowledge (their Definition 8.5) gives an argument
of knowledge with a similar loss, and HVZK gives statistical zero knowledge. Their construction
includes the prover messages in the hash chain; for the original BCS hash chain they need a
stronger form of RBR soundness (their Section 8.6). A classical-ROM theorem therefore does not
transfer to the QROM automatically, and using a hash-based commitment does not by itself make a
protocol post-quantum secure.

Hashing too little is a known source of real attacks. The "weak Fiat–Shamir" pattern, in which the
hash omits part of the statement or earlier messages, broke Helios [BPW12] and several deployed
proof systems [DMWG23]. Block et al. [BGKTTZ23] prove Fiat–Shamir security of FRI and related
SNARKs. Formal statements of the transformation are a direct way to rule out this class of bug.

### 4.3 Where the pieces sit

```text
IOR (legacy: OracleReduction; interaction layer: Oracle.Reduction)
  |  generalized BCS: commitments + opening arguments per query
  v
interactive reduction (legacy: Reduction)
  |  Fiat–Shamir: challenges from a hash of the statement and messages
  v
non-interactive reduction / argument, relative to a random oracle
```

The legacy layer's `oSpec` parameter (Section 6.4) is what lets the last two stages be stated with
the same `Reduction` type: the random oracle is a shared oracle available to prover and verifier.

## 5. Computational arguments and commitment schemes

Sections 2 to 4 treat the information-theoretic part of a succinct argument and the compilers that
remove its idealization. The argument that comes out is computational: it is sound only against
efficient provers, and only under an assumption about a cryptographic object. This section covers
the computational objects directly. Some protocols are designed in this setting from the start,
with commitments and algebraic structure inside the interaction rather than added by a compiler:
inner-product arguments, lattice-based arguments and folding schemes. Commitment schemes are the
component through which an assumption enters a compiled argument. Both are in ArkLib's scope.
Sections 5.7 and 5.8 cover two stronger security goals that ArkLib plans to address: security
against quantum adversaries, and security under universal composition.

### 5.1 Proofs and arguments

In an interactive proof, soundness holds against every prover, including computationally unbounded
ones. An *argument*, introduced by Brassard, Chaum and Crépeau [BCC88], asks for soundness only
against provers that run in polynomial time. Kilian's and Micali's succinct constructions [Kil92,
Mic94] (Section 2.2) are arguments in this sense.

Soundness of an argument is proved relative to an assumption. The proof turns every malicious
prover $\tilde{P}$ into an adversary $\mathcal{B}$ against the assumption, by an explicit
reduction, such that for every $x \notin \mathcal{L}$

$$\Pr[\langle \tilde{P}, V \rangle(x) = 1] \le \varepsilon_{\mathsf{s}} + \mathsf{Adv}(\mathcal{B}).$$

Here $\varepsilon_{\mathsf{s}}$ is a statistical error, typically from the size of the challenge
sets, and $\mathsf{Adv}(\mathcal{B})$ is the success probability of $\mathcal{B}$ against the
assumption. An asymptotic statement asks that $\mathcal{B}$ run in polynomial time whenever
$\tilde{P}$ does and that the right-hand side be negligible. A concrete statement records both
terms and the running time of $\mathcal{B}$. Knowledge soundness relative to an assumption
(Section 3.1) has the same shape: the probability that the prover succeeds while the extractor
fails to output a witness is at most the knowledge error plus the advantage of a reduction.

Two features recur in the knowledge soundness of computational arguments.

- **Computational special soundness.** From a tree of accepting transcripts (Section 3.4), the
  extractor computes either a witness or a solution to a hard problem. For the discrete-logarithm
  arguments of Bootle, Cerulli, Chaidos, Groth and Petit [BCCGP16], the hard problem is a
  nontrivial discrete-logarithm relation among the generators of the commitment key. For lattice
  arguments such as Greyhound [NS24], it is a short nonzero vector in the kernel of a public
  matrix, that is, a Module-SIS solution, computed from two different openings of one commitment
  [NS24, Lemma 2.11]. The tree-extraction results of Section 3.4 then give knowledge soundness,
  and the hard-problem branch is charged to the assumption.
- **Relaxed relations.** Lattice-based arguments usually cannot extract a witness as short as the
  one the honest prover uses. The extractor recovers a witness for a larger relation
  $\mathcal{R}' \supseteq \mathcal{R}$. LaBRADOR [BS23, Remark 3.4] states completeness for
  $\mathcal{R}$ and knowledge soundness for $\mathcal{R}'$. Greyhound [NS24, Section 2.5] calls
  the extracted commitment openings *weak openings*: each block $i$ carries an invertible challenge
  $c_i$ of small $\ell_1$ norm, and only $c_i \cdot s_i$, not the message block $s_i$ itself, is
  guaranteed to be short. The
  commitment must then be binding with respect to weak openings [NS24, Definition 2.9 and
  Lemma 2.11].

### 5.2 Arguments from computational assumptions

**Discrete logarithms.** Bootle et al. [BCCGP16] give an argument for arithmetic circuit
satisfiability with logarithmic communication and no trusted setup. It is built around an
inner-product argument for Pedersen vector commitments [Ped91], and its soundness rests on the
discrete-logarithm assumption. Bulletproofs [BBBPWM18] shorten the inner-product argument and apply
it to range proofs. In both, the verifier runs in time linear in the size of the commitment key.
Both are public-coin, so Fiat–Shamir (Section 4.2) makes them non-interactive.

**Pairings.** KZG-based SNARKs such as PLONK [GWZC19] and Marlin [CHMMVW20] are compiled from
polynomial IOPs (Section 4.1). Their original security proofs work in the algebraic group model
(Section 5.4). Later analyses prove PLONK knowledge sound in the random oracle model under the
falsifiable assumptions ARSDH and SplitRSDH [LPS25, CGKY25].

**Lattices.** LaBRADOR [BS23] is a recursively amortized proof system for R1CS whose knowledge
soundness rests on Module-SIS. Greyhound [NS24] is a polynomial commitment scheme from standard
lattice assumptions: a three-round evaluation protocol with verifier time $O(\sqrt{N})$ for
polynomials of degree $N$, composed with LaBRADOR to make the evaluation proof polylogarithmic in
$N$. Its knowledge soundness is proved through coordinate-wise special soundness [FMN24]
(Section 3.4). Hachi [NOZ26] builds on Greyhound's inner-outer Ajtai commitment to commit to
multilinear polynomials over extension fields, with a square-root verifier and security from
Module-SIS. Akita [DBK+26] builds on Hachi. It reduces verification time further by committing to
the public setup matrices ahead of time and proving the verifier's deferred work on them against
those commitments, again with security from Module-SIS.

**Folding.** A folding scheme reduces two instances of a relation to one (Section 2.6). Nova
[KST22] folds instances of relaxed R1CS that carry homomorphic commitments, instantiated with
Pedersen commitments under the discrete-logarithm assumption. LatticeFold [BC24] and LatticeFold+
[BC25] fold with lattice commitments under Module-SIS. Their main difficulty is to keep the norm of
extracted witnesses bounded across many folding steps, which the relaxed relations of Section 5.1
would otherwise let grow. In the vocabulary of Section 2.6, a folding scheme is a reduction from a
relation to itself whose knowledge soundness is computational.

### 5.3 Commitment schemes and their security notions

An ordinary commitment scheme has three algorithms: setup samples public parameters, commit maps a
message and randomness to a commitment and an opening, and verify checks an opening against a
commitment. It has two standard security properties.

- **Binding:** no efficient adversary can output one commitment with valid openings to two
  different messages.
- **Hiding:** the commitment reveals nothing about the message: commitments to two messages chosen
  by the adversary are indistinguishable.

Each property can hold perfectly, statistically or computationally, but no scheme is both
perfectly binding and perfectly hiding.

A *polynomial commitment* [KZG10] commits to a polynomial and later proves evaluation claims
$f(z) = y$. A *functional commitment* [LRY16] does the same for a class of functions of the
committed message. Bünz, Fisch and Szepieniec [BFS20] treat the evaluation proof as an interactive
argument for the relation of commitments $C$, points $z$ and values $y$ for which the prover knows
$f$ and randomness $r$ with $C = \mathsf{Commit}(f; r)$ and $f(z) = y$. The security notions for
these schemes refine binding.

- **Evaluation binding** [KZG10]: no efficient adversary can produce accepting evaluation proofs
  for one commitment, one point and two different values.
- **Function binding** [CGKY25]: no efficient adversary can produce accepting evaluation proofs
  for a list of query-answer pairs that no single function in the class satisfies. Two different
  answers to one query form such a list, so function binding implies evaluation binding.
- **Weak binding** [NS24]: binding with respect to the relaxed openings that lattice extractors
  produce (Section 5.1).
- **Extractability**, or knowledge soundness of openings: from an adversary that produces an
  accepting evaluation proof, an extractor recovers a function in the class that is consistent
  with the proved evaluation. Marlin's compiler requires an extractable polynomial commitment
  [CHMMVW20], and [BFS20] asks the evaluation argument to be an argument of knowledge. A
  *straightline* extractor reads only the adversary's commitment and its oracle queries, without
  rewinding.
- **Hiding:** the commitment and the evaluation proofs reveal nothing beyond the proved
  evaluations. Hiding is a sufficient ingredient in compilers such as [CHMMVW20]; Section 5.6
  notes compilers that do without it.

The standard instantiations rest on different assumptions and models.

| Scheme | Binding rests on | Other properties and models |
|---|---|---|
| Pedersen and vector Pedersen [Ped91] | discrete logarithm | perfectly hiding; additively homomorphic; used by [BCCGP16, BBBPWM18, KST22] |
| KZG [KZG10] | evaluation binding from $t$-SDH [BB04, KZG10]; function binding from ARSDH [LPS24, CGKY25] | needs a structured reference string with a secret trapdoor; extractability is proved in the algebraic group model [CHMMVW20]; [KZG10] gives a hiding variant |
| Ajtai [Ajt96] | SIS, or Module-SIS over a polynomial ring [LS15], for short messages | the basic scheme is not hiding; hiding variants add short randomness and rely on Module-LWE [BDLOP18] |
| Inner-outer Ajtai [NS24, NOZ26] | weak binding from Module-SIS | commits to polynomials through a gadget decomposition; openings are proved by the arguments of Section 5.2 |
| Merkle tree [Mer87] | collision resistance of the hash function | in the random oracle model, binding and straightline extractability with bounds in the number of queries [BCS16, CY24]; hiding needs salted leaves |

The pairing and lattice assumptions in the table are search problems.

- **$t$-SDH** ($t$-strong Diffie–Hellman). Given $g, g^{\tau}, \dots, g^{\tau^t}$ in a group of
  prime order $p$ (and, with a pairing, $g_2$ and $g_2^{\tau}$ in a second group), output
  $c \in \mathbb{Z}_p$ and $g^{1/(\tau + c)}$.
- **ARSDH** (adaptive rational strong Diffie–Hellman). Given the same structured reference string
  for degree $D$, output a set $S$ of $D + 1$ field elements and group elements $h_1 \ne 1$ and
  $h_2 = h_1^{1/Z_S(\tau)}$, where $Z_S(X) = \prod_{s \in S}(X - s)$ [LPS24].
- **Module-SIS.** Given a uniformly random matrix $A$ over $R_q = \mathbb{Z}_q[X]/(\varphi)$,
  output a nonzero short vector $z$ with $Az = 0$ [LS15].

### 5.4 Idealized models

Many of these proofs hold in an idealized model of a hash function or a group. A proof in such a
model shows security against every adversary that uses the hash function or the group only through
the model's interface. It says nothing directly about an adversary that exploits the concrete
hash function or the concrete representation of group elements.

**Random oracle model.** In the random oracle model [BR93], every party, including the adversary,
has oracle access to a uniformly random function, and security bounds are stated in the number of
oracle queries. A reduction may observe the adversary's queries, which is how straightline
extractors for Merkle commitments and for Fiat–Shamir arguments work, and some proofs also
program the oracle's answers. Canetti, Goldreich and Halevi [CGH04] show that the model does not
transfer to every concrete hash function: some schemes that are secure in the model are insecure
under every instantiation. Sections 4.2 and 5.7 discuss the quantum random oracle model.

**Generic group model.** In the generic group model, the adversary manipulates group elements only
through the group operation and equality tests. Shoup's model [Sho97] gives the adversary random
encodings of group elements, and Maurer's model [Mau05] gives it handles. Security bounds are then
information-theoretic in the number of group operations. For example, a generic algorithm needs
on the order of $\sqrt{p}$ group operations to compute discrete logarithms in a group of prime
order $p$ [Sho97].

**Algebraic group model.** The algebraic group model of Fuchsbauer, Kiltz and Loss [FKL18] lets the
adversary see real group elements, but requires it to output, with every group element it produces,
a representation of that element as a product of powers of the group elements it has received. A
reduction can read these representations. Proofs in this model therefore reduce to an assumption
such as the discrete logarithm or $q$-DLOG, rather than bounding the adversary outright. The model
sits between the generic group model and the standard model, and Jaeger and Mohan [JM24] study
when a proof in it transfers to the generic group model. Extractability of KZG is the typical
argument in this model: the representation of a commitment over the structured reference string
gives the coefficients of the committed polynomial [CHMMVW20].

**In ArkLib.** ArkLib's games are VCVio oracle computations (Section 7). An experiment is an
`OracleComp` over an oracle specification `oSpec`, and a query implementation decides how each
oracle answers. A random oracle is one such oracle, implemented by sampling on first query and
caching the answer (VCVio's `OracleSpec.randomOracle`). A statement in the random oracle model is
an experiment whose oracle specification contains the random oracle and whose implementation
samples it. Generic and algebraic group models are being consolidated in VCVio
([#1310](https://github.com/Verified-zkEVM/ArkLib/issues/1310)), and ArkLib's own group-model
module defines algebraic representations (Section 5.9).

### 5.5 Stating computational security in Lean

A Lean function has no resource bound. A statement "every adversary has advantage at most
$\varepsilon$" therefore quantifies over computationally unbounded adversaries, and for a
computational assumption such a statement is false. ArkLib proves this for its pairing
assumptions: `Groups.not_tSdhAssumption_univ` shows that $t$-SDH over all Lean adversaries cannot
have error below 1 when the verifier's generator is nontrivial, because a classical inverse of the
exponent map recovers the trapdoor from the structured reference string.
`Groups.not_arsdhAssumption_univ` is the corresponding result for ARSDH, under its stated
hypotheses.

ArkLib therefore states computational security as an explicit reduction. For each adversary
against the scheme, the theorem constructs an adversary against the assumption, and bounds the
first adversary's advantage by the second adversary's success probability. The theorem holds for
each adversary and relates its advantage to that of its constructed reduction, without assuming a
uniformly small hardness bound over unrestricted adversaries.

- `KZG.CommitmentScheme.binding_reduces_to_tSdh` bounds the evaluation-binding advantage of any
  adversary against KZG by the $t$-SDH success probability of `KZG.CommitmentScheme.bindingReduction`
  applied to it.
- `KZG.CommitmentScheme.function_binding_reduces_to_arsdh` does the same for function binding and
  ARSDH, following [CGKY25].
- `ArkLib.Lattices.Ajtai.Simple.bindingAdvantage_le_moduleSIS` bounds the binding advantage of the
  simple Ajtai commitment by a Module-SIS advantage.

A corollary such as `KZG.CommitmentScheme.binding` then assumes the hardness bound over an explicit
class of adversaries (`Groups.tSdhAssumption` takes the class as an argument) and requires the
reduction to belong to that class. The corollary is as strong as the class one can justify, for
example generic, algebraic or resource-bounded adversaries. VCVio also provides asymptotic
vocabulary in `VCVio/CryptoFoundations/Asymptotics/`: security games indexed by a security
parameter, reductions with polynomial loss, and a backend-relative notion of polynomial time.

### 5.6 Commitments and oracle reductions

Section 4.1 describes how ArkLib combines the two halves: each oracle interface is paired with a
functional commitment for that interface, every oracle message is replaced by a commitment, and
every verifier query is replaced by a run of the commitment's opening argument. The resulting
interactive reduction is an argument. It inherits the assumptions and model of both the input
reduction and the commitment, together with those required by any later Fiat–Shamir step. For an
information-theoretic input, the computational assumptions enter through the commitment.
Interactive Merkle-based arguments can be analyzed in the standard model under suitable hash
assumptions: collision resistance classically [Kil92], and collapsing against quantum provers
[CMSZ21, CDDGS25]. The non-interactive BCS analysis uses the random oracle model. KZG
instantiations rest on pairing assumptions, in the algebraic group model or under ARSDH, and
Greyhound, Hachi or Akita on Module-SIS; in each case the compiled argument needs the particular
binding or extraction assumption of the chosen compiler theorem.

Each security goal of the compiled argument draws on a different commitment property.

- **Soundness** needs a binding-type property that fixes the oracle the verifier queries. For
  state-restoration soundness of the interactive argument, which the later Fiat–Shamir step uses,
  Chiesa, Guan, Knabenhans and Yu [CGKY25] use state-restoration function binding, under the
  query-class conditions described in Section 4.1.
- **Knowledge soundness** classically uses extractability, so that the extractor of the oracle
  reduction can be run on extracted messages [CHMMVW20, BFS20]. For Merkle trees in the random
  oracle model, the extractor reads the committed messages from the prover's queries [BCS16, CY24].
  For state-restoration knowledge soundness, [CGKY25, Theorem 7.1] needs no separate
  extractability property. It uses state-restoration function binding of the commitment together
  with state-restoration knowledge soundness of the functional IOP, with the query-class tail
  errors and resource conditions described in Section 4.1.
- **Zero knowledge.** A standard route combines a suitably zero-knowledge oracle reduction
  (Section 3.5) with hiding commitments and zero-knowledge openings. Other compilers can use
  non-hiding commitments when masking and the polynomial IOP's simulation guarantees cover the
  additional leakage [KPT23].

A lattice commitment whose opening argument extracts only weak openings (Section 5.1) adds a
further obligation. The extracted message is determined only by weak binding, so knowledge
soundness of the compiled argument is naturally stated for a relaxed relation. Section 4.1 explains
why the construction alone is not a security theorem, and the
[oracle-elimination compiler design](docs/design/04-oracle-elimination-compiler.md) records the
obligations ArkLib's compiler places on the commitment.

### 5.7 Post-quantum security in the quantum random oracle model

A post-quantum argument must stay sound against provers that run on a quantum computer. Hash
functions are public code, so such a prover can evaluate the hash function on a superposition of
inputs. Boneh et al. [BDF+11] argue that post-quantum security in the random oracle model must
therefore be proved in the *quantum random oracle model* (QROM), where the adversary queries the
oracle in superposition. They separate the two models with a scheme that is secure against
classical oracle access but insecure against quantum access, and they identify *history-free*
reductions as a class of classical proofs that carry over.

Most classical random-oracle proofs use one of four techniques, and each breaks in the QROM.

- **Lazy sampling.** A classical simulator samples the oracle's answer when a point is first
  queried. A superposition query touches every point at once.
- **Recording queries.** A classical reduction reads the adversary's queries, for example to
  extract the committed messages of a Merkle tree. Copying a quantum query would measure it and
  disturb the adversary's state.
- **Programming the oracle.** Fiat–Shamir proofs set the oracle's answer at a point the adversary
  is about to use. With quantum queries, the adversary may already have queried that point in
  superposition.
- **Rewinding.** Special-soundness extractors run the prover again from an earlier state with new
  challenges. A quantum prover's state cannot be copied, and recording its answer disturbs it.
  This last problem does not involve a random oracle and affects interactive arguments in the
  standard model too.

**Compressed oracles.** Zhandry [Zha19] overcomes the recording barrier. Viewed in the Fourier
basis, a query writes to the oracle's register rather than to the adversary's, so a purified
oracle can be simulated by a sparse quantum database encoding the oracle's interaction with the
adversary. This database is a quantum register, generally in superposition, not a classical log.
Without extraction measurements, the compressed oracle is perfectly indistinguishable from the
random oracle for every adversary. Chung, Fehr, Huang and Liao [CFHL21] give an abstract
exposition of the technique, extend it to parallel queries, and give a framework in which quantum
query lower bounds follow from classical reasoning. Don, Fehr, Majenz and Schaffner [DFMS22a]
extract hash preimages *online*, without rewinding. A commutator bound shows that the compressed
oracle's evolution and the extraction measurement almost commute, which bounds the disturbance
that extraction causes. They apply this to commit-and-open Σ-protocols [DFMS22a, DFMS22b],
including Merkle-tree commitments [DFMS22b]. Grilo, Hövelmanns, Hülsing and Majenz [GHHM21] bound the
advantage of distinguishing an adaptively reprogrammed quantum random oracle from an untouched one,
and show the bound is tight.

**Fiat–Shamir in the QROM.** Unruh [Unr15] gives a transformation from Σ-protocols to
non-interactive zero-knowledge proofs of knowledge that is secure against quantum adversaries; the
Fiat–Shamir and Fischlin constructions were then known to be secure only against classical
adversaries. Don, Fehr, Majenz and Schaffner [DFMS19] then
reduce any quantum prover against the Fiat–Shamir transformation of a Σ-protocol in the QROM to a
quantum prover against the Σ-protocol itself, with a loss quadratic in the number of queries, so
soundness and proofs of knowledge against quantum provers are preserved. Liu and Zhandry [LZ19]
give mild conditions under which Fiat–Shamir is secure in the quantum setting, and
show that existing lattice signatures based on Fiat–Shamir are secure without modification. Don,
Fehr and Majenz [DFM20] extend measure-and-reprogram to multi-round protocols: for $n$ verifier
challenges the loss is $O(q^{2n})$ for fixed $n$, optimal up to a factor depending only on $n$.
Unruh [Unr17] shows that Fiat–Shamir is a zero-knowledge, simulation-sound proof system against
quantum adversaries when the Σ-protocol has computational zero knowledge and statistical soundness,
without showing that it is a proof of knowledge.

**Succinct arguments from IOPs.** Chiesa, Manohar and Spooner [CMS19] give the first evidence that
hash-based succinct arguments are post-quantum secure. They prove that Micali's construction is
unconditionally secure in the QROM and inherits the zero knowledge and proof of knowledge of the
PCP, and that the BCS construction is secure in the QROM when the IOP is round-by-round sound
(Section 4.2 gives their bounds). Their main tool is a lifting lemma that derives security against
quantum attackers from a classical property of the oracle game. Fractal [COS20] builds post-quantum,
transparent recursive proofs from a preprocessing zkSNARK obtained from holographic proofs. Chiesa, Di, Hu and Zheng
[CDHZ26] extend the analysis from IOPs to interactive oracle reductions. They prove that hash-based
succinct non-interactive reductions built from IORs are secure in the QROM when the IOR satisfies a
post-quantum analogue of state-restoration security, which round-by-round security implies. They
also obtain adaptively secure straightline quantum extraction, and they structure the proof around
a quantum extraction property of vector commitments that Merkle commitments satisfy, as in the
classical analysis. For a particular IOP, such as FRI, STIR or WHIR, these theorems reduce the
post-quantum security of the compiled SNARG to classical round-by-round (knowledge) soundness of
the IOP.

**Quantum rewinding.** Without a random oracle, the obstacle is rewinding. Watrous [Wat09]
introduces quantum rewinding for zero-knowledge *simulation*: he shows that protocols such as the
Goldreich–Micali–Wigderson graph-isomorphism protocol remain zero knowledge against quantum
verifiers. Knowledge *extraction* is harder, because the extractor must obtain several accepting
answers from one quantum prover. Ambainis, Rosmanis and Unruh [ARU14] show, relative to an oracle, that classically secure proofs of knowledge, including
Σ-protocols and the Fiat–Shamir construction, can be insecure against quantum adversaries, and
that ordinary computational binding gives almost no guarantee in the quantum setting. Unruh
[Unr12] gives a quantum rewinding technique for extraction and criteria under which a classical
proof of knowledge is a quantum proof of knowledge. He later defines *collapse-binding* commitments
[Unr16], a binding notion that works with rewinding. Chiesa, Ma, Spooner and Zhandry [CMSZ21]
prove that Kilian's succinct argument is post-quantum secure in the standard model when
instantiated with a non-adaptive PCP and any collapsing hash function, using a rewinding
procedure that obtains as many accepting transcripts as needed. Lombardi, Ma and Spooner [LMS22b] extract
information from several runs of a quantum adversary without disturbing its state, and use this
for post-quantum zero knowledge. Lai, Malavolta and Spooner [LMS22a] rewind across many rounds and
prove post-quantum knowledge soundness for multi-round protocols that satisfy *recursive special
soundness* and *last-round collapsing*. Chiesa, Dall'Agnol, Di, Guan and Spooner [CDDGS25] prove
post-quantum soundness of interactive BCS for public-coin semi-adaptive IOPs, in which a query to
the prover's round-$i$ message does not depend on answers from later rounds, using vector
commitments that are *collapse position binding*. Their knowledge-soundness theorem additionally
assumes post-quantum knowledge soundness of the IOP. The reduction extracts a quantum algorithm
implementing the IOP adversary, and the theorem does not cover fully adaptive IOP verifiers.
Collapse position binding is not the vector-commitment collapsing notion of [CMSZ21]: the two are
formally incomparable, and unlike the earlier notion, collapse position binding implies
post-quantum position binding. Merkle commitments from collapsing hash functions satisfy it.

**Lattice-based arguments.** Module-SIS is believed to be hard for quantum algorithms, but a
lattice argument is post-quantum knowledge sound only if its extractor works against quantum
provers. Bootle, Lyubashevsky, Nguyen and Seiler [BLNS20] adapt the folding technique of
Bulletproofs to lattices, and [ACK21] tightens their knowledge error against classical provers.
For the lattice-Bulletproofs protocols covered by [LMS22a], post-quantum knowledge soundness
follows under quantum (Ring-)LWE, used to establish fold-collapsing; Module-SIS hardness alone is
not the hypothesis of that result. For Fiat–Shamir versions, the QROM results above apply to
protocols that satisfy their hypotheses. Classical knowledge-soundness analyses, such as the analysis of non-interactive LaBRADOR by Aardal
et al. [AABKT24], do not by themselves give post-quantum security. Whether a given lattice argument,
such as Greyhound or Hachi, meets the hypotheses of a quantum extraction theorem has to be checked
protocol by protocol.

**In VCVio.** As of October 2026, VCVio provides quantum-program and QROM foundations on top of
[QuantumFoundations](https://github.com/lean-crypto-foundations/QuantumFoundations), a Mathlib-only
library of completely positive maps, instruments, pure states and oracle unitaries. Its main
branch contains quantum programs and runtimes with the QROM, the compressed random oracle with
commutator bounds, query-mass and hybrid arguments, and vector commitments with multi-extractability
of salted Merkle trees against quantum adversaries. Its
[quantum-layer design note](https://github.com/Verified-zkEVM/VCVio/blob/main/docs/design/quantum-layer.md)
records the model, its limitations and the open work. ArkLib has no quantum definitions; the
results described below remain planned. For ArkLib's implementation status, read
[ROADMAP.md](ROADMAP.md) and [docs/design/00-current-status.md](docs/design/00-current-status.md).

**Planned for ArkLib.** ArkLib plans to prove post-quantum soundness and knowledge soundness of
hash-based SNARGs in the QROM: the BCS transformation with Merkle commitments, from round-by-round
soundness and round-by-round knowledge soundness of the oracle reduction, following [CMS19] and its
extension to reductions [CDHZ26], and building on VCVio's QROM results for vector commitments.
It also plans the Fiat–Shamir transformation of oracle reductions in the QROM, and post-quantum
security of the lattice-based commitments of Section 5.3. None of this is formalized yet.

### 5.8 Universal composability

Knowledge soundness and zero knowledge are *standalone* notions: they describe one execution of a
protocol in isolation. Canetti's universal composability (UC) framework [Can01] instead compares a
protocol $\pi$ with an *ideal functionality* $\mathcal{F}$, a trusted party that performs the task
by definition. The protocol *UC-realizes* $\mathcal{F}$ if for every adversary attacking $\pi$
there is a simulator attacking $\mathcal{F}$ such that no environment, which chooses the inputs and
sees the outputs and interacts with the adversary throughout, can tell the two worlds apart. The
composition theorem then lets any larger protocol that uses $\mathcal{F}$ use $\pi$ instead.
Canetti, Dodis, Pass and Walfish [CDPW07] extend the framework to setups shared by all protocols,
such as one hash function used everywhere (generalized UC, or GUC).

Standalone knowledge soundness does not compose in this sense, for two reasons.

- **Rewinding.** A UC simulator cannot rewind the environment, so it must extract witnesses from
  proofs it sees *straightline*, without rewinding. Most knowledge-soundness proofs rewind
  (Section 3.4).
- **Malleability.** An adversary that sees honest proofs may transform them into proofs of related
  statements without knowing a witness. Knowledge soundness says nothing about an adversary that
  sees other proofs. *Simulation extractability* requires extraction to succeed even after the
  adversary has seen simulated proofs of statements of its choice.

A UC proof for a SNARK in the random oracle model must also say what the oracle is. A random oracle
local to one protocol, which the simulator can program and observe freely, does not model one hash
function shared by many protocols; a global random oracle restricts what the simulator may do.

**Global random oracles and straightline extraction.** Pass [Pas03] studies zero knowledge in the
random oracle model when the simulator may not program the oracle, motivated by deniability.
Fischlin [Fis05] gives non-interactive proofs of knowledge with online, that is straightline,
extractors in the random oracle model. Canetti, Jain and Scafuro [CJS14] obtain UC commitments,
zero knowledge and general secure computation from a single global, non-programmable random
oracle. Camenisch et al. [CDGLN18] study alternative global random oracles, which allow restricted
programming or observation of queries, and show that these let practical protocols, such as the
commitment $H(m \Vert r)$ and Schnorr signatures, be proved GUC-secure. Lysyanskaya and Rosenbloom
[LR22] determine the minimal properties needed for GUC non-interactive zero-knowledge proofs of
knowledge in any global random-oracle model, and construct efficient ones in the restricted
programmable and restricted observable models. Zhou et al. [ZZZR22] give impossibility and
feasibility results for GUC commitments from global random oracles. Chen et al. [CDGMSS25] give a
compiler that makes a Σ-protocol for an algebraic relation straightline extractable using an
additively homomorphic encryption scheme, without the repetitions that Fischlin's and Pass's
transformations need; applying Fiat–Shamir then gives a UC-secure NIZK in the local random oracle
model, where each protocol instance has its own programmable oracle, rather than with a global
one. Instantiated with class-group encryption whose public key is sampled obliviously by hashing,
it needs no common reference string.

**SNARKs in the random oracle model.** Chiesa and Fenzi [CF24] prove that zkSNARKs in the random
oracle model can be UC-secure *unconditionally*, meaning against adversaries that make a bounded
number of oracle queries and are otherwise unbounded. Their setup is the observable and restricted
programmable global random oracle of [CDGLN18], in the formulation of [LR22]. They prove this for
Micali's construction and for the BCS construction without modification, in contrast to prior
transformations that rely on computational assumptions and often lose succinctness. Badertscher et al. [BCCRS24] obtain
logarithmic, witness-succinct UC NIZKs with a global non-programmable random oracle by defining
their NIZK functionality in the shielded super-polynomial-oracle model of Broadnax et al.
[BDHMN17]. They state that this functionality preserves the usual soundness and
zero-knowledge properties and its compositional guarantees. They observe that among the
formalizations of [CDGLN18] their choice of setup is necessary for this result. They also give a construction based on [CF24] and show that it achieves a
slightly weaker version of their NIZK functionality.

Canetti and Chen [CC25, Section 3 and Appendix A] question the modular-security usefulness of
the programmable global random oracle of [CDGLN18], which [LR22] and [CF24] build on. In that
oracle any party, including the adversary, may program a point that has not been queried, and a
protocol party can ask through the `IsProgrammed` interface whether a point in its own session's
input space was programmed; the environment and the adversary cannot ask. A simulator for a
subprotocol may therefore program a point in another session's input space without invalidating
the proof that the subprotocol realizes its functionality. A surrounding protocol in that other
session can detect this programming, and so behave differently once the functionality is replaced
by the subprotocol; their example exposes a secret witness in one of the two executions. They
state that this side channel through the shared setup neither contradicts the UC composition
theorem nor refutes the proof that the subprotocol realizes its stated functionality.

They propose a global random oracle that confines privileged observation and programming to ideal
functionalities, each within its own session namespace: only an ideal functionality may observe or
program the oracle, only at inputs that begin with its own session identifier, and it may delegate
this to its simulator under its own policy. In that model they give UC-secure non-interactive
succinct commitments and vector commitments, and realize vector commitments by Merkle trees with
a separate commitment instance, and hence a separate session identifier, at each node. They prove
that the resulting variant of the Kilian–Micali zkSNARK, built from an honest-verifier
zero-knowledge extractable PCP, UC-realizes their adaptation of the NIZK functionality of [CF24].
Their security loss is linear in the PCP length $n$ and quadratic in the number $t$ of the
environment's oracle calls, against quadratic in $n$ and cubic in $t$ in [CF24]. They attribute
the improvement to their modular treatment of vector commitments; the per-node session
identifiers domain-separate the Merkle nodes and rule out collisions across nodes. A UC claim in this area must therefore specify both the
NIZK functionality and the global-oracle interface, including the access available to surrounding
protocols.

**Generic lifting through simulation extractability.** Another approach compiles a
simulation-extractable SNARK into a UC-secure one. C∅C∅ [KZM+15] applies strengthening
transformations to SNARKs to obtain UC-composable zero-knowledge proofs. Groth and Maller [GM17]
construct a pairing-based simulation-extractable SNARK and relate such SNARKs to signatures of
knowledge. Lift-and-Shift [ARS20] obtains simulation extractability generically for SNARKs with
subversion-resistant or updatable setup, and Abdolmaleki et al. [AGRS24] obtain UC-secure NIZKs
with updatable setup whose proofs grow with the witness. Ganesh et al. [GKOPTT23] give a compiler
that lifts any simulation-extractable NIZK argument of knowledge to a UC-secure one in the global
random oracle model while preserving witness succinctness, which with existing zkSNARKs gives the
first UC-secure zkSNARKs with constant-size proofs. Roustaeifar et al. [RZM+26] compose a
simulation-extractable zkSNARK with a key-updatable polynomial commitment to obtain UC security
with updatable setup.

**Simulation extractability of deployed SNARKs.** A line of work proves simulation extractability
of SNARKs as they are deployed, which is the input to the compilers above. These results use
different adversary models.

- **Bulletproofs and Spartan.** Ganesh et al. [GOPTT22] prove Fiat–Shamir Bulletproofs
  non-malleable in the algebraic group model; their later journal version is titled
  *... (in the Random Oracle Model)*. Dao and Grubbs [DG23] establish simulation extractability of
  Spartan and Bulletproofs under the discrete-logarithm assumption in the random oracle model,
  without the algebraic group model.
- **Polynomial IOPs with KZG.** Ganesh et al. [GKKNZ22] analyze simulation extractability of
  Plonk, Sonic and Marlin with updatable setup. Later, Kohlweiss, Pancholi and Takahashi
  [KPT23, Section 5] identify a gap in that Marlin unique-response analysis and in the claimed
  perfect trapdoorless simulation for Plonk with deterministic KZG. Their modular compiler
  establishes trapdoorless zero knowledge and weak unique responses under explicit conditions on
  the polynomial IOP and the commitment; knowledge soundness is an additional input to the
  simulation-extractability argument. Their case studies use a modified Marlin PIOP and randomized
  KZG for Plonk. Faonio et al. [FFKRZ23] define simulation extractability for the opening and
  evaluation proofs of polynomial commitments and use it to compile simulation-extractable
  zkSNARKs from polynomial IOPs such as Plonk and Marlin.
- **Optimized Plonk and Marlin.** Faonio, Fiore and Russo [FFR24] treat the optimized variants of
  Plonk and Marlin implemented in practice, including the linearization trick, which the earlier
  results for textbook or modified protocols [FFKRZ23, KPT23] do not cover. Their analysis uses
  a random oracle and the algebraic group model with oblivious sampling. For Plonk, Lipmaa
  [Lip25] obtains simulation extractability in the random oracle model under falsifiable
  assumptions, without the algebraic group model, building on [LPS25].
- **Sumcheck-based SNARKs.** Faonio and Russo [FR26] treat sumcheck-based zkSNARKs such as
  HyperPlonk, Spartan and Libra, for which the PST commitment satisfies a controlled form of
  malleability instead.

**The algebraic group model.** Anthoine, Fiore and Pancholi [AFP26] identify mostly standard
properties of a zkSNARK proved secure in the algebraic group model (optionally with a random
oracle) that imply UC security, check them using the formulation of the model by Jaeger and Mohan
[JM24], and conclude that Plonk and Marlin are UC-secure without overhead.

**Quantum adversaries.** Unruh [Unr10] gives a quantum version of the UC model with the same
composition guarantees, and shows that every statistically UC-secure classical protocol is also
statistically quantum UC-secure. Straightline extraction against quantum adversaries is available in the QROM
[DFMS22a, CDHZ26] (Section 5.7), which is the extraction a UC simulator needs.

**Open questions.** The literature does not yet agree on one global random oracle. [CJS14] uses a
non-programmable oracle; [CDGLN18] and [LR22] use restricted programmable and restricted
observable ones; [BCCRS24] find their setup necessary for their result among the formulations of
[CDGLN18]; and [CC25] identify the `IsProgrammed` side channel described above in the programmable
oracle that [LR22] and [CF24] build on, and propose a session-scoped formulation. The NIZK
functionality also differs between works. Each theorem holds for the functionality and setup its
paper fixes, so results stated for different global random oracles or NIZK functionalities are not
directly comparable.

**Machine-checked UC.** EasyUC [CSV19] mechanizes UC proofs in EasyCrypt. Lochbihler et al.
[LSBM19] formalize constructive cryptography, a composable framework, in CryptHOL. IPDL [GSFSM23]
is a core calculus for equational proofs of cryptographic protocols. SSProve (Section 7)
gives modular proofs through state-separating packages.

**In VCVio and ArkLib.** VCVio has a UC layer under
[`VCVio/Interaction/UC/`](https://github.com/Verified-zkEVM/VCVio/tree/main/VCVio/Interaction/UC),
built on PolyFun's theory of open systems. It states Canetti-style protocols, functionalities,
adversaries, environments, simulators and the execution experiment (`UCSecure`, `EXEC`), a
total-variation emulation relation over all plugs, with composition theorems
(`ObservedCompEmulates`), an asymptotic wrapper parameterized by a supplied PPT predicate
(`AsympObservedCompEmulates`), and a one-time-pad example. Its
[design note](https://github.com/Verified-zkEVM/VCVio/blob/main/docs/design/uc-campaign.md)
records computational UC from routed execution as work in progress. VCVio has no functionality for
non-interactive arguments yet, and ArkLib has no UC definitions.

**Planned for ArkLib.** ArkLib plans to prove UC security of SNARKs built from interactive oracle
reductions, starting with compilations in the random oracle model whose extractors are
straightline, following Chiesa and Fenzi [CF24]. The formalization must first fix the
global-oracle and NIZK functionalities, taking account of the modeling issue identified by [CC25].
None of this is formalized yet.

### 5.9 Where these objects sit in ArkLib

- **Functional commitments.**
  [`Commitments/Functional/Basic.lean`](ArkLib/Commitments/Functional/Basic.lean) defines
  `Commitment.Scheme`: key generation, commitment, and an opening argument that is a legacy-layer
  `Proof` relative to `oSpec`, for the data's oracle interface. Its games are
  `Commitment.correctness`, `Commitment.binding` (evaluation binding),
  `Commitment.functionBinding` (adapted from [CGKY25]) and `Commitment.extractability`, whose
  straightline extractor sees the commitment and the log of the committer's oracle queries. The
  setup and commitment phases run in the oracle state that later phases continue from.
  `Commitment.binding` bounds the experiment for every adversary; computational schemes such as
  KZG instead bound `Commitment.bindingExperiment` adversary by adversary (Section 5.5).
- **KZG.** [`Commitments/Functional/KZG/`](ArkLib/Commitments/Functional/KZG/) defines the scheme
  (`KZG.CommitmentScheme.kzg`), the $t$-SDH and ARSDH games (`Groups.tSdhExperiment`,
  `Groups.arsdhExperiment`) and the reductions of Section 5.5.
- **Lattice commitments.** [`Commitments/Ordinary/Ajtai/`](ArkLib/Commitments/Ordinary/Ajtai/) has
  the simple Ajtai commitment, and [`Data/Lattices/ModuleSIS.lean`](ArkLib/Data/Lattices/ModuleSIS.lean)
  the Module-SIS game. [`Commitments/Functional/Hachi/`](ArkLib/Commitments/Functional/Hachi/)
  formalizes the nonrecursive Hachi opening argument [NOZ26]. Its weak-binding reduction to Module-SIS is
  `ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding.advantage_le_moduleSIS`. Its soundness is
  coordinate-wise special soundness with *escape events*
  (`Verifier.coordinateWiseSpecialSoundWithEscape`, `ProtocolSpec.ChallengeTree.EscapeEvent`): on
  every structured accepting tree, either the extractor produces a witness or the tree exhibits the
  escape event. The documented contract of `EscapeEvent` requires every such event to yield a
  break of the ambient assumption, so this is the computational special soundness of
  Section 5.1.
- **BitZ.** [`Commitments/Functional/BitZ/`](ArkLib/Commitments/Functional/BitZ/) holds algebraic
  and probabilistic lemmas for the BitZ commitment [BGKLSW26].
- **Ordinary commitments.**
  [`Commitments/Ordinary/Basic.lean`](ArkLib/Commitments/Ordinary/Basic.lean) re-exports VCVio's
  `CommitmentScheme` with its hiding, binding and trapdoor-extraction games
  (`CommitmentScheme.hidingGame`, `CommitmentScheme.bindingExperiment`, `TrapdoorExtractor`).
  [`Commitments/Ordinary/SimpleRO.lean`](ArkLib/Commitments/Ordinary/SimpleRO.lean) is a hash
  commitment with the random oracle sampled as a function.
- **Group models.** [`ArkLib/AGM/`](ArkLib/AGM/) defines `AGM.GroupRepresentation`, the
  representation an algebraic adversary reports with each group element.
- **Hash-based building blocks.** VCVio has collision resistance
  (`VCVio/CryptoFoundations/HardnessAssumptions/CollisionResistance.lean`) and Merkle-tree
  extractability in the random oracle model (`VCVio/CryptoFoundations/MerkleTree/`).

For which of these results are proved, and under which hypotheses, read
[ROADMAP.md](ROADMAP.md#protocols-and-commitments) and
[docs/design/00-current-status.md](docs/design/00-current-status.md). The Akita formalization is
tracked in [#1378](https://github.com/Verified-zkEVM/ArkLib/issues/1378).

## 6. ArkLib's oracle reductions compared with the literature

The module documentation of
[`OracleReduction/Basic.lean`](ArkLib/OracleReduction/Basic.lean) says that ArkLib's formulation of
IORs "can be seen in the literature as **F-IORs**, where `F` denotes an arbitrary class of
oracles". The name follows the $\mathcal{F}$-IOPs of WHIR (Section 2.5): an $\mathcal{F}$-IOR is
an interactive oracle reduction in which each oracle comes with its own query interface from the
class $\mathcal{F}$. This section makes that precise for the legacy layer, compares it with Section 2's
definitions, and then explains what changes in the interaction layer. It describes definitions,
not results.

### 6.1 The legacy definition

A **protocol specification** `ProtocolSpec n`
([`ProtocolSpec/Basic.lean`](ArkLib/OracleReduction/ProtocolSpec/Basic.lean)) is a list of $n$
rounds, each with a direction (`.P_to_V` or `.V_to_P`) and a message type:

$$
\mathsf{pSpec} = \bigl( (d_0, T_0), \dots, (d_{n-1}, T_{n-1}) \bigr), \qquad d_i \in \{\mathsf{P{\to}V}, \mathsf{V{\to}P}\}.
$$

Rounds need not alternate, and message types are arbitrary Lean types. Prover rounds are
`MessageIdx`, verifier rounds are `ChallengeIdx`.

An **oracle reduction** `OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec`
has the following parts.

- A shared oracle `oSpec : OracleSpec ι` that both parties may query. In security games it is
  implemented by a stateful handler `impl : QueryImpl oSpec (StateT σ ProbComp)` started from
  `init : ProbComp σ`, which covers, for example, a lazily sampled random oracle.
- Input data: a public statement `StmtIn`, a family of input oracle statements `OStmtIn i`, each
  with an `OracleInterface`, and a private witness `WitIn`.
- A prover (`Prover`, and `OracleProver` when the input includes oracle statements) that sends
  messages, receives challenges, and outputs `StmtOut × WitOut` together with the output oracle
  statements. Its computations are `OracleComp oSpec` programs.
- An oracle verifier (`OracleVerifier`) whose decision procedure is

  ```lean
  verify : StmtIn → pSpec.Challenges →
    OptionT (OracleComp (oSpec + ([OStmtIn]ₒ + [pSpec.Message]ₒ))) StmtOut
  ```

  It receives the challenges, may query `oSpec`, the input oracles and every prover message
  through their interfaces, and either fails or outputs a new statement.
- An output-oracle specification `outputOracle`, which is one of two things:
  - an `OracleOutputEmbedding`: each output oracle *is* an input oracle or a prover message,
    given by an injection `ιₛₒ ↪ ιₛᵢ ⊕ pSpec.MessageIdx`;
  - an `OracleOutputSimulation`: each output oracle is a *virtual oracle* whose queries are
    answered by an `OracleComp` program over the input oracles and messages, which may depend on
    the challenges, together with an agreement law relating it to the materialized output.

The verifier is public-coin: challenges are sampled uniformly and are part of the transcript, and
the verifier has no private randomness beyond what `oSpec` provides. The special cases have their
own names: `Reduction` (no oracles), `Proof` and `OracleProof` (Boolean output, trivial output
witness and, for `OracleProof`, no output oracles), and `NonInteractiveReduction`. An `Indexer`
encodes an index into oracle form for holographic protocols. `OracleVerifier.toVerifier` turns an
oracle verifier into an ordinary one by answering every query from the full data; security notions
for oracle reductions are defined through this map (Section 6.4).

### 6.2 What 𝓕 means: oracle interfaces

The class of oracles is not fixed. Each message type carries an instance of
`OracleInterface` ([`OracleReduction/OracleInterface.lean`](ArkLib/OracleReduction/OracleInterface.lean)),
which declares a query type `Query` and, for each query $q$, a response type `Response q`, together
with an answer function. In the notation of WHIR's Definition 7.1, the message type plays the role
of an oracle set $\mathcal{O}_{i,j}$, `Query` the role of $\mathcal{W}_{i,j}$, and the answer
function the role of $F_{i,j}$. WHIR also specifies an interface per oracle. ArkLib packages
interfaces by Lean types and supports response types that depend on the query, where WHIR's answers
all lie in one alphabet $\Sigma$.

The library provides the following interfaces, among others. They are examples, not a realization
of every model in Section 2.5.

| Instance | Message | Query | Model it captures |
|---|---|---|---|
| `instFunction` | a function $\alpha \to \beta$ | a point of $\alpha$ | point-query IOP |
| `instVector`, `instListVector` | a vector | an index | point-query IOP over a fixed alphabet |
| `instPolynomial` | $R[X]$ | a point of $R$ | univariate polynomial IOP |
| `instPolynomialDegreeLE`, `instPolynomialDegreeLT` | $R[X]_{\le d}$, $R[X]_{< d}$ | a point of $R$ | polynomial IOP with a degree promise |
| `instMvPolynomial`, `instMvPolynomialDegreeLE` | multivariate polynomials | a point of $R^n$ | multilinear and multivariate polynomial IOPs |
| `instProd` | a pair | a query to either component | several oracles in one message |
| `instTensorProd` | a pair | a pair of queries | two oracles queried together |
| `instDefault` | any type | the unique query `()` | a message read in full |

`instTensorProd` combines two answer interfaces and returns the pair of answers. It is not by
itself the linear-query interface of tensor IOPs [BCG20]. ILC, tensor inner-product and
$\Sigma$-IOP queries each require their own answer functions.

`instDefault` returns the whole message, so a message read in full is the special case of an oracle
message whose only query reveals everything. It is not a registered instance; a protocol opts in
explicitly. This is how ArkLib covers Arc's informal Remark 5.1 about non-oracle messages, and how
an ordinary interactive reduction is an IOR in which every message uses this interface.

### 6.3 Comparison table

| | IOP [BCS16] | Oracle reduction [BCGGRS19] | RoK [KP23] | IOR [BMNW25] | $\mathcal{F}$-IOP [ACFY25] | ArkLib legacy layer | ArkLib interaction layer |
|---|---|---|---|---|---|---|---|
| Verifier output | accept / reject | instances and virtual oracles | new statement | new instance with oracles | accept / reject | new statement and oracle statements, or failure | new statement and claim over the accumulated oracles |
| Input oracles | no (IOPP: input oracle) | no | no | instance strings and index string | yes: input string $y$ | `OStmtIn`, any interfaces | input oracle resources, any interfaces |
| Oracle class | symbols of a string | symbols of a string | none | symbols of a string | per-oracle $F_{i,j}$, common answer alphabet $\Sigma$ | per-message `OracleInterface` | per-node `OracleInterface` |
| Verifier queries | point queries to received strings | none in the verifier; virtual oracles are non-adaptive | n/a | queries may be adaptive; deferred to a final query phase | non-adaptive | adaptive `OracleComp`; `OracleVerifier.NonAdaptive` as a special form | adaptive, may run after each received message |
| Output oracles | none | virtual oracles with bounded locality | n/a | selected from instance and proof oracles | none | embedding or simulated virtual oracle | open claims as query programs (`OpenClaim`) |
| Separate full-message access primitive | no; may query all symbols at their query cost | no | yes (all messages) | informal remark (Remark 5.1) | no | `instDefault` | public nodes |
| Round structure | alternating | alternating | interactive | alternating | alternating | arbitrary direction list | a tree; later rounds may depend on earlier public values |
| Verifier randomness | public coin (for BCS) | public coin optional; the paper's constructions are public coin | public coin optional | public coin | public coin | public-coin challenges | verifier moves are strategy outputs; security is stated for a challenge model |
| Shared oracle (e.g. RO) | no | no | RO variant | none in the information-theoretic IOR; RO in the compiled committed relation | no | `oSpec` | ambient oracle spec |
| Holography | no | no | no (public parameters from a generator) | indexer | no | `Indexer` | not built in |
| Soundness target | language | proximity to output relation | knowledge | language, RBR, RBR knowledge, over exact and relaxed promise relations | language or proximity, as specified by the relation and error | language, relation, knowledge, RBR, RBR knowledge | RBR soundness, RBR knowledge certificates, state restoration |

The table compresses definitions with different conventions; the notes below explain the entries
that matter most when transferring a theorem.

### 6.4 Differences in detail

**Queries and output oracles.** The oracle reductions of [BCGGRS19] separate an interaction phase
from a set of virtual oracles with bounded locality. The verifier outputs their descriptions after
the interaction, so they may already depend on its randomness. Arc's verifier selects each output
oracle from the old instance oracles and the received proof oracles by outputting a tuple of
indices (Remark 5.2). ArkLib offers two forms:

- `OracleOutputEmbedding` realizes fixed, injective, interface-preserving selection, given by an
  injection `ιₛₒ ↪ ιₛᵢ ⊕ pSpec.MessageIdx`. This is a restricted case of Arc's verifier-selected
  tuple. Selection that depends on the run is not supplied by the embedding and has to be
  represented by a broader construction.
- `OracleOutputSimulation` supports adaptive query programs over the input oracles and messages,
  which may depend on the challenges but take no separate input-statement argument. It carries an
  extensional obligation: a materialized output value whose interface answers agree with the query
  programs. Locality is not part of the type; it is a property one proves about the simulation.

`OracleVerifier.NonAdaptive` packages the non-adaptive form, in which the query lists are computed
from the statement and challenges before any answer is seen, as in WHIR's $\mathcal{F}$-IOPs.

**When the verifier queries.** The legacy verifier receives all challenges at once and then runs a
single `OracleComp`. Since the verifier is public-coin, this matches Arc's remark that a verifier
can be split into an interaction phase and a query phase without loss of generality. This
normalization concerns when querying occurs, not whether query addresses depend on earlier answers.
The interaction layer lifts this restriction: following its
[access contract](docs/design/01c-access-execution-contract.md), the verifier may run effects,
including oracle queries, immediately after each received message.

**Exact relations instead of distance.** Legacy soundness quantifies over input statements outside
a language `langIn` and bounds the probability that the output lies in `langOut`. Both are exact
sets of statements together with the full oracle data. A proximity statement such as Definition 5.2
of [BCGGRS19] is expressed by choosing a relation that already says "within distance $\delta$ of the
code", not by a separate notion.

**A malicious prover is an ordinary prover.** Soundness for an oracle reduction is defined as
soundness of `OracleVerifier.toVerifier`, the verifier that answers queries from full messages. The
malicious prover therefore chooses arbitrary values of the declared message types. If a message type
is refined, for example to $R[X]_{\le d}$ through `instPolynomialDegreeLE`, then every prover,
honest or malicious, sends a polynomial of degree at most $d$. This is exactly the promise of the
polynomial models in Section 2.5. The promise is sound only if the compiler enforces it. The
interaction layer's [oracle-reduction core design](docs/design/02-oracle-reduction-core.md) states
that "guarantees travel with oracles", and the
[compiler design](docs/design/04-oracle-elimination-compiler.md) makes guarantee transport an
obligation of every pass that removes a refined oracle.

**Shared oracle.** The parameter `oSpec` lets the prover and verifier query a common oracle.
Security predicates are parameterized by an initialization distribution `init` and a stateful
implementation `impl` of `oSpec`; a theorem chooses these parameters or explicitly quantifies over
an allowed class. This is how ArkLib states reductions relative to a random oracle, which are the
output of the Fiat–Shamir transformation, in the same framework as information-theoretic
reductions. The random-oracle variant of reductions of knowledge [KP23, Kot24] plays the same role.
Arc introduces random-oracle-relative committed relations at the compilation stage (its
Definition 5.7); these are distinct from the indexed oracle relations used by its IOR.

**Completeness.** `Reduction.completeness` asks that, for every $(x, w) \in \mathcal{R}_{\mathsf{in}}$,
the output pair is in $\mathcal{R}_{\mathsf{out}}$ *and* the prover's output statement equals the
verifier's, except with probability $\varepsilon$. This is the completeness condition of [KP23].

**Soundness, relation soundness and knowledge soundness.** `Verifier.soundness` is language
soundness against every prover with any witness types. `Verifier.knowledgeSoundnessWith` fixes a
straightline extractor (`Extractor.Straightline`) before the malicious prover. The extractor sees
the input statement, the prover's output witness, the full transcript, and the logs of the prover's
and verifier's queries to `oSpec`. The game bounds

$$
\Pr\bigl[\, (x, E(\cdots)) \notin \mathcal{R}_{\mathsf{in}} \;\wedge\; (x', w') \in \mathcal{R}_{\mathsf{out}} \,\bigr],
$$

where extractor failure counts as a bad event. Giving the extractor the output witness follows the
reduction-of-knowledge view, and seeing the query logs is the usual straightline extraction in the
random oracle model.

The definition places no bound on the extractor's cost. The existential form
`Verifier.knowledgeSoundness` is therefore equivalent to *relation soundness*: the theorem
`Verifier.knowledgeSoundness_iff_relationSoundness` in
[`Security/UnboundedExtraction.lean`](ArkLib/OracleReduction/Security/UnboundedExtraction.lean)
shows that an unbounded extractor can simply choose a witness when one exists. A cost bound for the
same named extractor makes `knowledgeSoundnessWith` an efficient straightline extraction statement;
[`Security/Resources.lean`](ArkLib/OracleReduction/Security/Resources.lean) states such bounds
through measured programs. [KP23] also permits adversary-dependent rewinding extraction, while the
RBR notion of [CMS19] extracts from a qualifying prefix. Transferring either result requires
matching its extractor access, quantifiers, success experiment, and efficiency assumptions.

**Round-by-round soundness.** In
[`Security/RoundByRound.lean`](ArkLib/OracleReduction/Security/RoundByRound.lean),
`Verifier.StateFunction` has the three properties of Section 3.2, with "doomed" read as "false".
`rbrSoundness` asks for one error per challenge round, bounding the probability that a uniformly
random challenge moves a false state to a true one for every statement outside the language and
every *fixed* transcript prefix. This is the worst-case formulation of [CCHLRRW19] and Arc's
Definition 5.4, with two differences from Arc. First, Arc's state function (its Definition 5.3) is
false at the empty transcript for every instance, and its terminal law uses the relaxed output
language; ArkLib's state function only forces falsehood outside the input language (`toFun_empty`),
and its terminal law uses whatever output language `langOut` the caller supplies. Representing an
Arc theorem in ArkLib therefore requires choosing `langIn` and `langOut` to match Arc's exact and
relaxed relations; the names alone do not identify them. Second, the terminal law depends on how
the shared oracle is run, as the next paragraph explains.

**Terminal laws and the shared-oracle state.** The terminal laws of `StateFunction` and of
`KnowledgeStateFunction` (below) evaluate the verifier in a fresh-`init` experiment, not from the
shared-oracle state that the interaction has produced. To obtain a bound for execution with an
already-used stateful shared oracle, one must supply the appropriate current-state or guarded
terminal bridge; the bare state-function definition does not establish that bridge.
[`Security/GuardedSoundness.lean`](ArkLib/OracleReduction/Security/GuardedSoundness.lean)
(`GuardedForm.soundness_of_rbrSoundness`) and
[`Security/GuardedBridges.lean`](ArkLib/OracleReduction/Security/GuardedBridges.lean) provide these
bridges for guarded verifiers, whose verdict depends only on the statement and transcript.

**Round-by-round knowledge soundness.** `rbrKnowledgeSoundness` indexes the state function by a
witness. A family of intermediate witness types `WitMid`, one per round, comes with an
`Extractor.RoundByRound` that maps the output witness backward one round at a time (`extractOut`,
then `extractMid`, then `extractIn`). The `KnowledgeStateFunction` requires that

- a true state at the empty transcript gives a valid input witness through `extractIn`;
- prover moves preserve truth backward through `extractMid`;
- a complete transcript whose output is in $\mathcal{R}_{\mathsf{out}}$ with positive probability,
  in the fresh-`init` experiment, is true for the witness computed by `extractOut`.

The RBR error bounds the probability that a challenge makes the state true for *some*
intermediate witness while it was false for that witness's backward image. Because extraction
starts from the output witness, this formulation is designed to avoid the limitation in Arc's
Remark 5.6. It is closest to WARP's witness-indexed formulation (Section 3.2). WARP's state is
defined up to a proximity bound, carries explicit per-round extraction times, and keeps the same
witness across prover moves. ArkLib allows a different witness type at each stage and backward maps
across prover moves as well as challenges, and imposes no cost bound; efficiency is a separate
obligation, as for straightline extraction. For nonempty input-witness types, the unbounded RBR
notions coincide for the induced languages, by `rbrSoundness_iff_rbrKnowledgeSoundness` in
[`Security/Implications.lean`](ArkLib/OracleReduction/Security/Implications.lean). Empty witness
types require the separate degenerate-case conditions in that file.

**Special soundness and CWSS.** `Verifier.specialSound`
([`Security/SpecialSoundness.lean`](ArkLib/OracleReduction/Security/SpecialSoundness.lean)) is
the instance of a shape-generic tree special soundness (`Verifier.treeSpecialSound`), and
`coordinateWiseSpecialSound`
([`Security/CoordinateWiseSpecialSoundness/Basic.lean`](ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Basic.lean))
follows [FMN24]. For reductions, the tree extractor consumes witness-labelled successful output
leaves: it receives a valid output witness at every leaf, the output-witness input of a
reduction-of-knowledge extractor. The accept/reject description of Section 3.4 is the
proof-system specialization. The leaves match those of RBRTE in [BMMS26]. ArkLib's
`ChallengeTreeShape` constrains the sibling challenges at each node, and
`treeSpecialSoundWithEscape` adds an escape event on the whole tree; no formal correspondence with
RBRTE's vertical and challenge predicates is claimed. Tree extraction is a rewinding route, unlike
WARP's straightline RBR knowledge.

**Composition and context lifting.** Sequential composition (`OracleReduction.append`,
`seqCompose`) concatenates protocol specifications. It corresponds to sequential composition of
reductions of knowledge [KP23] only once matching security and extractor-resource theorems are
proved for it. [KP23] itself allows only a constant number of sequential compositions without
further assumptions, because each step blows up the extractor polynomially. Context lifting
(`OracleReduction.liftContext`, with lenses in
[`LiftContext/Lens.lean`](ArkLib/OracleReduction/LiftContext/Lens.lean)) runs a reduction for a
sub-statement inside a larger statement, which is how a protocol such as sum-check is reused inside
a larger system. It is an operation on a sub-statement, not the parallel composition of [KP23],
which reduces several instance–witness pairs side by side.

**Not modelled in this definition.** The protocol's verifier-to-prover moves are generated as public
challenges; additional verifier effects are governed by the ambient oracle implementation. The
number of rounds and the message types are fixed before the protocol starts, and the definitions
above do not include zero knowledge. Holography is optional through `Indexer`. Whether any of these
matter for a given paper's theorem must be checked case by case.

### 6.5 The interaction layer

The interaction layer keeps the same mathematical object, up to how output claims are represented
(see below), and changes how protocols are described and executed. Its design is in [docs/design/](docs/design/README.md); the points that matter for
comparison with the literature are these.

**Protocols are trees.** An `Oracle.TypeTree`
([`Interaction/Oracle/TypeTree.lean`](ArkLib/Interaction/Oracle/TypeTree.lean)) is a free monad over
PolyFun's polynomial functors with two kinds of node: a `public` node carries a move that selects
the continuation, and an `oracle` node carries a message that the verifier never sees in full. An
`Oracle.Protocol` ([`Interaction/Oracle/Protocol.lean`](ArkLib/Interaction/Oracle/Protocol.lean))
decorates public nodes with roles and oracle nodes with an `OracleInterface`; oracle messages are
always sent by the prover. Because the continuation may depend on earlier public moves, the number
of remaining rounds and their message types can depend on the transcript so far. Plain reductions
([`Interaction/Reduction.lean`](ArkLib/Interaction/Reduction.lean)) also let the tree depend on the
input statement, and sequential composition (`Reduction.then`) lets the suffix depend on the whole
prefix. A fixed `ProtocolSpec` cannot express such protocols directly.

**The verifier runs during the interaction, without seeing oracle payloads.** The legacy
`OracleVerifier` already sees messages only through queries, but it runs once, after the
interaction. In the interaction layer the verifier is a strategy on the structural tree that runs
alongside the prover: at an oracle node it receives query access to the new message, never the
message itself ([`Interaction/Oracle/Execution.lean`](ArkLib/Interaction/Oracle/Execution.lean)). Oracle access is
an accumulated signature that grows as messages arrive
([`Interaction/Oracle/Access.lean`](ArkLib/Interaction/Oracle/Access.lean)). This is the IOP
access discipline enforced by typing rather than by convention.

**Output claims have three representations.** Virtual oracles
([`Interaction/Oracle/Virtual.lean`](ArkLib/Interaction/Oracle/Virtual.lean)) are query programs
interpreted against the available oracles. A claim
([`Interaction/Oracle/Claim.lean`](ArkLib/Interaction/Oracle/Claim.lean)) pairs a public statement
with an oracle component in one of three forms:

- an `OpenClaim` carries query programs over a source signature;
- a `ClosedClaim` carries arbitrary deterministic oracle behavior, a `QueryImpl` into `Id` for each
  output oracle;
- a `ConcreteClaim` carries realizations, values of the declared realization types interpreted
  through their interfaces.

Open claims are the general form of both [BCGGRS19]'s virtual oracles and Arc's oracle selection.
Relations are stated at the closed-claim boundary through a `Problem`, whose claim-dependent witness
relation must imply an explicit `admissible` predicate (`rel_admissible`). A closed claim need not
come from a concrete realization, and a query signature does not force a behavior to be, for
example, the evaluation of a polynomial of bounded degree. At the closed-claim relation boundary,
admissibility or a representation/guarantee theorem must express any restriction such as
bounded-degree polynomial behavior; the query interface alone does not impose it. This is the
interaction-layer counterpart of the guarantee-transport obligation in Section 6.4: in the legacy
layer a refined message type imposes the promise on every prover, while here it must be stated.

**Security notions.** RBR soundness
([`Security/RoundByRound.lean`](ArkLib/Interaction/Oracle/Security/RoundByRound.lean)) is stated
over every prefix of the tree, including prefixes that an honest run reaches with probability
zero, relative to a `ChallengeModel` that describes each verifier challenge as a fresh sampling
program. The local bounds are statements about that model, not about the verifier's code. The
theorem `executeStrategies_soundness`
([`Security/Soundness.lean`](ArkLib/Interaction/Oracle/Security/Soundness.lean)) connects the two:
given an `OrdinaryState` certificate, local bounds, a `ChallengeSchedule` that ranks the challenge
rounds, and a `FreshVerifier` proof relating the verifier's actual moves under the given handler to
the challenge model, it bounds every probabilistic prover strategy by the sum of the local errors.
Knowledge uses a `KnowledgeCertificate` with named backward witness maps
([`Security/Knowledge.lean`](ArkLib/Interaction/Oracle/Security/Knowledge.lean)), the analogue of
the legacy `KnowledgeStateFunction` and of WARP's witness-indexed state (Section 3.2). Its fresh
challenge programs likewise need a correspondence with the actual verifier where they are used.
[`Security/StateRestoration.lean`](ArkLib/Interaction/Oracle/Security/StateRestoration.lean)
states `restored_extraction_bound` for one specified game: fixed-round public-coin protocols with
salts, run against a cached random oracle with restoration. Its premises are prover preservation and
local bounds for the backward maps, an explicit map for the adversary's terminal witness, and a
total query bound $Q$ on the adversary. Its conclusion bounds by $(Q + k) \cdot \varepsilon$, for
$k$ rounds, the probability that the input lies in the target set and the terminal witness is valid
while the extracted input witness is not. It is a theorem about that game, not about every
interaction protocol or every restoration interface.

**Extractor efficiency is a separate obligation.** The core certificate names backward witness
maps but imposes neither computability nor a cost bound. Cryptographic knowledge claims must attach
execution and resource bounds for those same maps; the linked design documents
([03a](docs/design/03a-extractor-efficiency.md), [03b](docs/design/03b-extractor-execution.md))
describe that discipline.

The legacy and interaction layers coexist. A theorem about one does not by itself prove a theorem
about the other; correspondence results between them are tracked in the status documents linked at
the top of this page.

## 7. Related formalization efforts

ArkLib builds on VCVio, a Lean 4 framework for oracle computations [TH24, TDWHH26], which in turn
uses PolyFun for polynomial functors and interaction trees. The table lists other machine-checked
work on cryptographic proofs that is closest to ArkLib's scope. Scope descriptions summarize each
work's own account.

| Work | Tool | Scope |
|---|---|---|
| VCVio [TH24, TDWHH26] | Lean 4 | oracle computations with effects and handlers; forking lemma; Fiat–Shamir for Σ-protocols; rewinding |
| CertiCrypt [BGZ09] | Coq | code-based game-playing proofs in a probabilistic relational Hoare logic |
| Σ-protocols in CertiCrypt [BHZGH10] | Coq | completeness, special soundness and HVZK of Σ-protocols |
| EasyCrypt [BGHZ11] | EasyCrypt | game-based proofs in probabilistic relational Hoare logic with SMT automation |
| Zero knowledge in EasyCrypt [FU23] | EasyCrypt | rewinding-based zero knowledge and proofs of knowledge for Σ-protocols |
| Forking lemma in EasyCrypt [FJ26] | EasyCrypt | the general forking lemma and EUF-CMA security of Schnorr signatures |
| Fiat–Shamir with aborts [BBD+23] | EasyCrypt | the security proof of Fiat–Shamir with aborts, applied to Dilithium |
| FCF [PM15] | Coq | a probabilistic programming language and theory for concrete-security proofs |
| CryptHOL [Loc16, BLS20] | Isabelle/HOL | game-based proofs with probabilistic functions and oracles |
| Σ-protocols in CryptHOL [BLAG21] | Isabelle/HOL | Σ-protocols, commitment schemes, and commitments from Σ-protocols |
| SSProve [AHRV+21, HRVW+23] | Coq | state-separating proofs with a relational program logic |
| Sum-check [BBS24] | Isabelle/HOL | public-coin interactive proofs and soundness and completeness of a generalized sum-check |
| Linear-PCP SNARKs [BM24] | Lean | soundness of linear-PCP SNARKs such as Groth16, with a decision procedure |
| Isabelle/STARK [Mar26] | Isabelle/HOL | query-bounded soundness of a STARK-style protocol, including FRI, Merkle authentication and the Fiat–Shamir transcript |
| CatCrypt [Spi26] | Lean | Rust-to-Lean translation with cryptographic security proofs; the author reports coverage of Σ-protocols, FRI, PLONK, KZG and Nova, and notes that the work is still being audited |

Most of this work targets Σ-protocols, signatures and encryption. The sum-check, linear-PCP and
STARK formalizations are the closest to ArkLib. ArkLib differs in taking interactive oracle
reductions as the primary object, in aiming to cover the full pipeline from information-theoretic
reductions through commitments and Fiat–Shamir, and in also covering arguments and commitments
whose security is computational (Section 5).

## 8. References

Links point to the ePrint or ECCC page, the DOI, or the publisher's page. "KB" links to the
paper's page in the repository's [knowledge base](docs/kb/README.md).

**Proof systems and compilers**

- [ACFY24stir] Arnon, Chiesa, Fenzi, Yogev. *STIR: Reed–Solomon Proximity Testing with Fewer
  Queries*. CRYPTO 2024. [ePrint 2024/390](https://eprint.iacr.org/2024/390).
  [KB](docs/kb/papers/ACFY24stir.md)
- [ACFY25] Arnon, Chiesa, Fenzi, Yogev. *WHIR: Reed–Solomon Proximity Testing with Super-Fast
  Verification*. EUROCRYPT 2025. [ePrint 2024/1586](https://eprint.iacr.org/2024/1586).
  [KB](docs/kb/papers/ACFY25.md)
- [ACK21] Attema, Cramer, Kohl. *A Compressed Σ-Protocol Theory for Lattices*. CRYPTO 2021.
  [ePrint 2021/307](https://eprint.iacr.org/2021/307).
- [AFK22] Attema, Fehr, Klooß. *Fiat–Shamir Transformation of Multi-Round Interactive Proofs*.
  TCC 2022; J. Cryptology 36(4), 2023. [ePrint 2021/1377](https://eprint.iacr.org/2021/1377).
- [AFKR26] Attema, Fehr, Klooß, Resch. *The Fiat–Shamir Transformation of
  $(\Gamma_1, \dots, \Gamma_\mu)$-Special-Sound Interactive Proofs*. J. Cryptology 39:19, 2026.
  [doi:10.1007/s00145-025-09569-y](https://doi.org/10.1007/s00145-025-09569-y);
  [ePrint 2023/1945](https://eprint.iacr.org/2023/1945)
- [AFR23] Attema, Fehr, Resch. *Generalized Special-Sound Interactive Proofs and their Knowledge
  Soundness*. TCC 2023. [ePrint 2023/818](https://eprint.iacr.org/2023/818)
- [ALMSS98] Arora, Lund, Motwani, Sudan, Szegedy. *Proof Verification and the Hardness of
  Approximation Problems*. J. ACM 45(3), 1998 (FOCS 1992).
  [doi:10.1145/278298.278306](https://doi.org/10.1145/278298.278306)
- [AS98] Arora, Safra. *Probabilistic Checking of Proofs: A New Characterization of NP*. J. ACM
  45(1), 1998 (FOCS 1992). [doi:10.1145/273865.273901](https://doi.org/10.1145/273865.273901)
- [Bab85] Babai. *Trading Group Theory for Randomness*. STOC 1985.
  [doi:10.1145/22145.22192](https://doi.org/10.1145/22145.22192)
- [Bab93] Babai. *Transparent (Holographic) Proofs*. STACS 1993.
  [doi:10.1007/3-540-56503-5_52](https://doi.org/10.1007/3-540-56503-5_52)
- [BBHR18] Ben-Sasson, Bentov, Horesh, Riabzev. *Fast Reed–Solomon Interactive Oracle Proofs of
  Proximity*. ICALP 2018. [ECCC TR17-134](https://eccc.weizmann.ac.il/report/2017/134/)
- [BCFW25] Bünz, Chiesa, Fenzi, Wang. *Linear-Time Accumulation Schemes* (WARP). TCC 2025.
  [ePrint 2025/753](https://eprint.iacr.org/2025/753). [KB](docs/kb/papers/BCFW25.md)
- [BCG20] Bootle, Chiesa, Groth. *Linear-Time Arguments with Sublinear Verification from Tensor
  Codes*. TCC 2020. [ePrint 2020/1426](https://eprint.iacr.org/2020/1426)
- [BCGGHJ17] Bootle, Cerulli, Ghadafi, Groth, Hajiabadi, Jakobsen. *Linear-Time Zero-Knowledge
  Proofs for Arithmetic Circuit Satisfiability*. ASIACRYPT 2017.
  [ePrint 2017/872](https://eprint.iacr.org/2017/872)
- [BCGGRS19] Ben-Sasson, Chiesa, Goldberg, Gur, Riabzev, Spooner. *Linear-Size Constant-Query IOPs
  for Delegating Computation*. TCC 2019. [ePrint 2019/1230](https://eprint.iacr.org/2019/1230)
- [BCGRS17] Ben-Sasson, Chiesa, Gabizon, Riabzev, Spooner. *Interactive Oracle Proofs with Constant
  Rate and Query Complexity*. ICALP 2017. [ePrint 2016/324](https://eprint.iacr.org/2016/324);
  [ECCC TR16-046](https://eccc.weizmann.ac.il/report/2016/046/)
- [BCGV16] Ben-Sasson, Chiesa, Gabizon, Virza. *Quasi-Linear Size Zero Knowledge from
  Linear-Algebraic PCPs*. TCC 2016-A. [ePrint 2016/021](https://eprint.iacr.org/2016/021)
- [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf. *Proximity Gaps for Reed–Solomon Codes*.
  FOCS 2020; J. ACM 70(5), 2023. [ePrint 2020/654](https://eprint.iacr.org/2020/654).
  [KB](docs/kb/papers/BCIKS20.md)
- [BCIOP13] Bitansky, Chiesa, Ishai, Ostrovsky, Paneth. *Succinct Non-Interactive Arguments via
  Linear Interactive Proofs*. TCC 2013. [ePrint 2012/718](https://eprint.iacr.org/2012/718)
- [BCLMS21] Bünz, Chiesa, Lin, Mishra, Spooner. *Proof-Carrying Data Without Succinct Arguments*.
  CRYPTO 2021. [ePrint 2020/1618](https://eprint.iacr.org/2020/1618)
- [BCMS20] Bünz, Chiesa, Mishra, Spooner. *Recursive Proof Composition from Accumulation Schemes*.
  TCC 2020. [ePrint 2020/499](https://eprint.iacr.org/2020/499) (ePrint title: *Proof-Carrying Data
  from Accumulation Schemes*)
- [BCS16] Ben-Sasson, Chiesa, Spooner. *Interactive Oracle Proofs*. TCC 2016-B.
  [ePrint 2016/116](https://eprint.iacr.org/2016/116). [KB](docs/kb/papers/BCS16.md)
- [BFLS91] Babai, Fortnow, Levin, Szegedy. *Checking Computations in Polylogarithmic Time*.
  STOC 1991. [doi:10.1145/103418.103428](https://doi.org/10.1145/103418.103428)
- [BFS20] Bünz, Fisch, Szepieniec. *Transparent SNARKs from DARK Compilers*. EUROCRYPT 2020.
  [ePrint 2019/1229](https://eprint.iacr.org/2019/1229)
- [BG92] Bellare, Goldreich. *On Defining Proofs of Knowledge*. CRYPTO 1992.
  [doi:10.1007/3-540-48071-4_28](https://doi.org/10.1007/3-540-48071-4_28)
- [BGKTTZ23] Block, Garreta, Katz, Thaler, Tiwari, Zając. *Fiat–Shamir Security of FRI and Related
  SNARKs*. ASIACRYPT 2023. [ePrint 2023/1071](https://eprint.iacr.org/2023/1071)
- [BGTZ25] Block, Garreta, Tiwari, Zając. *On Soundness Notions for Interactive Oracle Proofs*.
  J. Cryptology 38(1), 2025. [ePrint 2023/1256](https://eprint.iacr.org/2023/1256)
- [BMMS26] Baweja, Mishra, Mopuri, Shtepel. *FICS and FACS: Fast IOPPs and Accumulation via
  Code-Switching*. CRYPTO 2026. [ePrint 2025/737](https://eprint.iacr.org/2025/737)
- [BMNW25] Bünz, Mishra, Nguyen, Wang. *Arc: Accumulation for Reed–Solomon Codes*. CRYPTO 2025.
  [ePrint 2024/1731](https://eprint.iacr.org/2024/1731)
- [BPW12] Bernhard, Pereira, Warinschi. *How Not to Prove Yourself: Pitfalls of the Fiat–Shamir
  Heuristic and Applications to Helios*. ASIACRYPT 2012.
  [doi:10.1007/978-3-642-34961-4_38](https://doi.org/10.1007/978-3-642-34961-4_38)
- [CCHLRRW19] Canetti, Chen, Holmgren, Lombardi, G. Rothblum, R. Rothblum, Wichs. *Fiat–Shamir:
  From Practice to Theory*. STOC 2019.
  [doi:10.1145/3313276.3316380](https://doi.org/10.1145/3313276.3316380)
- [CFFQR21] Campanelli, Faonio, Fiore, Querol, Rodríguez. *Lunar: A Toolbox for More Efficient
  Universal and Updatable zkSNARKs and Commit-and-Prove Extensions*. ASIACRYPT 2021.
  [ePrint 2020/1069](https://eprint.iacr.org/2020/1069)
- [CGKY25] Chiesa, Guan, Knabenhans, Yu. *On the Fiat–Shamir Security of Succinct Arguments from
  Functional Commitments*. [ePrint 2025/902](https://eprint.iacr.org/2025/902).
  [KB](docs/kb/papers/CGKY25.md)
- [CHMMVW20] Chiesa, Hu, Maller, Mishra, Vesely, Ward. *Marlin: Preprocessing zkSNARKs with
  Universal and Updatable SRS*. EUROCRYPT 2020. [ePrint 2019/1047](https://eprint.iacr.org/2019/1047)
- [CMS19] Chiesa, Manohar, Spooner. *Succinct Arguments in the Quantum Random Oracle Model*.
  TCC 2019. [ePrint 2019/834](https://eprint.iacr.org/2019/834)
- [CO25] Chiesa, Orrù. *A Fiat–Shamir Transformation From Duplex Sponges*. TCC 2025.
  [ePrint 2025/536](https://eprint.iacr.org/2025/536)
- [COS20] Chiesa, Ojha, Spooner. *Fractal: Post-Quantum and Transparent Recursive Proofs from
  Holography*. EUROCRYPT 2020. [ePrint 2019/1076](https://eprint.iacr.org/2019/1076)
- [CY24] Chiesa, Yogev. *Building Cryptographic Proofs from Hash Functions*. Online book, 2024.
  [snargsbook.org](https://snargsbook.org/)
- [DMWG23] Dao, Miller, Wright, Grubbs. *Weak Fiat–Shamir Attacks on Modern Proof Systems*. IEEE
  S&P 2023. [ePrint 2023/691](https://eprint.iacr.org/2023/691)
- [FMN24] Fenzi, Moghaddas, Nguyen. *Lattice-Based Polynomial Commitments: Towards Asymptotic and
  Concrete Efficiency*. J. Cryptology 37:31, 2024. [ePrint 2023/846](https://eprint.iacr.org/2023/846).
  [KB](docs/kb/papers/FMN24.md)
- [FS86] Fiat, Shamir. *How To Prove Yourself: Practical Solutions to Identification and Signature
  Problems*. CRYPTO 1986. [doi:10.1007/3-540-47721-7_12](https://doi.org/10.1007/3-540-47721-7_12)
- [GMR89] Goldwasser, Micali, Rackoff. *The Knowledge Complexity of Interactive Proof Systems*.
  SIAM J. Comput. 18(1), 1989 (STOC 1985). [doi:10.1137/0218012](https://doi.org/10.1137/0218012)
- [GWZC19] Gabizon, Williamson, Ciobotaru. *PLONK: Permutations over Lagrange-bases for Oecumenical
  Noninteractive arguments of Knowledge*. [ePrint 2019/953](https://eprint.iacr.org/2019/953).
  [KB](docs/kb/papers/GWZC19.md)
- [Hol19] Holmgren. *On Round-By-Round Soundness and State Restoration Attacks*.
  [ePrint 2019/1261](https://eprint.iacr.org/2019/1261)
- [IKO07] Ishai, Kushilevitz, Ostrovsky. *Efficient Arguments without Short PCPs*. CCC 2007,
  pp. 278–291. [doi:10.1109/CCC.2007.10](https://doi.org/10.1109/CCC.2007.10);
  [author copy](https://web.cs.ucla.edu/~rafail/PUBLIC/79.pdf)
- [Ish20] Ishai. *Zero-Knowledge Proofs from Information-Theoretic Proof Systems*, Parts I and II.
  ZKProof blog, 2020.
  [Part I](https://zkproof.org/2020/08/12/information-theoretic-proof-systems/),
  [Part II](https://zkproof.org/2020/10/15/information-theoretic-proof-systems-part-ii/)
- [Kil92] Kilian. *A Note on Efficient Zero-Knowledge Proofs and Arguments*. STOC 1992.
  [doi:10.1145/129712.129782](https://doi.org/10.1145/129712.129782)
- [Kot24] Kothapalli. *A Theory of Composition for Proofs of Knowledge*. PhD thesis, Carnegie
  Mellon University, CMU-CS-24-126, 2024.
  [PDF](https://csd.cmu.edu/sites/default/files/phd-thesis/CMU-CS-24-126.pdf)
- [KP23] Kothapalli, Parno. *Algebraic Reductions of Knowledge*. CRYPTO 2023.
  [ePrint 2022/009](https://eprint.iacr.org/2022/009)
- [KR08] Kalai, Raz. *Interactive PCP*. ICALP 2008.
  [ECCC TR07-031](https://eccc.weizmann.ac.il/report/2007/031/)
- [KS24] Kothapalli, Setty. *HyperNova: Recursive Arguments for Customizable Constraint Systems*.
  CRYPTO 2024. [ePrint 2023/573](https://eprint.iacr.org/2023/573)
- [KST22] Kothapalli, Setty, Tzialla. *Nova: Recursive Zero-Knowledge Arguments from Folding
  Schemes*. CRYPTO 2022. [ePrint 2021/370](https://eprint.iacr.org/2021/370)
- [KZG10] Kate, Zaverucha, Goldberg. *Constant-Size Commitments to Polynomials and Their
  Applications*. ASIACRYPT 2010. [KB](docs/kb/papers/KZG10.md)
- [LFKN92] Lund, Fortnow, Karloff, Nisan. *Algebraic Methods for Interactive Proof Systems*.
  J. ACM 39(4), 1992 (FOCS 1990). [doi:10.1145/146585.146605](https://doi.org/10.1145/146585.146605).
  [KB](docs/kb/papers/LFKN92.md)
- [Mic94] Micali. *CS Proofs*. FOCS 1994; *Computationally Sound Proofs*, SIAM J. Comput. 30(4),
  2000. [doi:10.1109/SFCS.1994.365746](https://doi.org/10.1109/SFCS.1994.365746)
- [RRR16] Reingold, G. Rothblum, R. Rothblum. *Constant-Round Interactive Proofs for Delegating
  Computation*. STOC 2016; SIAM J. Comput. 50(3), 2021.
  [ECCC TR16-061](https://eccc.weizmann.ac.il/report/2016/061/)
- [Tha22] Thaler. *Proofs, Arguments, and Zero-Knowledge*. Foundations and Trends in Privacy and
  Security 4(2–4), 2022. [doi:10.1561/3300000030](https://doi.org/10.1561/3300000030)

**Computational arguments, commitments and idealized models**

- [Ajt96] Ajtai. *Generating Hard Instances of Lattice Problems*. STOC 1996.
  [doi:10.1145/237814.237838](https://doi.org/10.1145/237814.237838). [KB](docs/kb/papers/Ajt96.md)
- [BB04] Boneh, Boyen. *Short Signatures Without Random Oracles*. EUROCRYPT 2004.
  [doi:10.1007/978-3-540-24676-3_4](https://doi.org/10.1007/978-3-540-24676-3_4)
- [BBBPWM18] Bünz, Bootle, Boneh, Poelstra, Wuille, Maxwell. *Bulletproofs: Short Proofs for
  Confidential Transactions and More*. IEEE S&P 2018.
  [ePrint 2017/1066](https://eprint.iacr.org/2017/1066)
- [BC24] Boneh, Chen. *LatticeFold: A Lattice-based Folding Scheme and its Applications to
  Succinct Proof Systems*. ASIACRYPT 2025.
  [doi:10.1007/978-981-95-5099-9_11](https://doi.org/10.1007/978-981-95-5099-9_11);
  [ePrint 2024/257](https://eprint.iacr.org/2024/257)
- [BC25] Boneh, Chen. *LatticeFold+: Faster, Simpler, Shorter Lattice-Based Folding for Succinct
  Proof Systems*. CRYPTO 2025. [ePrint 2025/247](https://eprint.iacr.org/2025/247)
- [BCC88] Brassard, Chaum, Crépeau. *Minimum Disclosure Proofs of Knowledge*. J. Comput. Syst.
  Sci. 37(2), 1988. [doi:10.1016/0022-0000(88)90005-0](https://doi.org/10.1016/0022-0000(88)90005-0)
- [BCCGP16] Bootle, Cerulli, Chaidos, Groth, Petit. *Efficient Zero-Knowledge Arguments for
  Arithmetic Circuits in the Discrete Log Setting*. EUROCRYPT 2016.
  [ePrint 2016/263](https://eprint.iacr.org/2016/263)
- [BDLOP18] Baum, Damgård, Lyubashevsky, Oechsner, Peikert. *More Efficient Commitments from
  Structured Lattice Assumptions*. SCN 2018. [ePrint 2016/997](https://eprint.iacr.org/2016/997)
- [BGKLSW26] Bloemen, Garreta, Kostrzewa, Londhe, Soukhanov, Wu. *BitZ: Proofs and Commitments in
  Arbitrary Rings through Binary Fields*. [ePrint 2026/2141](https://eprint.iacr.org/2026/2141).
  [KB](docs/kb/papers/BGKLSW26.md)
- [BLNS20] Bootle, Lyubashevsky, Nguyen, Seiler. *A Non-PCP Approach to Succinct Quantum-Safe
  Zero-Knowledge*. CRYPTO 2020.
  [doi:10.1007/978-3-030-56880-1_16](https://doi.org/10.1007/978-3-030-56880-1_16);
  [ePrint 2020/737](https://eprint.iacr.org/2020/737)
- [BR93] Bellare, Rogaway. *Random Oracles are Practical: A Paradigm for Designing Efficient
  Protocols*. CCS 1993. [doi:10.1145/168588.168596](https://doi.org/10.1145/168588.168596)
- [BS23] Beullens, Seiler. *LaBRADOR: Compact Proofs for R1CS from Module-SIS*. CRYPTO 2023.
  [ePrint 2022/1341](https://eprint.iacr.org/2022/1341)
- [CGH04] Canetti, Goldreich, Halevi. *The Random Oracle Methodology, Revisited*. J. ACM 51(4),
  2004 (STOC 1998). [doi:10.1145/1008731.1008734](https://doi.org/10.1145/1008731.1008734)
- [DBK+26] Dao, Bodaghi, Khajehpour, Vitto, Badakhshan, Georghiades, Liu, Zhang, Thaler. *Akita: A
  High-Performance Lattice-Based Polynomial Commitment Scheme*.
  [ePrint 2026/1983](https://eprint.iacr.org/2026/1983)
- [FKL18] Fuchsbauer, Kiltz, Loss. *The Algebraic Group Model and its Applications*. CRYPTO 2018.
  [ePrint 2017/620](https://eprint.iacr.org/2017/620)
- [JM24] Jaeger, Mohan. *Generic and Algebraic Computation Models: When AGM Proofs Transfer to the
  GGM*. CRYPTO 2024. [doi:10.1007/978-3-031-68388-6_2](https://doi.org/10.1007/978-3-031-68388-6_2).
  [KB](docs/kb/papers/JM24.md)
- [LPS24] Lipmaa, Parisella, Siim. *Constant-Size zk-SNARKs in ROM from Falsifiable Assumptions*.
  EUROCRYPT 2024. [ePrint 2024/173](https://eprint.iacr.org/2024/173)
- [LPS25] Lipmaa, Parisella, Siim. *On Knowledge-Soundness of Plonk in ROM from Falsifiable
  Assumptions*. CRYPTO 2025. [ePrint 2024/994](https://eprint.iacr.org/2024/994).
  [KB](docs/kb/papers/LPS24.md)
- [LRY16] Libert, Ramanna, Yung. *Functional Commitment Schemes: From Polynomial Commitments to
  Pairing-Based Accumulators from Simple Assumptions*. ICALP 2016.
  [doi:10.4230/LIPIcs.ICALP.2016.30](https://doi.org/10.4230/LIPIcs.ICALP.2016.30)
- [LS15] Langlois, Stehlé. *Worst-Case to Average-Case Reductions for Module Lattices*. Des. Codes
  Cryptogr. 75(3), 2015. [ePrint 2012/090](https://eprint.iacr.org/2012/090)
- [Mau05] Maurer. *Abstract Models of Computation in Cryptography*. IMA Cryptography and Coding
  2005. [doi:10.1007/11586821_1](https://doi.org/10.1007/11586821_1)
- [Mer87] Merkle. *A Digital Signature Based on a Conventional Encryption Function*. CRYPTO 1987.
  [doi:10.1007/3-540-48184-2_32](https://doi.org/10.1007/3-540-48184-2_32)
- [NOZ26] Nguyen, O'Rourke, Zhang. *Hachi: Efficient Lattice-Based Multilinear Polynomial
  Commitments over Extension Fields*. [ePrint 2026/156](https://eprint.iacr.org/2026/156).
  [KB](docs/kb/papers/NOZ26.md)
- [NS24] Nguyen, Seiler. *Greyhound: Fast Polynomial Commitments from Lattices*. CRYPTO 2024.
  [ePrint 2024/1293](https://eprint.iacr.org/2024/1293). [KB](docs/kb/papers/NS24.md)
- [Ped91] Pedersen. *Non-Interactive and Information-Theoretic Secure Verifiable Secret Sharing*.
  CRYPTO 1991. [doi:10.1007/3-540-46766-1_9](https://doi.org/10.1007/3-540-46766-1_9)
- [Sho97] Shoup. *Lower Bounds for Discrete Logarithms and Related Problems*. EUROCRYPT 1997.
  [doi:10.1007/3-540-69053-0_18](https://doi.org/10.1007/3-540-69053-0_18)

**Post-quantum and composable security**

- [AABKT24] Aardal, Aranha, Boudgoust, Kolby, Takahashi. *Aggregating Falcon Signatures with
  LaBRADOR*. CRYPTO 2024. [ePrint 2024/311](https://eprint.iacr.org/2024/311)
- [AFP26] Anthoine, Fiore, Pancholi. *What a Wonderful World: zkSNARKs in the Algebraic Group Model
  are Universally Composable*. [ePrint 2026/399](https://eprint.iacr.org/2026/399)
- [AGRS24] Abdolmaleki, Glaeser, Ramacher, Slamanig. *Circuit-Succinct Universally-Composable NIZKs
  with Updatable CRS*. CSF 2024. [ePrint 2023/097](https://eprint.iacr.org/2023/097)
- [ARS20] Abdolmaleki, Ramacher, Slamanig. *Lift-and-Shift: Obtaining Simulation Extractable
  Subversion and Updatable SNARKs Generically*. CCS 2020.
  [ePrint 2020/062](https://eprint.iacr.org/2020/062)
- [ARU14] Ambainis, Rosmanis, Unruh. *Quantum Attacks on Classical Proof Systems: The Hardness of
  Quantum Rewinding*. FOCS 2014. [ePrint 2014/296](https://eprint.iacr.org/2014/296)
- [BCCRS24] Badertscher, Campanelli, Ciampi, Russo, Siniscalchi. *Universally Composable SNARKs
  with Transparent Setup without Programmable Random Oracle*. CRYPTO 2025.
  [doi:10.1007/978-3-032-01907-3_8](https://doi.org/10.1007/978-3-032-01907-3_8);
  [ePrint 2024/1549](https://eprint.iacr.org/2024/1549)
- [BDF+11] Boneh, Dagdelen, Fischlin, Lehmann, Schaffner, Zhandry. *Random Oracles in a Quantum
  World*. ASIACRYPT 2011. [ePrint 2010/428](https://eprint.iacr.org/2010/428)
- [BDHMN17] Broadnax, Döttling, Hartung, Müller-Quade, Nagel. *Concurrently Composable Security
  with Shielded Super-Polynomial Simulators*. EUROCRYPT 2017.
  [ePrint 2016/1043](https://eprint.iacr.org/2016/1043)
- [Can01] Canetti. *Universally Composable Security: A New Paradigm for Cryptographic Protocols*.
  FOCS 2001. [ePrint 2000/067](https://eprint.iacr.org/2000/067)
- [CC25] Canetti, Chen. *Universally Composable Succinct Vector Commitments and Applications*.
  TCC 2025. [ePrint 2025/1103](https://eprint.iacr.org/2025/1103)
- [CDDGS25] Chiesa, Dall'Agnol, Di, Guan, Spooner. *Quantum Rewinding for IOP-Based Succinct
  Arguments*. TCC 2025. [ePrint 2025/947](https://eprint.iacr.org/2025/947)
- [CDGLN18] Camenisch, Drijvers, Gagliardoni, Lehmann, Neven. *The Wonderful World of Global Random
  Oracles*. EUROCRYPT 2018. [ePrint 2018/165](https://eprint.iacr.org/2018/165)
- [CDGMSS25] Chen, Dey, Ganesh, Mukherjee, Sarkar, Sasmal. *Universally Composable Non-Interactive
  Zero-Knowledge from Sigma Protocols via a New Straight-line Compiler*. PKC 2025.
  [ePrint 2024/1713](https://eprint.iacr.org/2024/1713)
- [CDHZ26] Chiesa, Di, Hu, Zheng. *How to Prove Post-Quantum Security for Succinct Non-Interactive
  Reductions*. EUROCRYPT 2026. [ePrint 2025/2166](https://eprint.iacr.org/2025/2166)
- [CDPW07] Canetti, Dodis, Pass, Walfish. *Universally Composable Security with Global Setup*.
  TCC 2007. [ePrint 2006/432](https://eprint.iacr.org/2006/432)
- [CF24] Chiesa, Fenzi. *zkSNARKs in the ROM with Unconditional UC-Security*. TCC 2024.
  [ePrint 2024/724](https://eprint.iacr.org/2024/724)
- [CFHL21] Chung, Fehr, Huang, Liao. *On the Compressed-Oracle Technique, and Post-Quantum Security
  of Proofs of Sequential Work*. EUROCRYPT 2021. [ePrint 2020/1305](https://eprint.iacr.org/2020/1305)
- [CJS14] Canetti, Jain, Scafuro. *Practical UC Security with a Global Random Oracle*. CCS 2014.
  [ePrint 2014/908](https://eprint.iacr.org/2014/908)
- [CMSZ21] Chiesa, Ma, Spooner, Zhandry. *Post-Quantum Succinct Arguments: Breaking the Quantum
  Rewinding Barrier*. FOCS 2021. [arXiv:2103.08140](https://arxiv.org/abs/2103.08140)
- [DFM20] Don, Fehr, Majenz. *The Measure-and-Reprogram Technique 2.0: Multi-Round Fiat–Shamir and
  More*. CRYPTO 2020. [ePrint 2020/282](https://eprint.iacr.org/2020/282)
- [DFMS19] Don, Fehr, Majenz, Schaffner. *Security of the Fiat–Shamir Transformation in the
  Quantum Random-Oracle Model*. CRYPTO 2019. [ePrint 2019/190](https://eprint.iacr.org/2019/190)
- [DFMS22a] Don, Fehr, Majenz, Schaffner. *Online-Extractability in the Quantum Random-Oracle
  Model*. EUROCRYPT 2022. [ePrint 2021/280](https://eprint.iacr.org/2021/280)
- [DFMS22b] Don, Fehr, Majenz, Schaffner. *Efficient NIZKs and Signatures from Commit-and-Open
  Protocols in the QROM*. CRYPTO 2022. [ePrint 2022/270](https://eprint.iacr.org/2022/270)
- [DG23] Dao, Grubbs. *Spartan and Bulletproofs are Simulation-Extractable (for Free!)*.
  EUROCRYPT 2023. [ePrint 2023/494](https://eprint.iacr.org/2023/494)
- [FFKRZ23] Faonio, Fiore, Kohlweiss, Russo, Zając. *From Polynomial IOP and Commitments to
  Non-malleable zkSNARKs*. TCC 2023. [ePrint 2023/569](https://eprint.iacr.org/2023/569)
- [FFR24] Faonio, Fiore, Russo. *Real-World Universal zkSNARKs are Non-Malleable*. CCS 2024.
  [ePrint 2024/721](https://eprint.iacr.org/2024/721)
- [Fis05] Fischlin. *Communication-Efficient Non-interactive Proofs of Knowledge with Online
  Extractors*. CRYPTO 2005. [doi:10.1007/11535218_10](https://doi.org/10.1007/11535218_10)
- [FR26] Faonio, Russo. *Sumcheck-Based zkSNARKs are Non-malleable*. CRYPTO 2026.
  [ePrint 2026/335](https://eprint.iacr.org/2026/335)
- [GHHM21] Grilo, Hövelmanns, Hülsing, Majenz. *Tight Adaptive Reprogramming in the QROM*.
  ASIACRYPT 2021. [ePrint 2020/1361](https://eprint.iacr.org/2020/1361)
- [GKKNZ22] Ganesh, Khoshakhlagh, Kohlweiss, Nitulescu, Zając. *What Makes Fiat–Shamir zkSNARKs
  (Updatable SRS) Simulation Extractable?* SCN 2022. [ePrint 2021/511](https://eprint.iacr.org/2021/511)
- [GKOPTT23] Ganesh, Kondi, Orlandi, Pancholi, Takahashi, Tschudi. *Witness-Succinct
  Universally-Composable SNARKs*. EUROCRYPT 2023. [ePrint 2022/1618](https://eprint.iacr.org/2022/1618)
- [GM17] Groth, Maller. *Snarky Signatures: Minimal Signatures of Knowledge from
  Simulation-Extractable SNARKs*. CRYPTO 2017. [ePrint 2017/540](https://eprint.iacr.org/2017/540)
- [GOPTT22] Ganesh, Orlandi, Pancholi, Takahashi, Tschudi. *Fiat–Shamir Bulletproofs are
  Non-Malleable (in the Algebraic Group Model)*. EUROCRYPT 2022.
  [ePrint 2021/1393](https://eprint.iacr.org/2021/1393). Journal version: *Fiat–Shamir
  Bulletproofs are Non-malleable (in the Random Oracle Model)*, J. Cryptology, 2024,
  [doi:10.1007/s00145-024-09525-2](https://doi.org/10.1007/s00145-024-09525-2)
- [KPT23] Kohlweiss, Pancholi, Takahashi. *How to Compile Polynomial IOP into
  Simulation-Extractable SNARKs: A Modular Approach*. TCC 2023.
  [ePrint 2023/1067](https://eprint.iacr.org/2023/1067)
- [KZM+15] Kosba, Zhao, Miller, Qian, Chan, Papamanthou, Pass, shelat, Shi. *C∅C∅: A Framework for
  Building Composable Zero-Knowledge Proofs*. [ePrint 2015/1093](https://eprint.iacr.org/2015/1093)
- [Lip25] Lipmaa. *Plonk is Simulation Extractable in ROM Under Falsifiable Assumptions*.
  TCC 2025. [ePrint 2025/1759](https://eprint.iacr.org/2025/1759)
- [LMS22a] Lai, Malavolta, Spooner. *Quantum Rewinding for Many-Round Protocols*. TCC 2022.
  [ePrint 2022/889](https://eprint.iacr.org/2022/889)
- [LMS22b] Lombardi, Ma, Spooner. *Post-Quantum Zero Knowledge, Revisited (or: How to Do Quantum
  Rewinding Undetectably)*. FOCS 2022. [ePrint 2021/1543](https://eprint.iacr.org/2021/1543)
- [LR22] Lysyanskaya, Rosenbloom. *Universally Composable Σ-protocols in the Global Random-Oracle
  Model*. TCC 2022. [ePrint 2022/290](https://eprint.iacr.org/2022/290)
- [LZ19] Liu, Zhandry. *Revisiting Post-Quantum Fiat–Shamir*. CRYPTO 2019.
  [ePrint 2019/262](https://eprint.iacr.org/2019/262)
- [Pas03] Pass. *On Deniability in the Common Reference String and Random Oracle Model*.
  CRYPTO 2003. [doi:10.1007/978-3-540-45146-4_19](https://doi.org/10.1007/978-3-540-45146-4_19)
- [RZM+26] Roustaeifar, Zarezadeh, Mehendale, Abdolmaleki, Delavar, Köpsell. *Witness-Succinct
  UC-Secure SNARKs with Weaker Trust Assumptions*. IMA Cryptography and Coding 2026.
  [ePrint 2026/2434](https://eprint.iacr.org/2026/2434)
- [Unr10] Unruh. *Universally Composable Quantum Multi-Party Computation*. EUROCRYPT 2010.
  [arXiv:0910.2912](https://arxiv.org/abs/0910.2912)
- [Unr12] Unruh. *Quantum Proofs of Knowledge*. EUROCRYPT 2012.
  [ePrint 2010/212](https://eprint.iacr.org/2010/212)
- [Unr15] Unruh. *Non-Interactive Zero-Knowledge Proofs in the Quantum Random Oracle Model*.
  EUROCRYPT 2015. [ePrint 2014/587](https://eprint.iacr.org/2014/587)
- [Unr16] Unruh. *Computationally Binding Quantum Commitments*. EUROCRYPT 2016.
  [ePrint 2015/361](https://eprint.iacr.org/2015/361)
- [Unr17] Unruh. *Post-Quantum Security of Fiat–Shamir*. ASIACRYPT 2017.
  [ePrint 2017/398](https://eprint.iacr.org/2017/398)
- [Wat09] Watrous. *Zero-Knowledge against Quantum Attacks*. SIAM J. Comput. 39(1), 2009
  (STOC 2006). [doi:10.1137/060670997](https://doi.org/10.1137/060670997)
- [Zha19] Zhandry. *How to Record Quantum Queries, and Applications to Quantum Indifferentiability*.
  CRYPTO 2019. [ePrint 2018/276](https://eprint.iacr.org/2018/276)
- [ZZZR22] Zhou, Zhang, Zhou, Ren. *GUC-Secure Commitments via Random Oracles: New Impossibility
  and Feasibility*. ASIACRYPT 2022. [ePrint 2022/1127](https://eprint.iacr.org/2022/1127)

**Formalizations**

- [AHRV+21] Abate, Haselwarter, Rivas, Van Muylder, Winterhalter, Hriţcu, Maillard, Spitters.
  *SSProve: A Foundational Framework for Modular Cryptographic Proofs in Coq*. CSF 2021.
  [doi:10.1109/CSF51468.2021.00048](https://doi.org/10.1109/CSF51468.2021.00048)
- [BBD+23] Barbosa, Barthe, Doczkal, Don, Fehr, Grégoire, Huang, Hülsing, Lee, Wu. *Fixing and
  Mechanizing the Security Proof of Fiat–Shamir with Aborts and Dilithium*. CRYPTO 2023.
  [doi:10.1007/978-3-031-38554-4_12](https://doi.org/10.1007/978-3-031-38554-4_12)
- [BBS24] Garvía Bosshard, Bootle, Sprenger. *Formal Verification of the Sumcheck Protocol*.
  CSF 2024. [doi:10.1109/CSF61375.2024.00014](https://doi.org/10.1109/CSF61375.2024.00014).
  [KB](docs/kb/papers/BBS24.md)
- [BGHZ11] Barthe, Grégoire, Heraud, Zanella Béguelin. *Computer-Aided Security Proofs for the
  Working Cryptographer*. CRYPTO 2011.
  [doi:10.1007/978-3-642-22792-9_5](https://doi.org/10.1007/978-3-642-22792-9_5)
- [BGZ09] Barthe, Grégoire, Zanella Béguelin. *Formal Certification of Code-Based Cryptographic
  Proofs*. POPL 2009. [doi:10.1145/1480881.1480894](https://doi.org/10.1145/1480881.1480894)
- [BHZGH10] Barthe, Hedin, Zanella Béguelin, Grégoire, Heraud. *A Machine-Checked Formalization of
  Sigma-Protocols*. CSF 2010. [doi:10.1109/CSF.2010.24](https://doi.org/10.1109/CSF.2010.24)
- [BLAG21] Butler, Lochbihler, Aspinall, Gascón. *Formalising Σ-Protocols and Commitment Schemes
  Using CryptHOL*. J. Automated Reasoning 65(4), 2021.
  [doi:10.1007/s10817-020-09581-w](https://doi.org/10.1007/s10817-020-09581-w)
- [BLS20] Basin, Lochbihler, Sefidgar. *CryptHOL: Game-Based Proofs in Higher-Order Logic*.
  J. Cryptology 33(2), 2020. [doi:10.1007/s00145-019-09341-z](https://doi.org/10.1007/s00145-019-09341-z)
- [BM24] Bailey, Miller. *Formalizing Soundness Proofs of Linear PCP SNARKs*. USENIX Security 2024.
  [USENIX](https://www.usenix.org/conference/usenixsecurity24/presentation/bailey). Earlier
  preprint version: *Formalizing Soundness Proofs of SNARKs*,
  [ePrint 2023/656](https://eprint.iacr.org/2023/656)
- [CSV19] Canetti, Stoughton, Varia. *EasyUC: Using EasyCrypt to Mechanize Proofs of Universally
  Composable Security*. CSF 2019. [doi:10.1109/CSF.2019.00019](https://doi.org/10.1109/CSF.2019.00019)
- [FJ26] Firsov, Janků. *Forking Lemma in EasyCrypt*. CSF 2026.
  [doi:10.1109/CSF68417.2026.00037](https://doi.org/10.1109/CSF68417.2026.00037)
- [FU23] Firsov, Unruh. *Zero-Knowledge in EasyCrypt*. CSF 2023.
  [doi:10.1109/CSF57540.2023.00015](https://doi.org/10.1109/CSF57540.2023.00015)
- [GSFSM23] Gancher, Sojakova, Fan, Shi, Morrisett. *A Core Calculus for Equational Proofs of
  Cryptographic Protocols*. POPL 2023. [doi:10.1145/3571223](https://doi.org/10.1145/3571223)
- [HRVW+23] Haselwarter, Rivas, Van Muylder, Winterhalter, Abate, Sidorenco, Hriţcu, Maillard,
  Spitters. *SSProve: A Foundational Framework for Modular Cryptographic Proofs in Coq*. ACM
  TOPLAS 45(3), 2023. Journal version of [AHRV+21], with an added author and a changed author
  order. [doi:10.1145/3594735](https://doi.org/10.1145/3594735);
  [ePrint 2021/397](https://eprint.iacr.org/2021/397)
- [Loc16] Lochbihler. *Probabilistic Functions and Cryptographic Oracles in Higher Order Logic*.
  ESOP 2016. [doi:10.1007/978-3-662-49498-1_20](https://doi.org/10.1007/978-3-662-49498-1_20)
- [LSBM19] Lochbihler, Sefidgar, Basin, Maurer. *Formalizing Constructive Cryptography using
  CryptHOL*. CSF 2019. [doi:10.1109/CSF.2019.00018](https://doi.org/10.1109/CSF.2019.00018)
- [Mar26] Marmsoler. *Isabelle/STARK: A Formalization of zk-STARK in Isabelle/HOL*.
  [arXiv:2608.01965](https://arxiv.org/abs/2608.01965)
- [PM15] Petcher, Morrisett. *The Foundational Cryptography Framework*. POST 2015.
  [doi:10.1007/978-3-662-46666-7_4](https://doi.org/10.1007/978-3-662-46666-7_4)
- [Spi26] Spitters. *CatCrypt: From Rust to Cryptographic Security in Lean*.
  [ePrint 2026/604](https://eprint.iacr.org/2026/604)
- [TDWHH26] Tuma, Dao, Waters, Hicks, Hopper. *VCVio: Verified Cryptography in Lean via Oracle
  Effects and Handlers*. [ePrint 2026/899](https://eprint.iacr.org/2026/899)
- [TH24] Tuma, Hopper. *VCVio: A Formally Verified Forking Lemma and Fiat-Shamir Transform, via a
  Flexible and Expressive Oracle Representation*. [ePrint 2024/1819](https://eprint.iacr.org/2024/1819)
