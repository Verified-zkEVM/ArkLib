# Bracha RBC and the Verified Distributed-Protocol Landscape

This note records two outcomes of the recent investigation around
`Interaction`.

- First, it explains why **Bracha reliable broadcast** is a particularly strong
  benchmark for the current `Interaction` design.
- Second, it maps the surrounding landscape of **theorem-prover verification of
  consensus, broadcast, and distributed protocols**, with an emphasis on what
  that landscape suggests for the long-term identity of `Interaction`.

The intended use of this note is design guidance. It is not meant to be a full
survey, but it should be accurate enough to ground near-term implementation
choices.

## 1. Bracha Reliable Broadcast as an `Interaction` Benchmark

Bracha reliable broadcast (RBC) is a very strong benchmark candidate for the
current concurrent and multiparty layers.

At a high level, RBC is a one-sender broadcast primitive in an asynchronous
Byzantine setting. A designated sender attempts to broadcast a value, and the
protocol guarantees that honest parties never deliver conflicting values. Under
the usual resilience condition `n > 3f`, the textbook asynchronous protocol is
built around the familiar `init` / `echo` / `vote` (or `ready`) phases and
quorum-intersection arguments.

Why RBC is a particularly good fit for `Interaction`:

- It is **well-known and non-trivial**, but it is still much smaller than full
  state-machine replication or consensus stacks.
- It is fundamentally about **interaction**, not only state reachability:
  messages are sent, relayed, voted on, and eventually delivered.
- It naturally needs an **adversarial scheduler**: message delivery order,
  selective delay, duplication, and byzantine injection all matter.
- It has a clean split between **safety** and **liveness under fairness**.
- It sits directly on the practical asynchronous-BFT path used by protocols and
  systems such as HoneyBadger and Dumbo, which build on RBC-style broadcast
  subroutines
  ([hbbft](https://github.com/poanetwork/hbbft),
  [Dumbo](https://eprint.iacr.org/2020/841)).

For `Interaction`, RBC stresses exactly the current distinctive features:

- `Concurrent.Process` and `Concurrent.Machine` for dynamic protocol semantics;
- `Multiparty.LocalView` for who sees what;
- `Concurrent.Fairness` and `Concurrent.Liveness` for fair-delivery arguments;
- `Concurrent.Refinement` and `Concurrent.Bisimulation` for relating concrete
  network behavior to an abstract broadcast specification;
- `Concurrent.Independence` and `Concurrent.Interleaving` for scheduler
  robustness and commuting deliveries.

In other words, RBC is a better early benchmark for `Interaction` than Paxos or
Raft if the goal is to showcase the library's **interaction-first** nature
rather than only its transition-system subset.

## 2. Historical Position of Bracha RBC

The immediate historical backdrop is:

- [Lamport, Shostak, and Pease (1982)](https://nakamotoinstitute.org/library/the-byzantine-generals-problem/),
  which formulated the Byzantine Generals problem;
- [Dolev and Strong (1983)](https://www.osti.gov/biblio/5170704), for the
  authenticated synchronous line;
- [Ben-Or (1983)](https://ying-zhang.cn/dist/1983-ben-or.html), for early
  randomized asynchronous agreement;
- [Bracha and Toueg (1985)](https://dblp.org/rec/journals/jacm/BrachaT85.html),
  for early asynchronous broadcast/consensus work;
- [Bracha (1987)](https://dblp.org/rec/journals/iandc/Bracha87), which remains
  the canonical source for the asynchronous byzantine-agreement line in which
  reliable broadcast became a core building block.

The protocol matters not only as an isolated primitive. It became a standard
subroutine in asynchronous Byzantine protocol design, especially when reducing
larger protocols to modular components such as:

- reliable broadcast;
- binary agreement;
- asynchronous common subset;
- and later validated / provable / accountable broadcast variants.

That is exactly why it makes sense as a benchmark for a general-purpose
interaction library: it is simultaneously classical, compositional, and
practically relevant.

## 3. What Should Be Proved About RBC in `Interaction`

For `Interaction`, the right target theorem suite is:

- **Integrity**:
  if an honest node delivers `v` from sender `q`, then `q` really broadcast `v`
  in the relevant round.
- **Agreement**:
  two honest nodes never deliver different values for the same sender and
  round.
- **Validity**:
  if the sender is honest and broadcasts `v`, then honest nodes only deliver
  `v`.
- **Global liveness / totality under fairness**:
  under fair delivery among honest nodes, if the sender is honest then honest
  nodes eventually deliver; more generally, if one honest node delivers then
  all honest nodes eventually deliver the same value.
- **Refinement**:
  a concrete adversarial network semantics refines an abstract broadcast
  specification.
- **Scheduler robustness**:
  reordering independent deliveries should not affect the delivered value or
  the abstract broadcast outcome.

This suite would exercise more of the current framework than an invariant-only
proof:

- `Machine` or `Process` for the network semantics;
- `LocalView` for sender/receiver/adversary/auditor observations;
- `Fairness` for eventual-delivery assumptions;
- `Refinement` for the abstract-spec proof story;
- optionally `Independence` for scheduler-insensitive equivalence.

## 4. Exact Status of Formal Verification for Bracha RBC

The strongest direct result we found is:

- **Bythos (Coq, CCS 2024)** explicitly verifies **Reliable Broadcast** and
  presents it as one of the first machine-checked formalizations of that
  protocol family:
  [Bythos paper](https://ilyasergey.net/assets/pdf/papers/bythos-ccs24.pdf),
  [artifact](https://zenodo.org/records/12787570).

The paper states that Bythos verifies both **safety and liveness** properties
for three basic Byzantine protocols:

- Reliable Broadcast;
- Provable Broadcast;
- Accountable Byzantine Confirmer.

The paper also presents this result as the **first machine-checked
formalization** of Bracha-style Reliable Broadcast and closely related
protocols. We did not find an earlier widely cited Coq/Isabelle/Lean/F*/Dafny
formalization contradicting that claim.

This matters for `Interaction` because it means:

- RBC is not already completely saturated as a benchmark across prover
  ecosystems;
- but there is now a modern theorem-prover result to compare against, rather
  than only textbook pseudocode.

## 5. How Bythos Models and Proves RBC

Bythos is the closest direct comparison point for RBC itself.

### 5.1. Semantic core

Bythos models Byzantine protocols in Coq using:

- a map from addresses to **local node state**;
- a global **packet soup**;
- four generic transition kinds:
  - stuttering,
  - packet delivery,
  - internal transitions,
  - and byzantine packet injection;
- a protocol-specific constraint `byzConstraints` restricting what byzantine
  packets may be injected.

The paper emphasizes two design features that matter for proofs:

- packets are never removed from the soup, so the soup only grows;
- packets mediate causal knowledge between sender and receiver states.

This is a strong model for Byzantine message-passing protocols, but it is still
more specialized than the current `Interaction` core in one important way:
Bythos does **not** make per-party local observation a first-class semantic
field in the way `Multiparty.LocalView` does.

### 5.2. Proof style

Bythos proves safety and liveness using two main ideas:

- **knowledge lemmas**, which summarize what can be inferred from a packet,
  quorum, or local-state fact;
- **temporal liveness proofs** via an embedding of TLA into Coq.

So the main lesson from Bythos for `Interaction` is not to copy its semantic
carrier wholesale. The lesson is that Byzantine protocol verification benefits
greatly from:

- a reusable library of knowledge-lemma patterns;
- phase-based liveness proofs;
- protocol-composition interfaces.

Those are proof-architecture ideas that transfer directly.

## 6. How Veil Models and Verifies Reliable Broadcast

Veil is a very different comparison point.

Its core semantic object is a **relational transition system**:

- `init`
- `assumptions`
- `next`
- `safe`
- `inv`

in [Veil/Model/TransitionSystem.lean](/Users/quang.dao/Documents/Lean/veil/Veil/Model/TransitionSystem.lean).

Its Reliable Broadcast benchmark is written in the Veil DSL as a classic
transition-system model with:

- message relations such as `initial_msg`, `echo_msg`, and `vote_msg`;
- node-state relations such as `echoed`, `voted`, and `delivered`;
- actions `broadcast`, `echo`, `vote`, and `deliver`;
- ghost state and many inductive invariants

in [ReliableBroadcast.lean](/Users/quang.dao/Documents/Lean/veil/Examples/Other/ReliableBroadcast.lean).

The corresponding CAV 2025 paper lists `ReliableBroadcast` among Veil's case
studies and emphasizes:

- automated invariant checking via SMT,
- support for benchmarks outside EPR,
- and seamless fallback to interactive Lean proofs when automation fails

([Veil paper](https://verse-lab.github.io/papers/veil-cav25.pdf)).

The key point for `Interaction` is this:

- Veil's semantic core is **flatter** and more verification-oriented.
- It does not natively center:
  - controller paths,
  - per-party `LocalView`,
  - structured multi-node step protocols,
  - or independence-based causal quotients.

That does **not** make Veil weaker overall. It means Veil and `Interaction`
have different centers of gravity:

- Veil optimizes for a solver-friendly transition-system workflow;
- `Interaction` aims for a richer semantic kernel for structured interaction.

## 7. The Broader Verified-Protocol Landscape

The most important surrounding frameworks and proof lines are:

- **Verdi (Coq)**: verified distributed systems, especially **Raft** and
  verified system transformers
  ([repo](https://github.com/uwplse/verdi),
  [PLDI 2015](https://homes.cs.washington.edu/~mernst/pubs/verify-distsystem-pldi2015-abstract.html)).
- **IronFleet (Dafny)**: verified practical distributed systems, including a
  Paxos-based replicated-state-machine implementation
  ([CACM overview](https://cacm.acm.org/research/ironfleet/),
  [paper](https://web.eecs.umich.edu/~manosk/assets/papers/ironfleet-sosp15.pdf)).
- **Disel (Coq)**: compositional verification of distributed protocols and
  their clients
  ([POPL 2018](https://popl18.sigplan.org/details/POPL-2018-papers/49/Programming-and-Proving-with-Distributed-Protocols)).
- **Aneris (Coq / Iris)**: modular reasoning about distributed programs and
  services
  ([project](https://iris-project.org/aneris/)).
- **Velisarios (Coq)**: Byzantine fault-tolerant protocol verification,
  especially PBFT-style reasoning
  ([paper](https://link.springer.com/chapter/10.1007/978-3-319-89884-1_22)).
- **Bythos (Coq)**: compositional verification of composite Byzantine
  protocols, including RBC
  ([paper](https://ilyasergey.net/assets/pdf/papers/bythos-ccs24.pdf)).
- **TLA+ / TLAPS**: canonical specification-and-proof line for Paxos-family and
  related protocols
  ([Multi-Paxos in TLAPS](https://arxiv.org/abs/1606.01387),
  [Byzantine Paxos](https://lamport.org/tla/byzpaxos.html)).
- **Isabelle/HOL**: classic machine-checked **Disk Paxos**
  ([AFP entry](https://devel.isa-afp.org/entries/DiskPaxos.html)).
- **Ivy / EPR**: automatic verification of many Paxos-family variants
  ([Paxos Made EPR](https://www.wisdom.weizmann.ac.il/~padon/paxos-made-epr.html)).
- **EventML / Nuprl**: specification, proof, and extraction line for
  distributed protocols including Paxos / Multi-Paxos
  ([paper](https://www.sciencedirect.com/science/article/pii/S0167642317301193)).
- **Veil (Lean)**: automated + interactive transition-system verification in
  Lean, including Reliable Broadcast as a benchmark
  ([Lean use case](https://lean-lang.org/use-cases/veil/),
  [CAV 2025](https://verse-lab.github.io/papers/veil-cav25.pdf)).
- **Agda**: abstract safety proofs for modern BFT protocols such as
  HotStuff/LibraBFT
  ([paper](https://arxiv.org/abs/2203.14711)).

Very roughly:

- **Paxos and its variants** are the most heavily mechanized consensus family.
- **Byzantine broadcast and BFT protocols** have historically had fewer
  theorem-prover formalizations.
- **Bracha RBC** appears to have reached theorem-prover verification later than
  Paxos-family protocols, which makes it a strong contemporary benchmark for a
  new framework.

## 8. What This Means for `Interaction`

The key conclusion is that `Interaction` should not try to become either
Bythos or Veil.

Instead:

- learn **proof methodology** from Bythos;
- learn **workflow lessons** from Veil;
- keep a more expressive semantic core than either one.

More concretely:

- `Interaction` should adopt Bythos-style:
  - knowledge lemmas,
  - phase decompositions,
  - fairness-aware liveness proof templates,
  - protocol-composition theorems.
- `Interaction` should adopt from Veil:
  - a disciplined verification subset over `Concurrent.Machine`,
  - explicit VC-generation style support where it makes sense,
  - ergonomic proof workflows over a simpler backend-facing fragment.

But `Interaction` should retain its own center:

- structured `Step` protocols rather than only flat action relations;
- `LocalView` as a first-class observation discipline;
- `Process` as a dynamic residual-process semantics;
- and causal refinement beyond raw transition traces.

## 9. Proof-Trust Policy for `Interaction`

This investigation also clarifies a design-policy choice for the split-out
library.

The intended proof story for `Interaction` should be:

- **Lean kernel only**,
- plus trusted Lean elaboration and the standard mathematical foundations used
  by Lean and mathlib,
- with no dependence on external SMT solvers for trusted proof steps,
- and no reliance on `native_decide` as the core verification mechanism.

That does not mean automation is forbidden. It means the automation story
should be of the following kind:

- proof search and tactic support inside Lean;
- reflection or normalization arguments whose correctness is proved in Lean;
- theorem-carrying compilation to restricted verification fragments;
- small, explicit trusted kernels when absolutely necessary, proved and audited
  inside Lean rather than delegated to external solvers.

So the Veil lesson for `Interaction` is not:

> “copy the SMT-backed workflow.”

It is instead:

> “provide a verification-friendly subset and a smooth workflow, but keep the
> trusted base entirely within Lean.”

That policy is fully compatible with the present semantic direction and should
be stated explicitly in future verification-layer design notes.

## 10. Near-Term Consequence

The most useful near-term benchmark for the next stage of `Interaction` is:

- a full Bracha RBC development in the current framework,

with the following layers:

1. an abstract reliable-broadcast specification;
2. a concrete adversarial network semantics;
3. safety proofs;
4. fairness and liveness proofs;
5. refinement from the concrete model to the abstract specification;
6. optionally, observational variants and scheduler-insensitivity results.

This would position `Interaction` well relative to the current landscape:

- concrete enough to compare with Bythos and Veil;
- expressive enough to showcase what is unique about the `Interaction` design;
- and foundational enough to respect the kernel-only proof policy stated above.
