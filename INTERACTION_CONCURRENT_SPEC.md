# Concurrent Interaction Specs: Design Reference

This document is the design reference for a future concurrent extension of
`ArkLib.Interaction`.

It complements the existing sequential `Interaction.Spec` design rather than
replacing it. The main purpose of the note is to explain:

- what "concurrency" should mean in this library;
- why the recommended minimal core is a continuation-based `par left right`
  syntax;
- what other equally natural models of concurrency exist;
- how those models relate to each other;
- how adversarial scheduling and multiparty local views fit into the picture;
- and how we can expose several concurrency viewpoints without bloating the
  trusted core.

The intended audience includes people with different mental models of
concurrency:

- protocol and cryptography researchers who think in terms of scheduling,
  delivery, and adversarial control;
- PL and semantics people who think in terms of residual processes,
  structural congruence, and independence;
- distributed-systems readers who think in terms of event frontiers, task
  pools, buffering, and spawning;
- and functional programmers who prefer continuation-based descriptions over
  explicit mutable state machines.

The design goal is therefore not to choose one "true" notion of concurrency
and hide the others. Instead, we want:

- one small, continuation-first kernel;
- several derived interfaces and interpretations;
- and a clear story about which viewpoint is primary and which ones are
  alternate presentations or semantic refinements.

This note is also explicitly historical rather than novelty-claiming.
The recommended architecture is a synthesis of several established traditions:

- process calculi and process algebra, where binary parallel composition is a
  basic structural constructor;
- structural operational semantics, which turns syntax into execution rules;
- distributed-systems and automata models, where enabled actions, scheduling,
  traces, and fairness are primitive;
- true-concurrency models, where partial order and independence matter more
  than mere interleaving;
- and modern theorem-prover semantics, where resumptions, coinduction, and
  interaction trees provide continuation-heavy executable models.

---

## 0. Historical Orientation and Attribution

The design space discussed in this document is spread across several classic
lines of work.

### 0.1. Structural parallelism and process syntax

The recommendation to begin with a small structural syntax containing a binary
parallel constructor belongs squarely to the process-calculus and process-
algebra tradition. The clearest historical anchors are:

- Hoare's original CSP paper (1978), which made communicating process
  composition central;
- Milner's CCS (1980), which established a small algebraic syntax for
  communicating processes and their labeled transitions;
- Bergstra and Klop's ACP line (from the early 1980s), which emphasized the
  algebraic laws of process composition.

So the proposed `par left right` core should be presented as a continuation-
friendly adaptation of a very classical idea, not as a new discovery.

### 0.2. Operational readings of syntax

The idea that a small syntax should receive its meaning through recursively
defined operational rules sits in the structural operational semantics line
associated especially with Plotkin's 1981 notes. But the concrete scheduler-
facing `Front` / `residual` view in this note also belongs to a broader
"currently enabled actions plus residual behavior" tradition:

- Milner's early process-as-interaction viewpoint (1975);
- Milne and Milner's separation between process syntax and process behavior
  (1979);
- Hennessy and Plotkin's resumption-style denotational treatment of simple
  parallel languages (1979);
- Hennessy-Milner observational work in the early 1980s;
- and later coinductive resumption semantics for interactive programs.

So the right attribution for this part of the note is not just "SOS in
general," but also the residual-process and resumption lines that view a
process by the actions it can currently perform and the residual behavior that
follows.

### 0.3. Enabled actions, schedulers, and explicit state

The scheduler-facing side of this note belongs more naturally to the
distributed-systems and automata tradition:

- Dijkstra's guarded-command view of nondeterministically choosing among
  enabled actions (1975);
- Lamport's 1978 event-ordering paper for the distinction between partial
  order and imposed total order;
- Lynch and Tuttle's I/O automata line (conference paper 1987, introductory
  paper 1989) for enabled actions, composition, and asynchronous components;
- Lamport's Temporal Logic of Actions (1994) for action-based system
  specification;
- dynamic I/O automata (introduced by Attie and Lynch in 2001, developed
  further later) for systems whose components and signatures can change over
  time.

This is the line of work to cite when we say that explicit state, enabled
transition sets, and scheduler control are perfectly natural interfaces for
concurrency and distributed protocols.

### 0.4. True concurrency and partial orders

The note's distinction between interleaving and true concurrency should be
attributed to several related but genuinely different partial-order strands:

- Petri's net-based view of concurrent behavior in the 1960s;
- Mazurkiewicz traces (1977), where independence is represented by quotienting
  sequential executions under commuting actions;
- Lamport's "happened-before" partial order (1978);
- Nielsen, Plotkin, and Winskel's program of relating Petri nets, event
  structures, and domains (1981);
- Pratt's pomset line (mid-1980s), where executions are directly partial
  orders;
- Winskel's mature event-structure account in the 1980s, where causality,
  conflict, and enabling are explicit;
- and later consolidations such as Aalbersberg and Rozenberg's trace theory
  survey (1988).

This is the right ancestry for our "independence as a later refinement"
position, but it is important not to flatten these strands into one theory.
Traces, pomsets, and event structures all support non-interleaving reasoning,
but they emphasize different mathematical structure.

### 0.5. Dynamic concurrency

The note's claim that there are natural concurrency presentations beyond a
fixed binary tree of `par` also has standard precedents:

- the original Actor work of Hewitt, Bishop, and Steiger (1973), then Agha's
  1986 formulation, for asynchronous message-passing and dynamic creation of
  agents;
- the Chemical Abstract Machine line (POPL 1990; journal version 1992) for
  multiset-style concurrent dynamics;
- the π-calculus (1992) for mobility and dynamic process topology;
- session initiation in structured communication calculi such as
  Honda-Vasconcelos-Kubo (1998), where fresh communication structure is created
  on demand;
- the join-calculus (late 1990s; tutorial exposition 2000) for distributed
  mobile programming with local synchronization;
- and dynamic I/O automata (from 2001 onward) for dynamic component creation in
  the automata setting.

These works are the right citations when we explain why indexed families,
thread-pool views, and spawn-oriented semantics are as natural as binary
`par`, even if they are not our chosen minimal core.

### 0.6. Continuation-heavy mechanized semantics

Finally, the note's preference for residual-process and continuation-based
presentations aligns well with modern mechanized semantics. The important
lesson from proof assistants is not that one encoding has won, but that several
styles coexist successfully:

- early coinductive process-calculus mechanization such as
  Honsell-Miculan-Scagnetto (2001);
- Capretta's coinductive partiality / recursion work (2005);
- Nakata and Uustalu's resumptions and mixed induction-coinduction for
  interactive semantics (2010);
- event-oriented distributed reasoning such as Bickford-Constable-Rahli (2012);
- related coinductive big-step work on concurrency and nondeterminism in the
  early 2010s;
- mechanized causal / proof-relevant concurrency such as Perera-Cheney (2015);
- large operational or process-calculus libraries such as psi-calculi in
  Isabelle and CCS in HOL4 (mid/late 2010s);
- state-heavy concurrent reasoning frameworks such as Iris (2018);
- interaction trees as a coinductive, continuation-based, mechanized semantic
  interface (POPL 2020);
- and choice trees / ctrees (2022/2023) as an especially relevant bridge from
  interactive trees to nondeterministic and concurrent process semantics.

These works do not by themselves settle the foundational theory of
concurrency, but they strongly support the aesthetic choice to keep the core
continuation-first and executable while still acknowledging that operational
and state-machine encodings remain central in mechanized reasoning.

## 1. Starting Point: Sequential `Spec`

The current `Interaction.Spec` is a continuation tree:

```lean
inductive Spec where
  | done
  | node (Moves : Type u) (rest : Moves → Spec)
```

This is already a very strong foundation.

It says:

- the currently enabled next moves are `Moves`;
- choosing one move `x : Moves` continues as `rest x`;
- no explicit mutable state is required;
- the "state of the protocol" is just the current residual continuation.

This continuation-first aesthetic is a major strength of the library and should
be preserved in the concurrent setting as much as possible.

So the concurrent question is not:

> How do we add an explicit global state machine?

but rather:

> How do we generalize the continuation-tree idea from one current node to a
> frontier of concurrently live subprotocols?

---

## 2. Design Goals

The concurrent extension should satisfy the following goals.

### 2.1. Preserve the continuation-first style

The primary formulation should avoid introducing explicit state unless state is
the best interface for a derived interpretation.

In particular, the first design should not be:

```lean
State : Type
Enabled : State → Type
step : State → Enabled σ → State
```

even though that design is perfectly valid.

Instead, the preferred foundational language should describe concurrency by
residual protocol structure.

### 2.2. Support adversarial scheduling naturally

The library should be able to describe:

- multiple currently enabled events;
- an adversary or scheduler choosing which one happens next;
- per-party differences in who observes that chosen event;
- and later behavior depending on that history.

### 2.3. Stay compatible with existing `Interaction`

The concurrent layer should feel like an extension of the current library,
not a completely separate semantic universe.

In particular:

- sequential `Spec` should remain the basic one-thread fragment;
- multiparty local views should have a natural concurrent analogue;
- and linearizations back to sequential behavior should make sense whenever the
  model is interleaving-based.

### 2.4. Serve multiple mental models of concurrency

Different fields use different primary intuitions:

- syntax of parallel composition;
- currently enabled frontier events;
- state machines;
- partial-order / event-structure semantics;
- dynamic spawning;
- synchronous joint moves.

We want the library to be broadly useful, so the design should acknowledge and
support those perspectives rather than pretending only one is legitimate.

### 2.5. Keep the core minimal

Even if the library eventually exposes many concurrency interfaces, the
foundational kernel should stay small.

The recommendation in this document is:

- a minimal structural concurrent syntax as the core source language;
- frontier/residual semantics as the primary execution view;
- richer interpretations layered on top.

---

## 3. Recommended Minimal Core: Binary Structural Parallelism

The recommended first core is:

```lean
inductive Concurrent.Spec where
  | done
  | node (Moves : Type u) (rest : Moves → Concurrent.Spec)
  | par (left right : Concurrent.Spec)
```

This is the direct concurrent generalization of the current sequential tree:

- `done` means no further behavior;
- `node Moves rest` means one current atomic event is available;
- `par left right` means both `left` and `right` are currently live.

Historically, this is the part of the design most directly inherited from the
process-calculus / process-algebra line of CSP, CCS, and ACP rather than from
distributed state-machine models.

### 3.1. Why binary `par`?

Binary `par` is not meant to say that concurrency itself is inherently binary.
It is meant to provide the smallest compositional syntax former.

The advantages are the usual ones:

- small inductive definition;
- strong induction and recursion principles;
- easy structural recursion for semantics;
- easy local reasoning: what happens in the left thread, what happens in the
  right thread;
- n-ary parallelism can be derived by iteration.

This is exactly analogous to using binary products or binary sums as the core
syntax even though many applications naturally involve larger families.

### 3.2. Why not stop at sequential nodes only?

Sequential `Spec` already describes one currently enabled move family.
What it cannot express directly is:

- two independent live subprotocols at once;
- a scheduler choosing between events originating from distinct live regions of
  the protocol tree.

`par` is the smallest direct way to add that capability while preserving the
continuation style.

### 3.3. What this core does and does not say

This core says:

- concurrency exists as structural composition;
- the residual protocol after one event is another concurrent protocol.

It does **not** yet say:

- whether `par S T` and `par T S` should be equal or merely equivalent;
- whether independent events commute semantically;
- how to interpret executions operationally;
- whether events are observed publicly or privately;
- whether new threads can be spawned dynamically.

Those belong to later layers.

---

## 4. Primary Operational View: Frontiers and Residuals

Even if `par` is the core syntax, the best operational interpretation is not
"inspect the syntax directly." The right operational notion is:

- what events are currently enabled?
- and what residual protocol remains after performing one of them?

So for a concurrent syntax we should define externally:

```lean
Front : Concurrent.Spec → Type u
residual : {S : Concurrent.Spec} → Front S → Concurrent.Spec
```

### 4.1. Intended equations

The intended equations are:

```lean
Front .done = PEmpty
Front (.node X rest) = X
Front (.par S T) = Front S ⊕ Front T

residual (.node X rest) x = rest x
residual (.par S T) (.inl e) = .par (residual e) T
residual (.par S T) (.inr e) = .par S (residual e)
```

This gives the scheduler/adversary semantics immediately:

- at any moment, choose an event from `Front S`;
- continue as `residual e`.

This execution view is where the design comes closest to scheduler-based
distributed-system semantics and automata models: a current frontier of
enabled actions, a scheduling choice, and a residual system after that choice.

### 4.2. Why this is so important

This frontier/residual view is the point where concurrency becomes maximally
compatible with:

- adversarial scheduling;
- generic execution engines;
- future multiparty observation profiles;
- and alternative semantic interpretations.

It is also still continuation-based. The "current state" is just the residual
concurrent process.

Historically, this is the place where several strands meet:

- Plotkin-style SOS and labeled transitions, where syntax determines currently
  enabled actions and successor processes;
- the Hennessy-Milner observational line, where a process is understood by what
  it can do next and how it then behaves;
- resumption semantics for interactive and concurrent programs, where the
  semantic object is explicitly "one step plus a continuation";
- and, in more recent mechanized form, interaction-tree style codata and
  related coinductive process trees.

This means our proposed `Front` / `residual` interface is not novel as a
semantic idea. What is distinctive here is the packaging: keep binary `par` as
the human-facing source syntax, but expose `Front` / `residual` as the
scheduler-facing execution interface.

### 4.3. Relationship to the current sequential `Spec`

Sequential `Spec` is recovered as the fragment with no `par`.

If desired, one can also imagine a forgetful map:

- concurrent syntax -> frontier/residual machine;
- frontier/residual machine with only singleton frontiers -> sequential syntax.

So the frontier view is not a different philosophy from the current library.
It is the same philosophy applied to multiple live subtrees.

---

## 5. Other Natural Models of Concurrency

Binary `par` is the recommended minimal core, but it is not the only natural
way to present or think about concurrency.

The library should ideally expose several of the following viewpoints.

### 5.1. N-ary / Indexed Parallelism

Instead of binary `par`, one can make the live family explicit:

```lean
| par (ι : Type u) (threads : ι → Concurrent.Spec)
```

or some finite-indexed variation.

#### Meaning

There is a whole indexed family of concurrently active subprocesses, not merely
two subprocesses composed by a binary tree.

#### Why it is natural

This can be more direct when concurrency really is "a family of threads":

- one thread per party;
- one thread per channel;
- one thread per pending task;
- one thread per active session.

People from distributed systems often find this presentation more intuitive
than repeated binary pairing.

#### Tradeoffs

- recursion and induction are heavier;
- compositional proofs are often less elegant;
- binary `par` already encodes this expressively.

#### Recommendation

Treat indexed parallelism as a derived interface or alternate source language,
not as the foundational kernel.

It may be very useful as a user-facing front-end later.

### 5.2. Frontier-Only / Residual-Only Process View

One can go even more operational and remove explicit syntax altogether:

```lean
structure Concurrent.Spec where
  Enabled : Type u
  step : Enabled → Concurrent.Spec
```

#### Meaning

The protocol directly presents:

- its currently enabled atomic events;
- and its residual continuation after each event.

#### Why it is natural

This is arguably the most continuation-pure formulation.

It is extremely close to the existing sequential `Spec.node X rest`.
In fact, it may be seen as "the same idea, but with no commitment to a
particular syntax of parallel composition."

#### Strengths

- excellent for schedulers and adversaries;
- no explicit state object;
- no commitment to binary vs n-ary vs spawned syntax;
- very elegant operationally.

#### Weaknesses

- loses compositional source structure;
- harder to recover how the concurrent object was assembled;
- not the best front-end for equational reasoning about `par`.

#### Recommendation

Use this as an operational interpretation, and possibly as an alternate API,
but not as the only exposed representation.

### 5.3. Explicit State-Machine Concurrency

A more conventional formulation is:

```lean
structure Concurrent.Machine where
  State : Type v
  init : State
  Enabled : State → Type u
  step : (σ : State) → Enabled σ → State
```

#### Meaning

The protocol is an explicit transition system.

#### Why it is natural

This is the dominant style in many distributed-systems and protocol models.
It works especially well when one wants to talk about:

- buffers;
- timers;
- corruption sets;
- channel state;
- long-lived network configuration;
- fairness conditions over runs.

#### Relationship to the continuation-first style

This should not be the foundational core for this library, but it is still a
valid and useful interpretation.

This is exactly the area where I/O automata, TLA/TLA+, and later distributed-
systems specification frameworks provide the most natural citations.

Conceptually, it is often just a different presentation of residual processes:

- explicit state corresponds to an encoded residual continuation;
- residual continuation corresponds to "hidden state" if one prefers that view.

#### Recommendation

Expose state-machine concurrency as a derived or alternate interpretation, not
as the primary definition.

### 5.4. Independence / Partial-Order / Event-Structure Semantics

The most important semantic refinement beyond plain interleaving is to make
independence explicit.

One can add something like:

```lean
Independent : {S : Concurrent.Spec} → Front S → Front S → Prop
```

together with commutation/diamond laws saying independent events can happen in
either order and lead to equivalent residual behavior.

#### Meaning

Two events are not merely "both enabled." They are semantically concurrent.
Different linearizations of them represent the same underlying behavior.

This is the part of the note that should be attributed primarily to the
Petri-net, event-structure, and true-concurrency traditions rather than to
interleaving process calculi alone.

More specifically:

- if the refinement only quotients sequential traces by commuting independent
  actions, the clean attribution is to Mazurkiewicz traces;
- if the refinement takes executions themselves to be partial orders, Pratt's
  pomset line is the closest match;
- if the refinement needs explicit causality, conflict, or branch-sensitive
  enabling, Winskel-style event structures and Petri-net unfoldings are the
  stronger reference point.

#### Why it matters

This is what moves the model from:

- interleaving concurrency

to:

- true partial-order concurrency.

It matters if one wants to reason about:

- causal structure;
- concurrent independence rather than mere nondeterministic ordering;
- event-structure or pomset semantics;
- commutation of independent scheduler choices.

#### Why it is not the first step

This layer is much heavier:

- more laws;
- equivalence rather than raw syntax;
- more proof burden;
- more semantic sophistication.

#### Recommendation

Treat this as a semantic refinement layered on top of the basic concurrent
syntax and frontier semantics.

### 5.5. Dynamic Spawning / Thread-Pool Models

Static `par S T` describes fixed concurrent composition.
Many real systems instead have **dynamic concurrency**, where events create,
destroy, or update concurrent subprocesses.

One way to think about this is:

- the running system is a family or multiset of active residuals;
- an event updates one part of that family and may spawn new ones.

#### Why it is natural

This fits:

- actor-style systems;
- async task systems;
- dynamic protocol sessions;
- network models with growing sets of pending messages.

The right historical anchors here are the Actor model, the π-calculus,
Chemical Abstract Machine / multiset-style operational views, join-calculus,
and dynamic I/O automata.

#### Relationship to binary `par`

Binary `par` can still serve as a source language, but dynamic spawning is more
naturally presented as:

- an indexed thread family;
- a multiset of active subprocesses;
- or a frontier machine whose residuals can expand the live family.

This is why actor systems, CHAM-style reaction semantics, join-calculus, and
session initiation are useful citations here: they show that "the live
concurrent system is a changing population of active entities" is not a niche
presentation, but a major recurring design pattern.

#### Recommendation

Do not put spawning into the very first minimal kernel.
But make sure the later semantics do not preclude it.

### 5.6. Simultaneous / Joint-Step Concurrency

Not all concurrency should be represented as interleaving between independent
threads. Sometimes the correct abstraction is a **joint atomic step**.

For example:

- synchronous rounds;
- simultaneous broadcasts;
- auction/bidding submissions;
- commit-reveal phases modeled as one logical step.

In such cases, a single node may already be the right abstraction:

```lean
node JointMoves rest
```

where `JointMoves` is itself a structured type of simultaneous contributions.

#### Why this matters for `Interaction`

The existing library is already well-suited to such nodes because
`SyntaxOver` and multiparty local views allow quite rich local node structure.

So some phenomena that one might casually call "concurrent" are better modeled
as:

- one richer atomic node,

rather than:

- a `par` composition of separate subprotocols.

#### Recommendation

Keep this possibility explicit in the design.
Concurrency is not only about parallel composition; sometimes it is about
simultaneous atomicity.

---

## 6. Which of These Are Fundamentally Different?

There are several independent axes here.

### 6.1. Syntax-first vs execution-first

Syntax-first:

- binary `par`;
- indexed `par`;
- spawn syntax.

Execution-first:

- frontier/residual machines;
- explicit state machines.

### 6.2. Static vs dynamic concurrency

Static:

- `par left right`;
- indexed family of fixed threads.

Dynamic:

- spawn / thread-pool semantics;
- state-machine models with changing enabled structure.

### 6.3. Interleaving vs true concurrency

Interleaving:

- frontier/residual without independence;
- scheduler chooses one enabled event at a time.

True concurrency:

- independence relations;
- event structures;
- partial-order semantics.

### 6.4. Independent steps vs simultaneous steps

Independent steps:

- `par`;
- frontier choice between events.

Simultaneous steps:

- richer atomic `node` types with joint moves.

These distinctions matter because different communities often collapse different
axes under the same word "concurrency."

---

## 7. Recommended Library Layering

The most compatible design with the current library is:

### Layer 1: Minimal concurrent source syntax

```lean
inductive Concurrent.Spec where
  | done
  | node (Moves : Type u) (rest : Moves → Concurrent.Spec)
  | par (left right : Concurrent.Spec)
```

This is the foundational source language.

### Layer 2: Frontier / residual execution view

```lean
Front : Concurrent.Spec → Type u
residual : Front S → Concurrent.Spec
```

This is the operational interface for schedulers, adversaries, interpreters,
and execution semantics.

### Layer 3: Optional semantic refinements

- indexed / n-ary parallel syntax;
- explicit machine semantics;
- independence / partial-order laws;
- dynamic spawning;
- scheduler fairness;
- joint-step interfaces;
- multiparty observation profiles.

This gives a clear division:

- small core;
- rich outer ecosystem.

---

## 8. Adversarial Scheduling in the Concurrent Setting

Concurrency and adversarial scheduling fit together especially well through the
frontier view.

At any residual concurrent protocol `S`, the adversary's power is:

1. inspect the currently enabled frontier `Front S`;
2. choose one event `e : Front S` that it is allowed to schedule;
3. continue in `residual e`;
4. do so adaptively based on the information it has observed so far.

This is the concurrent analogue of the sequential adversarial scheduling story.

### 8.1. Highest structured adversarial power

In the concurrent setting, the strongest sane structured adversary is one that
may:

- choose any enabled frontier event;
- condition on its observed history;
- control corrupted parties and corrupted channels;
- delay, drop, duplicate, reorder, reroute, or reveal events as allowed by the
  current residual protocol;
- and continue adaptively forever.

What it should **not** get by default is omniscience about hidden local state.

This section should be read as a protocol-semantics specialization of the
enabled-actions and scheduling traditions above, not as a claim that
adversarial delivery semantics were invented here.

For the strongest cryptographic reading of adversarial network control, the
closest established attribution is to UC-style protocol semantics, where the
environment and adversary control message delivery and scheduling subject to
the ambient communication model.

From the concurrency literature more broadly, the closest conceptual ancestors
for this scheduler-facing story are:

- Dijkstra-style nondeterministic choice among enabled guarded actions;
- Petri / automata views where the system exposes enabled transitions;
- Lamport's distinction between causal order and the particular total order
  imposed by a scheduler or run;
- and I/O-automata style modeling of asynchronous components and external
  scheduling.

So when this note treats an adversary as choosing from a frontier of enabled
events, that should be read as a protocol-specific specialization of a very
classical concurrency interface.

### 8.2. Multiparty local views

The current sequential multiparty layer suggests the right generalization:

- each frontier event has per-party local observations;
- some parties may observe the full event;
- some may observe only a quotient;
- some may observe nothing.

So a future concurrent multiparty interface will likely want:

- a notion of frontier events;
- and a per-party `LocalView` or observation profile on those events.

This integrates naturally with the existing multiparty local-view story.

---

## 9. How to Relate Concurrency Back to Sequential `Spec`

It is valuable to preserve a strong connection between concurrent and sequential
interaction.

### 9.1. Interleaving linearizations

Without independence refinements, a concurrent run is just a sequence of chosen
frontier events. So there is an evident "linearization" into a sequential
history.

This means:

- many concurrent systems can be interpreted as families of sequential traces;
- sequential proofs may still apply to chosen linearizations;
- schedulers can be seen as choosing an interleaving.

### 9.2. Quotienting by independence

If independence is added later, one can then quotient those sequential
linearizations by commuting independent steps.

So the story becomes:

- raw concurrent execution -> sequential linearizations;
- semantic refinement -> identify equivalent linearizations.

This is a strong reason to keep the frontier/residual view central.

---

## 10. Suggested API Sketch

This section is deliberately only a sketch.

### 10.1. Core syntax

```lean
namespace Interaction.Concurrent

inductive Spec where
  | done
  | node (Moves : Type u) (rest : Moves → Spec)
  | par (left right : Spec)
```

### 10.2. Frontiers

```lean
inductive Front : Spec → Type u

def residual : {S : Spec} → Front S → Spec
```

### 10.3. Execution traces

One possibility:

```lean
inductive Trace : Spec → Type u
  | nil : Trace .done
  | cons : (e : Front S) → Trace (residual e) → Trace S
```

This is the concurrent analogue of transcripts as sequences of scheduled
frontier events.

### 10.4. Derived interfaces

Potential later modules:

- `Interaction/Concurrent/Spec.lean`
- `Interaction/Concurrent/Frontier.lean`
- `Interaction/Concurrent/Trace.lean`
- `Interaction/Concurrent/Indexed.lean`
- `Interaction/Concurrent/Independence.lean`
- `Interaction/Concurrent/Spawn.lean`
- `Interaction/Concurrent/Multiparty.lean`

---

## 11. The Case for Exposing Multiple Concurrency Viewpoints

The library should explicitly support multiple interpretations because different
fields legitimately organize their thinking differently.

### 11.1. PL / semantics audience

They often want:

- structural `par`;
- congruence laws;
- independence / event-structure semantics.

### 11.2. Distributed-systems audience

They often want:

- enabled frontiers;
- state machines;
- fairness and scheduling;
- dynamic spawning or task-pool semantics.

### 11.3. Protocol / cryptography audience

They often want:

- adversarial scheduling;
- delivery/drop/reorder semantics;
- per-party observation models;
- partial information and corruption.

### 11.4. Functional-programming audience

They often want:

- continuation-first descriptions;
- residual-process interpretations;
- avoidance of explicit mutable state in the foundational definitions.

The recommended architecture supports all of these by:

- making the kernel small;
- making the operational interface explicit;
- and letting alternate viewpoints live as derived interfaces.

---

## 12. Recommendation and Roadmap

### Phase 1: Minimal core

Implement:

- binary `Concurrent.Spec`;
- `Front`;
- `residual`;
- basic trace/execution machinery.

This is the best first landing.

### Phase 2: Scheduler-facing semantics

Add:

- adversarial/scheduler choice over `Front`;
- multiparty local observation profiles on frontier events;
- linearization back to sequential runs.

This makes the design immediately useful for protocol semantics.

### Phase 3: Alternative front-ends

Add:

- indexed / n-ary parallel syntax;
- optional state-machine presentation;
- maybe spawn-oriented interfaces.

These broaden usability without changing the core.

### Phase 4: Semantic refinements

Add:

- independence / commutation laws;
- partial-order semantics;
- fairness / liveness layers if needed.

This is where "true concurrency" enters in a deeper sense.

---

## 13. Final Recommendation

The right first answer is:

- **yes**, start with `par left right`;
- **no**, do not pretend that is the only valid notion of concurrency;
- **yes**, expose other concurrency viewpoints later as alternate presentations
  and semantic refinements;
- and **yes**, keep the primary core continuation-based rather than
  state-machine-first.

So the final design stance of this note is:

1. The foundational source language should be a small structural concurrent
   syntax with binary `par`.
2. The primary operational interpretation should be frontier/residual.
3. Indexed parallelism, explicit machine semantics, independence models,
   spawn/thread-pool models, and simultaneous/joint-step views are all
   legitimate and should be supported as later layers.
4. This multi-view design makes the library broadly useful across fields while
   preserving a very small and elegant trusted core.

---

## 14. Suggested Historical Citations

The following sequence captures the main traditions that inform this design.

### Foundational concurrency and process syntax

- C. A. R. Hoare, *Communicating Sequential Processes* (1978).
- Robin Milner, *Processes: A Mathematical Model of Computing Agents* (1975).
- Robin Milner, *A Calculus of Communicating Systems* (1980).
- George Milne and Robin Milner, *Concurrent Processes and Their Syntax*
  (1979).
- Matthew Hennessy and Gordon Plotkin, *Full Abstraction for a Simple Parallel
  Programming Language* (1979).
- Jan A. Bergstra and Jan Willem Klop, *Algebra of Communicating Processes*
  (early 1980s; standard publication track begins 1984).
- Matthew Hennessy and Robin Milner, *Algebraic Laws for Nondeterminism and
  Concurrency* (1985), together with their observational work of the same
  period.
- Gordon Plotkin, *A Structural Approach to Operational Semantics* (1981).
- Robin Milner, *Communication and Concurrency* (1989).

### Partial order and true concurrency

- Carl Adam Petri, *Kommunikation mit Automaten* (1962).
- Antoni Mazurkiewicz, *Concurrent Program Schemes and their Interpretations*
  (1977).
- Leslie Lamport, *Time, Clocks, and the Ordering of Events in a Distributed
  System* (1978).
- Mogens Nielsen, Gordon Plotkin, and Glynn Winskel, *Petri Nets, Event
  Structures and Domains, Part I* (1981).
- Glynn Winskel, *Event Structure Semantics for CCS and Related Languages*
  (1982).
- Vaughan Pratt, *The Pomset Model of Parallel Processes* (1984), and
  *Modelling Concurrency with Partial Orders* (1986).
- Glynn Winskel, event-structure work of the 1980s, especially *Event
  Structures* (1987).
- I. J. Aalbersberg and Grzegorz Rozenberg, *Theory of Traces* (1988).

### Distributed systems, schedulers, and explicit state

- Edsger W. Dijkstra, *Guarded Commands, Nondeterminacy and Formal Derivation
  of Programs* (1975).
- Nancy Lynch and Mark Tuttle, I/O-automata papers beginning in 1987 and
  including *An Introduction to Input/Output Automata* (1989).
- Leslie Lamport, *The Temporal Logic of Actions* (1994).
- Paul Attie and Nancy Lynch, *Dynamic Input/Output Automata: A Formal Model
  for Dynamic Systems* (2001), with later compositional development.
- Ran Canetti, *Universally Composable Security: A New Paradigm for
  Cryptographic Protocols* (2001), for adversarially scheduled protocol
  composition.

### Dynamic concurrency and mobility

- Carl Hewitt, Peter Bishop, and Richard Steiger, *A Universal Modular ACTOR
  Formalism for Artificial Intelligence* (1973).
- Gul Agha, *Actors: A Model of Concurrent Computation in Distributed Systems*
  (1986).
- Gérard Berry and Gérard Boudol, *The Chemical Abstract Machine* (POPL 1990;
  journal version 1992).
- Robin Milner, Joachim Parrow, and David Walker, *A Calculus of Mobile
  Processes* (1992).
- Kohei Honda, Vasco Vasconcelos, and Makoto Kubo, *Language Primitives and
  Type Discipline for Structured Communication-Based Programming* (1998).
- Luca Cardelli and Andrew D. Gordon, *Mobile Ambients* (1998), for dynamic
  localities and movement.
- Cédric Fournet and Georges Gonthier, *The Join Calculus: A Language for
  Distributed Mobile Programming* (tutorial exposition, 2000).

### Continuation-heavy mechanized semantics

- Furio Honsell, Marino Miculan, and Ivan Scagnetto, *Pi-Calculus in
  (Co)Inductive Type Theory* (2001).
- Venanzio Capretta, *General Recursion via Coinductive Types* (2005).
- Keiko Nakata and Tarmo Uustalu, *Resumptions, Weak Bisimilarity and Big-Step
  Semantics for While with Interactive I/O* (2010).
- Mark Bickford, Robert Constable, and Vincent Rahli, *The Logic of Events: A
  Framework to Reason about Distributed Systems* (2012).
- James Perera and James Cheney, *Proof-relevant pi-calculus* (2015).
- Jesper Bengtson, Joachim Parrow, and Tjark Weber, *Psi-Calculi in Isabelle*
  (2016).
- Jianxu Tian, *A Formalization of the Process Algebra CCS in HOL4* (2017).
- Robbert Krebbers et al. / the Iris line, e.g. *Iris from the Ground Up*
  (2018), as evidence that state-rich operational concurrency remains central
  in mechanization.
- Li-yao Xia, Yannick Zakowski, Paul He, Chung-Kil Hur, Gregory Malecha,
  Benjamin C. Pierce, and Steve Zdancewic, *Interaction Trees: Representing
  Recursive and Impure Programs in Coq* (POPL 2020).
- Simon Foster, Chung-Kil Hur, and Jim Woodcock, *Formally Verified
  Simulations of State-Rich Processes using Interaction Trees in Isabelle/HOL*
  (2021).
- Andrea Chappe, Léo Andrès, and colleagues, *Choice Trees: Representing
  Nondeterministic, Recursive, and Impure Programs in Coq* (2022), for a close
  mechanized analogue of interactive trees plus internal choice.

---

## 15. Ranked Comparison Matrix

This section ranks nearby frameworks by closeness to the **current**
`Interaction.Concurrent` abstraction, not by historical importance.

The comparison point is the present kernel:

- a residual `Process`;
- whose current state exposes one finite sequential `Step`;
- with nodewise controller-path metadata;
- and per-party `LocalView` metadata;
- together with a machine-facing interpretation and an initial causal quotient
  layer.

So the relevant question is not merely:

> "Which frameworks formalize concurrency?"

but rather:

> "Which frameworks come closest to this particular mix of continuation-first
> residual behavior, explicit control, local observation, and later causal
> quotienting?"

| Rank | Framework family | Closest ArkLib layer | Why it is close | Main mismatch |
| --- | --- | --- | --- | --- |
| 1 | Interaction Trees / Choice Trees / resumptions | `Concurrent.Process`, `Concurrent.Execution`, future `Concurrent.Observation` | Continuation-first, executable, mechanized, and already comfortable with visible actions, residual behavior, and nondeterministic or concurrent semantics | They do not make scheduler ownership and per-party local views first-class in the way `NodeSemantics` does |
| 2 | Multiparty session types / choreographies | `Multiparty`, future `Interaction.Choreography`, future session frontends | Strongest existing global-to-local protocol story; projection, coherence, and endpoint correctness fit the roadmap directly | Usually narrower than `Interaction` on adversarial scheduling, quotient observations, and non-session protocol structure |
| 3 | I/O automata / Dynamic I/O automata / TLA+ | `Concurrent.Machine`, future `Concurrent.Fairness`, `Concurrent.Liveness`, `Concurrent.Verify` | Best references for enabled actions, explicit scheduling, refinement, fairness, and dynamic component creation | They are flatter than the current kernel because one ArkLib process step may itself be a structured finite sequential episode |
| 4 | Mazurkiewicz traces / event structures / pomsets | `Concurrent.Independence`, `Concurrent.Interleaving`, future `Concurrent.EventStructure`, `Concurrent.Pomset` | Best semantic match for moving from interleavings to causal equivalence and partial-order runs | These are best understood as a refinement layer, not as the first executable kernel |
| 5 | IITM / RSIM / UC | future `Interaction.Security.Protocol`, future `Interaction.Knowledge`, scheduler-sensitive wrappers over `Process` | Strongest adversarial and ideal/real composition lineage for scheduled, concurrent protocol semantics | They are security frameworks first, not neutral general-purpose local-view protocol kernels |
| 6 | Strand spaces / applied pi / ProVerif / Tamarin | cryptographic frontends and case-study layers | Strong for symbolic adversaries, protocol traces, causality, and information-flow case studies | Control and observation are usually encoded indirectly rather than exposed as first-class semantic fields |
| 7 | Join-calculus / CHAM / Rebeca / workflow nets | future dynamic-concurrency, mailbox, queue, workflow, and orchestration frontends | Strongest precedents once the live system is a changing population of entities, messages, or tasks | More domain-facing than the present kernel and usually less centered on per-party local views |
| 8 | EventML / Logic of Events | architectural wildcard for the split-out library | Unusually close in spirit to an umbrella framework about events, causality, observation, and distributed reasoning | Less of a directly reusable kernel for the present Lean development than the higher-ranked families |

The ranking should be read in the following way.

- Rank 1 is the closest **semantic-kernel** neighbor.
- Rank 2 is the closest **frontend** neighbor.
- Rank 3 is the closest **machine-facing backend** neighbor.
- Rank 4 is the closest **causal refinement** neighbor.
- Rank 5 is the closest **adversarial protocol** neighbor.

So there is still no single existing framework that covers all current axes at
once. The nearest external picture is a **constellation**, not a single
ancestor:

- `ctrees` / `itrees` for kernel style;
- session types / choreographies for projection;
- I/O automata / TLA+ for fairness and verification;
- event structures / pomsets for causal refinement;
- and IITM / RSIM / UC for adversarial composition.

---

## 16. What ArkLib Should Borrow, by Layer

The point of the comparison is not to imitate one existing framework wholesale.
It is to borrow the strongest ideas from each line while preserving the
distinctive center of `Interaction`.

### 16.1. `Concurrent.Process` and `Concurrent.Execution`

Primary references:

- interaction trees;
- choice trees;
- resumption semantics.

What to borrow:

- the conviction that the semantic center can remain continuation-first and
  executable;
- observational equivalence and interpreter/handler patterns over residual
  processes;
- a clean separation between the core semantic carrier and later effect,
  scheduler, or verification interpretations.

What not to borrow as primitive:

- reducing all node metadata to one undifferentiated event signature.

ArkLib's extra structure here is real and should stay explicit:

- controller paths;
- per-party `LocalView`;
- and the fact that one process step may itself be a structured finite
  interaction episode.

### 16.2. `Multiparty` and future choreography/session frontends

Primary references:

- binary and multiparty session types;
- choreographic programming;
- communicating finite-state or endpoint automata as checking backends.

What to borrow:

- projection algorithms from global protocols to local endpoints;
- coherence / well-formedness criteria for global descriptions;
- progress and communication-safety theorem templates;
- explicit distinction between global branching structure and local endpoint
  behavior.

What not to borrow as primitive:

- the claim that every protocol of interest is fundamentally a session-type
  protocol.

Session types should be a major frontend, not the definition of the whole
library.

### 16.3. `Concurrent.Machine`, `Concurrent.Fairness`, `Concurrent.Liveness`, and `Concurrent.Verify`

Primary references:

- I/O automata;
- dynamic I/O automata;
- TLA+.

What to borrow:

- enabled-action presentations for explicit state-indexed users;
- forward and backward simulation templates;
- weak and strong fairness patterns over stable event identifiers;
- dynamic-component creation ideas once the library grows true spawning;
- the discipline that verification-friendly subsets may be flatter than the
  source semantics, provided the compilation to them is justified.

What not to borrow as primitive:

- state-machine-first identity for the whole library.

The machine layer should remain a derived or alternate presentation of the
continuation-first core, not a replacement for it.

### 16.4. `Concurrent.Independence`, `Concurrent.Interleaving`, future `Concurrent.EventStructure`, and `Concurrent.Pomset`

Primary references:

- Mazurkiewicz trace theory;
- event structures;
- pomsets;
- proof-relevant accounts of concurrent residuals and causal equivalence.

What to borrow:

- the view that interleavings should be quotiented by independence rather than
  treated as the final semantic object;
- residuation and commuting-conversion structure beyond bare adjacency swaps;
- explicit configurations, causality, conflict, and partial-order executions;
- canonical run objects at the quotient level when raw trace equivalence stops
  being expressive enough.

What not to borrow as primitive:

- partial-order runs as the first executable representation.

For ArkLib, this is a refinement layer over the current interleaving-capable
kernel, not the very first semantic carrier.

### 16.5. Future `Interaction.Security.Protocol` and `Interaction.Knowledge`

Primary references:

- IITM;
- RSIM;
- UC;
- strand spaces and strand spaces with choice;
- applied pi and symbolic protocol tooling.

What to borrow:

- ideal/real wrappers and simulation-based refinement interfaces;
- explicit corruption, scheduling, and environment/adversary interfaces;
- observational-equivalence and information-flow proof obligations;
- causal / bundle-style views of runs where local knowledge matters;
- symbolic protocol DSLs as optional frontends for case studies.

What not to borrow as primitive:

- identifying the security layer with one single symbolic calculus or one
  single composition theorem format.

The semantic center should stay neutral enough to support several protocol
traditions.

### 16.6. Future spawn, mailbox, queue, and workflow frontends

Primary references:

- join-calculus;
- CHAM;
- actor models and Rebeca;
- workflow nets.

What to borrow:

- the idea that a live concurrent system may be a changing family or multiset
  of active residuals;
- mailbox and queue-oriented source languages that compile into the common
  process core;
- soundness/progress/completion criteria for orchestration-heavy systems.

What not to borrow as primitive:

- spawning or mailbox semantics in the first minimal kernel.

The first kernel should stay small enough that dynamic concurrency remains a
layered extension rather than a baked-in commitment.

### 16.7. Wildcard architectural lesson from EventML / Logic of Events

The strongest wildcard lesson is architectural rather than notational:

- an umbrella framework can center events, causality, and observation
  simultaneously;
- it need not reduce itself to one domain-specific protocol DSL;
- and it can still support extraction, synthesis, or verification workflows on
  top.

That reinforces the main thesis of this note:

- keep one small semantic center;
- keep several frontends;
- and make the bridges between them theorem-carrying.

### 16.8. Immediate consequences for the split-out roadmap

The comparison suggests the following short implementation order.

1. Finish `Process`-level observation, refinement, and fairness layers in a way
   that keeps the kernel continuation-first.
2. Build one serious choreography/session frontend over `LocalView`.
3. Strengthen `Independence` and `Trace.Equiv` toward event-structure or
   pomset semantics.
4. Add ideal/real and observational-equivalence layers for adversarial
   protocols.
5. Only then broaden into spawn-heavy, mailbox-heavy, or workflow-heavy domain
   frontends.

This order matches both the current codebase and the nearest surrounding
framework landscape.
