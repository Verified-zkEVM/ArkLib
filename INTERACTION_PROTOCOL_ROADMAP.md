# Interaction Protocol Roadmap

This note turns the recent literature scan into a concrete roadmap for the
long-term `Interaction` split-out.

The goal is not to chase one existing framework. Instead, the goal is to make
`Interaction` a good semantic home for protocols whose meaning depends on some
combination of:

- who controls a step,
- who observes which part of it,
- how a global protocol projects to local behavior,
- which concurrent steps commute,
- and what counts as the "same" run up to scheduling.

That is a broader target than ArkLib's current cryptographic use cases, and it
is also broader than any one existing frontend or proof workflow.

## Thesis

`Interaction` should aim to specialize in:

- structured steps rather than only atomic transitions,
- explicit local views and partial observation,
- explicit control and scheduler structure,
- global/local protocol projections,
- concurrency modulo independence rather than only raw interleavings,
- and reusable semantic frontends for several protocol traditions.

The current library already has the right nucleus for that:

- [`Interaction.Spec`](ArkLib/Interaction/Basic/Spec.lean)
- [`Interaction.Multiparty.LocalView`](ArkLib/Interaction/Multiparty/Core.lean)
- [`Interaction.Concurrent.Process`](ArkLib/Interaction/Concurrent/Process.lean)
- [`Interaction.Concurrent.Tree`](ArkLib/Interaction/Concurrent/Tree.lean)
- [`Interaction.Concurrent.Independence`](ArkLib/Interaction/Concurrent/Independence.lean)

## Literature-Driven Target Families

The table below gives a concrete "protocol family -> current fit -> missing
pieces -> theorem suite" map.

| Family | Representative literature | Why it fits `Interaction` | Current fit | Missing pieces | Core theorem suite |
| --- | --- | --- | --- | --- | --- |
| Binary and multiparty session protocols | [Honda, Vasconcelos, Kubo 1998](https://di.fc.ul.pt/~vv/papers/honda.vasconcelos.kubo_language-primitives.pdf), [Honda, Yoshida, Carbone](https://www.doc.ic.ac.uk/~yoshida/multiparty/multiparty.pdf), [Coherence Generalises Duality](https://homepages.inf.ed.ac.uk/wadler/papers/multiparty/multiparty.pdf) | Control, observation, and projection are first-class; branching is global but internal/external choice is local | Strong for binary and local multiparty views | Global choreography frontend, projection algorithms, coherence checks | duality, projection soundness, communication safety, progress, deadlock freedom |
| Choreographies and global protocol DSLs | [A Core Model for Choreographic Programming](https://www.sciencedirect.com/science/article/pii/S0304397519304311), [Dynamic Choreographies](https://arxiv.org/abs/1611.09067), [The Paths to Choreography Extraction](https://arxiv.org/abs/1610.10050) | A global protocol should compile to local behaviors by theorem, not by convention | Partial: `Spec` already gives dependent global trees | Native choreography syntax, endpoint synthesis, extraction from locals | endpoint compilation correctness, race freedom by construction, refinement |
| Adversarial network and cryptographic protocols | [UC](https://eprint.iacr.org/2000/067), [RSIM](https://eprint.iacr.org/2004/082.pdf), [IITM](https://link.springer.com/article/10.1007/s00145-020-09352-1), [Applied Pi Calculus](https://arxiv.org/abs/1609.03003), [Strand Spaces](https://people.csail.mit.edu/jherzog/papers/Strand_Spaces.pdf), [Strand Spaces with Choice](https://arxiv.org/abs/1904.09946) | Adversarial scheduling, selective delivery, adaptive corruption, and partial observability are central semantic objects | Strong semantic fit through `LocalView`, `NodeSemantics`, and `Process` | Knowledge/equivalence layer, fairness, ideal/real wrappers, cryptographic frontend notations | noninterference, secrecy/authentication, simulation/refinement, scheduler robustness |
| Knowledge and anonymity protocols | [Knowledge and Common Knowledge](https://arxiv.org/abs/cs/0006009), [Epistemic protocols for dynamic gossip](https://www.sciencedirect.com/science/article/pii/S1570868316301161), [Epistemic Model Checking for Anonymous Broadcast](https://arxiv.org/abs/1004.5130) | The interesting semantics is often "who knows what, and when" rather than only reachability | Very promising because `LocalView` already models partial knowledge | Epistemic layer, observational equivalence, anonymity/noninterference proof infrastructure | knowledge monotonicity, indistinguishability, anonymity, controlled release |
| True-concurrency and causal protocols | [Winskel Event Structures](https://www.cl.cam.ac.uk/~gw104/Winskel1987_Chapter_EventStructures.pdf), [Event Structures for Mixed Choice](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CONCUR.2019.11), [Causal Linearizability](https://arxiv.org/abs/1604.06734) | These protocols care about commuting independent steps, causal equivalence, and partial orders, not just traces | Good initial fit through `Independence` and `Trace.Equiv` | Event-structure or pomset frontend, quotient-level execution APIs, fairness over partial orders | diamond/commutation laws, causal equivalence, refinement modulo reordering, linearizability variants |
| Scheduler-first distributed algorithms | [I/O Automata](https://groups.csail.mit.edu/tds/i-o-automata.html), [TLA+](https://lamport.org/pubs/lamport-spec-tla-plus.pdf), [Dynamic Input/Output Automata](https://arxiv.org/abs/1604.06030) | Many distributed proofs are about enabledness, fairness, and action structure | Good `Machine` and `Process` fit | Native fairness/liveness, stronger machine-facing verification layer, automation subset | invariant preservation, refinement, fair-trace correctness, liveness under fairness |
| Actor, workflow, and asynchronous coordination protocols | [Rebeca](https://rebeca-lang.org/), [Workflow nets overview](https://www.sciencedirect.com/science/article/abs/pii/S0377221700002927), [Hybrid Rebeca](https://arxiv.org/abs/1901.02597) | Mailboxes, workflows, and orchestration naturally have explicit control transfer and concurrency structure | Moderate fit today | Dynamic spawning, queue/mailbox frontend, time and resource annotations | progress, absence of stuck states, causality-preserving refinement, orchestration correctness |
| Cyber-physical and human-in-the-loop protocols | [Timed I/O Automata](https://link.springer.com/book/10.1007/978-3-031-02003-2), [Hybrid Automata](https://arxiv.org/abs/1503.04928), [Human-Cyber-Physical Automata](https://www.sciencedirect.com/science/article/pii/S1383762123001686) | Authority handoff, timing, and observation boundaries matter | Limited today | Time, deadlines, continuous dynamics frontends, control-policy interpretation | safety envelopes, handoff correctness, timing refinement, mixed-initiative control properties |
| Games and strategic multi-agent interaction | [Games and Strategies as Event Structures](https://lmcs.episciences.org/3966), [Disentangling Parallelism and Interference in Game Semantics](https://arxiv.org/abs/2103.15453), [Concurrent Games in Dynamic Epistemic Logic](https://www.ijcai.org/proceedings/2020/260) | Control paths can be read as strategy ownership; local views as information sets | Conceptually aligned, but not implemented | Strategy semantics, winning conditions, game-theoretic refinements, synthesis | strategy refinement, equilibrium conditions, information-set soundness, game equivalence |

## What These Protocols Actually Look Like

The common pattern across the literature is not "just a state machine with a
different syntax". It is usually some richer tuple:

- a structured step shape,
- a local observation policy,
- a control or scheduler policy,
- a concurrency or causality structure,
- and a notion of behavioral equivalence or refinement.

Concrete examples that already fit the current library well:

- selective delivery, dropping, duplication, and metadata leakage,
- adaptive corruption where later local views depend on earlier adversarial
  choices,
- scheduler-sensitive message races,
- branching multi-party protocols with different endpoint views,
- concurrent systems where correctness is invariant under commuting
  independent steps.

Concrete examples that should become first-class next:

- choreography-to-endpoint protocol compilation,
- fair exchange and accountable delivery protocols,
- anonymous broadcast and gossip protocols,
- causal broadcast and replicated-object protocols,
- mailbox and workflow protocols with spawning and cancellation,
- fairness-sensitive distributed algorithms,
- timed supervisory or escalation protocols.

## Recommended Execution Order

The roadmap below is ordered by leverage against the current codebase, not by
historical priority.

### Phase 1: Finish the concurrent semantic core

Goal:
make the existing `Process`-centered concurrency layer the stable foundation
for future frontends and proof layers.

Work:

- Add fairness and liveness over stable tickets.
- Add a process-level observational equivalence layer.
- Add stronger quotient-facing APIs over `Independence` and
  `Trace.Equiv`.
- Add a process-level refinement relation and simulation templates.

Deliverables:

- `Concurrent/Fairness.lean`
- `Concurrent/Liveness.lean`
- `Concurrent/Refinement.lean`
- `Concurrent/Observation.lean`

Theorems:

- weak and strong fairness,
- safety under refinement,
- scheduler-robustness lemmas,
- observational congruence for process frontends.

### Phase 2: Choreography and session frontends

Goal:
make global protocol structure and local endpoint structure both first-class.

Work:

- Add a choreography/global-protocol frontend.
- Add projection to local endpoints.
- Recast binary and multiparty session views as canonical frontends.
- Add connection to communicating finite-state or machine views where useful.

Deliverables:

- `Interaction/Choreography/`
- `Interaction/Session/TwoParty/`
- `Interaction/Session/Multiparty/` only if it adds value beyond native
  `Multiparty`

Theorems:

- projection soundness,
- endpoint coherence,
- progress under coherence assumptions,
- refinement between choreography and process views.

### Phase 3: Knowledge and adversarial protocol semantics

Goal:
exploit `LocalView` as a primary semantic axis rather than a convenience.

Work:

- Add observational equivalence and information-flow definitions.
- Add knowledge-style views of traces or configurations.
- Add ideal/real wrappers for adversarial protocol reasoning.
- Add canonical examples: anonymous broadcast, adaptive corruption,
  selective-delivery network semantics, fair exchange.

Deliverables:

- `Interaction/Knowledge/`
- `Interaction/Security/Protocol/` or a similarly named neutral layer

Theorems:

- noninterference,
- controlled declassification,
- anonymity/unlinkability style properties,
- ideal/real or simulation-based refinement.

### Phase 4: Partial-order and event-structure semantics

Goal:
move from "interleavings plus independence lemmas" to genuine causal models.

Work:

- Add an event-structure or pomset frontend.
- Define translation from structural concurrent specs to partial-order views.
- Add configuration semantics and causal equivalences.
- Connect scheduler-trace quotienting to explicit causal objects.

Deliverables:

- `Concurrent/EventStructure.lean`
- `Concurrent/Pomset.lean` or one chosen canonical frontend

Theorems:

- soundness of event-structure semantics,
- equivalence of commuting traces and causal configurations,
- refinement modulo causality,
- causal linearizability style results.

### Phase 5: Solver-friendly verification subset

Goal:
benefit from automation without turning the whole library into a flat
transition-system DSL.

Work:

- Define a first-order or machine-friendly verification subset over
  `Concurrent.Machine`.
- Generate invariant and safety obligations.
- Add a compiler from suitable `Process` or `Tree` fragments into that subset.
- Keep room for interop with external automation and model-checking tools where
  that helps.

Deliverables:

- `Concurrent/Verify/`
- optional interop modules only when they clarify the design rather than
  distorting it

Theorems and tools:

- invariant preservation,
- safety from inductive invariants,
- compiler correctness from structured frontends to the verification subset.

This phase should be explicitly subordinate to the semantic design. Automation
is a backend for a subset, not the definition of the library.

### Phase 6: Domain-specific frontends

Goal:
support interaction-heavy domains outside classic cryptography and session
types.

Possible frontends:

- mailbox and queue protocols,
- workflow/orchestration protocols,
- timed and deadline-sensitive protocols,
- actor and spawn-heavy protocols,
- strategic or game-like protocols.

This phase should be driven by representative case studies rather than by
trying to pre-build every domain abstraction at once.

## Concrete Case Studies to Build

The following examples would exercise the roadmap in a disciplined way.

### Near-term

- A small choreography with projection and endpoint correctness proof.
- A selective-delivery adversarial network protocol with an
  observational-security statement.
- A causal-broadcast toy model with independence and reordering theorems.
- A machine-facing compiled example that admits automated invariant checking.

### Medium-term

- Anonymous broadcast or DC-net style protocol with local-view-based
  indistinguishability.
- Fair exchange or accountable delivery with scheduler-sensitive semantics.
- A workflow or actor example with spawning and cancellation.

### Long-term

- An async consensus or reliable-broadcast development where scheduler
  fairness and partial observation both matter.
- A reusable global-to-local protocol frontend that handles real multi-party
  examples.
- A partial-order refinement story for replicated objects or causally
  consistent services.

## Design Rules for the Split-Out Library

These should remain stable even as frontends multiply.

1. Keep the semantic center continuation-based.
   State-indexed frontends are welcome, but should compile into a smaller
   semantic core rather than define the library's identity.

2. Keep control and observation orthogonal.
   Who chooses a step and who learns about it are related, but not identical.

3. Treat concurrency as more than interleaving.
   Interleavings are useful, but independence and causal equivalence should
   remain first-class.

4. Prefer semantic bridges over replacement.
   Different fields already have their own surface syntaxes. `Interaction`
   should absorb them through common semantics and theorem-preserving
   translations.

5. Keep automation as a layer, not the foundation.
   The solver-friendly subset should be important, but it should not flatten
   away the structures that make `Interaction` distinctive.

## Bottom Line

The strongest long-term niche for `Interaction` is:

- a reusable semantic library for structured concurrent interaction,
- with first-class control, observation, projection, and causality,
- broad enough to support session protocols, adversarial distributed
  protocols, knowledge-sensitive systems, workflows, actor systems, and
  eventually timed or strategic variants,
- while still offering a disciplined machine-facing subset for automation.

That combination is broad enough to outgrow ArkLib, but concrete enough to
guide implementation choices now.
