# Proposed mathematical contract for the interaction-security night

Status: authorized by the user on October 3, 2026; run started at 00:56:52 America/New_York
(04:56:52Z), with an eight-hour deadline at 08:56:52 (12:56:52Z). These are the accepted mathematical
obligations. Proposed names are not a claim that Lean declarations already exist; literal public
types require the specified statement review. The [roadmap](05-roadmap.md#october-3-authorized-run)
records sequencing, and the [run record](../kb/audits/interaction-night-20261003.md) records evidence.

## 1. Common carrier and scope

Fix a native oracle protocol P and a fixed input x, including the realized input-oracle behavior
used to interpret its relations. Fixing that behavior for the mathematical experiment does not
give the prover or verifier unrestricted access to its representation.

- Pref(P) is the existing concrete ExecutionPrefix carrier.
- A step e : p -> q is one valid native extension, retaining the actual public move or oracle
  message. Its role comes from the protocol's existing role decoration. Oracle sends are prover
  steps. A public move is classified by its actual role, not its payload type.
- A finite segment is an existing native prefix continuation; a complete path is the existing
  ExecutionPath. Any list of steps used in a proof must be derived from those carriers, with a
  reconstruction law. It is not an independently supplied transcript or a second executor.
- At a verifier prefix p, mu_p is a specified fresh-challenge ProbComp program and q(p,a) is the
  native extension by its result. The result may include a public abort, e.g. Option F. A map
  from this local model to an actual verifier requires a proved execution equation.
- For the initial fragment, the terminal observation out(x,t) is deterministic from the fixed
  input and complete path t. Its equality to the supported verifier's actual output is a
  separate client theorem. It may include explicit rejection.

The deterministic path theory supports dependent continuations and witness types. The ordinary
probability theorem covers the supported native public-coin fragment with fresh verifier choices.
The state-restoration theorem below covers a general fixed-round public-coin IOR presentation,
embedded into native protocols with proved execution correspondence. It does not claim that every
dependent native protocol automatically has the same restoration presentation. Hidden persistent
worlds and commitment-query traces remain separate obligations.

## 2. Ordinary local security: proposed definitions

Let I(x) mean that the input claim is true, and let O(x,t) mean that the terminal output claim is
true. Rejection makes O false. Let S_x(p) be a scalar state predicate on concrete prefixes.

A proposed OrdinaryState certificate contains these structural laws:

1. Initial: not I(x) implies not S_x(root).
2. Prover preservation: for every prover step e : p -> q, S_x(q) implies S_x(p).
3. Terminal: O(x,t) implies S_x(terminal(t)).

The stronger CY-shaped specialization additionally requires not S_x(root) for every input,
including true inputs. Do not identify this stronger initial law with clause 1.

Define the local escape event at a verifier prefix p by

    Escape(x,p,a) := not S_x(p) and S_x(q(p,a)).

The proposed LocalSoundness certificate, for an error family epsilon, states

    for every x with not I(x), and every authored verifier prefix p:
      Pr[a <- mu_p; Escape(x,p,a)] <= epsilon(p).

Every authored prefix means every well-typed concrete prefix. It does not mean a prefix sampled
by honest earlier challenges, a reachable adversary prefix, or a positive-probability prefix.
The sampler and prefix are fixed before its fresh result is sampled. No efficient-adversary claim
is included. Package the experiment using pinned VCVio GameFamily/IsBounded; do not create a new
probability semantics. A certificate records a bound; defining the certificate does not prove
that a protocol satisfies it.

### O1: deterministic escape on an actual path

For every complete native path t, prove

    not I(x) and O(x,t)
      implies some verifier edge p -> q on t has not S_x(p) and S_x(q).

The witness edge must lie on t. The theorem uses the three state laws; it does not use a
probability bound. The empty path case is covered by the initial and terminal laws, rather than
silently assuming a positive number of challenges.

### O2: pointwise-to-random-author bound

For any ProbComp program A producing a pre-challenge prefix of one specified round/error bound,
if every such prefix has local error at most e, prove

    Pr[p <- A; a <- mu_p; Escape(x,p,a)] <= e.

A runs before the fresh challenge. It may fail to return; no normalization assumption may be
introduced without being stated. This is sequential averaging, not a theorem about a prefix
chosen after seeing a challenge, conditional sampling, or a shared hidden oracle world.

## 3. Sumcheck: the concrete MUST theorem

Fix a finite field F, a degree bound d, an injective finite summation-domain enumeration D,
a realized bounded multivariate input polynomial p, and a round i < n. Let the current statement
be (s,h), where h contains i prior challenges. Those challenges are arbitrary field elements;
they need not be drawn from a previous honest execution. Let C_i(p,s,h) be the existing native
closedRelation, with the original input oracle realized by p.

The prover's fixed message q is a univariate polynomial of degree at most d. Define

    check(s,q) := sum over z in D of q(z) = s

    next(s,h,q) :=
      if check(s,q) then sample uniform r in F and return some r
      else return none

    Good(None) := False
    Good(Some r) := C_(i+1)(p, q(r), h ++ [r]).

### S-local: guarded local error

Prove, with exactly the false-current-claim hypothesis,

    not C_i(p,s,h)
      implies Pr[a <- next(s,h,q); Good(a)] <= (d : ENNReal) / card(F).

The bound is at most d/card(F), not an equality. The oracle in Good remains the original p;
it is not replaced by q. Keep all hypotheses of the reused polynomial/successor lemmas explicit.

### S-native: prefix and execution correspondence

Construct the concrete authored prefix/current-state observation and prove that the q, s and h
above are its actual observations. Prove the corresponding segment of the native executor has
the following form, using the same continuation and closing environment as that executor:

    sample/receive the native prover's (q, respond);
    if check(s,q) then
      sample fresh uniform r;
      run respond(Some r);
      continue with (q(r), h ++ [r]) and the retained original oracle
    else
      run respond(None);
      take the actual public-abort branch.

These are proposed mathematical equations, not permission to replace the executor by that
program. They must be proved using its existing normal-form/split equations. In particular,
the response executes on both branches, private continuation data is retained, and response
failure is missing mass rather than successful rejection. The local inequality therefore
applies to the actual supported prefix segment. Merely wrapping an existing inequality in a
record fails this requirement.

A full-protocol scalar certificate for Sumcheck is SHOULD. The candidate for positive-round
protocols is false through the first pre-challenge phase, then the reconstructed current closed
relation after each continuing challenge; abort remains false. Its all-input initial law,
prover law, terminal law and local bound each need proof. For a zero-round protocol accepting
a true input, all-input initial-false and terminal-success-implies-true are incompatible at the
same root. Use the weaker ordinary initial law or state the zero-round false-input theorem
separately; do not hide this boundary case in a typeclass.

## 4. Witness transport: proposed definitions

A proposed WitnessTransport certificate on the same native carrier has:

- W(p), a witness type for each prefix p;
- K(p,w), a knowledge-state predicate;
- for every step e : p -> q, a named map E_e : W(q) -> W(p);
- for every prover step, K(q,w) implies K(p,E_e(w)).

The maps are data, supplied independently of the truth of K. The extraction algorithm must use
computable maps; it never decides K and never chooses a witness from an existential proof.

For the first endpoint theorem, use W(root) as the input-witness carrier and W(terminal(t)) as
the output-witness carrier. State explicit endpoint laws

    K(root,w) iff R_in(x,w)
    K(terminal(t),w) iff R_out(out(x,t),w).

Any use of existing Problem.Witness types needs named carrier identifications or transport maps,
and the client must prove them. Do not assume a bare structural path determines a verifier output;
out must have the S-native-style deterministic observation correspondence for the supported client.
Generalizing the endpoint iff to a one-way terminal extraction map is outside the minimum contract.

### W1: named backward extraction and composition

Define extract(t,w) by traversing the finite native segment t backward and applying its E maps.
For t = e_0 ... e_(m-1), this is

    E_e0(E_e1(... E_e(m-1)(w) ...)).

Prove the dependent split/glue law, with all carrier transports explicit:

    extract(prefix ++ suffix,w)
      = extract(prefix, extract(suffix,w)).

Here append is the existing native continuation operation. A private list fold with an assumed
correspondence to native append does not meet this theorem.

### W2: invalid extraction identifies a bad edge

For every complete native path t and every terminal witness w, prove

    R_out(out(x,t),w) and not R_in(x,extract(t,w))
      implies there is a verifier edge e : p -> q on t such that
        K(q, extract(suffix_after_e,w)) and
        not K(p, E_e(extract(suffix_after_e,w))).

The intermediate witness is the value produced by the named suffix algorithm. It is not an
arbitrary witness manufactured after the proof. This is a deterministic theorem; no security
error, efficient adversary or SR guarantee follows merely from W2.

### W3: the separate local knowledge-security contract

At every authored verifier prefix p, including zero ordinary-run mass prefixes, define

    Bad(p,a) := exists w : W(q(p,a)),
      not K(p, E_(p,a)(w)) and K(q(p,a),w).

A LocalKnowledge certificate with explicit error family epsilon states

    for every authored verifier prefix p:
      Pr[a <- mu_p; Bad(p,a)] <= epsilon(p).

The existential witness is inside the probability. The prefix is fixed before the fresh
challenge; the eventual witness may be chosen after the rest of the protocol. This is the
contract that permits W2 to support offline backward extraction. W2 itself does not need W3.
Reuse VCVio KnowledgeTransitionFamily for its supported fixed-carrier specialization; retain
an explicit adapter if prefix-dependent fibers require the more general GameFamily carrier.

### W4: WARP-shaped specialization, and exactly what is claimed

Specialize to a common witness carrier W, identity E on prover steps, deterministic terminal
observation and the endpoint iff laws. Prove that the prover law becomes

    K(q,w) implies K(p,w),

and that W3 becomes the fixed-prefix witness-indexed event in the inspected WARP/ABF comparison.
This is a clause-by-clause specialization of the mathematical certificate. A full encoding of
every fixed-round paper protocol into native dependent syntax is SHOULD, not part of that claim.
No equivalence with ArkLib's entire legacy definition is asserted: its one-way terminal law,
transformed prover witnesses and computational omissions remain recorded differences.

## 5. Primary targets: reusable general security theorems

The earlier plan made supporting examples into deliverables and deferred the main security
implications. That scope is superseded. The mathematical objective is now the three general
results G1-G3 below. Examples check these results; they are not substitutes for them. The
state-restoration implication G3 is the centerpiece. An eight-hour limit is a resource bound,
not a guarantee that all targets will be proved.

### G1: round-by-round soundness implies ordinary soundness

For a native public-coin protocol P with its actual verifier V and every native prover strategy A,
including probabilistic private memory and failure to return, prove

    not I(x) implies
      Pr[run <- execute(P,V,A,x); validOutput(run)] <= sum_{j<k} epsilon_j.

Assumptions must explicitly supply or prove:

- the ordinary state laws from Section 2;
- the actual verifier-step equation to the fresh program mu_p;
- the local escape bound at every authored prefix of challenge rank j;
- an explicit rank bound: at most k verifier challenges, increasing the rank once per challenge;
- native prefix/current-state reconstruction and the correct run-derived terminal relation.

The theorem is generic in the native protocol and prover, not specific to Sumcheck. Abort is
unsuccessful; missing probability mass is allowed. It must not assume the final bound or assume an
already bounded execution-averaged failure event. The fixed schedule gives sum epsilon_j; the
uniform corollary gives k*epsilon. A later sharper history-dependent budget is a separate claim.

Instantiate the theorem with the existing native Sumcheck protocol to derive count*d/card(F)
through the newly proved general implication. Reusing the existing per-round polynomial bound is
intended; citing the existing whole-protocol soundness theorem is not a derivation of G1. Treat the
zero-round case and positive-round CY initial-state specialization explicitly.

### G2: round-by-round knowledge certificates compose sequentially

Let P1 reduce R_in to R_mid, and let P2(y) reduce R_mid to R_out, where the suffix may depend on
the actual intermediate statement y and supported public history. Given local witness-indexed
certificates for both stages, construct a certificate for their native sequential composition.
The suffix certificate must hold for all relevant authored middle statements and prefixes,
including those for which R_mid has no valid witness. Do not assume an online middle witness.

Prove all of the following as one reusable composition theorem/package:

    E_comp(t1 ++ t2,w) = E1(t1, E2(y,t2,w))

    composite round errors = first-stage round errors followed by the suffix round errors

    composite input/output state laws and prover-step laws hold

    every composite local bad event is the corresponding stage's bad event
      under the proved native prefix/suffix and witness-type identifications.

The seam is the actual intermediate relation and observation:

    K1(terminal(t1),v) iff R_mid(y,v) iff K2_y(root,v).

Any witness-type conversion must be named and proved correct. Preserve well-formedness or
admissibility explicitly; structural output closure must be proved, or an additional error term
must be exposed. Do not replace this with the assumption that the middle relation is true.

The result must use native dependent append/split and actual intermediate output interpretation.
A list-fold identity alone is a supporting lemma, not G2. The probabilistic composition keeps
fresh suffix challenges; it does not assert the analogous theorem for arbitrary persistent worlds.
The existing W1/W2 lemmas become parts of this proof and of G3, not the final overnight achievement.

### G3: round-by-round knowledge soundness implies state-restoration knowledge soundness

Target the inspected WARP Definitions B.1-B.2 and Theorem B.4 with an explicit native realization.
Begin with arbitrary k-round public-coin IORs with finite message/challenge alphabets and uniform
nonempty challenge spaces, arbitrary input/output witness relations, and deterministic terminal
verification. Sizes, alphabets, relations and k are parameters, not a single protocol instance.
The finite presentation is an explicit initial scope restriction; removing it is not silently
claimed. Dependence of round message types on prior challenges needs a separate restoration
presentation and remains open for this theorem.

For every salt length s, every Q-query state-restoration adversary A, and statement set Z, prove

    Pr[z in Z and R_out(out(z,t),w_out)
       and not R_in(z, E(t,w_out))]
      <= (Q+k) * epsilon_max,

where epsilon_max uniformly bounds the local knowledge error over the permitted rounds,
statements in Z and authored prefixes. Relations may be parameterized by the source proximity
parameter delta; the relation-family specialization must retain its original parameter range.
The input z may be selected adaptively by the adversary. Fixing z before all queries is a weaker
intermediate theorem and must not be advertised as this target.

Freeze the restoration game as follows:

1. An adversarial query has key (round j, input z, prover messages through j, salts through j).
2. The key does NOT contain earlier verifier challenges. The adversary may query rounds in any
   order. A repeated key receives the same answer; a fresh key gets the round's uniform challenge.
3. The adversary outputs z, a complete prover-message/salt sequence and an output witness.
4. Completion obtains all k challenges for that sequence from those same random functions.
   It makes at most k additional accesses and does not resample existing answers.
5. The supported native verifier interprets that reconstructed transcript. The named extractor
   runs backward from the supplied output witness. Its allowed input includes the completed
   challenges; this is not ARC's challenge-erased extraction contract.

Use VCVio's existing cached-oracle and probability semantics. Prove the protocol/game execution
correspondence; a newly declared game with an assumed correspondence does not meet G3. Check the
old oracle-reduction challenge oracle for reusable definitions rather than adopting or discarding
it wholesale. Paper salts and adaptive statements remain visible in that comparison.

The hard reusable probability obligation is a fresh-query theorem that accounts for reconstructed
ancestor challenges. For a first access to a key at round j, its strict-ancestor keys are fixed by
that key, even if their responses have never been queried. Prove that secretly completing those
ancestor values and then drawing the target response gives the correct joint distribution.
Ancestor completion is a proof device: it gives the adversary no extra responses and consumes no
additional adversary query budget. Distinct round tags keep an ancestor key distinct from its
current target. Then prove the conditional bad-event bound for the first access and charge at
most Q+k distinct accessed keys, including final completion. Repeated accesses reuse the same event.

Neither an in-order-query restriction nor caching under a full transcript is an acceptable
replacement: both change the source game. Bounding only events measurable from the already-visible
history also skips the reconstructed-ancestor obligation. This proof, the bad-challenge theorem,
and the actual query count must all meet in the exported SR security theorem.

The source quantifies deterministic adversaries; arbitrary randomized adversaries are a desirable
coin-averaging extension. The extractor is the named computable backward algorithm. No polynomial
running-time claim is made without a formal cost proof; record that remaining difference from the
full source theorem. General semantic runtime accounting must not be inferred from Lean reduction.

## 6. Optional diagnostic witness client

Propose a small arithmetic relation-transport client over F = ZMod 5:

    R(a,b;w) := (w-b)^2 = a.

A challenge r changes the public statement (a,b) to (a,b+r); backward extraction maps w to w-r.
For every r,w, prove

    R(a,b+r;w) iff R(a,b;w-r).

Two native challenge stages r then s must yield extract(w) = w-s-r, with the split/glue law
derived through the native path operations. The local bad event is empty and has probability
zero. This is a mechanics client, not a new cryptographic argument or a claim of hard extraction.

At a=4, b=0, r=s=1, the valid terminal witnesses 4 and 0 extract to different valid input
witnesses 2 and 3. Use those to rule out an implementation that ignores the supplied later
witness. Check a nonzero-shift example to rule out identity extraction. Run the supplied
computable maps and extractor, in addition to proving their properties. The client need not
pretend its witness is cryptographically hidden.

This common-carrier client does not test dependent witness types. It is optional diagnostic
coverage and earns no credit toward G1-G3 by itself. Where the public composition theorem exposes
dependent witness types, its native clients and review must exercise those identifications.

## 7. Priority and publication contract

### MUST: the mathematical objective

1. G1: the general local-to-global ordinary-soundness theorem over actual native execution,
   instantiated to obtain native Sumcheck soundness through that theorem.
2. G2: sequential composition of local knowledge certificates with the actual intermediate
   relation, native transcript decomposition, named composed extractor and transported local bounds.
3. G3: the source-faithful round-by-round-to-state-restoration knowledge-soundness theorem with
   the (Q+k)*epsilon_max bound, including out-of-order queries, salts and adaptive statements.
4. Literal public-import consumers, principal axiom checks, required repository validation,
   orchestrator-owned strict semantic review and independent read-back, plus substantial PRs.

Definitions, deterministic supporting lemmas, finite examples and weaker intermediate theorems
are progress toward these targets. They do not count as completion of the mathematical objective.
If a target remains incomplete at deadline, report the actual proved frontier and keep the full
target visibly open. Do not downgrade it into optional work to claim a successful night.

### SHOULD

1. Formal extraction-cost composition using an existing cost model, with the sum of local
   extraction costs and any transcript-processing overhead stated separately. Do not invent a
   running-time claim from the number of function calls.
2. Sharper nonuniform/history-dependent error budgets, plus randomized-adversary extension of
   G3 if the primary proof follows the source's deterministic-adversary statement.
3. An exact comparison/adapter to relevant legacy definitions and textbook specializations,
   beyond the source-clause and native-execution correspondence required for G1-G3.

### HOPE

An additional genuine protocol application of G2/G3 beyond Sumcheck, chosen only after its witness
relation and premises have been checked; or a useful separation theorem that resolves an ambiguity
between the existing security notions. Small arithmetic examples are checks, not stretch outcomes.

### Substantial PRs and publication order

Each implementation PR must deliver one important mathematical result together with its actual
client and the evidence needed to review it. Target roughly 500-1500 changed lines (additions plus
deletions, across the whole PR). A well-contained important result below 500 lines is welcome.
Do not pad a diff, split a coherent result into definitions-only micro-PRs, or hide supporting
changes from the size accounting. If a slice grows beyond roughly 1500 lines, reconsider its
scope and split at a meaningful mathematical boundary while keeping each part independently
useful and reviewable. Small internal commits and worker checkpoints need not become separate PRs.

| PR | Contents | Base |
|---|---|---|
| 0 | Research notes and agreed contract, preserving proposed/open status | main |
| 1 | General round-by-round-to-ordinary soundness over native execution, with its Sumcheck instantiation (G1) | main |
| 2 | General sequential composition of round-by-round knowledge soundness, including backward extraction and native witness/relation correspondence (G2) | main, or PR 1 if a concrete shared helper is needed |
| 3 | Round-by-round knowledge soundness implies state-restoration knowledge soundness, including the fresh-query probability theorem (G3) | PR 2; include both only if the combined result stays coherent and within the size target |

PR 1 contains its Sumcheck consumer; PR 2 may progress independently. PR 3 depends on the
backward-extraction result and its reviewed observation contract. A necessary generic probability
lemma belongs at its library owner; do not force a toolchain migration or duplicate the semantics
to avoid that boundary. Do not open a PR containing only unused scaffolding. Draft status remains until
that slice's mandatory checks and semantic review pass; disclose pending CI. No merging is
authorized. The root orchestrator owns shared helpers, integration, all pushes and PR operations;
two Sol High workers own separate ordinary/Sumcheck and witness worktrees, with independent review.

### Orchestrator-owned strict review

The main orchestrator applies the user-invoked review-lean-formalization skill and personally
reviews every retained worker diff. Delegating an independent review does not delegate the
acceptance decision. Worker self-reports and successful builds are evidence to inspect, not
approval. Review the exact PR base/head and pinned dependencies, and record a verdict for each
PR and the assembled result: approve, request changes, or insufficient evidence.

For each main definition and theorem, the orchestrator checks the literal quantified statement,
implicit assumptions, satisfiable hypotheses, boundary cases, observations available to each
party/extractor, randomness order, failure event and claimed quantitative bound against this
contract and its source. Review the actual execution correspondence and clients; reject vacuous
certificates, assumed correspondence, hidden strengthening of hypotheses, and a weaker result
advertised as the target. Check whether a smaller existing definition or theorem suffices before
accepting new abstractions. Public names and explanations are part of this review.

Use a fresh independent reviewer for blind read-back of new principal statements and semantic
interfaces. Give it the necessary code, definitions, instances and pins, withholding the intended
claim and author explanation until its mathematical reading is recorded. The orchestrator then
compares that reading with the intended contract. A reviewer who has already read the intended
claim can give an ordinary review, but that review must not be called blind.

Check public imports, transitive axiom dependencies, executable extraction where claimed, and
required repository validation separately from semantic fidelity. No missing reviewer verdict
counts as approval. Findings identify the declaration, severity, consequence, smallest repair and
whether they block acceptance. Recheck material fixes and any changed principal type or dependency;
an earlier verdict does not approve a later unreviewed head. Unresolved correctness findings block
acceptance; unmet evidence gates remain explicitly pending.

### Language and naming for cryptographers

Implementation names, public types, theorem names, docstrings and PR descriptions must be broadly
understandable to a cryptographic audience. Follow the existing
[interaction naming guide](../wiki/interaction-naming.md). Prefer established words such as
prover, verifier, message, challenge, transcript, witness, relation, soundness, knowledge soundness,
extractor and sequential composition. Say what an object or theorem does in a proof system.

For example, explain W1 as backward witness extraction and propose names such as RoundExtractor,
extractWitness, extractWitness_append, and extraction_failure_implies_bad_challenge, subject to
existing namespace conventions. Explain O1 as a bad challenge on an accepting execution from a
false input. These are naming candidates, not new frozen Lean declarations. Internal proof labels
O1, W2 and S-native are contract references, not names to export as the public API.

Avoid newly coined abstract terms, unexplained acronyms, or long combinations of implementation
words when an ordinary cryptographic term is precise. In explanations, prefer "witness type at
this transcript prefix" to "witness fiber", "remaining prover strategy and private memory" to an
unexplained "continuation", and "a challenge where extraction fails" to an unexplained "bad edge".
Keep genuine distinctions explicit: an execution prefix can contain full oracle messages, whereas
a verifier's view may contain only queried answers. Simple language must not conflate those objects
or call a deterministic extraction lemma a knowledge-soundness theorem.

Every principal docstring starts with the mathematical claim and its assumptions. Explain the
representation only afterward, where needed. The orchestrator can return a mathematically correct
API for naming/exposition revision when its public terminology obscures its cryptographic meaning.

## 8. Uncertainty and no-drift rules

The largest uncertainty is the source-faithful restoration model and its fresh-response proof
when earlier challenges have not been queried. Other uncertainties are the native rank induction,
actual middle-statement/witness identification in dependent composition, the available cached-oracle
lemmas at the pinned VCVio revision, and the cost model for extraction. These are real mathematical
and implementation risks. The full G1-G3 target may exceed eight hours. They may not be bypassed by
changing the event, excluding out-of-order queries, granting extra observations, or assuming a
security bridge. Record a failed proof attempt's exact obstruction and strongest checked theorem.

The first worker deliverable in this run is the literal elaborated Lean types and their
contract comparison. A false target, missing native correspondence, or unexpectedly strong
hypothesis is reported as such. A restricted replacement is separately named and reviewed; the
original MUST remains incomplete. No classically chosen witnesses, new admissions, parallel
interpreter, dependency upgrade, or reused whole-security theorem may stand in for a missing core
obligation. The proposed mathematical naming is provisional; the mathematics is the freeze point.

Not targeted tonight: unconditional CY/ARC/BGTZ/WARP/tree-extraction equivalences; commitment
realization; Funky or duplex compiler proofs/repairs; zero knowledge; QROM; or a universal
persistent-world security model. G3's SR game and quantitative bound are now primary targets;
full extraction-time accounting is explicitly SHOULD. Those remain
explicit long-term targets in the [literature comparison](../kb/audits/interaction-literature-map.md).

The six-hour checkpoint is 06:56:52 America/New_York. Freeze expansion at 07:26:52 and reserve
the final 90 minutes for consolidation before the 08:56:52 deadline. If MUST remains unfinished, preserve and push the strongest
verified checkpoint, mark remaining PRs draft, and report exactly which mathematical obligations
remain. A successful time-boxed handoff does not mean an incomplete theorem was proved.
