# Chiesa-Yogev and the interaction framework: comparison and research notes

The long-term target is the Chiesa-Yogev textbook in ArkLib's own language and generality.
For a covered textbook result, we should recover its experiment, quantifiers, information
access and parameter bounds as a proved specialization. A stronger abstraction is useful only
if that recovery is explicit. A different experiment should be named and compared as such.

These are working research notes, not an adopted replacement architecture or a novelty claim.
They preserve promising directions alongside objections and unresolved alternatives. The
[roadmap investigation](../../design/05-roadmap.md#bounded-cy-theory-investigation-proposed)
owns the proposed execution plan; this page owns the literature comparison.

## Evidence and scope

Checked on October 2, 2026, America/New_York, against:

- ArkLib `ace55c3e29da1fc55a321378ada55ea4f7ed8790`.
- VCVio main `f5119c64ebb055d69c143704e12eba6df7dc386c`, while ArkLib actually pins
  `d7089e46d69e07640fa23b5ae6b1b966f1d4b949`.
- ArkLib's PolyFun pin `3710d71b28404a151b8d1f0ce080ea448778dec0` and Lean 4.34.0.
- [CY version 1.2, March 25, 2026][cy], official TeX at
  `305fa3d9d19ee6dba135de64b3156d1760df8426`; see [source metadata][metadata].

The observations below come from source inspection. Statements described as proved have proof
bodies in the inspected source; this research comparison is not a new transitive axiom audit.
Proposed theorems and counterexamples below have not been formalized by this investigation.
The archived pre-split oracle-reduction audit is historical: its missing-runtime and missing-log
claims must not be copied into a description of current native code.

## Where progress stands

The native C1-C8 foundation sequence is implemented: execution and continuation access,
routing and closing, persistent runtime and log composition, ordinary soundness, and query
budget certificates. See [current status](../../design/00-current-status.md) and the
[execution design](../../design/03-adversarial-oracle-execution.md).

Native Sumcheck has an ordinary soundness theorem for arbitrary native prover strategies,
with error at most `count * deg / |F|`, starting from a false claim about a realized bounded
polynomial input oracle and ending in a true closed evaluation claim. The output equality to
the original polynomial is a relation, not an extra verifier query silently performed at the
end. Computable messages/verifier and a general finite-enumeration honest prover have
whole-execution correspondence and completeness theorems. Computability is not an efficiency
claim. The current witness is `Unit`; this does not extract a hidden polynomial.

Sources: [protocol and output relation][sumcheck-protocol],
[ordinary soundness][sumcheck-soundness], [computable soundness][sumcheck-computable],
[computable completeness][sumcheck-completeness].

The central missing layer is the precise security theory connecting those native executions
to arbitrary-prefix games, state restoration, extraction and the compiler. Existing execution
infrastructure makes that work possible; it does not itself prove those connections.

## Whole-book direction, without a false coverage claim

| Book component | Current foothold | Still required or not yet audited |
|---|---|---|
| Random oracles and basic cryptography | VCVio oracle programs, cached worlds, logs, query and collision bounds | Match each source experiment and resource convention; no whole-chapter audit yet |
| Sigma protocols, IPs and Fiat-Shamir | Protocol and ROM infrastructure; legacy FS constructions | Exact transform, backtracking, malformed-query simulation and security correspondence |
| Commitments and online Merkle extraction | VCVio deterministic binding and strong raw-digest extraction results | Encoded payload, salt/configuration, event and resource transport |
| PCPs, Kilian and Micali | General proof-system and commitment ingredients | Source-specific constructions and theorem inventory not audited here |
| IOPs, interactive BCS and BCS | Native oracle reductions, output interfaces and compiler design | SR games, interactive lowering, hash-chain compiler and composed security |
| Special soundness and RBR | Legacy transcript-tree algebra and fixed-prefix conditions; native Sumcheck challenge lemma | Native contracts, source specialization, tree finding and probability/time bounds |
| Knowledge and zero knowledge | Several legacy extraction notions and modern runtime/log semantics | Observation/timing correspondence, efficient extractors, verifier views and simulation |
| Preprocessing, commit-and-open, witness indistinguishability | Potentially reusable general interfaces | Coverage deliberately unassessed; retain as targets |

This is a navigation map, not an exhaustive theorem matrix. A later coverage inventory should
record each source label and version, the native statement, its specialization theorem, exact
losses, implementation status and axiom status. Optional clear messages already appear in the
book, and its general oracle distributions can correlate functions: neither feature alone is
an original generalization by ArkLib.

## Differences that determine the mathematics

### 1. Reductions produce claims, rather than only decisions

ArkLib's reduction can return an output statement, a witness family and a virtual oracle
interface derived from earlier messages. CY's relevant proof-system security experiment
eventually asks whether a verifier accepts. A connection must specify the closing verifier,
the realized original input, the output relation and the information that the closer may query.
It cannot identify validity of an output relation with an actual verifier check for free.

This is a useful place for a conceptual contribution: prove how security and access guarantees
compose through intermediate claims, then recover terminal proof systems as special cases.
Whether every compiler stage materializes an oracle or preserves a virtual view remains open.
See [claims and closing](../../design/02-oracle-reduction-core.md).

### 2. Ideal refined messages versus arbitrary strings

Native message types can require a degree bound or another algebraic promise. A malicious
native strategy must inhabit that type. In the book's string IOP, a malicious prover supplies
arbitrary strings of the prescribed length. Merkle-committing an arbitrary vector does not
establish a degree or codeword promise.

Possible bridges include coefficient encodings with their actual evaluation/query costs,
low-degree or commitment-backed enforcement, and an explicitly relaxed relation with decoding
and query-agreement guarantees. Proximity alone does not supply exact codeword membership.
Keep the adopted ideal model; make its realization obligation explicit. No concrete backend
choice is settled here. See [compiler guarantees](../../design/04-oracle-elimination-compiler.md)
and [CY's IOP definition][cy-iop].

### 3. Dependent schedules, early rejection and public coins

The native [type tree][type-tree] and [protocol][native-protocol] permit a public move to choose
the continuation, including future message types. Native Sumcheck queries its round message
before returning an optional challenge, with `none` closing the interaction. The book's
[public-coin IOP][cy-public-coin] uses fixed rounds and independently uniform verifier messages;
queries can be postponed because they do not determine these messages.

One possible route is a certified fixed-schedule specialization for compiler theorems. Another
is a theorem for bounded dependent schedules with a proved fixed-round corollary. Neither is
adopted globally here. Ordinary native RBR can first treat a rejecting branch as a terminal
failure without normalizing the whole protocol. Recovering the book's exact syntax may still
need padding or normalization. Delaying rejection can execute extra prover/oracle effects:
acceptance preservation does not imply equality of complete traces or final world states.

Well-founded execution does not give a uniform round bound. A public natural number can select
a chain of that length: every path terminates, while path lengths are unbounded. A bound such
as `(B + r) * error` needs a uniform challenge rank or a separately charged completion budget.

### 4. Ordinary RBR is local at adversarially selected prefixes

In [CY's RBR experiment][cy-rbr], the adversary supplies previous prover strings **and previous
verifier challenges**. Only the selected next challenge is sampled freshly. The state starts
at zero, stays zero on prover moves, and a complete zero-state transcript must reject. The
bound is conditioned on the pre-challenge state being zero.

The legacy [round-by-round module][legacy-rbr] already contains two different conditions:

- `rbrSoundness`, near line 357, averages the bad-edge conjunction over `prover.runToRound`.
- `rbrSoundnessWorstCase`, near line 523, fixes a prefix; the implication to the averaged
  condition is proved near line 592.

For a fixed stateless prefix with preceding state zero, the latter conjunction has CY's local
meaning. Recovering the randomized-prefix formulation requires a mixture/conditioning lemma,
with an explicit convention or positive-mass hypothesis for conditioning on a null event.
An ordinary execution average cannot replace the local bound used after adversarial restoration.

**Candidate separating example.** Take an always-false instance, two independent uniform bit
challenges, `Unit` prover messages, and acceptance exactly when both bits are zero. Let the
state remain zero at every proper prefix, then equal acceptance. The averaged error vector
`(0, 1/4)` holds, hence so does uniform averaged error `1/4`. Any local certificate with uniform
error below `1/2` must stay zero after every first challenge: a single true outcome already has
mass `1/2`. The intervening prover move preserves zero. At the prefix with first bit zero,
terminal acceptance on second bit zero then forces a local error of at least `1/2`. Marking
all-zero challenge prefixes achieves local error `1/2`. This separates even the existential
uniform-error notions, rather than just certificates using the same state function. It is a
mathematical proposal awaiting a finite Lean proof.

The protocol is the two-round instance of CY's
[`claim:tightness-of-soundness-to-rbr-soundness`][cy-rbr-tightness], not a new lower-bound
construction. The added comparison here is to ArkLib's execution-averaged condition. Also,
the book proves a converse with worse parameters: for positive fixed round count `r`, ordinary
soundness error `delta` gives an RBR state with error at most `delta^(1/r)`
([`claim:soundness-to-rbr-soundness`][cy-soundness-rbr]). Thus the issue is preserving the
desired quantitative bound and experiment, not claiming that no ordinary-to-RBR implication
exists. That converse remains a useful later coverage target; its state need not be efficient.

The legacy initial-state law instead identifies state truth with input-language membership.
Restricting ordinary security to false inputs resolves that initial discrepancy. It does not
resolve the all-input knowledge definition. Also, the legacy terminal law executes a verifier
from fresh initialization; a native effectful theorem must refer to the actual retained runtime
state. The [native runtime soundness boundary][runtime-soundness] already follows the latter
discipline.

The pinned VCVio already provides [`RoundByRound.GameFamily`][vc-rbr] with context-dependent
sampling, `IsBounded` and an event-probability characterization. A first native package can
reuse it, adding prefix/state laws and a theorem identifying its local experiment with the
existing verifier interpreter. Sumcheck's guarded `Option` challenge fits this interface:
failing the sum check returns `none` and contributes zero; the passing branch uses the proved
uniform challenge lemma. Preserve the actual response effects even on `none`.

One state-law subtlety remains: the current closed relation may be true at the empty prefix,
where CY requires zero for every input. A proposed positive-round construction resets the
scalar state before the first challenge and thereafter uses the current closed relation, with
abort false. Local soundness is only required on false original inputs. Zero-round false-input
security needs its separate terminal case; do not assert a zero-initial all-input certificate
for an immediately accepting zero-round protocol.

### 5. Knowledge notions differ in observation, timing and bad event

[CY RBR knowledge][cy-rbr-knowledge] quantifies over every instance and arbitrary authored
prefix. After the selected fresh challenge, the adversary supplies an arbitrary adaptive tail
of prover strings. A single polynomial-time extractor receives the instance and all prover
strings, without a separate verifier-challenge input. The bad event is an invalid extracted
witness together with a state transition to one, conditioned on preceding state zero.

This restriction concerns this particular RBR definition. Other book extractors can receive
transcripts, logs or black-box prover access; do not erase those distinctions.

The legacy edge-local extractor instead transports a later witness backward using a transcript
prefix that contains challenges. Its worst-case bad event existentially quantifies an
intermediate witness inside the event. The one-shot variant has another timing contract. These
are different notions, not automatically a hierarchy with CY at the bottom.

Two important consequences:

1. In a dependent tree, a pair `path` together with `messages at path` exposes the public path.
   Naming it "prover messages" does not erase verifier randomness. A CY specialization needs
   an explicit observation and a proof that extraction factors through it. Even then, prover
   strings may themselves depend on challenges, which CY permits.
2. The complement of an existential bad-witness edge gives transport for **every** later
   witness. This can support offline backward extraction, including witnesses chosen after a
   suffix, when observation and effects are compatible. Prefix-available extraction is one
   sufficient route, not a necessary requirement for every knowledge-composition theorem.
   Plain terminal knowledge soundness alone supplies neither route.

Keep observation, execution privileges, witness transport and algorithmic cost explicit while
testing bridges. Do not force them into one universal extractor interface before the examples
show which identifications are sound. A noncomputable choice of an existing witness is not an
efficient extractor.

### 6. SR is an adaptive consistent-query game

In [CY's IOP state-restoration game][cy-sr], response-function inputs encode the instance and
salt/proof prefixes. Repeating a move returns the same challenge. The adversary has a move
budget, and final verification reconstructs all rounds from its output.

The [RBR-to-SR theorem][cy-rbr-sr] loses a factor `B + r`. Its proof needs:

1. Appending the final output's at most `r` reconstruction moves to the actual chronological
   adversarial trace.
2. Identical responses to duplicate moves.
3. Fresh independent randomness at the first occurrence of an unanswered move, after the
   complete prior adaptive history, so the arbitrary-prefix bound applies.

Neither independent suffix replay nor an ordinary union bound over an honestly sampled run
establishes this experiment. The legacy SR soundness declaration lacks a move-budget parameter
and assumes a distribution of response functions; it does not itself certify the required
independent random-function law. Its knowledge extractor type admits logs, but the game passes
empty default logs. See [legacy SR][legacy-sr].

### 7. The compiler needs causal extraction and actual promise transport

The book's [modular BCS construction][cy-bcs] applies hash-chain Fiat-Shamir to interactive BCS.
In the [interactive SR reduction][cy-ibcs-sr], a root is extracted using the Merkle log available
**before that move**, with persistent extraction state; salts absorb the root and old salt.
The proof bounds extraction calls by `Q_FS + 1` per configuration. This requires chronological
interleaving, not just two complete, separately filtered logs.

VCVio has substantial reusable support:

- Persistent runtime and query logging, with run/resume composition and query accounting.
- [Tagged leaf/node hashing][vc-hashing] and [deterministic encoded-leaf binding][vc-binding].
- [Stateful raw-digest extraction checkpoints][vc-stateful] and
  [`anyCheckpointDisagreement_rom_bound_of_prefixQueryBound`][vc-strong], covering accepted
  opening disagreement, repeated roots and terminal checkpoint evolution in a shared cached ROM.

The searched sources do not yet provide a complete encoded/salted payload online-extraction
adapter with the book's configuration law and resource accounting. Raw digest extraction and
encoded-leaf binding are ingredients, not that adapter. The numerical theorem must be transported
to the actual compiler events and budgets, with honest-verifier overhead charged explicitly.
Introduce generic causal trace machinery only when this or another concrete client requires it.

### 8. Hash-chain entropy and knowledge costs are real obligations

[CY's hash-chain construction][cy-hash-chain] pads short randomness so chain responses contain
at least the security parameter's number of bits. An arbitrary sampleable challenge type does
not justify the same collision bound. A separate digest plus decoded challenge, or a padded
challenge carrier, needs a distribution law and any decoding loss. The choice remains open.

Backtracking must recover a unique chain or fail, and malformed/unbacktrackable queries need
their own consistent simulation. VCVio's typed `ReplayFork` and sigma-signature game-hop chain
are useful but are not this multiround hash-chain theorem.

For [BCS knowledge extraction][cy-bcs-knowledge], the inner extractor is invoked at transformed
failure and time arguments: schematically `delta' = delta + error_MT + error_chain` and
`t' = t + time_MT + time_chain`, plus the outer adapter's time. A cost-only reduction structure
does not prove this joint substitution or an expected-time guarantee. Named computable
algorithms, oracle query counts and implementation running time must remain distinct claims.

## What to preserve from the old oracle-reduction layer

| Component | Evidence in the legacy source | Disposition |
|---|---|---|
| Transcript trees, structure predicates and witness fibers | [Basic][legacy-trees]; split/glue and `TreeBased.append` in [Composition][legacy-tree-composition] | Preserve algebra and prove a native correspondence; current arity is indexed by round, not arbitrary dependent path |
| Named coordinate/scalar extraction and backward composition | [Composition][legacy-cwss-composition], especially the right certificate establishing intermediate-language membership before the left runs | Reuse algorithms and proof structure; distinguish supplied-tree extraction from efficient tree finding |
| Committed scalar extraction-or-collision | [CommittedScalar][legacy-committed-scalar] and the non-`Unit` [ring-switching Lift client][lift] | Strong concrete target for a small native bridge |
| Guarded rejection and honest composition | [Guarded][legacy-guarded] and [GuardedCompleteness][legacy-guarded-complete] | Retain rejection and actual-state seam hypotheses, replace old operational interfaces selectively |
| Fixed-prefix ordinary RBR append | [Append/RoundByRound][legacy-rbr-append], with pure first verifier | Useful proof skeleton; do not drop purity or inherit fresh-state terminal assumptions |
| Salt construction and output-query simulation | [Salt][legacy-salt] | Keep concrete syntax/simulation lemmas; whole-execution and SR security transport remain obligations |
| General knowledge composition and RBR implications | [Append/Security][legacy-security-append] and [Implications][legacy-implications] contain admissions | Desired conclusions to restate and prove, not established infrastructure |
| Rewinding and SR operational interfaces | [Rewinding][legacy-rewinding] lacks an implemented runner; [SR][legacy-sr] discards actual logs in its knowledge game | Preserve intended capabilities in notes, replace deficient game contracts |
| BCS, slow FS and sponge security | [BCS][legacy-bcs] has a message rename with larger transforms commented; [FS][legacy-fs] has admitted completeness and unfinished security | No proved shortcut to the book's compiler |

The existing `RoundByRound` conversion using classical choice of an input witness makes no
time claim. Likewise, functional commitment `extractability` currently ends in a `False`
placeholder. Neither should be used to satisfy compiler knowledge obligations.

A promising small reuse experiment is to encode a native committed-scalar fork bundle as a
legacy extraction tree, read leaf witnesses from actual opening messages, define a direct
native algorithm and prove equality with the legacy algorithm. The `Lift` relation gives a
real polynomial-vector witness. Success would establish reuse of algebra; it would not prove
CY-compatible challenge erasure, black-box tree finding or a polynomial-time extractor.

## Questions to keep open

| Question | Candidate directions, not an exhaustive choice list | Evidence needed to resolve it |
|---|---|---|
| Which protocols admit a textbook compiler theorem? | Certified fixed-round fragment; bounded dependent schedule; a bridge between them | A real ordinary-security client and an exact source specialization |
| What may an extractor observe? | Explicit observation maps; protocol-specific encodings; indexed families with proved erasure | Same-observation examples and factorization theorems, including a non-`Unit` witness |
| How should knowledge compose? | Uniform local witness transport; supplied-tree extraction; prefix-available extraction; combinations | Exact access/effect hypotheses and a positive theorem or separating example |
| How are ideal algebraic guarantees realized? | Coefficients, local tests, commitment capabilities, relaxed relations | Claim/query transport and explicit enforcement or decoding error |
| What SR model handles dependent effects? | Typed arbitrary-prefix moves with runtime certificates; source fragment plus proved embedding | Consistent repeats, fresh-query law, actual histories and final completion budget |
| How are challenge and chain randomness related? | Separate digest/decoder; padding; another distribution-preserving encoding | Exact entropy/collision bound and sampling correspondence |
| How much complexity theory is required? | Concrete counters first; compositional time semantics; explicit external cost hypotheses | A compiler or extractor whose claimed bound cannot be discharged by query counts alone |
| What is the eventual theorem inventory? | Whole-book label-by-label coverage with native specializations | Separate audit of currently unassessed chapters, without removing them from scope |

Unanswered rows are research obligations. They are not permanent exclusions, and the candidate
directions are not constraints on future solutions. The first investigation should settle a
few precise bridges and expose failures while preserving these alternatives.

Potential conceptual contributions are the dependent reduction/closing theory, compositional
observation and witness transport, and compiler guarantees that carry semantic oracle promises
through concrete backends. Establishing novelty requires a wider literature comparison than
this book audit; the current notes do not establish priority.

## Source caveats to revisit

The [RBR-to-SR proof display][cy-mixture] conditions on `Y = 0` but multiplies by `Pr[Y = 1]`;
the surrounding decomposition appears to require conditioning on `Y = 1`. Also the printed
[knowledge RBR-to-SR theorem][cy-knowledge-sr] says public-coin IP although the surrounding
section discusses IOPs. Record and justify any correction or extension rather than silently
claiming literal agreement. Nearby informal language about the state bit is less reliable
than the formal empty/prover/full-transcript clauses.

[metadata]: ../sources/ChiesaYogev2024/metadata.yml
[cy]: https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/305fa3d9d19ee6dba135de64b3156d1760df8426/snargs-book.tex
[cy-iop]: https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/305fa3d9d19ee6dba135de64b3156d1760df8426/snargs-book.tex#L16640
[cy-public-coin]: https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/305fa3d9d19ee6dba135de64b3156d1760df8426/snargs-book.tex#L16682
[cy-rbr]: https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/305fa3d9d19ee6dba135de64b3156d1760df8426/snargs-book.tex#L23545
[cy-rbr-knowledge]: https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/305fa3d9d19ee6dba135de64b3156d1760df8426/snargs-book.tex#L23794
[cy-rbr-tightness]: https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/305fa3d9d19ee6dba135de64b3156d1760df8426/snargs-book.tex#L23735
[cy-soundness-rbr]: https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/305fa3d9d19ee6dba135de64b3156d1760df8426/snargs-book.tex#L23662
[cy-sr]: https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/305fa3d9d19ee6dba135de64b3156d1760df8426/snargs-book.tex#L16854
[cy-rbr-sr]: https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/305fa3d9d19ee6dba135de64b3156d1760df8426/snargs-book.tex#L23953
[cy-bcs]: https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/305fa3d9d19ee6dba135de64b3156d1760df8426/snargs-book.tex#L17990
[cy-ibcs-sr]: https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/305fa3d9d19ee6dba135de64b3156d1760df8426/snargs-book.tex#L18046
[cy-hash-chain]: https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/305fa3d9d19ee6dba135de64b3156d1760df8426/snargs-book.tex#L10503
[cy-bcs-knowledge]: https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/305fa3d9d19ee6dba135de64b3156d1760df8426/snargs-book.tex#L18533
[cy-mixture]: https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/305fa3d9d19ee6dba135de64b3156d1760df8426/snargs-book.tex#L24122
[cy-knowledge-sr]: https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/305fa3d9d19ee6dba135de64b3156d1760df8426/snargs-book.tex#L24162
[type-tree]: ../../../ArkLib/Interaction/Oracle/TypeTree.lean
[native-protocol]: ../../../ArkLib/Interaction/Oracle/Protocol.lean
[runtime-soundness]: ../../../ArkLib/Interaction/Oracle/RuntimeSoundness.lean
[sumcheck-protocol]: ../../../ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean
[sumcheck-soundness]: ../../../ArkLib/ProofSystem/Sumcheck/Interaction/ProtocolSoundness.lean
[sumcheck-computable]: ../../../ArkLib/ProofSystem/Sumcheck/Interaction/ComputableSoundness.lean
[sumcheck-completeness]: ../../../ArkLib/ProofSystem/Sumcheck/Interaction/ComputableCompleteness.lean
[legacy-rbr]: ../../../ArkLib/OracleReduction/Security/RoundByRound.lean
[legacy-sr]: ../../../ArkLib/OracleReduction/Security/StateRestoration.lean
[legacy-trees]: ../../../ArkLib/OracleReduction/Security/TranscriptTree/Basic.lean
[legacy-tree-composition]: ../../../ArkLib/OracleReduction/Security/TranscriptTree/Composition.lean
[legacy-cwss-composition]: ../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Composition.lean
[legacy-committed-scalar]: ../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean
[lift]: ../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean
[legacy-guarded]: ../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Guarded.lean
[legacy-guarded-complete]: ../../../ArkLib/OracleReduction/Composition/Sequential/GuardedCompleteness.lean
[legacy-rbr-append]: ../../../ArkLib/OracleReduction/Composition/Sequential/Append/RoundByRound.lean
[legacy-salt]: ../../../ArkLib/OracleReduction/Salt.lean
[legacy-security-append]: ../../../ArkLib/OracleReduction/Composition/Sequential/Append/Security.lean
[legacy-implications]: ../../../ArkLib/OracleReduction/Security/Implications.lean
[legacy-rewinding]: ../../../ArkLib/OracleReduction/Security/Rewinding.lean
[legacy-bcs]: ../../../ArkLib/OracleReduction/BCS/Basic.lean
[legacy-fs]: ../../../ArkLib/OracleReduction/FiatShamir/Basic.lean
[vc-hashing]: https://github.com/Verified-zkEVM/VCVio/blob/f5119c64ebb055d69c143704e12eba6df7dc386c/VCVio/CryptoFoundations/MerkleTree/Hashing/Defs.lean
[vc-binding]: https://github.com/Verified-zkEVM/VCVio/blob/f5119c64ebb055d69c143704e12eba6df7dc386c/VCVio/CryptoFoundations/MerkleTree/Hashing/Binding.lean
[vc-stateful]: https://github.com/Verified-zkEVM/VCVio/blob/f5119c64ebb055d69c143704e12eba6df7dc386c/VCVio/CryptoFoundations/MerkleTree/MultiExtractability/Stateful.lean
[vc-strong]: https://github.com/Verified-zkEVM/VCVio/blob/f5119c64ebb055d69c143704e12eba6df7dc386c/VCVio/CryptoFoundations/MerkleTree/MultiExtractability/StrongBound.lean
[vc-rbr]: https://github.com/Verified-zkEVM/VCVio/blob/d7089e46d69e07640fa23b5ae6b1b966f1d4b949/VCVio/CryptoFoundations/RoundByRound.lean#L60
