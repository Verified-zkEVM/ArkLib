# Interaction-security theory run, October 3, 2026

## Contract and clock

The user authorized the [general-theory contract](../../design/interaction-security-night-contract.md)
after reviewing its definitions, scope, ambitious targets, review requirements and PR sizing.
The mathematical targets are G1 (ordinary soundness), G2 (knowledge composition), and G3
(state-restoration knowledge soundness). Supporting examples do not count as their completion.

Start: 2026-10-03 00:56:52 America/New_York / 04:56:52Z.
Six-hour checkpoint: 06:56:52 local / 10:56:52Z.
Expansion freeze: 07:26:52 local / 11:26:52Z.
Deadline: 08:56:52 local / 12:56:52Z.

The earlier premature launch was interrupted with a clean worker tree. Its stopped timer does
not govern this run. The active clock is recorded in `/tmp/arklib-night-20261003/timing.json`;
the local timer writes checkpoint/freeze/deadline markers and never kills a build.

## Baseline and ownership

ArkLib baseline: `ace55c3e29da1fc55a321378ada55ea4f7ed8790`.
Research baseline: `c3e715d23a05a01ae1f7e6b0421d873476ec3f00`.
Supported pins: Lean 4.34.0, VCVio `d7089e46d69e07640fa23b5ae6b1b966f1d4b949`,
PolyFun `3710d71b28404a151b8d1f0ce080ea448778dec0`.
Origin: `https://github.com/Verified-zkEVM/ArkLib.git`.

| Owner | Worktree / branch | Work |
|---|---|---|
| Main orchestrator | `ArkLib` / `research/cy-interaction-theory` | Contract, notes, PR operations |
| Main orchestrator | `ArkLib-interaction-night` / `work/interaction-night-20261003` | G3 investigation, integration, final validation |
| Sol High worker A | `ArkLib-local-rbr` / `feat/native-local-rbr` | G1 and actual Sumcheck application |
| Sol High worker B | `ArkLib-witness-transport` / `feat/native-witness-transport` | G2 and named backward extraction |
| Independent reviewer | `ArkLib-interaction-review` / `review/interaction-night-20261003` | Statement/read-back and code review |

All paths are under `/Users/quangdao/Documents/Lean`. The unrelated
`ArkLib-runtime-soundness` worktree is outside scope. Workers do not push, open PRs, merge, or
edit one another's files. The main orchestrator reviews and owns acceptance.

Project build outputs are private copies. Dependencies use the existing exact-revision shared
cache. All run-owned Lean/Lake writes are serialized through
`/tmp/arklib-night-20261003/with-build-lock.py`. VCVio, PolyFun and Mathlib revisions/origin URLs
were inspected; PolyFun has only the cache manager's untracked `.lean-deps-immutable` marker,
not a source change. No dependency reset or upgrade is authorized merely to pass a check.

## Live theorem status

| Target | Status | Required next evidence |
|---|---|---|
| G1: generic ordinary soundness | Generic native execution theorem checked; Sumcheck application in progress | Actual Sumcheck freshness and terminal-output correspondence, then full validation |
| G2: knowledge composition | Native certificate composition, extraction, freshness and closed-output equations checked | Dependent ordinary-import client, final-head review and full validation |
| G3: restoration security | Adaptive-query probability theorem and native salted-key reconstruction checked separately | Join completion, extraction and native verifier semantics in the final security game |

No implementation theorem or code PR is claimed at launch. Public names must use clear
cryptographic terminology; an abstraction's representation does not justify inscrutable names.

## Review, validation and publication evidence

The pre-launch mathematical proposal received an independent ordinary review. That is not a
blind read-back or an implementation verdict. New principal Lean types will receive a fresh
blind read-back, followed by the orchestrator's comparison against the contract and sources.
Each substantive code PR also requires source/axiom/API checks and full repository validation.

Expected substantial code PRs: G1 with Sumcheck; G2 with its native composition proof; G3 with
the quantitative restoration theorem. Aim for roughly 500-1500 changed lines per PR, preserving
important coherent smaller results. No definitions-only micro-PRs and no merging into main.

Validation commands, exact revisions, reviewer verdicts, PR links and incomplete obligations
will be added here as evidence becomes available. The final report distinguishes checked partial
theory from completion of G1/G2/G3 and records any pending CI or validation.

## First-hour checkpoint (approximately 06:00Z)

These are checked working-tree results, not accepted final PR heads. All three MUST targets
remain open until their complete statements, clients and validation meet the contract.

- **G1:** `executeStrategies_state_bound`, `executeStrategies_soundness` and the uniform-error
  corollary prove the sum bound over the actual native executor. The monad and ambient handler
  permit failure and arbitrary prover private memory; a checked failing-query consumer has zero
  successful mass. Covered verifier challenge actions must have the fresh model's lossless move
  marginal. The independent read-back caught and caused repair of an earlier overly narrow
  lossless-only interface. The Sumcheck all-authored state/rank/local-bound proofs are checked;
  actual verifier freshness and the output relation bridge are still being developed.
- **G2:** the package constructs dependent native appended extractors, endpoint equivalences,
  concatenated schedules and local knowledge certificates. Suffix certificates cover every
  concrete middle path, including false middle claims. Native freshness composition uses the
  actual closed middle oracle and retains all receive/continuation effects. The blind read-back
  found no mathematical defect in its frozen packet, but did not certify intended-contract
  fidelity or final integration. Terminal-relation convenience statements added afterward
  require final-head review. Exact attachment is an explicit hypothesis of freshness transport;
  arbitrary persistent stateful handlers are not thereby covered.
- **G3 probability:** a new VCVio theorem bounds adaptive bad queries by `n * error`, allowing
  the bad event to inspect unqueried table cells. It is connected to the actual cached random
  oracle, with dependent finite answer types and consistent repeated queries. The independent
  read-back and selected axiom sweep found no extra trust assumption. This is a probability
  theorem, not yet the complete state-restoration theorem.
- **G3 native presentation:** checked definitions use exact round/input/message-prefix/salt-prefix
  keys, without earlier challenges in the key. Reconstructing a key's strict ancestors uses the
  same table. A checked theorem proves that replacing its own challenge cannot change that
  reconstructed pre-challenge extractor. Native all-prefix local bounds therefore apply to
  each fixed key. Completion returns the existing native path and has a checked `k` query bound.

The probability slice currently requires a finite key domain. The contract does not explicitly
restrict the input type to be finite; a finite reachable-key reduction is being investigated so
that adaptive input selection is not silently weakened. The full quantitative game and its native
verifier interpretation remain obligations, as does extraction cost.

The generic probability work is in `VCVio-interaction-night`, branch
`feat/restoration-fresh-query`, based on ArkLib's pinned VCVio revision. Advancing to current VCVio
main would introduce unrelated API changes. Development currently tests new VCVio artifacts via
an explicit scratch import overlay; this is not a final dependency pin or reproducibility claim.

## Publication and current validation

Research notes and the accepted contract are pushed in
[ArkLib PR 1258](https://github.com/Verified-zkEVM/ArkLib/pull/1258), currently through commit
`2a542f87e`. The superseded smaller night plan was removed so that the accepted contract is the
single normative scope. Its required validation passed (91 seconds); existing bibliography
warnings were unchanged. No implementation PR or merge is claimed at this checkpoint.

Working evidence is retained under `/tmp/arklib-night-20261003/readback/` and
`/tmp/arklib-night-20261003/restoration/`; final reviewed statements, hashes, commands and verdicts
will be recorded durably before handoff. VCVio full validation with axioms is now running under
the shared build lock. The root owns the final contract comparison and acceptance decisions.

## Checked advances after the first-hour checkpoint

- The general adaptive-query theorem now removes the finite key-domain assumption. A fixed
  oracle program with finite answer types has finitely many syntactically reachable keys.
  Restriction preserves the exact lazy `ProbComp` program from an empty cache, including repeats.
  The universal background-table and trace hypotheses justify fixing outside coordinates in the
  proof. This bounds the actual output event; it does not claim to sample an infinite random
  table. A fresh blind read-back found no defect and independently checked the public theorem
  and selected axiom closures. The infinite-`Nat`-key ordinary-import consumer also checks adaptive
  key choice and repeated-query consistency.
- `restored_extraction_bound` is checked in the native scratch development with arbitrary input
  and salt types, adaptive selected input, actual cached adversary/completion program, native
  completed paths and the `(Q + rounds.length) * error` coefficient. Its endpoint is currently
  terminal knowledge and failed extracted input knowledge. The actual native verifier/output
  relation realization is still being constructed, so this is not yet completion of G3.
- The native Sumcheck theorem `Sumcheck.Interaction.Native.roundByRound_soundness` is checked.
  It invokes the new generic native execution theorem and the one-round polynomial bound,
  retains the realized original polynomial, and bounds the actual returned output relation.
  It permits failing ambient effects and arbitrary native prover strategies, with exact attachment
  and a uniform fresh challenge marginal as explicit hypotheses. The initial frozen proof's
  SHA256 is `9fce96710cfeb2253aec20566d53ec7a506911e5e5223731cd977b26033bbe24`;
  selected axioms are only `propext`, `Classical.choice`, and `Quot.sound`. Fresh independent
  read-back, production promotion and final validation are still pending.
- G2 passed canonical full validation with axioms: 18,081 declarations across 923 modules,
  unchanged 286 sorry-tainted declarations and zero nonstandard-axiom taint; elapsed 151.1 seconds.
  Root inspected the final endpoint additions and dependent native client, finding no mathematical
  defect. A structural module split subsequently passed targeted checks and is undergoing the
  canonical gate again. This splits the approximately 1,955-line work into two substantial PRs:
  roughly 760 lines of backward extraction/native append theory, followed by roughly 1,220 lines
  of actual closed-middle certificate/freshness composition and its dependent client. Both together
  must satisfy G2; the split does not reduce the mathematical target.

The root-authored generic VCVio probability slice passed its earlier complete validation
(316.5 seconds) before the finite-domain removal; final full validation of the stronger head is
running. Its public read-back pins the frozen statement separately from later docstring wrapping.
No proof relies on sampling an infinite table or selecting a valid witness by classical choice.


## Reviewed publication checkpoint (06:55Z)

The following evidence supersedes the explicitly provisional statuses above.

- **G2 is implemented and reviewed as a two-PR stack.**
  [PR 1259](https://github.com/Verified-zkEVM/ArkLib/pull/1259), head
  `388bb2486d7621d36e9b4edf993e6d23f76b703f`, contains 760 added lines of backward extraction
  and dependent native append laws. [PR 1260](https://github.com/Verified-zkEVM/ArkLib/pull/1260),
  head `372f071dd72ff9364eceb5d5361db987e120271e`, adds 1,221 lines of actual closed-middle
  composition and its dependent client, based on PR 1259. The post-split canonical
  `./scripts/validate.sh --axioms` passed in 115 seconds: 18,081 declarations, 924 modules,
  unchanged 286 sorry-tainted declarations, zero nonstandard-axiom taint. Root semantic review
  and independent final-head review both approve. The latter separately compiled an ordinary
  import client and checked principal axiom closures. All triggered CI checks passed; the
  stacked PR triggers interaction/summarize CI, while the main-based foundation also ran full
  build, imports and docs checks. No merge was performed.
- **The general probability component of G3 is published.**
  [VCVio PR 823](https://github.com/Verified-zkEVM/VCVio/pull/823), head
  `fc521031a00158648973bb06a68cac288cd5b71a`, targets current main
  `f5119c64ebb055d69c143704e12eba6df7dc386c`. It proves the unrestricted-key
  `prEvent_randomOracle_le_of_bad_queries` theorem, retaining finite nonempty answer types,
  arbitrary query order and repeats, and bad events inspecting unqueried coordinates.
  Full current-main validation with axioms passed in 288 seconds: 22,071 declarations,
  781 modules, unchanged 14 sorry-tainted declarations, zero nonstandard taint. Independent
  blind theorem review and final exact-head port review approve; the latter checked preservation
  of current-main public APIs/imports and compiled its own ordinary-import axiom canary.
  Current-main policy removes redundant `Finite`/`Nonempty` binders implied by `SampleableType`.
  The probability theorem makes no extraction-cost or whole-protocol security claim.
- **ArkLib's precise compatible dependency is reproducible.** Its restoration branch now pins
  pushed VCVio commit `731851a844ee20bc71cf9fe82c25cdc90c78c8c2`, based on the original
  ArkLib VCVio pin. That compatible version passed final full validation with axioms in
  127.5 seconds (22,055 declarations, 777 modules, unchanged 33 sorry-tainted declarations,
  zero nonstandard taint). Only the VCVio revision changes in the ArkLib manifest; no unrelated
  dependency API migration is included. Production `StateRestoration.lean` built against this
  exact pin in 36.3 seconds, without the scratch overlay. Its actual native verifier/output
  endpoint remains in progress; this does not yet close G3.
- **G1's actual native Sumcheck principal theorem passed fresh independent read-back**, including
  a separately compiled frozen source and ordinary-import axiom check. No mathematical defect
  was found; selected roots depend only on the standard Lean axioms. Production promotion also
  compiled successfully. The explicit positive-round CY state specialization and the promised
  deterministic-path/random-author supporting statements are being incorporated before the final
  validation and publication of this slice.

The G2 final reviewed source hashes are:

| Module | SHA256 |
|---|---|
| Knowledge | `803dbe0bc24e46178b9384d9a0fc5ed87c90b6f4e24971f2bcc46fb5e39cd22b` |
| KnowledgeAppend | `6a4d3e049e2d4ecea73c6ed1f27305633ce06964f10e6685dcbd8f95c56583f7` |
| KnowledgeComposition | `fc8db56fd86d4fc9c75216edf2bf34233a938d99b25871b9cd27a6ccdc03aef2` |
| Dependent composition client | `1b021dea855cb9f948131af2ad689487319f31c4add62c3efbb888f7d7f1ea88` |

The restoration game under construction reads only its completed native path when replaying the
actual verifier; a complete table is available only to the probability proof. The endpoint must
still identify the actual source-query observation, the supplied output witness and named
backward input extraction. This distinction is a tracked proof obligation, not an assumed game
equation or permission to weaken G3.


## Ordinary soundness publication (07:10Z)

[ArkLib PR 1261](https://github.com/Verified-zkEVM/ArkLib/pull/1261), head
`8fa5d756fa7096e94c60f353f2732d6faaa22458`, contains G1, its native Sumcheck derivation,
the deterministic actual-path escape theorem and failure-aware random-prefix averaging. It is
based on unchanged current main `ace55c3e29da1fc55a321378ada55ea4f7ed8790`. The positive-count
main proof consumes the CY state with all-input initial falsity; zero count uses the ordinary
false-input initial law. The final reviewed Git tree is
`be93ab71e41797a5a4df12dddcbc09bb05fd6f12`.

Canonical full validation with axioms passed in 137.4 seconds: 18,099 declarations, 924 modules,
unchanged 286 sorry-tainted declarations and zero nonstandard taint. Root reviewed the full
supporting/execution/test diff and final CY proof. Independent final review approves and compiled
its own failure-author/public-import canary in 12.9 seconds; selected roots use only standard
Lean axioms. An initial source-policy failure identified missing generated umbrella imports;
regenerating and staging those imports repaired it before the successful complete gate.

This PR has 1,716 additions across eight files. The root accepted the modest size overage because
the generic implication and required Sumcheck derivation form one coherent acceptance criterion;
no definitions-only split was introduced. CI is pending at publication. No merge is authorized.

G3's `verificationGame_eq` and relation-valued `stateRestoration_knowledge_soundness` now compile
in production against the exact compatible pin. Its ordinary-import principal axiom check passed
in 12.6 seconds using only standard axioms. Independent blind endpoint review and the actual
source-query/dependent-output consumer are in progress, so final G3 acceptance remains pending.
The [source/legacy correspondence note](interaction-state-restoration-correspondence.md) records
why the old challenge oracle is useful, what is not inherited, and the unproved runtime bridge.


## State-restoration publication and final integration (07:45Z)

[ArkLib PR 1263](https://github.com/Verified-zkEVM/ArkLib/pull/1263), head
`be65c8051aa36398069ab76853f063c4382a589c`, contains the native G3 theorem, actual
execution correspondence, closed oracle output endpoint, and private-coin averaging corollaries.
It is stacked on PR 1260. The 1,583 changed lines keep these connected obligations and their
public client together. The PR is draft while canonical validation and CI finish.

Independent final semantic review approves the frozen production packet and client. Root's
review found that the earlier scalar/source-observation endpoint alone did not establish the
required oracle-output interpretation. Independent review confirmed this P1 gap. The new
`stateRestoration_oracle_knowledge_soundness` closes the actual returned optional open claim
under the same native path's accumulated handler. Its output relation sees the closed statement
and behavior; `none` cannot win. The actual execution equation is proved, rather than assumed.
This repair is essential to acceptance, not an optional example.

The supported round list, message interfaces and challenge alphabets are fixed independently
of the selected input and previous challenges. Inputs and salts may be infinite. The common
supplied output-witness type is identified with each terminal witness type by an explicit named
equivalence. No input-dependent/challenge-dependent restoration presentation or arbitrary
varying-cardinality terminal witness interface is claimed. Private coins are independent,
possibly failing pre-sampled tapes; equivalence with arbitrarily interleaved randomness remains
unproved. Extraction runtime and ARC challenge-erased extraction remain open.

The final independent ordinary-import canary passed in 3.4 seconds against the exact pin below.
Principal and client axioms are only `propext`, `Classical.choice`, and `Quot.sound`. Besides the
client's actual payload7 observations, the reviewer checked the same public branch with payload3:
the closed virtual output returns `some (3,3)` and backward extraction returns 5. This distinguishes
actual source interpretation from copying the first example's answer. The client also verifies
rejection, nonidentity extraction, and missing mass from a failing private-coin author.

### VCVio test initialization repair and validation scope correction

The first CI run of [VCVio PR 823](https://github.com/Verified-zkEVM/VCVio/pull/823) found
that a dependent finite test sampler introduced unwanted module-initialization enumeration.
The production probability theorem was unchanged. Explicit finite/nonempty proof instances
and a noncomputable test sampler through `Fintype.ofFinite` remove the generated enumeration.
Independent review inspected the generated code and approved this test-only fix.

The current-main PR head is now `48190ba81afd83fb3c7dc8a74695c9731d25e889`.
Its complete `VCVioTest` build passed in 7.7 seconds and test-library initialization sweep in
12.8 seconds. The byte-identical compatible fix is pushed at
`fe608a46c3df4608ea774611662a255326b5d1ff`; its test build passed in 36.8 seconds and
initialization sweep in 14.5 seconds. G3 now pins this exact compatible revision. All other
manifest dependency revisions are unchanged. Current-main CI is rerunning.

For precision, earlier VCVio “full validation with axioms” entries mean the full requested
`./scripts/validate.sh --axioms` gate. That command does not include VCVio's optional `--test`
checks. They did not establish that every test-library initialization check had passed. The
changed test library and its initialization sweep are now separately checked as recorded above;
CI remains the evidence for the broader pipeline. ArkLib's canonical gate does include its
acceptance tests and compiled runtime checks.

G1 PR 1261 and both G2 PRs 1259–1260 have passed their triggered CI and are ready for review.
No PR has been merged. The combined integration branch includes their exact source changes and
G3; only generated umbrella-import conflicts needed resolution. Final combined validation is
still pending, so assembled-stack acceptance remains open.


G3's canonical `./scripts/validate.sh --axioms` rerun passed in 198.2 seconds at the published
head: 18,188 declarations across 929 modules, unchanged 286 baseline sorry-tainted declarations,
zero nonstandard axiom taint. The first full attempt failed only on the new test file's missing
copyright header; the standard header was added with its entire Lean body unchanged, independently
verified, and all requested checks rerun successfully. Combined integration validation is running
at `a43dc43b9` with the exact new compatible dependency pin.
