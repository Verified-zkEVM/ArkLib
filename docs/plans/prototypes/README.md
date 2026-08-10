# Prototypes for `computable-cwss-extractors.md`

Machine-checked developments backing the evidence table (§6) of
[`../computable-cwss-extractors.md`](../computable-cwss-extractors.md), built against branch
`tr/computable-extractors` (tree-split rework included), all verified green.

These four files hold the design: the notion with its gates, transports and purity-as-data;
the composition operator and all four composition theorems; the three leaf engines with their
certificates; and the computable presentation layer. Milestones M1–M6 of the plan
transcribe from them, so a wrong declaration name here is a defect. They are **not** part of
the library build (nothing imports them; they are not under `ArkLib/`). Check one with:

```bash
lake env lean docs/plans/prototypes/<file>.lean
```

Each prints `#print axioms` lines; the pass criterion is **no `sorryAx`** anywhere in the
output. All four additionally print `#eval` values and `IR PRESENT` probes;
`CM_presentation.lean` also prints one `NO IR AS EXPECTED` line — its negative control
reproduces today's `liftPackage` failure and is *supposed* to have no IR.

| File | Evidence | Contents |
| --- | --- | --- |
| `CM_gates.lean` (855 ln) | E1–E8, E20, E24–E26, E34, E35 | The notion (`LeafWitnesses`, the verifier-relative ∃-form `IsValid`, the bare-function `TreeBased`, one-clause `treeSpecialSoundWith` + escape twin) and the gates that pin its shape: G0 the ∀-variant vacuity kill, G1 ∃-form satisfiability on the same fixture, G2 non-vacuity for every extractor, G3 the reachability pair (`reachable_sound`/`free_refuted` — dropping reachability breaks a sound forwarding engine), G4 no closure at `none`, G5 `canonWitnesses` validity; the three transports at the single `HEq`; **purity as data** (`PureForm`, `GuardedForm`, forgetful maps, computable `PureForm.append`, the reachability producers `pure_verdict_mem_outputs` / `support_init_nonempty_of_accepting`); **the pure-case collapse** `isValid_iff_pure`; the two-way classical bridge with a computability-preserving `ofClassical` (IR-gated, instance-free); `onlyPath`; arity-0 degeneracy; codegen calibration. Step 2b's source, and the source of `TranscriptTree/NonVacuity.lean`. |
| `CM_append.lean` (997 ln) | E10–E16, E19 | The `verify₁`-parameterized `TreeBased.append` (the seam statement is the left verifier's verdict function, passed as data — packages read `isPure.verify`/`isGuarded.out`), the leaf-path glue (`AppendSplit.gluePath` + transcript specs — the only path machinery composition needs), and **all four composition theorems**: plain, escape, guarded-left, and **escape × guarded-left, which is the statement `Guarded.lean:141` hides behind a `sorry` today, proved in full generality** — the escape twins at the repo's UNCHANGED `EscapeEvent.append`, the guarded twins via `somePath`/`hcheck` and the guarded output-set lemmas (incl. `guarded_verdict_mem_outputs`). Runtime demos: 2-fold chain `#eval`s to `some 11`, 3-fold to `some 211` (the composed seam function — `PureForm.append`'s data — splits transcripts at runtime), kernel-`rfl`-checked, IR-gated. Steps 3b/4a's source. |
| `CM_enginecerts.lean` (744 ln) | E17, E18, E24, E27–E29 | **The three leaf engines and their certificates in full**: `ReduceClaim` (`rcTreeExtractor`, classical-free, with `rc_coordinateWiseSpecialSoundWith`), `SingleRound` (`branchPathOf`, `collect`, `treeExtractor`; both `*_of_mkWitness*` certificates at TODAY's `hpure`/`hmk`, the UNCHANGED `escEvent`, `[Nonempty WitOut]` dropped, escape decided by a classical case split on the event), and the `ScalarRound` transplant (both certificates at unchanged `escEventScalar`, `hmk` at `Function.Injective fam`). Certificates consume validity via `isValid_iff_pure`; `fullTranscript_branchPathOf` closes by bare `rfl`; no inverse path readers, no star-path classification. Real-engine runtime demo kernel-`rfl`s (`some 21` / `none`). M5/M6's source. |
| `CM_presentation.lean` (514 ln) | E30–E33 | **The computable presentation layer** (§5): `Presentation`/`IsPresentation` with `CPolynomial` data and `toPoly`-stated laws; the ENTIRE `Lift/Presentation.lean` proof engine transcribed verbatim under the mechanical `toPoly` rename; the retyped `LiftedWitness` + `checkAt` + `recover`; the computable `cyclotomicPresentation` with its laws discharged from the QuotientLift lemmas verbatim; the package-shaped IR gate with the Mathlib-typed **negative control** (today's `liftPackage` failure, reproduced); and the runtime demo constructing the previously-unconstructible values (concrete modulus, `Rq` element, `LiftedWitness` — `#eval`s end-to-end through a package-shaped extraction). M1's source. |

Maintenance: these are vendored evidence, not living code. If a repo refactor breaks one, record
the breakage in the plan rather than patching the prototype — the plan's regression gates
(`TranscriptTree/NonVacuity.lean` once step 2b lands) are the living copies.
