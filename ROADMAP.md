# Roadmap

ArkLib develops executable protocol specifications and Lean proofs of completeness and security.
This page maps the current work and contribution directions. The
[interaction roadmap](docs/design/05-roadmap.md) owns the detailed composition milestones;
[the blueprint](blueprint/src/content.tex) organizes the mathematical development.
Use [open issues](https://github.com/Verified-zkEVM/ArkLib/issues) for bounded tasks and
[CONTRIBUTING.md](CONTRIBUTING.md) for the development and review process.

A protocol definition, a proved security theorem, and a compiled implementation are separate
results. Existing `sorry` declarations remain in several developments. The
[axiom regression gate](docs/wiki/quickstart.md#filling-a-sorry-or-work-that-must-stay-axiom-clean)
tracks that debt; a successful library build does not mean every protocol has a complete proof.

## Immediate direction: finish the native Sumcheck path

The [native Sumcheck modules](ArkLib/ProofSystem/Sumcheck/Interaction/) prove ordinary soundness
and honest completeness for arbitrary round counts. Their composition proof retains the actual
whole prover, private continuation, exported oracle behavior, and final closed claim. The final
relation compares the original polynomial oracle with the claimed value.

The next Sumcheck work precedes the native FRI migration:

1. Complete the computable honest prover using CompPoly and prove its correspondence with
   the native mathematical specification. The
   [computable verifier and executor](ArkLib/ProofSystem/Sumcheck/Interaction/Computable.lean)
   already use bounded coefficient-array messages, with proved execution and ordinary-soundness
   bridges. [Compiled checks](scripts/SumcheckRuntime.lean) cover concrete executions, aborts,
   and the final evaluation relation. The general honest-prover
   [implementation module](ArkLib/ProofSystem/Sumcheck/Impl/Basic.lean) remains a scaffold.
2. Prove native round-by-round (RBR) soundness, knowledge soundness, and round-by-round
   knowledge soundness. Ordinary soundness does not supply an extractor or a witness available
   at an intermediate boundary.
3. Exercise the same interfaces in a small FRI or Spartan client, proving correspondence with
   its established presentation before migrating further protocol layers.

The [interaction framework](ArkLib/Interaction/) now supplies native sequential composition,
restricted oracle routing, actual source logs, persistent-runtime execution and soundness, and
canonical access and weighted query-cost certificates. Its
[maintained status](docs/design/00-current-status.md) and
[adversarial execution design](docs/design/03-adversarial-oracle-execution.md) explain the contracts
and remaining extraction work. A cost or access certificate accompanies a security theorem;
it does not establish security by itself.

## Protocol and commitment developments

### Sumcheck, Spartan, and ring switching

- [Sumcheck](ArkLib/ProofSystem/Sumcheck/) includes legacy and native presentations. Preserve
  existing component correspondences, and prove any further legacy-to-native correspondence
  before transferring security claims.
- [Spartan](ArkLib/ProofSystem/Spartan/Basic.lean) contains protocol components and admitted
  definitions. Completing the composed protocol and its security proofs remains work.
- [Ring switching](ArkLib/ProofSystem/RingSwitching/) includes proved transport and lifting
  results. Packing, batching, and Sumcheck-phase developments still contain admissions;
  complete those obligations before claiming security of the full assembly.

### FRI, STIR, and Binius

- [FRI](ArkLib/ProofSystem/Fri/) and [batched FRI](ArkLib/ProofSystem/BatchedFri/) have protocol
  specifications and security developments. Batched FRI still has admitted obligations.
- [STIR](ArkLib/ProofSystem/Stir/) has component results and an incomplete main-theorem chain.
  Further codeword-folding and WHIR work should state which protocol presentation it formalizes.
- [Binius](ArkLib/ProofSystem/Binius/) includes Binary Basefold and FRI-Binius developments;
  some core interaction and security proofs remain admitted.

Codeword folding in these protocols is distinct from Nova-style folding for incremental
verifiable computation (IVC). IVC folding is a later direction, not a completed consequence of
codeword-folding results.

### KZG and lattice-based commitments

- [KZG](ArkLib/Commitments/Functional/KZG/) has proved correctness and binding developments,
  including function binding, under their declared algebraic and hardness assumptions.
  These modules contain no local `sorry` declarations. This is not a claim of an unconditional
  security theorem or a verified external implementation.
- [Lattices](ArkLib/Data/Lattices/) and [Ajtai commitments](ArkLib/Commitments/Ordinary/Ajtai/)
  support the [Hachi development](ArkLib/Commitments/Functional/Hachi/). Its nonrecursive opening
  chain has formalized results and [compiled runtime checks](scripts/HachiRuntime.lean).
  Recursive opening and related handoffs still contain admitted obligations and documented
  soundness gaps. Keep those boundaries explicit when extending the scheme.

## Supporting mathematics and upstream ownership

- [Coding theory](ArkLib/Data/CodingTheory/) supplies code definitions, Reed–Solomon results,
  list-decoding and correlated-agreement bounds, and proximity-gap developments. Some advanced
  bounds remain admitted. New protocol error bounds should identify the exact theorem and
  parameter regime they use.
- [Polynomial additions](ArkLib/Data/Polynomial/) and
  [multivariate polynomial theory](ArkLib/Data/MvPolynomial/) support local proof needs.
  Computable univariate and multilinear representations, binary tower fields, and prime-field
  implementations are developed upstream in [CompPoly](https://github.com/Verified-zkEVM/CompPoly).
  ArkLib's local additions and bridges live in [ToCompPoly](ArkLib/ToCompPoly/).
- Oracle computations, probability semantics, query tracking, and Merkle-tree developments
  belong upstream in [VCVio](https://github.com/Verified-zkEVM/VCVio). Generic interaction and
  strategy laws belong in [PolyFun](https://github.com/Verified-zkEVM/PolyFun).
  ArkLib still needs concrete backend adapters; upstream Merkle results alone do not complete
  ArkLib's commitment compiler.

Use the versions pinned by [lakefile.toml](lakefile.toml) and
[lake-manifest.json](lake-manifest.json). Avoid maintaining parallel implementations of relocated
components or treating old unchecked lists as their current upstream status.

## Later framework and implementation work

The detailed dependency order belongs in the
[interaction roadmap](docs/design/05-roadmap.md#later-extraction-and-compiler-work):

- Establish causal witness extraction and state-restoration facts for knowledge composition.
- Connect the [BCS transform](ArkLib/OracleReduction/BCS/) and
  [Fiat–Shamir developments](ArkLib/OracleReduction/FiatShamir/) to the native framework through
  proved correspondences and concrete commitment adapters.
- Carry security, privacy, access, and execution costs through the
  [oracle-elimination compiler](docs/design/04-oracle-elimination-compiler.md).
- Extend the [algebraic group model](ArkLib/AGM/), zero-knowledge theory, and further proof-system
  families as their first concrete clients require. Plonk, IVC folding, and a mechanized PCP
  theorem remain broader directions rather than completed end-to-end formalizations.
- Verify correspondence with external implementations only after the relevant Lean protocol
  path compiles and its mathematical specification and security assumptions are explicit.

For examples of the difference between proofs and execution checks, see the
[toy-problem runtime](scripts/ToyProblemRuntime.lean) and
[nonrecursive Hachi runtime](scripts/HachiRuntime.lean). Their concrete checks do not certify
performance or full security of every protocol family.
