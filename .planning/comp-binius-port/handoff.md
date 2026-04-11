# Handoff — comp-binius-port

> Written at END of each session. Read at START of next session, then cleared.

**From:**
**To:** next agent
**Session duration:** long-running migration pass on 2026-04-11
**Build state:** `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.General ArkLib.ProofSystem.Binius.FRIBinius.General` passes.

**Current focus:**
- Keep `polynomialFromNovelCoeffsF₂` consumers on the computable helper path, not
  `MultilinearPoly.ofHypercubeEvals`.
- Continue statement-shape migration toward computable carriers in the remaining Binius soundness
  and relation files.

**Files most recently changed:**
- `ArkLib/ProofSystem/Binius/BinaryBasefold/Prelude.lean`
- `ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean`
- `ArkLib/ProofSystem/Binius/BinaryBasefold/Relations.lean`
- `ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/QueryPhasePrelims.lean`
- `ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean`
- `ArkLib/Data/FieldTheory/AdditiveNTT/Impl.lean`
