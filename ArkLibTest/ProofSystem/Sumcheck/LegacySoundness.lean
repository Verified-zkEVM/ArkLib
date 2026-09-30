/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Sumcheck.Spec.General
import Mathlib.Data.ZMod.Basic

/-!
# Legacy Sumcheck soundness assumptions

Every exported RBR soundness route accepts a finite commutative semiring with `IsDomain`, and
finite fields remain valid clients. The zero-divisor ring `ZMod 4` cannot instantiate these
statements. These are API checks of existing admitted claims, not new security proofs.
-/

namespace Sumcheck.LegacySoundnessTest

open OracleComp OracleSpec Spec.SingleRound

section Domain

variable (R : Type) [CommSemiring R] [IsDomain R] [Fintype R]
  [DecidableEq R] [SampleableType R] (deg : ℕ) {m : ℕ} (D : Fin m ↪ R)
  {ι : Type} (oSpec : OracleSpec ι) {σ : Type} (init : ProbComp σ)
  (impl : QueryImpl oSpec (StateT σ ProbComp)) {n : ℕ} (i : Fin n)

example := Simpler.oracleVerifier_rbrKnowledgeSoundness R deg D oSpec (init := init) (impl := impl)

example := Simple.verifier_rbrKnowledgeSoundness R deg D oSpec (init := init) (impl := impl)

example := Simple.oracleVerifier_rbrKnowledgeSoundness R deg D oSpec (init := init) (impl := impl)

example := Spec.SingleRound.verifier_rbrKnowledgeSoundness
  (R := R) (deg := deg) (D := D) (oSpec := oSpec) (init := init) (impl := impl) i

example := Spec.SingleRound.oracleVerifier_rbrKnowledgeSoundness
  (R := R) (deg := deg) (D := D) (oSpec := oSpec) (init := init) (impl := impl) i

example := Spec.oracleVerifier_rbrKnowledgeSoundness R deg D n oSpec (init := init) (impl := impl)

end Domain

section Field

variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  (deg : ℕ) {m : ℕ} (D : Fin m ↪ F) {ι : Type} (oSpec : OracleSpec ι)
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  {n : ℕ} (i : Fin n)

example := Simpler.oracleVerifier_rbrKnowledgeSoundness F deg D oSpec (init := init) (impl := impl)

example := Simple.verifier_rbrKnowledgeSoundness F deg D oSpec (init := init) (impl := impl)

example := Simple.oracleVerifier_rbrKnowledgeSoundness F deg D oSpec (init := init) (impl := impl)

example := Spec.SingleRound.verifier_rbrKnowledgeSoundness
  (R := F) (deg := deg) (D := D) (oSpec := oSpec) (init := init) (impl := impl) i

example := Spec.SingleRound.oracleVerifier_rbrKnowledgeSoundness
  (R := F) (deg := deg) (D := D) (oSpec := oSpec) (init := init) (impl := impl) i

example := Spec.oracleVerifier_rbrKnowledgeSoundness F deg D n oSpec (init := init) (impl := impl)

end Field

/-- All six routes reject a zero-divisor client, despite its valid uniform sampler. -/
example (_deg : ℕ) {m : ℕ} (_D : Fin m ↪ ZMod 4) {ι : Type} (_oSpec : OracleSpec ι)
    {σ : Type} (_init : ProbComp σ) (_impl : QueryImpl _oSpec (StateT σ ProbComp))
    {n : ℕ} (_i : Fin n) : True := by
  let : SampleableType (ZMod 4) := SampleableType.ofFintype (ZMod 4)
  fail_if_success
    have _ := Simpler.oracleVerifier_rbrKnowledgeSoundness (ZMod 4) _deg _D _oSpec
      (init := _init) (impl := _impl)
  fail_if_success
    have _ := Simple.verifier_rbrKnowledgeSoundness (ZMod 4) _deg _D _oSpec
      (init := _init) (impl := _impl)
  fail_if_success
    have _ := Simple.oracleVerifier_rbrKnowledgeSoundness (ZMod 4) _deg _D _oSpec
      (init := _init) (impl := _impl)
  fail_if_success
    have _ := Spec.SingleRound.verifier_rbrKnowledgeSoundness
      (R := ZMod 4) (deg := _deg) (D := _D) (oSpec := _oSpec) (init := _init) (impl := _impl) _i
  fail_if_success
    have _ := Spec.SingleRound.oracleVerifier_rbrKnowledgeSoundness
      (R := ZMod 4) (deg := _deg) (D := _D) (oSpec := _oSpec) (init := _init) (impl := _impl) _i
  fail_if_success
    have _ := Spec.oracleVerifier_rbrKnowledgeSoundness (ZMod 4) _deg _D n _oSpec
      (init := _init) (impl := _impl)
  trivial

end Sumcheck.LegacySoundnessTest
