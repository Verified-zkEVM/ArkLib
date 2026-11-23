/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.Prelude
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Spec
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Commitment
public import ArkLib.ProofSystem.RingSwitching.Packing.Compatibility
public import CompPoly.Multilinear.Unique
public import CompPoly.Multivariate.MvPolyEquiv.Instances
public import CompPoly.Multivariate.Operations

/-!
# FRI-Binius IOPCS Prelude
This module contains the preliminary definitions for the FRI-Binius IOPCS. Hypercube indices
use the canonical least-significant-bit-first order. Relaxed compatibility permits unique-radius
closeness; strict compatibility requires an exact first-codeword encoding. Functionality and
honest coverage certify this oracle relation separately from the later opening protocol.
-/

@[expose] public section

noncomputable section

namespace Binius.FRIBinius

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial
  MvPolynomial TensorProduct Module Sumcheck.Structured
open scoped NNReal

section BooleanWitness

open CompPoly CPoly

variable {R : Type} [CommRing R] {n : ℕ}

@[no_expose] private def polynomialFromTable [DecidableEq R] (a : (Fin n → Fin 2) → R) :
    MvPolynomial (Fin n) R :=
  let table : CMlPolynomialEval R n := Vector.ofFn (a ∘ finFunctionFinEquiv.symm)
  let coeffs := CMlPolynomial.lagrangeToMono n table
  CPoly.fromCMvPolynomial (∑ j : Fin (2 ^ n),
    CMvPolynomial.monomial (Vector.ofFn fun (i : Fin n) => Nat.getBit i.val j.val) (coeffs.get j))

private theorem polynomialFromTable_eq [DecidableEq R] (a : (Fin n → Fin 2) → R) :
    polynomialFromTable a =
      (CMlPolynomialEval.toMvPolynomial (Vector.ofFn (a ∘ finFunctionFinEquiv.symm))) := by
  unfold polynomialFromTable CMlPolynomialEval.toMvPolynomial CMlPolynomial.toMvPolynomial
  rw [CMvPolynomial.fromCMvPolynomial_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [CMvPolynomial.fromCMvPolynomial_monomial]
  have hMono : CMvMonomial.toFinsupp (Vector.ofFn fun (i : Fin n) =>
      Nat.getBit i.val j.val) = CMlPolynomial.monomialOfNat j.val := by
    apply Finsupp.ext
    intro i
    simp [CMvMonomial.toFinsupp, CMlPolynomial.monomialOfNat]
  rw [hMono]
  rfl

/-- Construct the multilinear extension of the Boolean table with computable coefficients. -/
@[no_expose]
def multilinearOfTable [DecidableEq R] (a : (Fin n → Fin 2) → R) : MultilinearPoly R n :=
  ⟨polynomialFromTable a, by
    rw [polynomialFromTable_eq]
    exact CMlPolynomial.toMvPolynomial_is_multilinear _⟩

/-- Evaluating the constructed polynomial on a Boolean point recovers the table entry. -/
theorem eval_multilinearOfTable [DecidableEq R] (a : (Fin n → Fin 2) → R)
    (y : Fin n → Fin 2) : (multilinearOfTable a).val.eval (y : Fin n → R) = a y := by
  have h := CMlPolynomialEval.eval_toMvPolynomial_vertex
    (Vector.ofFn (a ∘ finFunctionFinEquiv.symm)) (finFunctionFinEquiv y)
  change (polynomialFromTable a).eval (y : Fin n → R) = a y
  rw [polynomialFromTable_eq]
  have hVertex : (CMlPolynomialEval.vertex (R := R) (finFunctionFinEquiv y)).get =
      (y : Fin n → R) := by
    calc
      _ = Binius.BinaryBasefold.bitsOfIndex (finFunctionFinEquiv y) := by
        funext i
        simp [CMlPolynomialEval.vertex, Binius.BinaryBasefold.bitsOfIndex,
          BitVec.getLsb]
      _ = ((finFunctionFinEquiv.symm (finFunctionFinEquiv y) : Fin n → Fin 2) : Fin n → R) :=
        (Binius.BinaryBasefold.coe_fin_pow_two_eq_bitsOfIndex _).symm
      _ = _ := congrArg (fun a : Fin n → Fin 2 => (a : Fin n → R))
        (Equiv.symm_apply_apply _ _)
  rw [hVertex] at h
  have ha : (Vector.ofFn (a ∘ finFunctionFinEquiv.symm))[finFunctionFinEquiv y] = a y := by
    change (Vector.ofFn (a ∘ finFunctionFinEquiv.symm)).get (finFunctionFinEquiv y) = _
    simp only [Vector.get_ofFn, Function.comp_apply, Equiv.symm_apply_apply]
  exact h.trans ha

private theorem toTable_multilinearOfTable [DecidableEq R] [IsDomain R]
    (a : (Fin n → Fin 2) → R) :
    MvPolynomial.MLEEquiv (R := R) (σ := Fin n) (multilinearOfTable a) = a :=
  funext (eval_multilinearOfTable a)

private theorem multilinearOfTable_toTable [DecidableEq R] [IsDomain R]
    (p : MultilinearPoly R n) :
    multilinearOfTable (fun x : Fin n → Fin 2 => p.val.eval (x : Fin n → R)) = p := by
  let e := MvPolynomial.MLEEquiv (R := R) (σ := Fin n)
  have hp : (fun x : Fin n → Fin 2 => p.val.eval (x : Fin n → R)) = e p := rfl
  rw [hp]
  exact e.injective (toTable_multilinearOfTable (e p))

/-- Equivalence of Boolean tables and multilinear witnesses, with executable conversions. -/
@[no_expose]
def tableWitnessEquiv [DecidableEq R] [IsDomain R] :
    ((Fin n → Fin 2) → R) ≃ MultilinearPoly R n where
  toFun := multilinearOfTable
  invFun t y := t.val.eval (y : Fin n → R)
  left_inv a := funext (eval_multilinearOfTable a)
  right_inv := multilinearOfTable_toTable

/-- The forward conversion constructs the multilinear extension of the table. -/
theorem tableWitnessEquiv_apply [DecidableEq R] [IsDomain R] (a : (Fin n → Fin 2) → R) :
    tableWitnessEquiv a = multilinearOfTable a := by
  unfold tableWitnessEquiv
  rfl

end BooleanWitness

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [Field L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [Field K]
local instance [Finite K] : Fact (Nat.Prime (ringChar K)) :=
  ⟨CharP.prime_ringChar K⟩
variable [Fintype K] [DecidableEq K]
variable [hF₂ : Fact (Fintype.card K = 2)]
variable [Algebra K L]
variable (β : Basis (Fin (2 ^ κ)) K L)
variable (ℓ ℓ' 𝓡 ϑ γ_repetitions : ℕ) [NeZero ℓ] [NeZero ℓ'] [NeZero 𝓡] [NeZero ϑ]
variable (h_ℓ_add_R_rate : ℓ' + 𝓡 < 2 ^ κ)
variable (h_l : ℓ = ℓ' + κ)
variable [hdiv : Fact (ϑ ∣ ℓ')]

/-- The canonical radix-two enumeration of the Boolean hypercube. -/
def hypercubeEquivFin : (Fin κ → Fin 2) ≃ Fin (2 ^ κ) :=
  finFunctionFinEquiv

/-- The basis reindexed by Boolean-hypercube coordinates. -/
def booleanHypercubeBasis : Basis (Fin κ → Fin 2) K L :=
  β.reindex (e := (hypercubeEquivFin κ).symm)

instance instFactLinearIndependentBasis : Fact (LinearIndependent K ⇑β) := by
  constructor
  exact β.linearIndependent

/-- The Binius ring-switching profile: the tensor-product profile at the Boolean-hypercube
reindexing `booleanHypercubeBasis` of `β`. -/
def biniusProfile : RingSwitching.RingSwitchingProfile K L κ :=
  RingSwitching.tensorProductProfile κ K L (booleanHypercubeBasis κ L K β)

/-- The shared Binary Basefold first-oracle interface at the packed dimension. -/
def binaryBasefoldInput : RingSwitching.AbstractOStmtIn L ℓ' :=
  BinaryBasefold.firstOracleInterface K β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)

omit [NeZero κ] [SampleableType L] [DecidableEq K] [NeZero 𝓡] in
/-- Unique-radius compatibility determines the initial committed polynomial. -/
theorem binaryBasefold_initialCompatibility_functional :
    (binaryBasefoldInput κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).Functional :=
  BinaryBasefold.firstOracleInterface_functional K β ϑ

/-- Honest first-codeword oracles cover every packed polynomial. -/
def honestPackedOracle (t : MultilinearPoly L ℓ') :
    ∀ j, (binaryBasefoldInput κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).OStmtIn j :=
  BinaryBasefold.honestInitialOracleStatement K β ϑ
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t

omit [NeZero κ]  [SampleableType L] [DecidableEq K] [NeZero 𝓡] in
/-- Honest families also meet the exact encoding premise used for completeness. -/
theorem honestPackedOracle_strictCompatible (t : MultilinearPoly L ℓ') :
    (binaryBasefoldInput κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).strictInitialCompatibility
      (t, honestPackedOracle κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate t) := by
  classical
  exact BinaryBasefold.firstOracleInterface_strictInitialCompatibility_honest K β ϑ t

end Binius.FRIBinius
