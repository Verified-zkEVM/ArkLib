/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Search.Proofs
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Global.Multiplicity
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FiniteField.TotalDegreeExtension
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Output.CanonicalOutputProofRoots
public import ArkLib.Data.MvPolynomial.QuadraticInputSemantics
/-!
# From actual interpolation certificates to base roots and physical extension inputs

The base-field local constraints imply the differential identity at every qualifying message.
Scalar naturality then transports that identity. Physical dense layout is proved from the
actual interpolation emitter and successful search, independently of polynomial equality.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.PreparedDecoderCertificate

open PolynomialDifferential
open Polynomial HiddenDerivative
open MvPolynomial (rename)

variable {F : Type*} [Field F] [DecidableEq F]

/-- Exact interpolation constraints force every sufficiently agreeing base message to be a root. -/
theorem certified_root {D d m A k n : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (out : NonzeroInterpolationMachine.Output F)
    (hc : NonzeroInterpolationMachine.Certified (d := d) D m A
      (List.ofFn fun i ↦ (domain i, received i)) out)
    (hk : k ≤ D + 1) (f : F[X]) (hd : f.degree < k)
    (ha : A ≤ Code.agree (evalOnPoints domain f) received) :
    differentialSpecialization (NonzeroInterpolationMachine.sourceOutput (d := d) D m A out)
      f = 0 := by
  obtain ⟨_hl, _hj, _hc, _ht, _hkeys, _hcoeff, _hrep, _hne, _helig, hw, hlocal⟩ := hc
  have hf : f.natDegree ≤ D := by
    by_cases hz : f = 0
    · simp [hz]
    · have hlt := (natDegree_lt_iff_degree_lt hz).mpr hd
      omega
  let indices := Finset.univ.filter fun i ↦ f.eval (domain i) = received i
  apply differentialSpecialization_eq_zero_of_global_multiplicity domain indices m A _ f
    domain.injective.injOn ha
  · intro i hi
    apply X_sub_C_pow_dvd_differentialSpecialization_of_contact _ f (domain i) (received i)
      (Finset.mem_filter.mp hi).2
    exact hlocal (domain i, received i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · exact (natDegree_differentialSpecialization_le _ f hf).trans_lt hw

/-- The root identity transports through the canonical coefficient map, without new constraints. -/
theorem certified_embedded_root {E : Type*} [CommSemiring E] (ι : F →+* E)
    {D d m A k n : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (out : NonzeroInterpolationMachine.Output F)
    (hc : NonzeroInterpolationMachine.Certified (d := d) D m A
      (List.ofFn fun i ↦ (domain i, received i)) out)
    (hk : k ≤ D + 1) (f : F[X]) (hd : f.degree < k)
    (ha : A ≤ Code.agree (evalOnPoints domain f) received) :
    differentialSpecialization
      (MvPolynomial.map ι (NonzeroInterpolationMachine.sourceOutput (d := d) D m A out))
      (f.map ι) = 0 := by
  rw [← map_differentialSpecialization, certified_root domain received out hc hk f hd ha,
    Polynomial.map_zero]

/-- Explicitly budgeted interpolation constraints force every agreeing message to be a root. -/
theorem certified_rootWithBudget {D d m J A k n : ℕ} (domain : Fin n ↪ F)
    (received : Fin n → F) (out : NonzeroInterpolationMachine.Output F)
    (hc : NonzeroInterpolationMachine.CertifiedWithBudget (d := d) D m J A
      (List.ofFn fun i ↦ (domain i, received i)) out)
    (hk : k ≤ D + 1) (f : F[X]) (hd : f.degree < k)
    (ha : A ≤ Code.agree (evalOnPoints domain f) received) :
    differentialSpecialization
      (NonzeroInterpolationMachine.sourceOutputWithBudget (d := d) D m J A out) f = 0 := by
  obtain ⟨_hl, _hj, _hc, _ht, _hkeys, _hcoeff, _hrep, _hne, _helig, hw, hlocal⟩ := hc
  have hf : f.natDegree ≤ D := by
    by_cases hz : f = 0
    · simp [hz]
    · have hlt := (natDegree_lt_iff_degree_lt hz).mpr hd
      omega
  let indices := Finset.univ.filter fun i ↦ f.eval (domain i) = received i
  apply differentialSpecialization_eq_zero_of_global_multiplicity domain indices m A _ f
    domain.injective.injOn ha
  · intro i hi
    apply X_sub_C_pow_dvd_differentialSpecialization_of_contact _ f (domain i) (received i)
      (Finset.mem_filter.mp hi).2
    exact hlocal (domain i, received i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · exact (natDegree_differentialSpecialization_le _ f hf).trans_lt hw

/-- The explicitly budgeted root identity transports through any coefficient map. -/
theorem certified_embedded_rootWithBudget {E : Type*} [CommSemiring E] (ι : F →+* E)
    {D d m J A k n : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (out : NonzeroInterpolationMachine.Output F)
    (hc : NonzeroInterpolationMachine.CertifiedWithBudget (d := d) D m J A
      (List.ofFn fun i ↦ (domain i, received i)) out)
    (hk : k ≤ D + 1) (f : F[X]) (hd : f.degree < k)
    (ha : A ≤ Code.agree (evalOnPoints domain f) received) :
    differentialSpecialization
      (MvPolynomial.map ι
        (NonzeroInterpolationMachine.sourceOutputWithBudget (d := d) D m J A out))
      (f.map ι) = 0 := by
  rw [← map_differentialSpecialization,
    certified_rootWithBudget domain received out hc hk f hd ha, Polynomial.map_zero]

omit [DecidableEq F] in
/-- The interpolation and root machines use precisely the same variable encoding. -/
theorem variableIndex_eq_encodeJet {d : ℕ} :
    NonzeroInterpolationMachine.variableIndex (d := d) = HighestJetTransport.encodeJet := by
  funext v
  cases v <;> rfl

omit [DecidableEq F] in
/-- The actual scalar allocation represents the coefficient extension of the certified equation. -/
theorem embedded_representation {D d m A : ℕ} (rows : List (F × F))
    (out : NonzeroInterpolationMachine.Output F)
    (hc : NonzeroInterpolationMachine.Certified (d := d) D m A rows out) (a : F) :
    MvPolynomial.EvaluationMachine.sparsePolynomial
      (MvPolynomial.QuadraticInputMachine.embedded (a := a) out.terms) =
      rename HighestJetTransport.encodeJet
        (MvPolynomial.map (algebraMap F (QuadraticAlgebra F a 0))
          (NonzeroInterpolationMachine.sourceOutput (d := d) D m A out)) := by
  rw [MvPolynomial.QuadraticInputMachine.sparsePolynomial_embedded,
    hc.2.2.2.2.2.2.1, variableIndex_eq_encodeJet, MvPolynomial.map_rename]

omit [DecidableEq F] in
/-- Scalar allocation represents the equation returned at strict jet cutoff `J`. -/
theorem embedded_representationWithBudget {D d m J A : ℕ} (rows : List (F × F))
    (out : NonzeroInterpolationMachine.Output F)
    (hc : NonzeroInterpolationMachine.CertifiedWithBudget (d := d) D m J A rows out) (a : F) :
    MvPolynomial.EvaluationMachine.sparsePolynomial
      (MvPolynomial.QuadraticInputMachine.embedded (a := a) out.terms) =
      rename HighestJetTransport.encodeJet
        (MvPolynomial.map (algebraMap F (QuadraticAlgebra F a 0))
          (NonzeroInterpolationMachine.sourceOutputWithBudget (d := d) D m J A out)) := by
  rw [MvPolynomial.QuadraticInputMachine.sparsePolynomial_embedded,
    hc.2.2.2.2.2.2.1, variableIndex_eq_encodeJet, MvPolynomial.map_rename]

/-- Factor allocation retains the entire variable range, including positions of zero powers. -/
theorem factors_layout (v : List ℕ) :
    ((NonzeroInterpolationMachine.factors 0 v).1.map Prod.fst) = List.range v.length := by
  rw [NonzeroInterpolationMachine.factors_correct]
  simp only [List.map_ofFn, Nat.zero_add]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

/-- Every successfully emitted term has the support vector's full physical width. -/
theorem emit_layout {d : ℕ} (vs : List (List ℕ)) (cs : List F)
    (hv : ∀ v ∈ vs, v.length = d + 2) (ts : List (NonzeroInterpolationMachine.Term F))
    (he : (NonzeroInterpolationMachine.emit vs cs).1 = some ts) :
    MvPolynomial.DenseNormalizeMachine.DenseLayout (List.range (d + 2)) ts := by
  refine ⟨List.nodup_range, ?_⟩
  induction vs generalizing cs ts with
  | nil => cases cs <;> simp_all [NonzeroInterpolationMachine.emit]
  | cons v vs ih =>
      cases cs with
      | nil => simp [NonzeroInterpolationMachine.emit] at he
      | cons c cs =>
          have ht := ih cs (fun v hm ↦ hv v (by simp [hm]))
          simp only [NonzeroInterpolationMachine.emit] at he
          split at he
          · cases he
          · rename_i rest hrest
            split at he
            · cases he
              exact ht _ hrest
            · cases he
              intro t hm
              rcases List.mem_cons.mp hm with rfl | hm
              · simp only [factors_layout, hv v (by simp)]
              · exact ht _ hrest t hm

/-- A successful actual interpolation attempt supplies its physical dense layout. -/
theorem attempt_layout (D d m A : ℕ) (rows : List (F × F))
    (out : NonzeroInterpolationMachine.Output F)
    (hr : (NonzeroInterpolationMachine.run D d m A rows).1 = some out) :
    MvPolynomial.DenseNormalizeMachine.DenseLayout (List.range (d + 2)) out.terms := by
  obtain ⟨c, hs, _hc⟩ :=
    InterpolationSupportMachine.enumerateWithBudget_correct D d m (2 * m) A
  change (NonzeroInterpolationMachine.runWithBudget D d m (2 * m) A rows).1 = some out at hr
  simp only [NonzeroInterpolationMachine.runWithBudget, hs] at hr
  split at hr
  · cases hr
  · split at hr
    · rename_i mat hm j cs hsol
      generalize he : (NonzeroInterpolationMachine.emit
        (InterpolationSupportMachine.supportSpec
          (InterpolationSupportMachine.parametersWithBudget D d m (2 * m) A)) cs).1 = result at hr
      cases result with
      | none => cases hr
      | some ts =>
          cases hr
          apply emit_layout _ cs _ ts he
          intro v hv
          simpa [InterpolationSupportMachine.parametersWithBudget] using
            InterpolationSupportMachine.supportSpec_width _ hv
    · cases hr

/-- A successful interpolation attempt at strict cutoff `J` supplies dense physical layout. -/
theorem attemptWithBudget_layout (D d m J A : ℕ) (rows : List (F × F))
    (out : NonzeroInterpolationMachine.Output F)
    (hr : (NonzeroInterpolationMachine.runWithBudget D d m J A rows).1 = some out) :
    MvPolynomial.DenseNormalizeMachine.DenseLayout (List.range (d + 2)) out.terms := by
  obtain ⟨c, hs, _hc⟩ := InterpolationSupportMachine.enumerateWithBudget_correct D d m J A
  simp only [NonzeroInterpolationMachine.runWithBudget, hs] at hr
  split at hr
  · cases hr
  · split at hr
    · rename_i mat hm j cs hsol
      generalize he : (NonzeroInterpolationMachine.emit
        (InterpolationSupportMachine.supportSpec
          (InterpolationSupportMachine.parametersWithBudget D d m J A)) cs).1 = result at hr
      cases result with
      | none => cases hr
      | some ts =>
          cases hr
          apply emit_layout _ cs _ ts he
          intro v hv
          simpa [InterpolationSupportMachine.parametersWithBudget] using
            InterpolationSupportMachine.supportSpec_width _ hv
    · cases hr

/-- A successful descending search returns an interpolant from an actual successful attempt. -/
theorem search_origin (d m A count D : ℕ) (rows : List (F × F))
    (out : AmbientSearchMachine.Output F)
    (hr : (AmbientSearchMachine.search d m A rows count D).1 = some out) :
    (NonzeroInterpolationMachine.run out.degree d m A rows).1 = some out.interpolant := by
  change (AmbientSearchMachine.searchWithBudget d m (2 * m) A rows count D).1 = some out at hr
  change (NonzeroInterpolationMachine.runWithBudget out.degree d m (2 * m) A rows).1 =
    some out.interpolant
  induction count generalizing D with
  | zero => simp [AmbientSearchMachine.searchWithBudget] at hr
  | succ count ih =>
      simp only [AmbientSearchMachine.searchWithBudget] at hr
      split at hr
      · rename_i interp hi
        cases hr
        exact hi
      · exact ih (D - 1) hr

/-- The public search's actual output has dense layout; no physical-layout oracle is required. -/
theorem run_layout (k d m A : ℕ) (rows : List (F × F))
    (out : AmbientSearchMachine.Output F)
    (hr : (AmbientSearchMachine.run k d m A rows).1 = some out) :
    MvPolynomial.DenseNormalizeMachine.DenseLayout (List.range (d + 2)) out.interpolant.terms := by
  apply attempt_layout out.degree d m A rows out.interpolant
  apply search_origin d m A _ _ rows out
  exact hr

/-- Scalar execution on the actual search output preserves its equation and physical layout. -/
theorem converted_search_correct (k d m A : ℕ) (rows : List (F × F))
    (out : AmbientSearchMachine.Output F)
    (hr : (AmbientSearchMachine.run k d m A rows).1 = some out) (a : F) :
    ∃ ts c, MvPolynomial.QuadraticInputMachine.runFuel
        (2 * out.interpolant.terms.length + 3)
        (.scan out.interpolant.terms [] : MvPolynomial.QuadraticInputMachine.Configuration F a) =
          (.done ts, c) ∧
      MvPolynomial.EvaluationMachine.sparsePolynomial ts =
        rename HighestJetTransport.encodeJet
          (MvPolynomial.map (algebraMap F (QuadraticAlgebra F a 0))
            (NonzeroInterpolationMachine.sourceOutput (d := d) out.degree m A out.interpolant)) ∧
      MvPolynomial.DenseNormalizeMachine.DenseLayout (List.range (d + 2)) ts ∧
      c.total = 18 * out.interpolant.terms.length + 11 := by
  obtain ⟨result, rc, he, _hb, hs⟩ := AmbientSearchMachine.run_complete k d m A rows
  have he' := congrArg Prod.fst he
  rw [hr] at he'
  change some out = result at he'
  subst result
  have hc := (hs out rfl).2.2
  obtain ⟨c, hrun, hcost⟩ := MvPolynomial.QuadraticInputMachine.evaluation_runFuel
    (a := a) out.interpolant.terms
  exact ⟨_, c, hrun, embedded_representation rows out.interpolant hc a,
    MvPolynomial.QuadraticInputMachine.embedded_layout _ _ (run_layout k d m A rows out hr),
    hcost⟩

end ReedSolomon.ListDecoding.PreparedDecoderCertificate
