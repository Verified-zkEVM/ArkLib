/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.FieldTheory.Perfect
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.MvPolynomial.Expand

/-!
# Frobenius pullback for multivariate polynomials

This file records the coefficient twist used in the pullback of an inseparable root equation over
a perfect field.  If `s = p ^ e`, raising the inverse-Frobenius coefficient twist to the `s`-th
power applies the `s`-th power substitution to every variable.

The split identity assumes an already supplied equation
`F = rootPowerSubstitution (p ^ e) G`.  This file does not extract a maximal Frobenius factor,
prove separability of `G`, or establish the geometric image and agreement bounds needed for MCA.
-/

@[expose] public section

namespace MvPolynomial

noncomputable section

variable {K σ : Type*} [Field K] (p e : ℕ) [ExpChar K p] [PerfectField K]

/-- Apply the inverse of the `e`-fold Frobenius to every coefficient. -/
def inverseFrobeniusTwist (G : MvPolynomial σ K) : MvPolynomial σ K :=
  G.map (iterateFrobeniusEquiv K p e).symm

/-- The inverse-Frobenius coefficient twist becomes the full Frobenius variable pullback after
raising it to the corresponding prime power. -/
theorem inverseFrobeniusTwist_pow (G : MvPolynomial σ K) :
    inverseFrobeniusTwist p e G ^ (p ^ e) = G.expand (p ^ e) := by
  have hcomp : (iterateFrobenius K p e).comp (iterateFrobeniusEquiv K p e).symm =
      RingHom.id K := by
    ext x
    exact (iterateFrobeniusEquiv K p e).apply_symm_apply x
  simpa only [inverseFrobeniusTwist, map_expand, map_map, hcomp, map_id] using
    (map_iterateFrobenius_expand p (inverseFrobeniusTwist p e G) e).symm

/-- Twisting coefficients through the inverse Frobenius automorphism preserves irreducibility. -/
theorem Irreducible.map_inverseFrobeniusTwist {G : MvPolynomial σ K} (hG : Irreducible G) :
    Irreducible (inverseFrobeniusTwist p e G) := by
  simpa [inverseFrobeniusTwist] using hG.map (mapEquiv σ (iterateFrobeniusEquiv K p e).symm)

/-- Evaluation form of `inverseFrobeniusTwist_pow`. -/
theorem eval_inverseFrobeniusTwist_pow (G : MvPolynomial σ K) (v : σ → K) :
    eval v (inverseFrobeniusTwist p e G) ^ (p ^ e) = eval (v ^ (p ^ e)) G := by
  rw [← eval_pow, inverseFrobeniusTwist_pow, eval_expand]

/-- A root of the Frobenius-pulled equation lifts to a root of the coefficient twist. -/
theorem eval_inverseFrobeniusTwist_eq_zero (G : MvPolynomial σ K) (v : σ → K)
    (hG : eval (v ^ (p ^ e)) G = 0) :
    eval v (inverseFrobeniusTwist p e G) = 0 := by
  apply eq_zero_of_pow_eq_zero
  rw [eval_inverseFrobeniusTwist_pow, hG]

/-- The prime-power map is injective on a perfect field.  This is the set-theoretic fact needed
when exceptional pulled challenges are counted in the original challenge coordinate. -/
theorem pow_primePow_injective : Function.Injective (fun x : K ↦ x ^ (p ^ e)) := by
  intro x y hxy
  exact (iterateFrobeniusEquiv K p e).injective hxy

/-- Every challenge over a perfect field has a unique prime-power pullback. -/
theorem existsUnique_pow_eq_primePow (z : K) : ∃! w : K, w ^ (p ^ e) = z :=
  (iterateFrobeniusEquiv K p e).bijective.existsUnique z

/-! ## Splitting the pullback between base and root variables -/

section VariablePowerSubstitution

variable {R τ : Type*} [CommSemiring R]

/-- Substitute `X i ^ q i` for each variable `X i`. -/
def variablePowerSubstitution (q : τ → ℕ) (G : MvPolynomial τ R) : MvPolynomial τ R :=
  bind₁ (fun i ↦ X i ^ q i) G

/-- Variable-wise power substitutions compose by multiplying their exponents. -/
theorem variablePowerSubstitution_comp (q r : τ → ℕ) (G : MvPolynomial τ R) :
    variablePowerSubstitution q (variablePowerSubstitution r G) =
      variablePowerSubstitution (fun i ↦ q i * r i) G := by
  simp only [variablePowerSubstitution, bind₁_bind₁, map_pow, bind₁_X_right, pow_mul]

/-- Applying one common power to every variable is `MvPolynomial.expand`. -/
theorem variablePowerSubstitution_const (s : ℕ) (G : MvPolynomial τ R) :
    variablePowerSubstitution (fun _ ↦ s) G = G.expand s := by
  apply DFunLike.congr_fun (algHom_ext fun i ↦ ?_) G
  simp

/-- Evaluation commutes with a variable-wise power substitution. -/
theorem eval_variablePowerSubstitution (q : τ → ℕ) (G : MvPolynomial τ R) (v : τ → R) :
    eval v (variablePowerSubstitution q G) = eval (fun i ↦ v i ^ q i) G := by
  rw [variablePowerSubstitution]
  change eval v (eval₂ C (fun i ↦ X i ^ q i) G) = _
  rw [← eval_assoc]
  simp [Function.comp_def]

/-- Exponents for applying the Frobenius power only to the root variable `Y = X 2`. -/
def rootVariableExponent (s : ℕ) (i : Fin 3) : ℕ :=
  if i = 2 then s else 1

/-- Exponents for applying the Frobenius power only to the two base variables `X = X 0` and
`Z = X 1`. -/
def baseVariableExponent (s : ℕ) (i : Fin 3) : ℕ :=
  if i = 2 then 1 else s

/-- Substitute `Y ^ s` for `Y` while leaving the two base variables fixed. -/
def rootPowerSubstitution (s : ℕ) (G : MvPolynomial (Fin 3) R) :
    MvPolynomial (Fin 3) R :=
  variablePowerSubstitution (rootVariableExponent s) G

/-- Substitute `X ^ s` and `Z ^ s` for the base variables while leaving `Y` fixed. -/
def basePowerSubstitution (s : ℕ) (F : MvPolynomial (Fin 3) R) :
    MvPolynomial (Fin 3) R :=
  variablePowerSubstitution (baseVariableExponent s) F

theorem baseVariableExponent_mul_rootVariableExponent (s : ℕ) (i : Fin 3) :
    baseVariableExponent s i * rootVariableExponent s i = s := by
  by_cases hi : i = 2 <;> simp [baseVariableExponent, rootVariableExponent, hi]

/-- Pulling back the base variables after replacing `Y` by `Y ^ s` is the full power
substitution. -/
theorem basePowerSubstitution_rootPowerSubstitution (s : ℕ)
    (G : MvPolynomial (Fin 3) R) :
    basePowerSubstitution s (rootPowerSubstitution s G) = G.expand s := by
  rw [basePowerSubstitution, rootPowerSubstitution, variablePowerSubstitution_comp]
  rw [← variablePowerSubstitution_const s G]
  apply congrArg (fun q ↦ variablePowerSubstitution q G)
  funext i
  exact baseVariableExponent_mul_rootVariableExponent s i

/-- Evaluating the base-variable pullback at `(T,W,U)` evaluates the original polynomial at
`(T ^ s,W ^ s,U)`. -/
theorem eval_basePowerSubstitution (s : ℕ) (F : MvPolynomial (Fin 3) R) (t w u : R) :
    eval ![t, w, u] (basePowerSubstitution s F) = eval ![t ^ s, w ^ s, u] F := by
  rw [basePowerSubstitution, eval_variablePowerSubstitution]
  apply congrArg (fun v ↦ eval v F)
  funext i
  fin_cases i <;> simp [baseVariableExponent]

/-- Evaluating the root-variable substitution at `(T,W,U)` evaluates the original polynomial at
`(T,W,U ^ s)`. -/
theorem eval_rootPowerSubstitution (s : ℕ) (G : MvPolynomial (Fin 3) R) (t w u : R) :
    eval ![t, w, u] (rootPowerSubstitution s G) = eval ![t, w, u ^ s] G := by
  rw [rootPowerSubstitution, eval_variablePowerSubstitution]
  apply congrArg (fun v ↦ eval v G)
  funext i
  fin_cases i <;> simp [rootVariableExponent]

end VariablePowerSubstitution

/-- Polynomial form of the identity
`Gtilde(T,W,U) ^ s = F(T ^ s, W ^ s, U)` when `F(X,Z,Y) = G(X,Z,Y ^ s)` and
`s = p ^ e`. -/
theorem inverseFrobeniusTwist_pow_eq_basePowerSubstitution
    (F G : MvPolynomial (Fin 3) K) (hF : F = rootPowerSubstitution (p ^ e) G) :
    inverseFrobeniusTwist p e G ^ (p ^ e) = basePowerSubstitution (p ^ e) F := by
  rw [hF, basePowerSubstitution_rootPowerSubstitution, inverseFrobeniusTwist_pow]

/-- Root transport for the split three-variable identity. -/
theorem eval_inverseFrobeniusTwist_eq_zero_of_basePowerSubstitution
    (F G : MvPolynomial (Fin 3) K) (hF : F = rootPowerSubstitution (p ^ e) G)
    (v : Fin 3 → K) (hroot : eval v (basePowerSubstitution (p ^ e) F) = 0) :
    eval v (inverseFrobeniusTwist p e G) = 0 := by
  apply eq_zero_of_pow_eq_zero
  rw [← eval_pow, inverseFrobeniusTwist_pow_eq_basePowerSubstitution p e F G hF, hroot]

/-- Coordinate form of root transport: if `F(X,Z,Y) = G(X,Z,Y ^ s)` and
`F(T ^ s,W ^ s,U) = 0`, then the coefficient twist of `G` vanishes at `(T,W,U)`. -/
theorem eval_inverseFrobeniusTwist_eq_zero_of_rootPowerSubstitution
    (F G : MvPolynomial (Fin 3) K) (hF : F = rootPowerSubstitution (p ^ e) G)
    (t w u : K) (hroot : eval ![t ^ (p ^ e), w ^ (p ^ e), u] F = 0) :
    eval ![t, w, u] (inverseFrobeniusTwist p e G) = 0 := by
  apply eval_inverseFrobeniusTwist_eq_zero_of_basePowerSubstitution p e F G hF
  rwa [eval_basePowerSubstitution]

/-- A nonconstant three-variable canary for the split pullback and root transport.  The polynomial
`X + Z - Y` vanishes after pullback at `(T,W,T + W)` because iterated Frobenius preserves
addition. -/
theorem inverseFrobeniusTwist_root_canary (t w : K) :
    eval ![t, w, t + w]
      (inverseFrobeniusTwist p e
        (X 0 + X 1 - X 2 : MvPolynomial (Fin 3) K)) = 0 := by
  let G : MvPolynomial (Fin 3) K := X 0 + X 1 - X 2
  let F := rootPowerSubstitution (p ^ e) G
  apply eval_inverseFrobeniusTwist_eq_zero_of_rootPowerSubstitution p e F G rfl
  rw [show F = rootPowerSubstitution (p ^ e) G by rfl, eval_rootPowerSubstitution]
  simp only [G, eval_sub, eval_add, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  exact sub_eq_zero.mpr (RingHom.map_add (iterateFrobenius K p e) t w).symm

/-- A coefficient canary that distinguishes the inverse twist from both the identity and forward
Frobenius.  In a perfect field of characteristic two, a root of `a ^ 3 + a + 1` has inverse
Frobenius `a ^ 2 + a`, whereas forward Frobenius sends it to the distinct value `a ^ 2`. -/
theorem inverseFrobeniusTwist_cubicCoefficient_canary
    {L : Type*} [Field L] [CharP L 2] [PerfectField L] (a : L)
    (ha : a ^ 3 + a + 1 = 0) :
    inverseFrobeniusTwist 2 1
        (C a * X 0 + X 1 : MvPolynomial (Fin 2) L) = C (a ^ 2 + a) * X 0 + X 1 ∧
      a ^ 2 + a ≠ a ^ 2 := by
  have hcoeff : (frobeniusEquiv L 2).symm a = a ^ 2 + a := by
    have hcubic : a ^ 3 = a + 1 := by
      apply sub_eq_zero.mp
      rw [CharTwo.sub_eq_add]
      simpa only [add_assoc] using ha
    have hfour : a ^ 4 = a ^ 2 + a := by
      calc
        a ^ 4 = a * a ^ 3 := by ring
        _ = a * (a + 1) := by rw [hcubic]
        _ = a ^ 2 + a := by ring
    have hsquare : (a ^ 2 + a) ^ 2 = a := by
      have hadd := RingHom.map_add (frobenius L 2) (a ^ 2) a
      change (a ^ 2 + a) ^ 2 = (a ^ 2) ^ 2 + a ^ 2 at hadd
      calc
        (a ^ 2 + a) ^ 2 = (a ^ 2) ^ 2 + a ^ 2 := hadd
        _ = a ^ 4 + a ^ 2 := by rw [← pow_mul]
        _ = (a ^ 2 + a) + a ^ 2 := by rw [hfour]
        _ = (a ^ 2 + a ^ 2) + a := by ac_rfl
        _ = a := by rw [CharTwo.add_self_eq_zero, zero_add]
    apply (frobeniusEquiv L 2).injective
    rw [RingEquiv.apply_symm_apply]
    exact hsquare.symm
  constructor
  · simp [inverseFrobeniusTwist, hcoeff]
  · have ha0 : a ≠ 0 := by
      intro hzero
      rw [hzero] at ha
      simp at ha
    intro hforward
    apply ha0
    apply add_left_cancel (a := a ^ 2)
    simpa using hforward

end

end MvPolynomial
