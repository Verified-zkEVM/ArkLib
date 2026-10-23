/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.ComputeDegree

/-!
# Sumcheck: soundness by counting, and compressed round messages

The protocol of Lund, Fortnow, Karloff and Nisan, as Thaler states it in
"Proofs, Arguments, and Zero-Knowledge", Section 4.1, with a deterministic prover strategy.

The prover claims `H = ∑_{b ∈ {0,1}^n} g(b)` for `g` of degree at most `d` in each variable.
Round `i`: the prover sends `g_i` of degree at most `d`; the verifier checks
`g_i(0) + g_i(1) = c_i`, samples `r_i`, and sets `c_{i+1} = g_i(r_i)`.
At the end the verifier checks `g(r) = c_n`.

## Results

- `completeness`: the honest prover is accepted on every challenge vector.
- `soundness`: against a false claim and any causal prover, at most `n d |F|^(n-1)` of the
  `|F|^n` challenge vectors accept, an error of `n d / |F|`.
- `accepts_induced_iff`, `soundness_decoded`, `completeness_decoded`: a verifier that receives a
  message `m_i` and decodes `g_i = dec(c_i, m_i)` with the running claim, where every decoding has
  degree at most `d` and passes the sum check by construction, accepts exactly when the verifier
  above accepts the decoded polynomials.
- `decEval_encEval`: the common compression of a quadratic round to `h(0)` and its leading
  coefficient, with `h(1) = c - h(0)`, is such a decoding, and every admissible quadratic has
  a message.

The statements need only mathlib; they complement the `OracleComp` development in
`ArkLib.ProofSystem.Sumcheck.Interaction`.
-/

@[expose] public section

namespace Sumcheck.Counting

open Finset

section Spec

open MvPolynomial

variable {F : Type _} [CommRing F] [DecidableEq F]

/-- The Boolean cube {0,1}^n, as points of F^n. -/
def cube (n : ℕ) : Finset (Fin n → F) := Fintype.piFinset fun _ => {0, 1}

/-- The sum of g over the Boolean cube. -/
noncomputable def cubeSum {n : ℕ} (g : MvPolynomial (Fin n) F) : F :=
  ∑ b ∈ cube n, eval b g

/-- g has degree at most d in each variable. -/
def IndividualDegreeLE {n : ℕ} (g : MvPolynomial (Fin n) F) (d : ℕ) : Prop :=
  ∀ i, g.degreeOf i ≤ d

/-- g with its first variable set to a. -/
noncomputable def fixFirst {n : ℕ} (a : F) (g : MvPolynomial (Fin (n + 1)) F) :
    MvPolynomial (Fin n) F :=
  Polynomial.eval (C a) (finSuccEquiv F n g)

/-- The honest first message: the first variable is kept, the others are summed over the cube.

```text
    s(X) = sum_{b in {0,1}^n} g(X, b)
```
-/
noncomputable def honestMessage {n : ℕ} (g : MvPolynomial (Fin (n + 1)) F) : Polynomial F :=
  ∑ b ∈ cube n, (finSuccEquiv F n g).map (eval b)

/-- The honest prover: round 0 sends the honest first message, and later rounds recurse on g with
its first variable set to r_0. -/
noncomputable def honestProver :
    {n : ℕ} → MvPolynomial (Fin n) F → Fin n → (Fin n → F) → Polynomial F
  | 0, _ => fun i => i.elim0
  | _ + 1, g => fun i r =>
    Fin.cases (honestMessage g) (fun j => honestProver (fixFirst (r 0) g) j (Fin.tail r)) i

/-- A prover strategy is causal when its message in round i reads only the challenges before i. -/
def Causal {α : Type _} {n : ℕ} (P : Fin n → (Fin n → F) → α) : Prop :=
  ∀ i r r', (∀ j : Fin n, j < i → r j = r' j) → P i r = P i r'

/-- The verifier accepts the claim c against the prover P on the challenges r.

Every round checks the degree bound and the sum g_i(0) + g_i(1) = c_i.

The last check is g(r) = c_n.
-/
def Accepts (d : ℕ) :
    {n : ℕ} → MvPolynomial (Fin n) F → F → (Fin n → (Fin n → F) → Polynomial F) →
    (Fin n → F) → Prop
  | 0, g, c, _, r => eval r g = c
  | _ + 1, g, c, P, r =>
    (P 0 r).natDegree ≤ d ∧ (P 0 r).eval 0 + (P 0 r).eval 1 = c ∧
      Accepts d (fixFirst (r 0) g) ((P 0 r).eval (r 0))
        (fun i r' => P i.succ (Fin.cons (r 0) r')) (Fin.tail r)

end Spec

section Proofs

open MvPolynomial

variable {F : Type _} [CommRing F] [DecidableEq F]

/-! ## The cube and the first variable -/

theorem sum_cube_succ {M : Type _} [AddCommMonoid M] {n : ℕ} (f : (Fin (n + 1) → F) → M) :
    ∑ b ∈ cube (n + 1), f b =
      ∑ a ∈ ({0, 1} : Finset F), ∑ b ∈ cube n, f (Fin.cons a b) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun b => (b 0, Fin.tail b)) (fun p => Fin.cons p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · intro b hb
    simp only [cube, Fintype.mem_piFinset] at hb
    simp [cube, Fin.tail, hb]
  · rintro ⟨a, b⟩ h
    simp only [mem_product, cube, Fintype.mem_piFinset] at h ⊢
    intro i
    exact Fin.cases (by simpa using h.1) (fun j => by simpa using h.2 j) i
  · intro b _; simp
  · rintro ⟨a, b⟩ _; simp
  · intro b _; simp

omit [DecidableEq F] in
theorem eval_fixFirst {n : ℕ} (a : F) (g : MvPolynomial (Fin (n + 1)) F) (s : Fin n → F) :
    eval s (fixFirst a g) = eval (Fin.cons a s) g := by
  rw [eval_eq_eval_mv_eval', fixFirst, Polynomial.eval_map, Polynomial.eval, Polynomial.hom_eval₂]
  simp

theorem eval_honestMessage {n : ℕ} (g : MvPolynomial (Fin (n + 1)) F) (a : F) :
    (honestMessage g).eval a = cubeSum (fixFirst a g) := by
  simp [honestMessage, cubeSum, Polynomial.eval_finsetSum, eval_fixFirst, eval_eq_eval_mv_eval']

theorem cubeSum_succ {n : ℕ} (g : MvPolynomial (Fin (n + 1)) F) :
    cubeSum g = cubeSum (fixFirst 0 g) + cubeSum (fixFirst 1 g) := by
  by_cases h : (0 : F) = 1
  · have : Subsingleton F := subsingleton_of_zero_eq_one h
    simp [Subsingleton.elim (cubeSum g) 0, Subsingleton.elim (cubeSum (fixFirst 0 g)) 0,
      Subsingleton.elim (cubeSum (fixFirst 1 g)) 0]
  · simp [cubeSum, sum_cube_succ, Finset.sum_pair h, eval_fixFirst]

theorem honestMessage_sum {n : ℕ} (g : MvPolynomial (Fin (n + 1)) F) :
    (honestMessage g).eval 0 + (honestMessage g).eval 1 = cubeSum g := by
  rw [eval_honestMessage, eval_honestMessage, cubeSum_succ]

/-! ## Degrees -/

theorem natDegree_honestMessage_le {n d : ℕ} {g : MvPolynomial (Fin (n + 1)) F}
    (hg : IndividualDegreeLE g d) : (honestMessage g).natDegree ≤ d :=
  Polynomial.natDegree_sum_le_of_forall_le _ _ fun _ _ =>
    (Polynomial.natDegree_map_le).trans ((natDegree_finSuccEquiv g).le.trans (hg 0))

omit [DecidableEq F] in
theorem individualDegreeLE_fixFirst {n d : ℕ} {g : MvPolynomial (Fin (n + 1)) F}
    (hg : IndividualDegreeLE g d) (a : F) : IndividualDegreeLE (fixFirst a g) d := by
  intro i
  rw [fixFirst, Polynomial.eval_eq_sum, Polynomial.sum_def]
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun k _ => ?_)
  rw [← map_pow]
  exact (degreeOf_mul_C_le _ _ _).trans ((degreeOf_coeff_finSuccEquiv g i k).trans (hg i.succ))

/-! ## Completeness -/

/-- The honest prover makes the verifier accept the true sum, on every challenge vector. -/
theorem completeness {d : ℕ} :
    ∀ {n : ℕ} (g : MvPolynomial (Fin n) F), IndividualDegreeLE g d →
    ∀ r, Accepts d g (cubeSum g) (honestProver g) r
  | 0, g, _, r => by
    simp [Accepts, cubeSum, cube, Subsingleton.elim r (fun i => i.elim0)]
    rfl
  | n + 1, g, hg, r => by
    refine ⟨natDegree_honestMessage_le hg, honestMessage_sum g, ?_⟩
    simp only [honestProver, Fin.cases_zero, Fin.cases_succ, Fin.tail_cons]
    rw [eval_honestMessage]
    exact completeness _ (individualDegreeLE_fixFirst hg _) _

/-! ## Soundness -/

omit [CommRing F] [DecidableEq F] in
theorem card_filter_succ {n : ℕ} [Fintype F] (p : (Fin (n + 1) → F) → Prop)
    [DecidablePred p] :
    #{r | p r} = ∑ a : F, #{t : Fin n → F | p (Fin.cons a t)} := by
  simp only [card_filter]
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => F)
    (fun x => if p (Fin.cons x.1 x.2) then 1 else 0)
    _ (fun _ => rfl), Fintype.sum_prod_type]

/-- Two distinct polynomials of degree at most d agree at most at d points. -/
theorem card_eval_eq_le [IsDomain F] [Fintype F] {d : ℕ} {p q : Polynomial F} (hpq : p ≠ q)
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) : #{a | p.eval a = q.eval a} ≤ d := by
  have h0 : p - q ≠ 0 := sub_ne_zero.mpr hpq
  calc #{a | p.eval a = q.eval a} ≤ (p - q).roots.toFinset.card :=
        card_le_card fun a ha => by simpa [h0, sub_eq_zero] using ha
    _ ≤ (p - q).roots.card := Multiset.toFinset_card_le _
    _ ≤ (p - q).natDegree := Polynomial.card_roots' _
    _ ≤ d := (Polynomial.natDegree_sub_le _ _).trans (max_le hp hq)

open scoped Classical in
/-- Against a false claim, at most n d |F|^(n-1) challenge vectors accept,
for every causal prover. -/
theorem soundness [IsDomain F] [Fintype F] {d : ℕ} :
    ∀ {n : ℕ} (g : MvPolynomial (Fin n) F), IndividualDegreeLE g d →
      ∀ (H : F), H ≠ cubeSum g →
      ∀ P, Causal P → #{r | Accepts d g H P r} * Fintype.card F ≤ n * d * Fintype.card F ^ n
  | 0, g, _, H, hH, P, _ => by
    have : ∀ r : Fin 0 → F, ¬ Accepts d g H P r := fun r h => hH <| by
      simp only [Accepts] at h
      simp [← h, cubeSum, cube, Subsingleton.elim r (fun i => i.elim0)]
      rfl
    simp [Finset.filter_false_of_mem fun r _ => this r]
  | n + 1, g, hg, H, hH, P, hP => by
    -- The first message reads no challenge.
    set p := P 0 (fun _ => 0)
    have hp : ∀ r, P 0 r = p := fun r => hP 0 _ _ fun j hj => absurd hj (Fin.not_lt_zero j)
    set s := honestMessage g
    by_cases hacc : ∃ r, Accepts d g H P r
    swap
    · push Not at hacc
      simp [Finset.filter_false_of_mem fun r _ => hacc r]
    -- A first message that passes the sum check is not the honest one.
    obtain ⟨r₀, hr₀⟩ := hacc
    simp only [Accepts, hp] at hr₀
    have hps : p ≠ s := fun he => hH (hr₀.2.1 ▸ he ▸ honestMessage_sum g)
    -- On the first challenge a, the rest of the run is a sumcheck of g(a, .) against p(a).
    set Q : F → Fin n → (Fin n → F) → Polynomial F := fun a i r' => P i.succ (Fin.cons a r')
    have hQ : ∀ a, Causal (Q a) := fun a i r r' h => hP _ _ _ fun j hj => by
      exact Fin.cases (fun _ => rfl) (fun k hk => by simp [h k (Fin.succ_lt_succ_iff.mp hk)]) j hj
    have key : ∀ a, #{t | Accepts d g H P (Fin.cons a t)} * Fintype.card F ≤
        if p.eval a = s.eval a then Fintype.card F ^ n * Fintype.card F
        else n * d * Fintype.card F ^ n := by
      intro a
      split_ifs with ha
      · exact Nat.mul_le_mul_right _ ((card_le_univ _).trans (by simp))
      · refine le_trans (Nat.mul_le_mul_right _ (card_le_card fun t ht => ?_))
          (soundness _ (individualDegreeLE_fixFirst hg a) (p.eval a)
            (by rwa [← eval_honestMessage]) (Q a) (hQ a))
        simp only [mem_filter, mem_univ, true_and, Accepts, hp, Fin.cons_zero,
          Fin.tail_cons] at ht ⊢
        exact ht.2.2
    have hroots := card_eval_eq_le hps hr₀.1 (natDegree_honestMessage_le hg)
    rw [card_filter_succ, Finset.sum_mul]
    refine (Finset.sum_le_sum fun a _ => key a).trans ?_
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
    have := card_le_univ (univ.filter fun a => ¬ p.eval a = s.eval a)
    calc _ ≤ d * (Fintype.card F ^ n * Fintype.card F) +
          Fintype.card F * (n * d * Fintype.card F ^ n) :=
          add_le_add (Nat.mul_le_mul_right _ hroots) (Nat.mul_le_mul_right _ this)
      _ = _ := by ring

end Proofs

section Decoded

open MvPolynomial

variable {F : Type _} [CommRing F] [DecidableEq F] {Msg : Type _}

/-- The claim left after replaying the messages against the challenges. -/
def finalClaim (dec : F → Msg → Polynomial F) (c : F) : List Msg → List F → F
  | m :: ms, r :: rs => finalClaim dec ((dec c m).eval r) ms rs
  | _, _ => c

omit [DecidableEq F] in
theorem finalClaim_snoc (dec : F → Msg → Polynomial F) (c : F) :
    ∀ (ms : List Msg) (rs : List F), ms.length = rs.length → ∀ m r,
      finalClaim dec c (ms ++ [m]) (rs ++ [r]) = (dec (finalClaim dec c ms rs) m).eval r
  | [], [], _, _, _ => rfl
  | m' :: ms, r' :: rs, h, m, r => by
    simp only [List.cons_append, finalClaim]
    exact finalClaim_snoc dec _ ms rs (by simpa using h) m r

/-- The polynomials the verifier decodes, as a prover strategy of Section 4.1. -/
noncomputable def induced (dec : F → Msg → Polynomial F) :
    {n : ℕ} → F → (Fin n → (Fin n → F) → Msg) → Fin n → (Fin n → F) →
      Polynomial F
  | 0, _, _ => fun i => i.elim0
  | _ + 1, c, M => fun i r =>
    Fin.cases (dec c (M 0 r))
      (fun j => induced dec ((dec c (M 0 r)).eval (r 0)) (fun i r' => M i.succ (Fin.cons (r 0) r'))
        j (Fin.tail r)) i

omit [CommRing F] [DecidableEq F] in
theorem causal_zero {α : Type _} {n : ℕ} {M : Fin (n + 1) → (Fin (n + 1) → F) → α}
    (hM : Causal M)
    (r r' : Fin (n + 1) → F) : M 0 r = M 0 r' :=
  hM 0 r r' fun j hj => absurd hj (Fin.not_lt_zero j)

omit [CommRing F] [DecidableEq F] in
theorem causal_shift {α : Type _} {n : ℕ} {M : Fin (n + 1) → (Fin (n + 1) → F) → α}
    (hM : Causal M)
    (a : F) : Causal fun (i : Fin n) r' => M i.succ (Fin.cons a r') := fun i r r' h =>
  hM _ _ _ fun j hj =>
    Fin.cases (fun _ => rfl) (fun k hk => by simp [h k (Fin.succ_lt_succ_iff.mp hk)]) j hj

omit [DecidableEq F] in
theorem induced_zero (dec : F → Msg → Polynomial F) {n : ℕ} (c : F)
    (M : Fin (n + 1) → (Fin (n + 1) → F) → Msg) (r : Fin (n + 1) → F) :
    induced dec c M 0 r = dec c (M 0 r) := rfl

omit [DecidableEq F] in
theorem induced_succ (dec : F → Msg → Polynomial F) {n : ℕ} (c : F)
    {M : Fin (n + 1) → (Fin (n + 1) → F) → Msg} (hM : Causal M) (r : Fin (n + 1) → F) :
    (fun i r' => induced dec c M i.succ (Fin.cons (r 0) r')) =
      induced dec ((dec c (M 0 r)).eval (r 0)) (fun i r' => M i.succ (Fin.cons (r 0) r')) := by
  funext i r'
  simp only [induced, Fin.cases_succ, Fin.cons_zero, Fin.tail_cons,
    causal_zero hM (Fin.cons (r 0) r') r]

omit [DecidableEq F] in
/-- A causal message strategy decodes to a causal prover. -/
theorem induced_causal (dec : F → Msg → Polynomial F) :
    ∀ {n : ℕ} (c : F) (M : Fin n → (Fin n → F) → Msg), Causal M →
      Causal (induced dec c M)
  | 0, _, _, _ => fun i => i.elim0
  | n + 1, c, M, hM => fun i r r' h => by
    refine Fin.cases (by simp [induced, causal_zero hM r r']) (fun j h => ?_) i h
    have h0 : r 0 = r' 0 := h 0 (Fin.succ_pos j)
    simp only [induced, Fin.cases_succ, causal_zero hM r r', h0]
    refine induced_causal dec _ _ (causal_shift hM _) j _ _ fun k hk => ?_
    simpa [Fin.tail] using h k.succ (Fin.succ_lt_succ_iff.mpr hk)

omit [DecidableEq F] in
/-- The verifier of Section 4.1 accepts the decoded polynomials exactly when g(r) is the replayed
claim. -/
theorem accepts_induced_iff (dec : F → Msg → Polynomial F) {d : ℕ}
    (hdeg : ∀ c m, (dec c m).natDegree ≤ d)
    (hsum : ∀ c m, (dec c m).eval 0 + (dec c m).eval 1 = c) :
    ∀ {n : ℕ} (g : MvPolynomial (Fin n) F) (c : F) (M : Fin n → (Fin n → F) → Msg),
      Causal M →
      ∀ r, Accepts d g c (induced dec c M) r ↔
        eval r g = finalClaim dec c (List.ofFn fun i => M i r) (List.ofFn r)
  | 0, g, c, M, _, r => by simp [Accepts, finalClaim]
  | n + 1, g, c, M, hM, r => by
    simp only [Accepts, induced_zero, hdeg, hsum, true_and, List.ofFn_succ, finalClaim]
    rw [induced_succ dec c hM r, accepts_induced_iff dec hdeg hsum _ _ _ (causal_shift hM _),
      eval_fixFirst, Fin.cons_self_tail]
    rfl

open scoped Classical in
/-- Against a false claim, at most n d |F|^(n-1) challenge vectors replay to g(r), for every causal
message strategy. -/
theorem soundness_decoded [IsDomain F] [Fintype F] (dec : F → Msg → Polynomial F) {d : ℕ}
    (hdeg : ∀ c m, (dec c m).natDegree ≤ d)
    (hsum : ∀ c m, (dec c m).eval 0 + (dec c m).eval 1 = c)
    {n : ℕ} (g : MvPolynomial (Fin n) F) (hg : IndividualDegreeLE g d) (H : F)
    (hH : H ≠ cubeSum g)
    (M : Fin n → (Fin n → F) → Msg) (hM : Causal M) :
    #{r | eval r g = finalClaim dec H (List.ofFn fun i => M i r) (List.ofFn r)} * Fintype.card F ≤
      n * d * Fintype.card F ^ n := by
  have := soundness g hg H hH _ (induced_causal dec H M hM)
  simpa only [accepts_induced_iff dec hdeg hsum g H M hM] using this

/-- When every polynomial of degree at most d with g_i(0) + g_i(1) = c has a message, the honest
messages replay to g(r). -/
theorem completeness_decoded (dec : F → Msg → Polynomial F) (enc : Polynomial F → Msg)
    {d : ℕ}
    (henc : ∀ c p, p.natDegree ≤ d → p.eval 0 + p.eval 1 = c → dec c (enc p) = p) :
    ∀ {n : ℕ} (g : MvPolynomial (Fin n) F), IndividualDegreeLE g d → ∀ r,
      eval r g = finalClaim dec (cubeSum g) (List.ofFn fun i => enc (honestProver g i r))
        (List.ofFn r)
  | 0, g, _, r => by
    simp [finalClaim, cubeSum, cube, Subsingleton.elim r (fun i => i.elim0)]
    rfl
  | n + 1, g, hg, r => by
    simp only [List.ofFn_succ, finalClaim, honestProver, Fin.cases_zero, Fin.cases_succ]
    rw [henc _ _ (natDegree_honestMessage_le hg) (honestMessage_sum g), eval_honestMessage,
      ← Fin.cons_self_tail r, ← eval_fixFirst]
    simpa using
      completeness_decoded dec enc henc _ (individualDegreeLE_fixFirst hg (r 0)) (Fin.tail r)

end Decoded

section Quadratic

open Polynomial

variable {F : Type _} [Field F]

/-- The quadratic with values e0, e1 at 0, 1 and coefficient e_inf on X^2. -/
noncomputable def quad (e0 e1 e_inf : F) : F[X] :=
  C e0 * (1 - X) + C e1 * X + C e_inf * (X * (X - 1))

theorem natDegree_quad (e0 e1 e_inf : F) : (quad e0 e1 e_inf).natDegree ≤ 2 := by
  unfold quad; compute_degree

theorem quad_eq (e0 e1 e_inf : F) :
    quad e0 e1 e_inf = C e0 + C (e1 - e0 - e_inf) * X + C e_inf * X ^ 2 := by
  simp only [quad, map_sub]; ring

theorem eval_zero_quad (e0 e1 e_inf : F) : (quad e0 e1 e_inf).eval 0 = e0 := by simp [quad]

theorem eval_one_quad (e0 e1 e_inf : F) : (quad e0 e1 e_inf).eval 1 = e1 := by simp [quad]

theorem coeff_two_quad (e0 e1 e_inf : F) : (quad e0 e1 e_inf).coeff 2 = e_inf := by
  simp [quad_eq]

/-- A polynomial of degree at most 2 is the quadratic through its values at 0, 1 and its X^2
coefficient. -/
theorem eq_quad {p : F[X]} (hp : p.natDegree ≤ 2) :
    p = quad (p.eval 0) (p.eval 1) (p.coeff 2) := by
  have h1 : p.eval 1 = p.coeff 0 + p.coeff 1 + p.coeff 2 := by
    simp [eval_eq_sum_range' (show p.natDegree < 3 by omega), Finset.sum_range_succ]
  rw [quad_eq, h1, ← coeff_zero_eq_eval_zero]
  ext (_ | _ | _ | n)
  · simp
  · simp [coeff_C]; ring
  · simp
  · simp [coeff_eq_zero_of_natDegree_lt (show p.natDegree < n + 3 by omega)]

/-- The X^2 coefficient of a product of two polynomials of degree at most 1 is the product of their
slopes. -/
theorem coeff_two_mul_of_linear {p q : F[X]} (hp : p.natDegree ≤ 1) (hq : q.natDegree ≤ 1) :
    (p * q).coeff 2 = (p.eval 1 - p.eval 0) * (q.eval 1 - q.eval 0) := by
  rw [eq_X_add_C_of_natDegree_le_one hp, eq_X_add_C_of_natDegree_le_one hq,
    show (C (p.coeff 1) * X + C (p.coeff 0)) * (C (q.coeff 1) * X + C (q.coeff 0)) =
      C (p.coeff 1 * q.coeff 1) * X ^ 2 + (C (p.coeff 1 * q.coeff 0 + p.coeff 0 * q.coeff 1) * X +
        C (p.coeff 0 * q.coeff 0)) by simp only [map_mul, map_add]; ring]
  simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  simp

/-! ## The evaluation basis -/

/-- The polynomial a message [h(0), h(inf)] stands for under the claim c. -/
noncomputable def decEval (c : F) (m : F × F) : F[X] := quad m.1 (c - m.1) m.2

/-- The message of a quadratic: its value at 0 and its X^2 coefficient. -/
noncomputable def encEval (p : F[X]) : F × F := (p.eval 0, p.coeff 2)

theorem natDegree_decEval (c : F) (m : F × F) : (decEval c m).natDegree ≤ 2 :=
  natDegree_quad _ _ _

theorem decEval_sum (c : F) (m : F × F) : (decEval c m).eval 0 + (decEval c m).eval 1 = c := by
  simp [decEval, eval_zero_quad, eval_one_quad]

theorem decEval_encEval {c : F} {p : F[X]} (hp : p.natDegree ≤ 2) (hc : p.eval 0 + p.eval 1 = c) :
    decEval c (encEval p) = p := by
  rw [eq_quad hp]
  simp [decEval, encEval, eval_zero_quad, coeff_two_quad, ← hc]

end Quadratic

end Sumcheck.Counting
