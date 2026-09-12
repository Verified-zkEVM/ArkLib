/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.GCDSplit

/-!
# The generic-field universal-agreement scan

This is the first loop of `FirstOrderNormCandidates`: reduce each residual, compute its monic
common factor with each live modulus, and record universal positions only on the common-factor
child. The transcript distinguishes universal, coprime, and proper-split decisions.

The coefficient field is generic. Instantiation at a stored function field and descent to
polynomial components are later obligations; these theorems do not assert coverage of every
specialized projection fiber. The chart-dependent bound on the number of universal positions
is also separate.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderNormProducer.UniversalAgreements

open CompPoly CPolynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- A current polynomial component and the received positions universal on that component. -/
structure Block (F : Type*) [Zero F] [BEq F] where
  modulus : CPolynomial F
  universal : List ℕ

/-- The three branches of the paper's generic component split. -/
inductive Decision where
  | universal
  | coprime
  | split
  deriving DecidableEq, BEq, Repr

/-- A split records its decision and its one or two resulting components. -/
structure StepOutput (F : Type*) [Zero F] [BEq F] where
  decision : Decision
  blocks : List (Block F)

/-- Execute the reduced-residual gcd and the paper's three-way component decision. -/
def step (i : ℕ) (e : CPolynomial F) (b : Block F) : StepOutput F :=
  let residual := e.modByMonic b.modulus
  let d := gcdFactor b.modulus residual
  if d == b.modulus then
    ⟨.universal, [⟨b.modulus, i :: b.universal⟩]⟩
  else if d == 1 then
    ⟨.coprime, [b]⟩
  else
    ⟨.split, [⟨d, i :: b.universal⟩,
      ⟨gcdComplement b.modulus residual, b.universal⟩]⟩

/-- One row of the actual branch transcript, preserving input component order. -/
structure Stage where
  position : ℕ
  decisions : List Decision

/-- The final components and ordered decisions for every processed received position. -/
structure Output (F : Type*) [Zero F] [BEq F] where
  blocks : List (Block F)
  transcript : List Stage

/-- Execute the remaining received positions, starting from a supplied live family. -/
def scanFrom (i : ℕ) (residuals : List (CPolynomial F)) (blocks : List (Block F)) : Output F :=
  match residuals with
  | [] => ⟨blocks, []⟩
  | e :: es =>
    let steps := blocks.map (step i e)
    let out := scanFrom (i + 1) es (steps.flatMap StepOutput.blocks)
    ⟨out.blocks, ⟨i, steps.map StepOutput.decision⟩ :: out.transcript⟩

/-- Start the universal-agreement loop with the original component and no recorded positions. -/
def run (h : CPolynomial F) (residuals : List (CPolynomial F)) : Output F :=
  scanFrom 0 residuals [⟨h, []⟩]

/-- Reduction changes neither common factor nor complement on the certified monic domain. -/
theorem step_eq (i : ℕ) (e : CPolynomial F) (b : Block F) (hb : b.modulus.monic) :
    step i e b =
      if gcdFactor b.modulus e == b.modulus then
        ⟨.universal, [⟨b.modulus, i :: b.universal⟩]⟩
      else if gcdFactor b.modulus e == 1 then
        ⟨.coprime, [b]⟩
      else
        ⟨.split, [⟨gcdFactor b.modulus e, i :: b.universal⟩,
          ⟨gcdComplement b.modulus e, b.universal⟩]⟩ := by
  simp only [step, gcdFactor_modByMonic _ _ hb, gcdComplement_modByMonic _ _ hb]

/-- A step preserves the exact component product, including its scalar normalization. -/
theorem step_product (i : ℕ) (e : CPolynomial F) (b : Block F) (hb : b.modulus.monic) :
    ((step i e b).blocks.map Block.modulus).prod = b.modulus := by
  rw [step_eq _ _ _ hb]
  split
  · simp
  · split
    · simp
    · simpa using gcdFactor_mul_gcdComplement
        ((toPoly_eq_zero_iff b.modulus).not.mp ((monic_toPoly_iff _).mp hb).ne_zero)

/-- Every resulting component is monic. -/
theorem step_monic (i : ℕ) (e : CPolynomial F) (b : Block F) (hb : b.modulus.monic) :
    ∀ c ∈ (step i e b).blocks, c.modulus.monic := by
  rw [step_eq _ _ _ hb]
  split
  · simpa using hb
  · split
    · simpa using hb
    · simpa using And.intro
        (gcdFactor_monic
          ((toPoly_eq_zero_iff b.modulus).not.mp ((monic_toPoly_iff _).mp hb).ne_zero))
        (gcdComplement_monic hb)

/-- Every resulting component is a polynomial divisor of its parent. -/
theorem step_dvd (i : ℕ) (e : CPolynomial F) (b : Block F) (hb : b.modulus.monic) :
    ∀ c ∈ (step i e b).blocks, c.modulus.toPoly ∣ b.modulus.toPoly := by
  rw [step_eq _ _ _ hb]
  split
  · simp
  · split
    · simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      intro c hc
      rcases hc with rfl | rfl
      · exact gcdFactor_dvd_left _ _
      · have hprod := congrArg CPolynomial.toPoly (gcdFactor_mul_gcdComplement
          (h := b.modulus) (e := e)
          ((toPoly_eq_zero_iff b.modulus).not.mp ((monic_toPoly_iff _).mp hb).ne_zero))
        rw [toPoly_mul] at hprod
        exact ⟨(gcdFactor b.modulus e).toPoly, by rw [← hprod]; ring⟩

/-- Squarefree input components remain squarefree through the executed step. -/
theorem step_squarefree (i : ℕ) (e : CPolynomial F) (b : Block F) (hb : b.modulus.monic)
    (hs : Squarefree b.modulus.toPoly) :
    ∀ c ∈ (step i e b).blocks, Squarefree c.modulus.toPoly :=
  fun c hc => hs.squarefree_of_dvd (step_dvd i e b hb c hc)

/-- The newly processed position is either universally zero or coprime to the block modulus. -/
def Classified (b : Block F) (i : ℕ) (e : CPolynomial F) : Prop :=
  (i ∈ b.universal → b.modulus.toPoly ∣ e.toPoly) ∧
    (i ∉ b.universal → IsCoprime b.modulus.toPoly e.toPoly)

/-- Under squarefreeness a fresh position receives the exact zero/unit classification. -/
theorem step_classified (i : ℕ) (e : CPolynomial F) (b : Block F)
    (hb : b.modulus.monic) (hs : Squarefree b.modulus.toPoly) (hi : i ∉ b.universal) :
    ∀ c ∈ (step i e b).blocks, Classified c i e := by
  have hn := (toPoly_eq_zero_iff b.modulus).not.mp ((monic_toPoly_iff _).mp hb).ne_zero
  rw [step_eq _ _ _ hb]
  split
  · rename_i hd
    have hd' : gcdFactor b.modulus e = b.modulus := by simpa using hd
    have hv := gcdFactor_dvd_right b.modulus e
    rw [hd'] at hv
    simpa [Classified] using hv
  · split
    · rename_i hd
      have hd' : gcdFactor b.modulus e = 1 := by simpa using hd
      have heq := gcdFactor_mul_gcdComplement (h := b.modulus) (e := e) hn
      rw [hd', one_mul] at heq
      have hc := gcdComplement_isCoprime_right hn hs (e := e)
      rw [heq] at hc
      simpa [Classified, hi] using hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      intro c hc
      rcases hc with rfl | rfl
      · simpa [Classified] using gcdFactor_dvd_right b.modulus e
      · simpa [Classified, hi] using gcdComplement_isCoprime_right hn hs (e := e)

/-- Other position labels are inherited unchanged by both children. -/
theorem step_mem_universal_iff (i j : ℕ) (e : CPolynomial F) (b : Block F)
    (hb : b.modulus.monic) (hji : j ≠ i) :
    ∀ c ∈ (step i e b).blocks, (j ∈ c.universal ↔ j ∈ b.universal) := by
  rw [step_eq _ _ _ hb]
  split
  · simp [hji]
  · split <;> simp [hji]

/-- Divisibility of a child and inherited labels preserve every previous classification. -/
theorem step_preserves_classified (i j : ℕ) (e q : CPolynomial F) (b : Block F)
    (hb : b.modulus.monic) (hji : j ≠ i) (hq : Classified b j q) :
    ∀ c ∈ (step i e b).blocks, Classified c j q := by
  intro c hc
  have hm := step_mem_universal_iff i j e b hb hji c hc
  have hd := step_dvd i e b hb c hc
  exact ⟨fun hj => hd.trans (hq.1 (hm.mp hj)),
    fun hj => (hq.2 (fun hjb => hj (hm.mpr hjb))).of_isCoprime_of_dvd_left hd⟩

/-- The family after one received position. This is the flattening used by `scanFrom`. -/
def advance (i : ℕ) (e : CPolynomial F) (bs : List (Block F)) : List (Block F) :=
  (bs.map (step i e)).flatMap StepOutput.blocks

@[simp] theorem mem_advance (i : ℕ) (e : CPolynomial F) (bs : List (Block F)) (c : Block F) :
    c ∈ advance i e bs ↔ ∃ b ∈ bs, c ∈ (step i e b).blocks := by
  simp [advance]

@[simp] theorem scanFrom_cons_blocks (i : ℕ) (e : CPolynomial F)
    (es : List (CPolynomial F)) (bs : List (Block F)) :
    (scanFrom i (e :: es) bs).blocks = (scanFrom (i + 1) es (advance i e bs)).blocks := rfl

/-- One full received position preserves monicity of every live component. -/
theorem advance_monic (i : ℕ) (e : CPolynomial F) (bs : List (Block F))
    (hb : ∀ b ∈ bs, b.modulus.monic) :
    ∀ c ∈ advance i e bs, c.modulus.monic := by
  intro c hc
  obtain ⟨b, hbm, hbc⟩ := (mem_advance _ _ _ _).mp hc
  exact step_monic i e b (hb b hbm) c hbc

/-- One full received position preserves the exact product of component moduli. -/
theorem advance_product (i : ℕ) (e : CPolynomial F) (bs : List (Block F))
    (hb : ∀ b ∈ bs, b.modulus.monic) :
    ((advance i e bs).map Block.modulus).prod = (bs.map Block.modulus).prod := by
  induction bs with
  | nil => simp [advance]
  | cons b bs ih =>
    simp only [advance, List.map_cons, List.flatMap_cons, List.map_append, List.prod_append,
      List.prod_cons]
    rw [step_product i e b (hb b (by simp))]
    exact congrArg (b.modulus * ·) (ih (fun c hc => hb c (by simp [hc])))

/-- A reusable invariant follows the executed descendants through every remaining position. -/
theorem scanFrom_all (P : Block F → Prop)
    (hstep : ∀ i e b, b.modulus.monic → P b → ∀ c ∈ (step i e b).blocks, P c)
    (i : ℕ) (es : List (CPolynomial F)) (bs : List (Block F))
    (hb : ∀ b ∈ bs, b.modulus.monic) (hp : ∀ b ∈ bs, P b) :
    ∀ c ∈ (scanFrom i es bs).blocks, P c := by
  induction es generalizing i bs with
  | nil => exact hp
  | cons e es ih =>
    rw [scanFrom_cons_blocks]
    apply ih (i + 1) (advance i e bs) (advance_monic i e bs hb)
    intro c hc
    obtain ⟨b, hbm, hbc⟩ := (mem_advance _ _ _ _).mp hc
    exact hstep i e b (hb b hbm) (hp b hbm) c hbc

/-- The complete scan preserves the product of the supplied live moduli. -/
theorem scanFrom_product (i : ℕ) (es : List (CPolynomial F)) (bs : List (Block F))
    (hb : ∀ b ∈ bs, b.modulus.monic) :
    ((scanFrom i es bs).blocks.map Block.modulus).prod = (bs.map Block.modulus).prod := by
  induction es generalizing i bs with
  | nil => rfl
  | cons e es ih =>
    rw [scanFrom_cons_blocks, ih _ _ (advance_monic i e bs hb), advance_product i e bs hb]

/-- The actual output reconstructs the original monic input polynomial. -/
theorem run_product (h : CPolynomial F) (es : List (CPolynomial F)) (hh : h.monic) :
    ((run h es).blocks.map Block.modulus).prod = h := by
  simpa [run] using scanFrom_product 0 es [⟨h, []⟩] (by simpa using hh)

/-- The actual output consists of monic components. -/
theorem run_monic (h : CPolynomial F) (es : List (CPolynomial F)) (hh : h.monic) :
    ∀ b ∈ (run h es).blocks, b.modulus.monic :=
  scanFrom_all (fun b => b.modulus.monic) (fun i e b hb _ => step_monic i e b hb)
    0 es [⟨h, []⟩] (by simpa using hh) (by simpa using hh)

/-- The actual output consists of squarefree components on the certified squarefree domain. -/
theorem run_squarefree (h : CPolynomial F) (es : List (CPolynomial F)) (hh : h.monic)
    (hs : Squarefree h.toPoly) :
    ∀ b ∈ (run h es).blocks, Squarefree b.modulus.toPoly :=
  scanFrom_all (fun b => Squarefree b.modulus.toPoly)
    (fun i e b hb hs => step_squarefree i e b hb hs)
    0 es [⟨h, []⟩] (by simpa using hh) (by simpa using hs)

/-- Recorded labels belong to positions already processed. -/
def Before (b : Block F) (i : ℕ) : Prop := ∀ j ∈ b.universal, j < i

/-- A step can add only the currently tested label. -/
theorem step_labels (i : ℕ) (e : CPolynomial F) (b : Block F) :
    ∀ c ∈ (step i e b).blocks, ∀ j ∈ c.universal, j = i ∨ j ∈ b.universal := by
  simp only [step]
  split
  · simp
  · split <;> simp <;> aesop

/-- Processing the next position keeps all recorded labels strictly below the new cursor. -/
theorem step_before (i : ℕ) (e : CPolynomial F) (b : Block F) (hb : Before b i) :
    ∀ c ∈ (step i e b).blocks, Before c (i + 1) := by
  intro c hc j hj
  rcases step_labels i e b c hc j hj with hji | hjb
  · omega
  · exact Nat.lt_succ_of_lt (hb j hjb)

/-- Squarefreeness of the live family is preserved by one whole received position. -/
theorem advance_squarefree (i : ℕ) (e : CPolynomial F) (bs : List (Block F))
    (hb : ∀ b ∈ bs, b.modulus.monic) (hs : ∀ b ∈ bs, Squarefree b.modulus.toPoly) :
    ∀ c ∈ advance i e bs, Squarefree c.modulus.toPoly := by
  intro c hc
  obtain ⟨b, hbm, hbc⟩ := (mem_advance _ _ _ _).mp hc
  exact step_squarefree i e b (hb b hbm) (hs b hbm) c hbc

/-- Every live label remains behind the scan cursor. -/
theorem advance_before (i : ℕ) (e : CPolynomial F) (bs : List (Block F))
    (hb : ∀ b ∈ bs, Before b i) : ∀ c ∈ advance i e bs, Before c (i + 1) := by
  intro c hc
  obtain ⟨b, hbm, hbc⟩ := (mem_advance _ _ _ _).mp hc
  exact step_before i e b (hb b hbm) c hbc

/-- Later component refinements preserve the zero/unit status of an earlier received position. -/
theorem scanFrom_preserves_classified (i j : ℕ) (es : List (CPolynomial F))
    (bs : List (Block F)) (q : CPolynomial F) (hji : j < i)
    (hb : ∀ b ∈ bs, b.modulus.monic) (hq : ∀ b ∈ bs, Classified b j q) :
    ∀ c ∈ (scanFrom i es bs).blocks, Classified c j q := by
  induction es generalizing i bs with
  | nil => exact hq
  | cons e es ih =>
    rw [scanFrom_cons_blocks]
    apply ih (i + 1) (advance i e bs) (Nat.lt_succ_of_lt hji) (advance_monic i e bs hb)
    intro c hc
    obtain ⟨b, hbm, hbc⟩ := (mem_advance _ _ _ _).mp hc
    exact step_preserves_classified i j e q b (hb b hbm) (Nat.ne_of_lt hji)
      (hq b hbm) c hbc

/-- Every supplied residual receives its zero/unit classification on every final component.
The hypotheses are the monic squarefree generic-field domain, not a supplied component partition. -/
theorem scanFrom_classified (i : ℕ) (es : List (CPolynomial F)) (bs : List (Block F))
    (hb : ∀ b ∈ bs, b.modulus.monic) (hs : ∀ b ∈ bs, Squarefree b.modulus.toPoly)
    (hi : ∀ b ∈ bs, Before b i) :
    ∀ n e, es[n]? = some e → ∀ c ∈ (scanFrom i es bs).blocks, Classified c (i + n) e := by
  induction es generalizing i bs with
  | nil => simp
  | cons e es ih =>
    intro n q hq
    rw [scanFrom_cons_blocks]
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hq
      subst q
      simp only [Nat.add_zero]
      apply scanFrom_preserves_classified (i + 1) i es (advance i e bs) e
        (Nat.lt_succ_self i) (advance_monic i e bs hb)
      intro c hc
      obtain ⟨b, hbm, hbc⟩ := (mem_advance _ _ _ _).mp hc
      exact step_classified i e b (hb b hbm) (hs b hbm)
        (fun hm => Nat.lt_irrefl i (hi b hbm i hm)) c hbc
    | succ n =>
      have htail := ih (i + 1) (advance i e bs) (advance_monic i e bs hb)
        (advance_squarefree i e bs hb hs) (advance_before i e bs hi) n q hq
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/-- All processed agreements are either identically zero or coprime on each returned component. -/
theorem run_classified (h : CPolynomial F) (es : List (CPolynomial F)) (hh : h.monic)
    (hs : Squarefree h.toPoly) :
    ∀ n e, es[n]? = some e → ∀ b ∈ (run h es).blocks, Classified b n e := by
  simpa [run] using scanFrom_classified 0 es [⟨h, []⟩]
    (by simpa using hh) (by simpa using hs) (by simp [Before])

private theorem eval₂_prod_moduli {K : Type*} [Field K] (φ : F →+* K) (x : K)
    (bs : List (Block F)) :
    ((bs.map Block.modulus).prod).toPoly.eval₂ φ x = 0 ↔
      ∃ b ∈ bs, b.modulus.toPoly.eval₂ φ x = 0 := by
  induction bs with
  | nil => simp [toPoly_one]
  | cons b bs ih =>
    simp [toPoly_mul, Polynomial.eval₂_mul, mul_eq_zero, ih]


/-- Exact root coverage in every extension of the generic coefficient field. Polynomial
component descent is still needed before interpreting this as coverage of projection fibers. -/
theorem run_root_coverage {K : Type*} [Field K] (φ : F →+* K) (x : K)
    (h : CPolynomial F) (es : List (CPolynomial F)) (hh : h.monic) :
    h.toPoly.eval₂ φ x = 0 ↔ ∃ b ∈ (run h es).blocks, b.modulus.toPoly.eval₂ φ x = 0 := by
  conv_lhs => rw [← run_product h es hh]
  exact eval₂_prod_moduli φ x _

/-- The transcript has one row for every residual, even if the live family is empty. -/
theorem scanFrom_transcript_length (i : ℕ) (es : List (CPolynomial F)) (bs : List (Block F)) :
    (scanFrom i es bs).transcript.length = es.length := by
  induction es generalizing i bs with
  | nil => rfl
  | cons e es ih => simp [scanFrom, ih]

/-- A fresh label never introduces duplicate universal positions. -/
theorem step_nodup (i : ℕ) (e : CPolynomial F) (b : Block F) (hb : b.modulus.monic)
    (hi : i ∉ b.universal) (hn : b.universal.Nodup) :
    ∀ c ∈ (step i e b).blocks, c.universal.Nodup := by
  rw [step_eq _ _ _ hb]
  split
  · simp [hi, hn]
  · split <;> simp [hi, hn]

/-- Every output label is a distinct processed position; this does not assert the separate
chart-geometric bound `|U| ≤ k-1`. -/
theorem scanFrom_labels (i : ℕ) (es : List (CPolynomial F)) (bs : List (Block F))
    (hb : ∀ b ∈ bs, b.modulus.monic) (hi : ∀ b ∈ bs, Before b i)
    (hn : ∀ b ∈ bs, b.universal.Nodup) :
    ∀ c ∈ (scanFrom i es bs).blocks,
      Before c (i + es.length) ∧ c.universal.Nodup := by
  induction es generalizing i bs with
  | nil => exact fun c hc => ⟨hi c hc, hn c hc⟩
  | cons e es ih =>
    rw [scanFrom_cons_blocks]
    have hnext : ∀ c ∈ advance i e bs, c.universal.Nodup := by
      intro c hc
      obtain ⟨b, hbm, hbc⟩ := (mem_advance _ _ _ _).mp hc
      exact step_nodup i e b (hb b hbm)
        (fun hm => Nat.lt_irrefl i (hi b hbm i hm)) (hn b hbm) c hbc
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (i + 1) (advance i e bs) (advance_monic i e bs hb) (advance_before i e bs hi) hnext

/-- Output universal lists really represent subsets of the received positions. -/
theorem run_labels (h : CPolynomial F) (es : List (CPolynomial F)) (hh : h.monic) :
    ∀ b ∈ (run h es).blocks, Before b es.length ∧ b.universal.Nodup := by
  simpa [run] using scanFrom_labels 0 es [⟨h, []⟩] (by simpa using hh)
    (by simp [Before]) (by simp)

end ReedSolomon.ListDecoding.FirstOrderNormProducer.UniversalAgreements
