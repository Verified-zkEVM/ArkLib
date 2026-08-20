/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.PermTraceFacts

/-!
# Stopped-prefix causality for eager permutation sampling

This module turns the four-query support of a transposition of a sampled permutation into the
stopped base-prefix fact required by the no-replacement proof of the `E_p` and `E_{p^{-1}}`
terms in Lemma 5.8.  It deliberately proves equality only before the charged representative;
subsequent adaptive queries may legitimately differ.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS

namespace BadEventDS

open DuplexSpongeFS.DSTraceStorage

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]

variable {StmtOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [codec : CodecCore pSpec U] {δ : ℕ} [DecidableEq StmtIn] [DecidableEq U]
  [VCVCompatible U] [SampleableType U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

private lemma takeWhile_eq_take_of_first_false {α : Type} {p : α → Bool}
    {l : List α} {k : ℕ} {e : α}
    (hget : l[k]? = some e) (hfalse : p e = false)
    (hbefore : ∀ m < k, ∀ e', l[m]? = some e' → p e' = true) :
    l.takeWhile p = l.take k := by
  induction l generalizing k with
  | nil =>
      cases k <;> simp at hget
  | cons a rest ih =>
      cases k with
      | zero =>
          change some a = some e at hget
          injection hget with ha
          subst a
          simp [List.takeWhile, hfalse]
      | succ k =>
          have ha : p a = true := by
            exact hbefore 0 (by omega) a rfl
          have hgetRest : rest[k]? = some e := hget
          have hbeforeRest : ∀ m < k, ∀ e', rest[m]? = some e' → p e' = true := by
            intro m hm e' hget'
            exact hbefore (m + 1) (by omega) e' hget'
          have hih := ih hgetRest hbeforeRest
          simp [List.takeWhile, ha, hih]

private lemma take_length_takeWhile {α : Type} {p : α → Bool} (l : List α) :
    l.take (l.takeWhile p).length = l.takeWhile p := by
  induction l with
  | nil =>
      rfl
  | cons a rest ih =>
      by_cases ha : p a = true
      · simp [List.takeWhile, ha, ih]
      · have haFalse : p a = false := by
          cases hp : p a
          · rfl
          · exact False.elim (ha hp)
        simp [List.takeWhile, haFalse]

private lemma getElem?_true_of_lt_takeWhile {α : Type} {p : α → Bool}
    {l : List α} {m : ℕ} {e : α}
    (hm : m < (l.takeWhile p).length) (hget : l[m]? = some e) :
    p e = true := by
  induction l generalizing m with
  | nil =>
      cases hm
  | cons a rest ih =>
      cases m with
      | zero =>
          by_cases ha : p a = true
          · change some a = some e at hget
            injection hget with he
            rw [← he]
            exact ha
          · have haFalse : p a = false := by
              cases hp : p a
              · rfl
              · exact False.elim (ha hp)
            simp [List.takeWhile, haFalse] at hm
      | succ m =>
          by_cases ha : p a = true
          · simp [List.takeWhile, ha] at hm
            exact ih hm hget
          · have haFalse : p a = false := by
              cases hp : p a
              · rfl
              · exact False.elim (ha hp)
            simp [List.takeWhile, haFalse] at hm

/-- The forward branch of the four-domain swap support. -/
private lemma fwdSwapAffected_forward_of_true
    (p : Equiv.Perm (CanonicalSpongeState U))
    (x y' s : CanonicalSpongeState U)
    (hbad : permFwdSwapAffected (StmtIn := StmtIn) p x y' (.inr (.inl s)) = true) :
    s = x ∨ s = p.symm y' := by
  unfold permFwdSwapAffected at hbad
  exact of_decide_eq_true hbad

/-- The inverse branch of the four-domain swap support. -/
private lemma fwdSwapAffected_backward_of_true
    (p : Equiv.Perm (CanonicalSpongeState U))
    (x y' z : CanonicalSpongeState U)
    (hbad : permFwdSwapAffected (StmtIn := StmtIn) p x y' (.inr (.inr z)) = true) :
    z = p x ∨ z = y' := by
  unfold permFwdSwapAffected at hbad
  exact of_decide_eq_true hbad

private lemma fwdSwapAffected_forward_x_true
    (p : Equiv.Perm (CanonicalSpongeState U))
    (x y' : CanonicalSpongeState U) :
    permFwdSwapAffected (StmtIn := StmtIn) p x y' (.inr (.inl x)) = true := by
  unfold permFwdSwapAffected
  exact decide_eq_true (Or.inl rfl)

private lemma fwdSwapAffected_forward_preimage_true
    (p : Equiv.Perm (CanonicalSpongeState U))
    (x y' : CanonicalSpongeState U) :
    permFwdSwapAffected (StmtIn := StmtIn) p x y' (.inr (.inl (p.symm y'))) = true := by
  unfold permFwdSwapAffected
  exact decide_eq_true (Or.inr rfl)

private lemma fwdSwapAffected_backward_image_true
    (p : Equiv.Perm (CanonicalSpongeState U))
    (x y' : CanonicalSpongeState U) :
    permFwdSwapAffected (StmtIn := StmtIn) p x y' (.inr (.inr (p x))) = true := by
  unfold permFwdSwapAffected
  exact decide_eq_true (Or.inl rfl)

private lemma fwdSwapAffected_backward_fresh_true
    (p : Equiv.Perm (CanonicalSpongeState U))
    (x y' : CanonicalSpongeState U) :
    permFwdSwapAffected (StmtIn := StmtIn) p x y' (.inr (.inr y')) = true := by
  unfold permFwdSwapAffected
  exact decide_eq_true (Or.inr rfl)

private lemma bwdSwapAffected_forward_of_true
    (p : Equiv.Perm (CanonicalSpongeState U))
    (y x' s : CanonicalSpongeState U)
    (hbad : permBwdSwapAffected (StmtIn := StmtIn) p y x' (.inr (.inl s)) = true) :
    s = p.symm y ∨ s = x' := by
  unfold permBwdSwapAffected at hbad
  exact of_decide_eq_true hbad

private lemma bwdSwapAffected_backward_of_true
    (p : Equiv.Perm (CanonicalSpongeState U))
    (y x' z : CanonicalSpongeState U)
    (hbad : permBwdSwapAffected (StmtIn := StmtIn) p y x' (.inr (.inr z)) = true) :
    z = y ∨ z = p x' := by
  unfold permBwdSwapAffected at hbad
  exact of_decide_eq_true hbad

private lemma bwdSwapAffected_forward_preimage_true
    (p : Equiv.Perm (CanonicalSpongeState U))
    (y x' : CanonicalSpongeState U) :
    permBwdSwapAffected (StmtIn := StmtIn) p y x' (.inr (.inl (p.symm y))) = true := by
  unfold permBwdSwapAffected
  exact decide_eq_true (Or.inl rfl)

private lemma bwdSwapAffected_forward_fresh_true
    (p : Equiv.Perm (CanonicalSpongeState U))
    (y x' : CanonicalSpongeState U) :
    permBwdSwapAffected (StmtIn := StmtIn) p y x' (.inr (.inl x')) = true := by
  unfold permBwdSwapAffected
  exact decide_eq_true (Or.inr rfl)

private lemma bwdSwapAffected_backward_y_true
    (p : Equiv.Perm (CanonicalSpongeState U))
    (y x' : CanonicalSpongeState U) :
    permBwdSwapAffected (StmtIn := StmtIn) p y x' (.inr (.inr y)) = true := by
  unfold permBwdSwapAffected
  exact decide_eq_true (Or.inl rfl)

private lemma bwdSwapAffected_backward_image_true
    (p : Equiv.Perm (CanonicalSpongeState U))
    (y x' : CanonicalSpongeState U) :
    permBwdSwapAffected (StmtIn := StmtIn) p y x' (.inr (.inr (p x'))) = true := by
  unfold permBwdSwapAffected
  exact decide_eq_true (Or.inr rfl)

private lemma first_fwdSwap_affected_not_redundant
    (h : StmtIn → Vector U SpongeSize.C)
    (p : Equiv.Perm (CanonicalSpongeState U))
    (x y' : CanonicalSpongeState U)
    (raw : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hcons : ∀ e ∈ raw, e.2 = spongeAnswer (h, p) e.1)
    {k : ℕ} {entry : Sigma (duplexSpongeChallengeOracle StmtIn U)}
    (hget : raw[k]? = some entry)
    (hbad : permFwdSwapAffected (StmtIn := StmtIn) p x y' entry.1 = true)
    (hfirst : ∀ m < k, ∀ e, raw[m]? = some e →
      permFwdSwapAffected (StmtIn := StmtIn) p x y' e.1 ≠ true) :
    ¬ isRedundantEntryOfPrefix (raw.take k) entry := by
  have hmem : entry ∈ raw := by
    rw [List.mem_iff_getElem?]
    exact ⟨k, hget⟩
  have hans := hcons entry hmem
  have hprior : ∀ e, e ∈ raw.take k →
      permFwdSwapAffected (StmtIn := StmtIn) p x y' e.1 ≠ true := by
    intro e he
    rw [List.mem_take_iff_getElem] at he
    obtain ⟨m, hm, hgetm⟩ := he
    have hmk : m < k := lt_of_lt_of_le hm (Nat.min_le_left _ _)
    have hmLen : m < raw.length := lt_of_lt_of_le hm (Nat.min_le_right _ _)
    have hgetm' : raw[m]? = some e := by
      rw [List.getElem?_eq_getElem hmLen]
      exact congrArg some hgetm
    exact hfirst m hmk e hgetm'
  rcases entry with ⟨dom, rng⟩
  cases dom with
  | inl stmt =>
      unfold permFwdSwapAffected at hbad
      cases hbad
  | inr permDom =>
      cases permDom with
      | inl s =>
          have hs := fwdSwapAffected_forward_of_true (StmtIn := StmtIn) p x y' s hbad
          have hrng : rng = p s := by
            change rng = p s at hans
            exact hans
          rw [hrng]
          simp only [isRedundantEntryOfPrefix]
          intro hred
          rcases hred with hsame | hflip
          · exact hprior ⟨.inr (.inl s), p s⟩ hsame hbad
          · apply hprior ⟨.inr (.inr (p s)), s⟩ hflip
            rcases hs with hs | hs
            · subst s
              exact fwdSwapAffected_backward_image_true (StmtIn := StmtIn) p x y'
            · subst s
              rw [Equiv.apply_symm_apply]
              exact fwdSwapAffected_backward_fresh_true (StmtIn := StmtIn) p x y'
      | inr z =>
          have hz := fwdSwapAffected_backward_of_true (StmtIn := StmtIn) p x y' z hbad
          have hrng : rng = p.symm z := by
            change rng = p.symm z at hans
            exact hans
          rw [hrng]
          simp only [isRedundantEntryOfPrefix]
          intro hred
          rcases hred with hsame | hflip
          · exact hprior ⟨.inr (.inr z), p.symm z⟩ hsame hbad
          · apply hprior ⟨.inr (.inl (p.symm z)), z⟩ hflip
            rcases hz with hz | hz
            · subst z
              rw [Equiv.symm_apply_apply]
              exact fwdSwapAffected_forward_x_true (StmtIn := StmtIn) p x y'
            · subst z
              exact fwdSwapAffected_forward_preimage_true (StmtIn := StmtIn) p x y'

private lemma first_bwdSwap_affected_not_redundant
    (h : StmtIn → Vector U SpongeSize.C)
    (p : Equiv.Perm (CanonicalSpongeState U))
    (y x' : CanonicalSpongeState U)
    (raw : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hcons : ∀ e ∈ raw, e.2 = spongeAnswer (h, p) e.1)
    {k : ℕ} {entry : Sigma (duplexSpongeChallengeOracle StmtIn U)}
    (hget : raw[k]? = some entry)
    (hbad : permBwdSwapAffected (StmtIn := StmtIn) p y x' entry.1 = true)
    (hfirst : ∀ m < k, ∀ e, raw[m]? = some e →
      permBwdSwapAffected (StmtIn := StmtIn) p y x' e.1 ≠ true) :
    ¬ isRedundantEntryOfPrefix (raw.take k) entry := by
  have hmem : entry ∈ raw := by
    rw [List.mem_iff_getElem?]
    exact ⟨k, hget⟩
  have hans := hcons entry hmem
  have hprior : ∀ e, e ∈ raw.take k →
      permBwdSwapAffected (StmtIn := StmtIn) p y x' e.1 ≠ true := by
    intro e he
    rw [List.mem_take_iff_getElem] at he
    obtain ⟨m, hm, hgetm⟩ := he
    have hmk : m < k := lt_of_lt_of_le hm (Nat.min_le_left _ _)
    have hmLen : m < raw.length := lt_of_lt_of_le hm (Nat.min_le_right _ _)
    have hgetm' : raw[m]? = some e := by
      rw [List.getElem?_eq_getElem hmLen]
      exact congrArg some hgetm
    exact hfirst m hmk e hgetm'
  rcases entry with ⟨dom, rng⟩
  cases dom with
  | inl stmt =>
      unfold permBwdSwapAffected at hbad
      cases hbad
  | inr permDom =>
      cases permDom with
      | inl s =>
          have hs := bwdSwapAffected_forward_of_true (StmtIn := StmtIn) p y x' s hbad
          have hrng : rng = p s := by
            change rng = p s at hans
            exact hans
          rw [hrng]
          simp only [isRedundantEntryOfPrefix]
          intro hred
          rcases hred with hsame | hflip
          · exact hprior ⟨.inr (.inl s), p s⟩ hsame hbad
          · apply hprior ⟨.inr (.inr (p s)), s⟩ hflip
            rcases hs with hs | hs
            · subst s
              rw [Equiv.apply_symm_apply]
              exact bwdSwapAffected_backward_y_true (StmtIn := StmtIn) p y x'
            · subst s
              exact bwdSwapAffected_backward_image_true (StmtIn := StmtIn) p y x'
      | inr z =>
          have hz := bwdSwapAffected_backward_of_true (StmtIn := StmtIn) p y x' z hbad
          have hrng : rng = p.symm z := by
            change rng = p.symm z at hans
            exact hans
          rw [hrng]
          simp only [isRedundantEntryOfPrefix]
          intro hred
          rcases hred with hsame | hflip
          · exact hprior ⟨.inr (.inr z), p.symm z⟩ hsame hbad
          · apply hprior ⟨.inr (.inl (p.symm z)), z⟩ hflip
            rcases hz with hz | hz
            · subst z
              exact bwdSwapAffected_forward_preimage_true (StmtIn := StmtIn) p y x'
            · subst z
              rw [Equiv.symm_apply_apply]
              exact bwdSwapAffected_forward_fresh_true (StmtIn := StmtIn) p y x'

private lemma first_fwdSwap_forward_x_not_redundant_after_swap
    (h : StmtIn → Vector U SpongeSize.C)
    (p p' : Equiv.Perm (CanonicalSpongeState U))
    (x y' : CanonicalSpongeState U)
    (raw : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hpx : p' x = y')
    (hcons : ∀ e ∈ raw, e.2 = spongeAnswer (h, p') e.1)
    {k : ℕ} {entry : Sigma (duplexSpongeChallengeOracle StmtIn U)}
    (hget : raw[k]? = some entry)
    (hdom : entry.1 = .inr (.inl x))
    (hfirst : ∀ m < k, ∀ e, raw[m]? = some e →
      permFwdSwapAffected (StmtIn := StmtIn) p x y' e.1 ≠ true) :
    ¬ isRedundantEntryOfPrefix (raw.take k) entry := by
  have hmem : entry ∈ raw := by
    rw [List.mem_iff_getElem?]
    exact ⟨k, hget⟩
  rcases entry with ⟨dom, rng⟩
  cases dom with
  | inl stmt =>
      cases hdom
  | inr permDom =>
      cases permDom with
      | inl s =>
          simp only [Sum.inr.injEq, Sum.inl.injEq] at hdom
          subst s
          have hrng := hcons _ hmem
          change rng = p' x at hrng
          rw [hpx] at hrng
          rw [hrng]
          simp only [isRedundantEntryOfPrefix]
          intro hred
          rcases hred with hsame | hflip
          · rw [List.mem_take_iff_getElem] at hsame
            obtain ⟨m, hm, hgetm⟩ := hsame
            have hmk : m < k := lt_of_lt_of_le hm (Nat.min_le_left _ _)
            have hmLen : m < raw.length := lt_of_lt_of_le hm (Nat.min_le_right _ _)
            have hgetm' : raw[m]? = some (⟨.inr (.inl x), y'⟩ :
                Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
              rw [List.getElem?_eq_getElem hmLen]
              exact congrArg some hgetm
            exact (hfirst m hmk _ hgetm')
              (fwdSwapAffected_forward_x_true (StmtIn := StmtIn) p x y')
          · rw [List.mem_take_iff_getElem] at hflip
            obtain ⟨m, hm, hgetm⟩ := hflip
            have hmk : m < k := lt_of_lt_of_le hm (Nat.min_le_left _ _)
            have hmLen : m < raw.length := lt_of_lt_of_le hm (Nat.min_le_right _ _)
            have hgetm' : raw[m]? = some (⟨.inr (.inr y'), x⟩ :
                Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
              rw [List.getElem?_eq_getElem hmLen]
              exact congrArg some hgetm
            exact (hfirst m hmk _ hgetm')
              (fwdSwapAffected_backward_fresh_true (StmtIn := StmtIn) p x y')
      | inr sOut =>
          cases hdom

private lemma first_bwdSwap_backward_y_not_redundant_after_swap
    (h : StmtIn → Vector U SpongeSize.C)
    (p p' : Equiv.Perm (CanonicalSpongeState U))
    (y x' : CanonicalSpongeState U)
    (raw : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hpy : p'.symm y = x')
    (hcons : ∀ e ∈ raw, e.2 = spongeAnswer (h, p') e.1)
    {k : ℕ} {entry : Sigma (duplexSpongeChallengeOracle StmtIn U)}
    (hget : raw[k]? = some entry)
    (hdom : entry.1 = .inr (.inr y))
    (hfirst : ∀ m < k, ∀ e, raw[m]? = some e →
      permBwdSwapAffected (StmtIn := StmtIn) p y x' e.1 ≠ true) :
    ¬ isRedundantEntryOfPrefix (raw.take k) entry := by
  have hmem : entry ∈ raw := by
    rw [List.mem_iff_getElem?]
    exact ⟨k, hget⟩
  rcases entry with ⟨dom, rng⟩
  cases dom with
  | inl stmt =>
      cases hdom
  | inr permDom =>
      cases permDom with
      | inl s =>
          cases hdom
      | inr z =>
          simp only [Sum.inr.injEq, Sum.inr.injEq] at hdom
          subst z
          have hrng := hcons _ hmem
          change rng = p'.symm y at hrng
          rw [hpy] at hrng
          rw [hrng]
          simp only [isRedundantEntryOfPrefix]
          intro hred
          rcases hred with hsame | hflip
          · rw [List.mem_take_iff_getElem] at hsame
            obtain ⟨m, hm, hgetm⟩ := hsame
            have hmk : m < k := lt_of_lt_of_le hm (Nat.min_le_left _ _)
            have hmLen : m < raw.length := lt_of_lt_of_le hm (Nat.min_le_right _ _)
            have hgetm' : raw[m]? = some (⟨.inr (.inr y), x'⟩ :
                Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
              rw [List.getElem?_eq_getElem hmLen]
              exact congrArg some hgetm
            exact (hfirst m hmk _ hgetm')
              (bwdSwapAffected_backward_y_true (StmtIn := StmtIn) p y x')
          · rw [List.mem_take_iff_getElem] at hflip
            obtain ⟨m, hm, hgetm⟩ := hflip
            have hmk : m < k := lt_of_lt_of_le hm (Nat.min_le_left _ _)
            have hmLen : m < raw.length := lt_of_lt_of_le hm (Nat.min_le_right _ _)
            have hgetm' : raw[m]? = some (⟨.inr (.inl x'), y⟩ :
                Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
              rw [List.getElem?_eq_getElem hmLen]
              exact congrArg some hgetm
            exact (hfirst m hmk _ hgetm')
              (bwdSwapAffected_forward_fresh_true (StmtIn := StmtIn) p y x')

/-- If base index `j` is the forward query `x`, then the base prefix before `j` is exactly the
raw deterministic trace before its first query whose answer can change under the local swap
`p ∘ swap (p x) y'`.  The freshness side condition says precisely that the alternate output
`y'` has not been exposed by an earlier normalized representative. -/
lemma spongeDetTrace_permFwd_basePrefix_eq_takeWhile
    [Fintype U]
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (h : StmtIn → Vector U SpongeSize.C)
    (p : Equiv.Perm (CanonicalSpongeState U))
    {j : ℕ} {x y' : CanonicalSpongeState U}
    (hnow : permFwdInputAt (getBaseTrace
        ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver (h, p)).1 ++
         (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver (h, p)).2)) j = some x)
    (hy' : y' ∉ permExposedRangeFinset (getBaseTrace
        ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver (h, p)).1 ++
         (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver (h, p)).2)) j) :
    let bad := permFwdSwapAffected (StmtIn := StmtIn) p x y'
    let good := eagerDetNarrowEntryGood (StmtIn := StmtIn) (U := U) bad
    let raw :=
      (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver (h, p)).1 ++
      (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver (h, p)).2
    (getBaseTrace raw).take j = getBaseTrace (raw.takeWhile good) ∧
      ∃ hstop : (raw.takeWhile good).length < raw.length,
        raw[(raw.takeWhile good).length].1 = .inr (.inl x) := by
  classical
  let fam : (D_𝔖 StmtIn U).Carrier := (h, p)
  let raw : QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
    (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
      (δ := δ) V maliciousProver fam).1 ++
    (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
      (δ := δ) V maliciousProver fam).2
  let bt : QueryLog (duplexSpongeChallengeOracle StmtIn U) := getBaseTrace raw
  let bad := permFwdSwapAffected (StmtIn := StmtIn) p x y'
  let good := eagerDetNarrowEntryGood (StmtIn := StmtIn) (U := U) bad
  change permFwdInputAt bt j = some x at hnow
  change y' ∉ permExposedRangeFinset bt j at hy'
  obtain ⟨sOut, hbtj⟩ := exists_getElem?_permFwd_of_permFwdInputAt hnow
  have hsOut := spongeDetTrace_permFwd_entry_output_eq
    (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
    (U := U) (δ := δ) V maliciousProver fam hbtj
  rw [hsOut] at hbtj
  have hbaseMem : (⟨.inr (.inl x), p x⟩ :
      Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ bt := by
    rw [List.mem_iff_getElem?]
    exact ⟨j, hbtj⟩
  have hrawMem : (⟨.inr (.inl x), p x⟩ :
      Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ raw :=
    (getBaseTrace_sublist (StmtIn := StmtIn) (U := U) raw).subset hbaseMem
  have hbadCurrent : bad (.inr (.inl x)) = true := by
    exact fwdSwapAffected_forward_x_true (StmtIn := StmtIn) p x y'
  have hExists : ∃ k : ℕ, ∃ e, raw[k]? = some e ∧ bad e.1 = true := by
    rw [List.mem_iff_getElem?] at hrawMem
    obtain ⟨k, hget⟩ := hrawMem
    exact ⟨k, ⟨.inr (.inl x), p x⟩, hget, hbadCurrent⟩
  let P : ℕ → Prop := fun k => ∃ e, raw[k]? = some e ∧ bad e.1 = true
  let k := Nat.find hExists
  have hk : P k := Nat.find_spec hExists
  obtain ⟨entry, hkGet, hkBad⟩ := hk
  have hkFirst : ∀ m < k, ∀ e, raw[m]? = some e → bad e.1 ≠ true := by
    intro m hm e hget hbad
    have hPm : P m := ⟨e, hget, hbad⟩
    exact Nat.not_lt_of_ge (Nat.find_min' hExists hPm) hm
  have hcons := spongeDetTrace_append_consistent
    (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
    (U := U) (δ := δ) V maliciousProver fam
  have hnr := first_fwdSwap_affected_not_redundant
    (StmtIn := StmtIn) h p x y' raw hcons hkGet hkBad hkFirst
  obtain ⟨hb, hprefix, hbEntry⟩ :=
    DuplexSpongeFS.basePrefix_of_getElem?_not_redundant (StmtIn := StmtIn) (U := U)
      raw hkGet hnr
  let b := (getBaseTrace (raw.take k)).length
  have hbtb : bt[b]? = some entry := by
    change (getBaseTrace raw)[b]? = some entry
    rw [List.getElem?_eq_getElem hb]
    exact congrArg some hbEntry
  have hnotBlt : ¬ b < j := by
    intro hbj
    rcases entry with ⟨dom, rng⟩
    cases dom with
    | inl stmt =>
        unfold bad permFwdSwapAffected at hkBad
        cases hkBad
    | inr permDom =>
        cases permDom with
        | inl s =>
            have hs := fwdSwapAffected_forward_of_true (StmtIn := StmtIn) p x y' s hkBad
            have hrawEntry : (⟨.inr (.inl s), rng⟩ :
                Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ raw := by
              rw [List.mem_iff_getElem?]
              exact ⟨k, hkGet⟩
            have hrng := hcons _ hrawEntry
            change rng = p s at hrng
            rcases hs with hs | hs
            · subst s
              have hprior : permFwdInputAt bt b = some x := by
                unfold permFwdInputAt
                rw [hbtb]
                rfl
              exact (spongeDetTrace_no_prior_permFwdInput_same_shared
                (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
                (U := U) (δ := δ) V maliciousProver fam hbj hnow) hprior
            · subst s
              apply hy'
              refine (mem_permExposedRangeFinset_iff (StmtIn := StmtIn) (U := U)).mpr
                ⟨b, hbj, ?_⟩
              unfold permRangeStateAt
              rw [hbtb, hrng, Equiv.apply_symm_apply]
              rfl
        | inr z =>
            have hz := fwdSwapAffected_backward_of_true (StmtIn := StmtIn) p x y' z hkBad
            rcases hz with hz | hz
            · subst z
              have hprior : permBwdOutputAt bt b = some (p x) := by
                unfold permBwdOutputAt
                rw [hbtb]
                rfl
              exact (spongeDetTrace_no_prior_permBwdOutput_of_permFwdInput_shared
                (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
                (U := U) (δ := δ) V maliciousProver fam hbj hnow) hprior
            · subst z
              apply hy'
              refine (mem_permExposedRangeFinset_iff (StmtIn := StmtIn) (U := U)).mpr
                ⟨b, hbj, ?_⟩
              unfold permRangeStateAt
              rw [hbtb]
              rfl
  have hnotJlt : ¬ j < b := by
    intro hjb
    have hbtjLen : j < bt.length := by
      rw [List.getElem?_eq_some_iff] at hbtj
      exact hbtj.1
    have hbtjGet : bt[j] = (⟨.inr (.inl x), p x⟩ :
        Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
      have hsome : some bt[j] = some (⟨.inr (.inl x), p x⟩ :
          Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
        rw [← List.getElem?_eq_getElem hbtjLen]
        exact hbtj
      exact Option.some.inj hsome
    have hmemPrefix : (⟨.inr (.inl x), p x⟩ :
        Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ bt.take b := by
      rw [List.mem_take_iff_getElem]
      exact ⟨j, by omega, hbtjGet⟩
    have hmemBasePrefix : (⟨.inr (.inl x), p x⟩ :
        Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ getBaseTrace (raw.take k) := by
      rw [← hprefix]
      exact hmemPrefix
    have hmemRawPrefix : (⟨.inr (.inl x), p x⟩ :
        Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ raw.take k :=
      (getBaseTrace_sublist (StmtIn := StmtIn) (U := U) (raw.take k)).subset hmemBasePrefix
    rw [List.mem_take_iff_getElem] at hmemRawPrefix
    obtain ⟨m, hm, hrawGet⟩ := hmemRawPrefix
    have hmk : m < k := lt_of_lt_of_le hm (Nat.min_le_left _ _)
    have hmLen : m < raw.length := lt_of_lt_of_le hm (Nat.min_le_right _ _)
    have hrawGet' : raw[m]? = some (⟨.inr (.inl x), p x⟩ :
        Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
      rw [List.getElem?_eq_getElem hmLen]
      exact congrArg some hrawGet
    exact (hkFirst m hmk _ hrawGet') hbadCurrent
  have hbEqj : b = j := by omega
  have hfalse : good entry = false := by
    unfold good eagerDetNarrowEntryGood
    rw [hkBad]
    rfl
  have hbefore : ∀ m < k, ∀ e, raw[m]? = some e → good e = true := by
    intro m hm e hget
    unfold good eagerDetNarrowEntryGood
    cases hbad : bad e.1 with
    | false => rfl
    | true => exact False.elim ((hkFirst m hm e hget) hbad)
  have htw : raw.takeWhile good = raw.take k :=
    takeWhile_eq_take_of_first_false hkGet hfalse hbefore
  have hprefixEq : bt.take j = getBaseTrace (raw.takeWhile good) := by
    rw [← hbEqj]
    change bt.take b = getBaseTrace (raw.takeWhile good)
    rw [htw]
    exact hprefix
  have hkLen : k < raw.length := by
    rw [List.getElem?_eq_some_iff] at hkGet
    exact hkGet.1
  have htwLen : (raw.takeWhile good).length = k := by
    rw [htw, List.length_take]
    exact min_eq_left (Nat.le_of_lt hkLen)
  have hentryDom : entry.1 = .inr (.inl x) := by
    rw [hbEqj] at hbtb
    rcases entry with ⟨dom, rng⟩
    cases dom with
    | inl stmt =>
        unfold permFwdInputAt at hnow
        rw [hbtb] at hnow
        simp only [Option.bind_some, reduceCtorEq] at hnow
    | inr permDom =>
        cases permDom with
        | inl s =>
            unfold permFwdInputAt at hnow
            rw [hbtb] at hnow
            simp only [Option.bind_some, Option.some.injEq] at hnow
            subst s
            rfl
        | inr sOut =>
            unfold permFwdInputAt at hnow
            rw [hbtb] at hnow
            simp only [Option.bind_some, reduceCtorEq] at hnow
  refine ⟨hprefixEq, ?_⟩
  have hstop : (raw.takeWhile good).length < raw.length := by
    rw [htwLen]
    exact hkLen
  refine ⟨hstop, ?_⟩
  have hgetStop : raw[(raw.takeWhile good).length]? = some entry := by
    rw [htwLen]
    exact hkGet
  have hentryStop : raw[(raw.takeWhile good).length] = entry := by
    rw [List.getElem?_eq_getElem hstop] at hgetStop
    exact Option.some.inj hgetStop
  rw [hentryStop]
  exact hentryDom

/-- Resampling the output of the charged forward representative to an unexposed full state
does not change its base-trace prefix, its input, or its finite capacity-target set.  This is the
local deferred-decision step used by the eager `E_p` bound; it intentionally makes no assertion
about the trace after the charged representative. -/
lemma spongeDetTrace_permFwd_swap_prefix_read_targets
    [Fintype U]
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (h : StmtIn → Vector U SpongeSize.C)
    (p : Equiv.Perm (CanonicalSpongeState U))
    {j : ℕ} {x y' : CanonicalSpongeState U}
    (hread : permFwdInputAt (getBaseTrace
        ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver (h, p)).1 ++
         (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver (h, p)).2)) j = some x)
    (hy' : y' ∉ permExposedRangeFinset (getBaseTrace
        ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver (h, p)).1 ++
         (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver (h, p)).2)) j) :
    let p' := p.trans (Equiv.swap (p x) y')
    let bt₀ := getBaseTrace
      ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver (h, p)).1 ++
       (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver (h, p)).2)
    let bt₁ := getBaseTrace
      ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver (h, p')).1 ++
       (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver (h, p')).2)
    bt₁.take j = bt₀.take j ∧
      permFwdInputAt bt₁ j = some x ∧
      permFwdCapacityTargetFinset bt₁ j = permFwdCapacityTargetFinset bt₀ j := by
  classical
  let p' : Equiv.Perm (CanonicalSpongeState U) := p.trans (Equiv.swap (p x) y')
  let fam₀ : (D_𝔖 StmtIn U).Carrier := (h, p)
  let fam₁ : (D_𝔖 StmtIn U).Carrier := (h, p')
  let raw₀ : QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
    (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
      (δ := δ) V maliciousProver fam₀).1 ++
    (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
      (δ := δ) V maliciousProver fam₀).2
  let raw₁ : QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
    (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
      (δ := δ) V maliciousProver fam₁).1 ++
    (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
      (δ := δ) V maliciousProver fam₁).2
  let bt₀ := getBaseTrace raw₀
  let bt₁ := getBaseTrace raw₁
  let bad := permFwdSwapAffected (StmtIn := StmtIn) p x y'
  let good := eagerDetNarrowEntryGood (StmtIn := StmtIn) (U := U) bad
  change permFwdInputAt bt₀ j = some x at hread
  change y' ∉ permExposedRangeFinset bt₀ j at hy'
  have hbase : bt₀.take j = getBaseTrace (raw₀.takeWhile good) ∧
      ∃ hstop : (raw₀.takeWhile good).length < raw₀.length,
        raw₀[(raw₀.takeWhile good).length].1 = .inr (.inl x) := by
    dsimp only [bt₀, raw₀, fam₀, good, bad]
    exact spongeDetTrace_permFwd_basePrefix_eq_takeWhile
      (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) (δ := δ)
      V maliciousProver h p hread hy'
  obtain ⟨hprefix₀, hstop₀, hdom₀⟩ := hbase
  have hsync := spongeDetTrace_append_first_bad_domain_fwdSwapAffected_eq
    (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) (δ := δ)
    V maliciousProver h p x y'
  change raw₁.takeWhile good = raw₀.takeWhile good ∧
      ((raw₁.takeWhile good).length < raw₁.length ↔
        (raw₀.takeWhile good).length < raw₀.length) ∧
      (∀ (h₁ : (raw₁.takeWhile good).length < raw₁.length)
          (h₀ : (raw₀.takeWhile good).length < raw₀.length),
        raw₁[(raw₁.takeWhile good).length].1 =
          raw₀[(raw₀.takeWhile good).length].1) at hsync
  have hstop₁ : (raw₁.takeWhile good).length < raw₁.length := hsync.2.1.mpr hstop₀
  have hdom₁ : raw₁[(raw₁.takeWhile good).length].1 = .inr (.inl x) := by
    rw [hsync.2.2 hstop₁ hstop₀]
    exact hdom₀
  have hp'x : p' x = y' := by
    change (Equiv.swap (p x) y') (p x) = y'
    exact Equiv.swap_apply_left _ _
  have hget₁ : raw₁[(raw₁.takeWhile good).length]? =
      some raw₁[(raw₁.takeWhile good).length] := by
    rw [List.getElem?_eq_getElem hstop₁]
  have hcons₁ := spongeDetTrace_append_consistent
    (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
    (U := U) (δ := δ) V maliciousProver fam₁
  have hfirst₁ : ∀ m < (raw₁.takeWhile good).length, ∀ e, raw₁[m]? = some e →
      bad e.1 ≠ true := by
    intro m hm e hget hbad
    have hgood := getElem?_true_of_lt_takeWhile (p := good) hm hget
    unfold good eagerDetNarrowEntryGood at hgood
    rw [hbad] at hgood
    cases hgood
  have hnr₁ := first_fwdSwap_forward_x_not_redundant_after_swap
    (StmtIn := StmtIn) h p p' x y' raw₁ hp'x hcons₁ hget₁ hdom₁ hfirst₁
  obtain ⟨hb₁, hprefix₁, hbentry₁⟩ :=
    DuplexSpongeFS.basePrefix_of_getElem?_not_redundant (StmtIn := StmtIn) (U := U)
      raw₁ hget₁ hnr₁
  let b₁ := (getBaseTrace (raw₁.take (raw₁.takeWhile good).length)).length
  have hprefix₁' : bt₁.take b₁ = getBaseTrace (raw₁.takeWhile good) := by
    change bt₁.take b₁ = getBaseTrace (raw₁.takeWhile good)
    rw [← take_length_takeWhile raw₁]
    exact hprefix₁
  have hbtEq : bt₁.take b₁ = bt₀.take j := by
    rw [hprefix₁', hsync.1, ← hprefix₀]
  have hjlt : j < bt₀.length := by
    obtain ⟨sOut, hbtj⟩ := exists_getElem?_permFwd_of_permFwdInputAt hread
    rw [List.getElem?_eq_some_iff] at hbtj
    exact hbtj.1
  have hb₁le : b₁ ≤ bt₁.length := by
    exact Nat.le_of_lt hb₁
  have hbEq : b₁ = j := by
    have hlength := congrArg List.length hbtEq
    rw [List.length_take, List.length_take, min_eq_left hb₁le,
      min_eq_left (Nat.le_of_lt hjlt)] at hlength
    exact hlength
  have hread₁ : permFwdInputAt bt₁ j = some x := by
    unfold permFwdInputAt
    rw [← hbEq]
    have hbtentry : bt₁[b₁]? = some raw₁[(raw₁.takeWhile good).length] := by
      rw [List.getElem?_eq_getElem hb₁]
      exact congrArg some hbentry₁
    rw [hbtentry]
    cases hentry : raw₁[(raw₁.takeWhile good).length] with
    | mk dom rng =>
        rw [hentry] at hdom₁
        cases dom with
        | inl stmt =>
            cases hdom₁
        | inr permDom =>
            cases permDom with
            | inl s =>
                simp only [Sum.inr.injEq, Sum.inl.injEq] at hdom₁
                subst s
                rfl
            | inr sOut =>
                cases hdom₁
  have hprefix : bt₁.take j = bt₀.take j := by
    rw [hbEq] at hbtEq
    exact hbtEq
  have htargets := permFwdCapacityTargetFinset_eq_of_take_eq_of_permFwdInputAt_eq
    (StmtIn := StmtIn) (U := U) hprefix hread₁ hread
  dsimp [p', bt₀, bt₁, raw₀, raw₁, fam₀, fam₁]
  exact ⟨hprefix, hread₁, htargets⟩

/-- The inverse-query analogue of `spongeDetTrace_permFwd_basePrefix_eq_takeWhile`.  The first
query that can notice a resampled preimage is precisely the charged inverse representative. -/
lemma spongeDetTrace_permBwd_basePrefix_eq_takeWhile
    [Fintype U]
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (h : StmtIn → Vector U SpongeSize.C)
    (p : Equiv.Perm (CanonicalSpongeState U))
    {j : ℕ} {y x' : CanonicalSpongeState U}
    (hnow : permBwdOutputAt (getBaseTrace
        ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver (h, p)).1 ++
         (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver (h, p)).2)) j = some y)
    (hx' : x' ∉ permExposedDomainFinset (getBaseTrace
        ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver (h, p)).1 ++
         (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver (h, p)).2)) j) :
    let bad := permBwdSwapAffected (StmtIn := StmtIn) p y x'
    let good := eagerDetNarrowEntryGood (StmtIn := StmtIn) (U := U) bad
    let raw :=
      (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver (h, p)).1 ++
      (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver (h, p)).2
    (getBaseTrace raw).take j = getBaseTrace (raw.takeWhile good) ∧
      ∃ hstop : (raw.takeWhile good).length < raw.length,
        raw[(raw.takeWhile good).length].1 = .inr (.inr y) := by
  classical
  let fam : (D_𝔖 StmtIn U).Carrier := (h, p)
  let raw : QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
    (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
      (δ := δ) V maliciousProver fam).1 ++
    (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
      (δ := δ) V maliciousProver fam).2
  let bt : QueryLog (duplexSpongeChallengeOracle StmtIn U) := getBaseTrace raw
  let bad := permBwdSwapAffected (StmtIn := StmtIn) p y x'
  let good := eagerDetNarrowEntryGood (StmtIn := StmtIn) (U := U) bad
  change permBwdOutputAt bt j = some y at hnow
  change x' ∉ permExposedDomainFinset bt j at hx'
  obtain ⟨sIn, hbtj⟩ := exists_getElem?_permBwd_of_permBwdOutputAt hnow
  have hsIn := spongeDetTrace_permBwd_entry_range_eq
    (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
    (U := U) (δ := δ) V maliciousProver fam hbtj
  rw [hsIn] at hbtj
  have hbaseMem : (⟨.inr (.inr y), p.symm y⟩ :
      Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ bt := by
    rw [List.mem_iff_getElem?]
    exact ⟨j, hbtj⟩
  have hrawMem : (⟨.inr (.inr y), p.symm y⟩ :
      Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ raw :=
    (getBaseTrace_sublist (StmtIn := StmtIn) (U := U) raw).subset hbaseMem
  have hbadCurrent : bad (.inr (.inr y)) = true := by
    exact bwdSwapAffected_backward_y_true (StmtIn := StmtIn) p y x'
  have hExists : ∃ k : ℕ, ∃ e, raw[k]? = some e ∧ bad e.1 = true := by
    rw [List.mem_iff_getElem?] at hrawMem
    obtain ⟨k, hget⟩ := hrawMem
    exact ⟨k, ⟨.inr (.inr y), p.symm y⟩, hget, hbadCurrent⟩
  let P : ℕ → Prop := fun k => ∃ e, raw[k]? = some e ∧ bad e.1 = true
  let k := Nat.find hExists
  have hk : P k := Nat.find_spec hExists
  obtain ⟨entry, hkGet, hkBad⟩ := hk
  have hkFirst : ∀ m < k, ∀ e, raw[m]? = some e → bad e.1 ≠ true := by
    intro m hm e hget hbad
    have hPm : P m := ⟨e, hget, hbad⟩
    exact Nat.not_lt_of_ge (Nat.find_min' hExists hPm) hm
  have hcons := spongeDetTrace_append_consistent
    (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
    (U := U) (δ := δ) V maliciousProver fam
  have hnr := first_bwdSwap_affected_not_redundant
    (StmtIn := StmtIn) h p y x' raw hcons hkGet hkBad hkFirst
  obtain ⟨hb, hprefix, hbEntry⟩ :=
    DuplexSpongeFS.basePrefix_of_getElem?_not_redundant (StmtIn := StmtIn) (U := U)
      raw hkGet hnr
  let b := (getBaseTrace (raw.take k)).length
  have hbtb : bt[b]? = some entry := by
    change (getBaseTrace raw)[b]? = some entry
    rw [List.getElem?_eq_getElem hb]
    exact congrArg some hbEntry
  have hnotBlt : ¬ b < j := by
    intro hbj
    rcases entry with ⟨dom, rng⟩
    cases dom with
    | inl stmt =>
        unfold bad permBwdSwapAffected at hkBad
        cases hkBad
    | inr permDom =>
        cases permDom with
        | inl s =>
            have hs := bwdSwapAffected_forward_of_true (StmtIn := StmtIn) p y x' s hkBad
            rcases hs with hs | hs
            · subst s
              have hprior : permFwdInputAt bt b = some (p.symm y) := by
                unfold permFwdInputAt
                rw [hbtb]
                rfl
              exact (spongeDetTrace_no_prior_permFwdInput_of_permBwdOutput_shared
                (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
                (U := U) (δ := δ) V maliciousProver fam hbj hnow) hprior
            · subst s
              apply hx'
              refine (mem_permExposedDomainFinset_iff (StmtIn := StmtIn) (U := U)).mpr
                ⟨b, hbj, ?_⟩
              unfold permDomainStateAt
              rw [hbtb]
              rfl
        | inr z =>
            have hz := bwdSwapAffected_backward_of_true (StmtIn := StmtIn) p y x' z hkBad
            rcases hz with hz | hz
            · subst z
              have hprior : permBwdOutputAt bt b = some y := by
                unfold permBwdOutputAt
                rw [hbtb]
                rfl
              exact (spongeDetTrace_no_prior_permBwdOutput_same_shared
                (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
                (U := U) (δ := δ) V maliciousProver fam hbj hnow) hprior
            · subst z
              have hrawEntry : (⟨.inr (.inr (p x')), rng⟩ :
                  Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ raw := by
                rw [List.mem_iff_getElem?]
                exact ⟨k, hkGet⟩
              have hrng := hcons _ hrawEntry
              change rng = p.symm (p x') at hrng
              rw [Equiv.symm_apply_apply] at hrng
              apply hx'
              refine (mem_permExposedDomainFinset_iff (StmtIn := StmtIn) (U := U)).mpr
                ⟨b, hbj, ?_⟩
              unfold permDomainStateAt
              rw [hbtb, hrng]
              rfl
  have hnotJlt : ¬ j < b := by
    intro hjb
    have hbtjLen : j < bt.length := by
      rw [List.getElem?_eq_some_iff] at hbtj
      exact hbtj.1
    have hbtjGet : bt[j] = (⟨.inr (.inr y), p.symm y⟩ :
        Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
      have hsome : some bt[j] = some (⟨.inr (.inr y), p.symm y⟩ :
          Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
        rw [← List.getElem?_eq_getElem hbtjLen]
        exact hbtj
      exact Option.some.inj hsome
    have hmemPrefix : (⟨.inr (.inr y), p.symm y⟩ :
        Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ bt.take b := by
      rw [List.mem_take_iff_getElem]
      exact ⟨j, by omega, hbtjGet⟩
    have hmemBasePrefix : (⟨.inr (.inr y), p.symm y⟩ :
        Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ getBaseTrace (raw.take k) := by
      rw [← hprefix]
      exact hmemPrefix
    have hmemRawPrefix : (⟨.inr (.inr y), p.symm y⟩ :
        Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ raw.take k :=
      (getBaseTrace_sublist (StmtIn := StmtIn) (U := U) (raw.take k)).subset hmemBasePrefix
    rw [List.mem_take_iff_getElem] at hmemRawPrefix
    obtain ⟨m, hm, hrawGet⟩ := hmemRawPrefix
    have hmk : m < k := lt_of_lt_of_le hm (Nat.min_le_left _ _)
    have hmLen : m < raw.length := lt_of_lt_of_le hm (Nat.min_le_right _ _)
    have hrawGet' : raw[m]? = some (⟨.inr (.inr y), p.symm y⟩ :
        Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
      rw [List.getElem?_eq_getElem hmLen]
      exact congrArg some hrawGet
    exact (hkFirst m hmk _ hrawGet') hbadCurrent
  have hbEqj : b = j := by omega
  have hfalse : good entry = false := by
    unfold good eagerDetNarrowEntryGood
    rw [hkBad]
    rfl
  have hbefore : ∀ m < k, ∀ e, raw[m]? = some e → good e = true := by
    intro m hm e hget
    unfold good eagerDetNarrowEntryGood
    cases hbad : bad e.1 with
    | false => rfl
    | true => exact False.elim ((hkFirst m hm e hget) hbad)
  have htw : raw.takeWhile good = raw.take k :=
    takeWhile_eq_take_of_first_false hkGet hfalse hbefore
  have hprefixEq : bt.take j = getBaseTrace (raw.takeWhile good) := by
    rw [← hbEqj]
    change bt.take b = getBaseTrace (raw.takeWhile good)
    rw [htw]
    exact hprefix
  have hkLen : k < raw.length := by
    rw [List.getElem?_eq_some_iff] at hkGet
    exact hkGet.1
  have htwLen : (raw.takeWhile good).length = k := by
    rw [htw, List.length_take]
    exact min_eq_left (Nat.le_of_lt hkLen)
  have hentryDom : entry.1 = .inr (.inr y) := by
    rw [hbEqj] at hbtb
    rcases entry with ⟨dom, rng⟩
    cases dom with
    | inl stmt =>
        unfold permBwdOutputAt at hnow
        rw [hbtb] at hnow
        simp only [Option.bind_some, reduceCtorEq] at hnow
    | inr permDom =>
        cases permDom with
        | inl sIn =>
            unfold permBwdOutputAt at hnow
            rw [hbtb] at hnow
            simp only [Option.bind_some, reduceCtorEq] at hnow
        | inr sOut =>
            unfold permBwdOutputAt at hnow
            rw [hbtb] at hnow
            simp only [Option.bind_some, Option.some.injEq] at hnow
            subst sOut
            rfl
  refine ⟨hprefixEq, ?_⟩
  have hstop : (raw.takeWhile good).length < raw.length := by
    rw [htwLen]
    exact hkLen
  refine ⟨hstop, ?_⟩
  have hgetStop : raw[(raw.takeWhile good).length]? = some entry := by
    rw [htwLen]
    exact hkGet
  have hentryStop : raw[(raw.takeWhile good).length] = entry := by
    rw [List.getElem?_eq_getElem hstop] at hgetStop
    exact Option.some.inj hgetStop
  rw [hentryStop]
  exact hentryDom

/-- Resampling the preimage of the charged inverse representative to an unexposed full state
preserves the strict base prefix, inverse readout, and inverse target set. -/
lemma spongeDetTrace_permBwd_swap_prefix_read_targets
    [Fintype U]
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (h : StmtIn → Vector U SpongeSize.C)
    (p : Equiv.Perm (CanonicalSpongeState U))
    {j : ℕ} {y x' : CanonicalSpongeState U}
    (hread : permBwdOutputAt (getBaseTrace
        ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver (h, p)).1 ++
         (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver (h, p)).2)) j = some y)
    (hx' : x' ∉ permExposedDomainFinset (getBaseTrace
        ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver (h, p)).1 ++
         (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver (h, p)).2)) j) :
    let p' := (Equiv.swap (p.symm y) x').trans p
    let bt₀ := getBaseTrace
      ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver (h, p)).1 ++
       (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver (h, p)).2)
    let bt₁ := getBaseTrace
      ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver (h, p')).1 ++
       (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver (h, p')).2)
    bt₁.take j = bt₀.take j ∧
      permBwdOutputAt bt₁ j = some y ∧
      permBwdCapacityTargetFinset bt₁ j = permBwdCapacityTargetFinset bt₀ j := by
  classical
  let p' : Equiv.Perm (CanonicalSpongeState U) := (Equiv.swap (p.symm y) x').trans p
  let fam₀ : (D_𝔖 StmtIn U).Carrier := (h, p)
  let fam₁ : (D_𝔖 StmtIn U).Carrier := (h, p')
  let raw₀ : QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
    (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
      (δ := δ) V maliciousProver fam₀).1 ++
    (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
      (δ := δ) V maliciousProver fam₀).2
  let raw₁ : QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
    (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
      (δ := δ) V maliciousProver fam₁).1 ++
    (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
      (δ := δ) V maliciousProver fam₁).2
  let bt₀ := getBaseTrace raw₀
  let bt₁ := getBaseTrace raw₁
  let bad := permBwdSwapAffected (StmtIn := StmtIn) p y x'
  let good := eagerDetNarrowEntryGood (StmtIn := StmtIn) (U := U) bad
  change permBwdOutputAt bt₀ j = some y at hread
  change x' ∉ permExposedDomainFinset bt₀ j at hx'
  have hbase : bt₀.take j = getBaseTrace (raw₀.takeWhile good) ∧
      ∃ hstop : (raw₀.takeWhile good).length < raw₀.length,
        raw₀[(raw₀.takeWhile good).length].1 = .inr (.inr y) := by
    dsimp only [bt₀, raw₀, fam₀, good, bad]
    exact spongeDetTrace_permBwd_basePrefix_eq_takeWhile
      (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) (δ := δ)
      V maliciousProver h p hread hx'
  obtain ⟨hprefix₀, hstop₀, hdom₀⟩ := hbase
  have hsync := spongeDetTrace_append_first_bad_domain_bwdSwapAffected_eq
    (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) (δ := δ)
    V maliciousProver h p y x'
  change raw₁.takeWhile good = raw₀.takeWhile good ∧
      ((raw₁.takeWhile good).length < raw₁.length ↔
        (raw₀.takeWhile good).length < raw₀.length) ∧
      (∀ (h₁ : (raw₁.takeWhile good).length < raw₁.length)
          (h₀ : (raw₀.takeWhile good).length < raw₀.length),
        raw₁[(raw₁.takeWhile good).length].1 =
          raw₀[(raw₀.takeWhile good).length].1) at hsync
  have hstop₁ : (raw₁.takeWhile good).length < raw₁.length := hsync.2.1.mpr hstop₀
  have hdom₁ : raw₁[(raw₁.takeWhile good).length].1 = .inr (.inr y) := by
    rw [hsync.2.2 hstop₁ hstop₀]
    exact hdom₀
  have hp'y : p'.symm y = x' := by
    apply p'.injective
    rw [Equiv.apply_symm_apply]
    change y = p ((Equiv.swap (p.symm y) x') x')
    rw [Equiv.swap_apply_right, Equiv.apply_symm_apply]
  have hget₁ : raw₁[(raw₁.takeWhile good).length]? =
      some raw₁[(raw₁.takeWhile good).length] := by
    rw [List.getElem?_eq_getElem hstop₁]
  have hcons₁ := spongeDetTrace_append_consistent
    (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
    (U := U) (δ := δ) V maliciousProver fam₁
  have hfirst₁ : ∀ m < (raw₁.takeWhile good).length, ∀ e, raw₁[m]? = some e →
      bad e.1 ≠ true := by
    intro m hm e hget hbad
    have hgood := getElem?_true_of_lt_takeWhile (p := good) hm hget
    unfold good eagerDetNarrowEntryGood at hgood
    rw [hbad] at hgood
    cases hgood
  have hnr₁ := first_bwdSwap_backward_y_not_redundant_after_swap
    (StmtIn := StmtIn) h p p' y x' raw₁ hp'y hcons₁ hget₁ hdom₁ hfirst₁
  obtain ⟨hb₁, hprefix₁, hbentry₁⟩ :=
    DuplexSpongeFS.basePrefix_of_getElem?_not_redundant (StmtIn := StmtIn) (U := U)
      raw₁ hget₁ hnr₁
  let b₁ := (getBaseTrace (raw₁.take (raw₁.takeWhile good).length)).length
  have hprefix₁' : bt₁.take b₁ = getBaseTrace (raw₁.takeWhile good) := by
    change bt₁.take b₁ = getBaseTrace (raw₁.takeWhile good)
    rw [← take_length_takeWhile raw₁]
    exact hprefix₁
  have hbtEq : bt₁.take b₁ = bt₀.take j := by
    rw [hprefix₁', hsync.1, ← hprefix₀]
  have hjlt : j < bt₀.length := by
    obtain ⟨sIn, hbtj⟩ := exists_getElem?_permBwd_of_permBwdOutputAt hread
    rw [List.getElem?_eq_some_iff] at hbtj
    exact hbtj.1
  have hb₁le : b₁ ≤ bt₁.length := by
    exact Nat.le_of_lt hb₁
  have hbEq : b₁ = j := by
    have hlength := congrArg List.length hbtEq
    rw [List.length_take, List.length_take, min_eq_left hb₁le,
      min_eq_left (Nat.le_of_lt hjlt)] at hlength
    exact hlength
  have hread₁ : permBwdOutputAt bt₁ j = some y := by
    unfold permBwdOutputAt
    rw [← hbEq]
    have hbtentry : bt₁[b₁]? = some raw₁[(raw₁.takeWhile good).length] := by
      rw [List.getElem?_eq_getElem hb₁]
      exact congrArg some hbentry₁
    rw [hbtentry]
    cases hentry : raw₁[(raw₁.takeWhile good).length] with
    | mk dom rng =>
        rw [hentry] at hdom₁
        cases dom with
        | inl stmt =>
            cases hdom₁
        | inr permDom =>
            cases permDom with
            | inl sIn =>
                cases hdom₁
            | inr sOut =>
                simp only [Sum.inr.injEq, Sum.inr.injEq] at hdom₁
                subst sOut
                rfl
  have hprefix : bt₁.take j = bt₀.take j := by
    rw [hbEq] at hbtEq
    exact hbtEq
  have htargets := permBwdCapacityTargetFinset_eq_of_take_eq_of_permBwdOutputAt_eq
    (StmtIn := StmtIn) (U := U) hprefix hread₁ hread
  dsimp [p', bt₀, bt₁, raw₀, raw₁, fam₀, fam₁]
  exact ⟨hprefix, hread₁, htargets⟩

end BadEventDS

end DuplexSpongeFS
