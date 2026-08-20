/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.Infrastructure
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.HashSupport

/-!
# Hash collision bounds for Lemma 5.8
-/

open OracleComp OracleSpec ProtocolSpec

open scoped ENNReal

namespace DuplexSpongeFS

namespace BadEventDS

open DuplexSpongeFS.DSTraceStorage

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]

variable (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))


variable {StmtOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [codec : CodecCore pSpec U] {δ : ℕ} [DecidableEq StmtIn] [DecidableEq U]
  [VCVCompatible U] [SampleableType U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]


/-! ### Per-index collision and freshness bounds


For each side, at base-trace position `j` (`0`-indexed, so `j` priors), the freshly-sampled `j`-th
answer capacity is uniform in `Σ^c` and collides with `≤ 2j` (h) / `≤ 2j+1` (p, p⁻¹) / `≤ j` (func)
prior capacities.  Sponge side: `h` uniform random function, `p`/`p⁻¹` random permutation
(near-uniform ⇒ the new permutation-freshness lemma), and `E_func` never fires (`p` genuine
function) so its bound is `0 ≤ j/|Σ|^c`.  Sigma side: all answers lazily uniform (`d2sQueryImpl`),
`E_func` via the `Cache_p ∩ tr` count. -/
section PerIndexCollisionBounds


variable [Fintype U] [Nonempty U]

/-! #### Union-bound reduction of the per-index E_h/E_p/E_pinv events


Each `E_X_at · j` is covered by the ≤ 2j pairwise capacity collisions between the entry at base
position `j` and the ≤ 2 capacity segments exposed by each earlier position `j' < j`.  This
reduces the per-index probability to a sum of collision *atoms* `Pr[collision(j,j',k)] ≤ 1/|Σ|^c`
(the atoms are the genuinely probabilistic obligation; the reduction below is pure). -/
section HashCollisionReduction



/-- A defined hash-output readout identifies some hash query at the same base position. -/
lemma exists_hashQueryAt_of_hashOutCapAt
    {bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {j : ℕ} {c : Vector U SpongeSize.C}
    (hout : hashOutCapAt bt j = some c) :
    ∃ q : StmtIn, hashQueryAt bt j = some q := by
  unfold hashOutCapAt at hout
  unfold hashQueryAt
  cases hbt : bt[j]? with
  | none =>
      rw [hbt] at hout
      simp only [Option.bind_none, reduceCtorEq] at hout
  | some entry =>
      cases entry with
      | mk dom rng =>
          cases dom with
          | inl stmt =>
              rw [hbt] at hout
              simp only [Option.bind_some, Option.some.injEq] at hout
              exact ⟨stmt, by simp only [hbt, Option.bind_some]⟩
          | inr _permDom =>
              rw [hbt] at hout
              simp only [Option.bind_some, reduceCtorEq] at hout

/-- A defined hash query readout identifies the corresponding base-trace hash entry. -/
lemma exists_getElem?_hash_of_hashQueryAt
    {bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {j : ℕ} {q : StmtIn}
    (hq : hashQueryAt bt j = some q) :
    ∃ c : Vector U SpongeSize.C, bt[j]? = some ⟨.inl q, c⟩ := by
  unfold hashQueryAt at hq
  cases hbt : bt[j]? with
  | none =>
      rw [hbt] at hq
      simp only [Option.bind_none, reduceCtorEq] at hq
  | some entry =>
      rcases entry with ⟨dom, rng⟩
      cases dom with
      | inr _permDom =>
          rw [hbt] at hq
          simp only [Option.bind_some, reduceCtorEq] at hq
      | inl stmt =>
          rw [hbt] at hq
          simp only [Option.bind_some, Option.some.injEq] at hq
          subst stmt
          refine ⟨rng, ?_⟩
          rfl

/-- In the deterministic eager sponge trace, a hash entry with query `q` is answered by the sampled
hash table `h q`. -/
lemma spongeDetTrace_hashQuery_output_eq
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) :
    ∀ h p j q,
      hashQueryAt (getBaseTrace
          ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
            (δ := δ) V maliciousProver (h, p)).1 ++
           (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
            (δ := δ) V maliciousProver (h, p)).2)) j = some q →
      hashOutCapAt (getBaseTrace
          ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
            (δ := δ) V maliciousProver (h, p)).1 ++
           (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
            (δ := δ) V maliciousProver (h, p)).2)) j =
        some ((show StmtIn → Vector U SpongeSize.C from h) q) := by
  intro h p j q hq
  let fam : (D_𝔖 StmtIn U).Carrier := (h, p)
  let bt : QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
    getBaseTrace
      ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver fam).1 ++
       (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver fam).2)
  change hashOutCapAt bt j = some ((show StmtIn → Vector U SpongeSize.C from h) q)
  change hashQueryAt bt j = some q at hq
  have hcons := spongeDetTrace_baseTrace_consistent (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver fam
  unfold hashQueryAt at hq
  cases hbt : bt[j]? with
  | none =>
      rw [hbt] at hq
      simp only [Option.bind_none, reduceCtorEq] at hq
  | some entry =>
      cases entry with
      | mk dom rng =>
          cases dom with
          | inl stmt =>
              have hstmt : stmt = q := by
                rw [hbt] at hq
                simp only [Option.bind_some, Option.some.injEq] at hq
                exact hq
              subst q
              rw [List.getElem?_eq_some_iff] at hbt
              obtain ⟨hj, hget⟩ := hbt
              have hmem : (⟨Sum.inl stmt, rng⟩ :
                  Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ bt := by
                rw [← hget]
                exact List.getElem_mem _
              have hAns : rng = spongeAnswer fam (.inl stmt) := hcons _ hmem
              have hAns' : rng = (show StmtIn → Vector U SpongeSize.C from h) stmt := by
                simp [fam, spongeAnswer] at hAns
                exact hAns
              unfold hashOutCapAt
              rw [show bt[j]? = some ⟨Sum.inl stmt, rng⟩ by
                rw [List.getElem?_eq_getElem hj, hget]]
              simp [hAns']
          | inr _permDom =>
              rw [hbt] at hq
              simp only [Option.bind_some, reduceCtorEq] at hq

/-- In a no-redundant base trace, the exact same hash pair cannot occur at a strict earlier
position.  This is the trace-only "first representative" fact used by the sponge ROM-causality
argument. -/
lemma noRedundant_hash_pair_not_prior
    {bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hNoRedundant : hasNoRedundantEntries bt)
    {j j' : ℕ} (hj' : j' < j) {q : StmtIn} {c : Vector U SpongeSize.C}
    (hj : bt[j]? = some ⟨.inl q, c⟩)
    (hjPrior : bt[j']? = some ⟨.inl q, c⟩) :
    False := by
  rw [List.getElem?_eq_some_iff] at hj hjPrior
  obtain ⟨hjLen, hjEq⟩ := hj
  obtain ⟨hj'Len, hj'Eq⟩ := hjPrior
  have hPriorMem : (⟨.inl q, c⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ bt.take j := by
    rw [List.mem_take_iff_getElem]
    exact ⟨j', lt_min hj' hj'Len, hj'Eq⟩
  have hRed : isRedundantEntryOfPrefix (bt.take j) bt[j] := by
    rw [hjEq]
    exact hPriorMem
  exact hNoRedundant j hjLen hRed

/-- In a deterministic eager sponge base trace, a hash query domain occurs at most once.  The
base trace removes exact duplicates, and consistency of the eager hash table makes every answer to
the same hash query exact-equal. -/
lemma spongeDetTrace_no_prior_hashQuery_same
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (fam : (D_𝔖 StmtIn U).Carrier)
    {j j' : ℕ} {q : StmtIn}
    (hj' : j' < j)
    (hq : hashQueryAt (getBaseTrace
        ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).1 ++
         (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).2)) j = some q) :
    hashQueryAt (getBaseTrace
        ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).1 ++
         (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).2)) j' ≠ some q := by
  classical
  let bt : QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
    getBaseTrace
      ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver fam).1 ++
       (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver fam).2)
  change hashQueryAt bt j = some q at hq
  intro hq'
  change hashQueryAt bt j' = some q at hq'
  unfold hashQueryAt at hq hq'
  cases hjGet : bt[j]? with
  | none =>
      rw [hjGet] at hq
      simp only [Option.bind_none, reduceCtorEq] at hq
  | some ej =>
      cases hj'Get : bt[j']? with
      | none =>
          rw [hj'Get] at hq'
          simp only [Option.bind_none, reduceCtorEq] at hq'
      | some ej' =>
          rcases ej with ⟨dom, rng⟩
          rcases ej' with ⟨dom', rng'⟩
          cases dom with
          | inr _ =>
              rw [hjGet] at hq
              simp only [Option.bind_some, reduceCtorEq] at hq
          | inl stmt =>
              cases dom' with
              | inr _ =>
                  rw [hj'Get] at hq'
                  simp only [Option.bind_some, reduceCtorEq] at hq'
              | inl stmt' =>
                  rw [hjGet] at hq
                  rw [hj'Get] at hq'
                  simp only [Option.bind_some, Option.some.injEq] at hq hq'
                  subst stmt
                  subst stmt'
                  have hcons := spongeDetTrace_baseTrace_consistent
                    (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
                    (U := U) (δ := δ) V maliciousProver fam
                  have hjMem : (⟨Sum.inl q, rng⟩ :
                      Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ bt := by
                    rw [List.mem_iff_getElem?]
                    exact ⟨j, hjGet⟩
                  have hj'Mem : (⟨Sum.inl q, rng'⟩ :
                      Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ bt := by
                    rw [List.mem_iff_getElem?]
                    exact ⟨j', hj'Get⟩
                  have hrng : rng = rng' := by
                    calc
                      rng = spongeAnswer fam (.inl q) := hcons _ hjMem
                      _ = rng' := (hcons _ hj'Mem).symm
                  subst rng'
                  exact noRedundant_hash_pair_not_prior
                    (StmtIn := StmtIn) (U := U) (bt := bt)
                    (getBaseTrace_noRedundant (StmtIn := StmtIn) (U := U) _)
                    hj' hjGet hj'Get

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
          have ih' := ih hgetRest hbeforeRest
          simp [List.takeWhile, ha, ih']

private lemma length_takeWhile_lt_of_mem_false {α : Type} {p : α → Bool}
    {l : List α} {x : α} (hmem : x ∈ l) (hfalse : p x = false) :
    (l.takeWhile p).length < l.length := by
  induction l with
  | nil =>
      cases hmem
  | cons a rest ih =>
      rw [List.mem_cons] at hmem
      rcases hmem with hxa | hxrest
      · subst x
        simp [List.takeWhile, hfalse]
      · by_cases ha : p a = true
        · simp [List.takeWhile, ha]
          exact ih hxrest
        · have haFalse : p a = false := by
            cases hp : p a
            · rfl
            · exact False.elim (ha hp)
          simp [List.takeWhile, haFalse]

private lemma takeWhile_stop_value_false {α : Type} {p : α → Bool}
    {l : List α} (hstop : (l.takeWhile p).length < l.length) :
    p l[(l.takeWhile p).length] = false := by
  induction l with
  | nil =>
      cases hstop
  | cons a rest ih =>
      by_cases ha : p a = true
      · simp [List.takeWhile, ha] at hstop ⊢
        exact ih hstop
      · have haFalse : p a = false := by
          cases hp : p a
          · rfl
          · exact False.elim (ha hp)
        simp [List.takeWhile, haFalse]

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

private lemma hashBad_domain_eq_of_true
    {q : StmtIn} {dom : (duplexSpongeChallengeOracle StmtIn U).Domain}
    (hbad : (match dom with
      | .inl q' => decide (q' = q)
      | .inr _ => false) = true) :
    dom = .inl q := by
  cases dom with
  | inl q' =>
      simp only at hbad
      have hq' : q' = q := of_decide_eq_true hbad
      rw [hq']
  | inr permDom =>
      simp only at hbad
      cases hbad

/-- If deterministic base index `j` is the hash query `q`, then the prefix before `j` is exactly
the base trace of the raw projected transcript before the first raw query to `q`. -/
lemma spongeDetTrace_hashQuery_basePrefix_eq_takeWhile
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (fam : (D_𝔖 StmtIn U).Carrier)
    {j : ℕ} {q : StmtIn}
    (hq : hashQueryAt (getBaseTrace
        ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).1 ++
         (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).2)) j = some q) :
    let bad : (duplexSpongeChallengeOracle StmtIn U).Domain → Bool :=
      fun dom => match dom with
        | .inl q' => decide (q' = q)
        | .inr _ => false
    let good := eagerDetNarrowEntryGood (StmtIn := StmtIn) (U := U) bad
    let raw :=
      (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
        (U := U) (δ := δ) V maliciousProver fam).1 ++
      (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
        (U := U) (δ := δ) V maliciousProver fam).2
    (getBaseTrace raw).take j = getBaseTrace (raw.takeWhile good) := by
  classical
  let raw : QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
    (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
      (U := U) (δ := δ) V maliciousProver fam).1 ++
    (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
      (U := U) (δ := δ) V maliciousProver fam).2
  let bt : QueryLog (duplexSpongeChallengeOracle StmtIn U) := getBaseTrace raw
  change hashQueryAt bt j = some q at hq
  obtain ⟨cap, hbtj⟩ : ∃ cap : Vector U SpongeSize.C,
      bt[j]? = some ⟨.inl q, cap⟩ := by
    unfold hashQueryAt at hq
    cases hget : bt[j]? with
    | none =>
        rw [hget] at hq
        simp only [Option.bind_none, reduceCtorEq] at hq
    | some entry =>
        rcases entry with ⟨dom, rng⟩
        cases dom with
        | inr _ =>
            rw [hget] at hq
            simp only [Option.bind_some, reduceCtorEq] at hq
        | inl stmt =>
            rw [hget] at hq
            simp only [Option.bind_some, Option.some.injEq] at hq
            subst stmt
            exact ⟨rng, rfl⟩
  have hbaseMem : (⟨Sum.inl q, cap⟩ :
      Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ bt := by
    rw [List.mem_iff_getElem?]
    exact ⟨j, hbtj⟩
  have hrawMem : (⟨Sum.inl q, cap⟩ :
      Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ raw :=
    (getBaseTrace_sublist (StmtIn := StmtIn) (U := U) raw).subset hbaseMem
  have hExists : ∃ k : ℕ, ∃ cap' : Vector U SpongeSize.C,
      raw[k]? = some (⟨.inl q, cap'⟩ :
        Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
    rw [List.mem_iff_getElem?] at hrawMem
    obtain ⟨k, hk⟩ := hrawMem
    exact ⟨k, cap, hk⟩
  let P : ℕ → Prop := fun k =>
    ∃ cap' : Vector U SpongeSize.C, raw[k]? = some (⟨.inl q, cap'⟩ :
      Sigma (duplexSpongeChallengeOracle StmtIn U))
  let k := Nat.find hExists
  have hkSpec : P k := Nat.find_spec hExists
  obtain ⟨capFirst, hkGet⟩ := hkSpec
  have hkFirst : ∀ m < k, ¬ P m := by
    intro m hm hPm
    exact Nat.not_lt_of_ge (Nat.find_min' hExists hPm) hm
  have hnr : ¬ isRedundantEntryOfPrefix (raw.take k)
      (⟨Sum.inl q, capFirst⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
    intro hred
    simp only [isRedundantEntryOfPrefix] at hred
    rw [List.mem_take_iff_getElem] at hred
    obtain ⟨m, hm, hgetm⟩ := hred
    have hmLen : m < raw.length := lt_of_lt_of_le hm (Nat.min_le_right _ _)
    have hmLt : m < k := lt_of_lt_of_le hm (Nat.min_le_left _ _)
    apply hkFirst m hmLt
    exact ⟨capFirst, by
      rw [List.getElem?_eq_getElem hmLen]
      exact congrArg some hgetm⟩
  obtain ⟨hb, hprefix, hbEntry⟩ :=
    DuplexSpongeFS.basePrefix_of_getElem?_not_redundant (StmtIn := StmtIn) (U := U)
      raw hkGet hnr
  let b := (getBaseTrace (raw.take k)).length
  have hbEntry? : bt[b]? = some ⟨.inl q, capFirst⟩ := by
    change (getBaseTrace raw)[b]? = some ⟨Sum.inl q, capFirst⟩
    rw [List.getElem?_eq_getElem hb]
    exact congrArg some hbEntry
  have hq_b : hashQueryAt bt b = some q := by
    unfold hashQueryAt
    rw [hbEntry?]
    rfl
  have hbEqj : b = j := by
    by_cases hbj : b < j
    · have hnot := spongeDetTrace_no_prior_hashQuery_same
        (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
        (U := U) (δ := δ) V maliciousProver fam hbj hq
      exact False.elim (hnot hq_b)
    · by_cases hjb : j < b
      · have hnot := spongeDetTrace_no_prior_hashQuery_same
          (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
          (U := U) (δ := δ) V maliciousProver fam hjb hq_b
        exact False.elim (hnot hq)
      · omega
  let bad : (duplexSpongeChallengeOracle StmtIn U).Domain → Bool :=
    fun dom => match dom with
      | .inl q' => decide (q' = q)
      | .inr _ => false
  let good := eagerDetNarrowEntryGood (StmtIn := StmtIn) (U := U) bad
  have hfalse : good (⟨Sum.inl q, capFirst⟩ :
      Sigma (duplexSpongeChallengeOracle StmtIn U)) = false := by
    simp [good, bad, eagerDetNarrowEntryGood]
  have hbefore : ∀ m < k, ∀ e', raw[m]? = some e' → good e' = true := by
    intro m hm e' hgetm
    rcases e' with ⟨dom, rng⟩
    cases dom with
    | inr permDom =>
        cases permDom <;> simp [good, bad, eagerDetNarrowEntryGood]
    | inl stmt =>
        by_cases hstmt : stmt = q
        · subst stmt
          have hPm : P m := ⟨rng, hgetm⟩
          exact False.elim (hkFirst m hm hPm)
        · simp [good, bad, eagerDetNarrowEntryGood, hstmt]
  have htw : raw.takeWhile good = raw.take k :=
    takeWhile_eq_take_of_first_false hkGet hfalse hbefore
  change bt.take j = getBaseTrace (raw.takeWhile good)
  rw [← hbEqj]
  change bt.take b = getBaseTrace (raw.takeWhile good)
  rw [htw]
  change (getBaseTrace raw).take (getBaseTrace (raw.take k)).length =
    getBaseTrace (raw.take k)
  exact hprefix

/-- Hash-query target readouts transfer between two deterministic sponge traces that agree on all
queries except the charged hash query `q`.

This is the formal version of the ROM deferred-decision step for `E_h`: before the first raw
query to `q`, the projected transcript and hence the base-trace prefix are identical. -/
lemma sponge_hashTarget_hashQuery_transfer_of_agree_off_hash
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (fam₁ fam₂ : (D_𝔖 StmtIn U).Carrier)
    (q : StmtIn) (j : ℕ) (i : Fin (2 * j)) (c : Vector U SpongeSize.C)
    (hagree : ∀ dom,
      (match dom with
        | .inl q' => decide (q' = q)
        | .inr _ => false) = false →
        spongeAnswer fam₁ dom = spongeAnswer fam₂ dom) :
    let tr₁ := spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
      (U := U) (δ := δ) V maliciousProver fam₁
    let tr₂ := spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
      (U := U) (δ := δ) V maliciousProver fam₂
    (priorCapacityTargetAt (getBaseTrace (tr₁.1 ++ tr₁.2)) j i = some c ∧
        hashQueryAt (getBaseTrace (tr₁.1 ++ tr₁.2)) j = some q) →
      (priorCapacityTargetAt (getBaseTrace (tr₂.1 ++ tr₂.2)) j i = some c ∧
        hashQueryAt (getBaseTrace (tr₂.1 ++ tr₂.2)) j = some q) := by
  classical
  let tr₁ := spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
    (U := U) (δ := δ) V maliciousProver fam₁
  let tr₂ := spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
    (U := U) (δ := δ) V maliciousProver fam₂
  let raw₁ : QueryLog (duplexSpongeChallengeOracle StmtIn U) := tr₁.1 ++ tr₁.2
  let raw₂ : QueryLog (duplexSpongeChallengeOracle StmtIn U) := tr₂.1 ++ tr₂.2
  let bt₁ : QueryLog (duplexSpongeChallengeOracle StmtIn U) := getBaseTrace raw₁
  let bt₂ : QueryLog (duplexSpongeChallengeOracle StmtIn U) := getBaseTrace raw₂
  let bad : (duplexSpongeChallengeOracle StmtIn U).Domain → Bool :=
    fun dom => match dom with
      | .inl q' => decide (q' = q)
      | .inr _ => false
  let good := eagerDetNarrowEntryGood (StmtIn := StmtIn) (U := U) bad
  have hlock :=
    spongeDetTrace_append_first_bad_domain_eq (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver fam₁ fam₂ bad (by
        intro dom hdom
        exact hagree dom hdom)
  change List.takeWhile good raw₁ = List.takeWhile good raw₂ ∧
      ((List.takeWhile good raw₁).length < raw₁.length ↔
        (List.takeWhile good raw₂).length < raw₂.length) ∧
      (∀ (h₁ : (List.takeWhile good raw₁).length < raw₁.length)
          (h₂ : (List.takeWhile good raw₂).length < raw₂.length),
        raw₁[(List.takeWhile good raw₁).length].1 =
          raw₂[(List.takeWhile good raw₂).length].1) at hlock
  change (priorCapacityTargetAt bt₁ j i = some c ∧ hashQueryAt bt₁ j = some q) →
    (priorCapacityTargetAt bt₂ j i = some c ∧ hashQueryAt bt₂ j = some q)
  intro h
  rcases h with ⟨htarget₁, hq₁⟩
  obtain ⟨cap₁, hbt₁j⟩ := exists_getElem?_hash_of_hashQueryAt (StmtIn := StmtIn)
    (U := U) (bt := bt₁) hq₁
  have hbt₁jLen : j < bt₁.length := by
    have hsome := hbt₁j
    rw [List.getElem?_eq_some_iff] at hsome
    exact hsome.1
  have hbaseMem₁ : (⟨Sum.inl q, cap₁⟩ :
      Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ bt₁ := by
    rw [List.mem_iff_getElem?]
    exact ⟨j, hbt₁j⟩
  have hrawMem₁ : (⟨Sum.inl q, cap₁⟩ :
      Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ raw₁ :=
    (getBaseTrace_sublist (StmtIn := StmtIn) (U := U) raw₁).subset hbaseMem₁
  have hfalseHash₁ : good (⟨Sum.inl q, cap₁⟩ :
      Sigma (duplexSpongeChallengeOracle StmtIn U)) = false := by
    simp [good, bad, eagerDetNarrowEntryGood]
  have hstop₁ : (List.takeWhile good raw₁).length < raw₁.length :=
    length_takeWhile_lt_of_mem_false hrawMem₁ hfalseHash₁
  have hstop₂ : (List.takeWhile good raw₂).length < raw₂.length :=
    hlock.2.1.mp hstop₁
  have hfalseStop₂ : good raw₂[(List.takeWhile good raw₂).length] = false :=
    takeWhile_stop_value_false hstop₂
  have hbadStop₂ : bad raw₂[(List.takeWhile good raw₂).length].1 = true := by
    cases hb : bad raw₂[(List.takeWhile good raw₂).length].1
    · simp [good, eagerDetNarrowEntryGood, hb] at hfalseStop₂
    · rfl
  have hdomStop₂ : raw₂[(List.takeWhile good raw₂).length].1 = .inl q := by
    exact hashBad_domain_eq_of_true (StmtIn := StmtIn) (U := U) (q := q) hbadStop₂
  obtain ⟨cap₂, hentry₂⟩ : ∃ cap₂ : Vector U SpongeSize.C,
      raw₂[(List.takeWhile good raw₂).length] = ⟨.inl q, cap₂⟩ := by
    cases hentryRaw : raw₂[(List.takeWhile good raw₂).length] with
    | mk dom rng =>
        cases dom with
        | inl stmt =>
            rw [hentryRaw] at hbadStop₂
            have hstmt : stmt = q := by
              unfold bad at hbadStop₂
              exact of_decide_eq_true hbadStop₂
            subst stmt
            exact ⟨rng, rfl⟩
        | inr permDom =>
            rw [hentryRaw] at hbadStop₂
            unfold bad at hbadStop₂
            simp only at hbadStop₂
            cases hbadStop₂
  have hget₂ : raw₂[(List.takeWhile good raw₂).length]? =
      some (⟨.inl q, cap₂⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
    rw [List.getElem?_eq_getElem hstop₂, hentry₂]
  have hnr₂ : ¬ isRedundantEntryOfPrefix (raw₂.take (List.takeWhile good raw₂).length)
      (⟨Sum.inl q, cap₂⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
    intro hred
    simp only [isRedundantEntryOfPrefix] at hred
    rw [List.mem_take_iff_getElem] at hred
    obtain ⟨m, hm, hgetm⟩ := hred
    have hmLen : m < raw₂.length := lt_of_lt_of_le hm (Nat.min_le_right _ _)
    have hmLt : m < (List.takeWhile good raw₂).length :=
      lt_of_lt_of_le hm (Nat.min_le_left _ _)
    have hgetm? : raw₂[m]? =
        some (⟨Sum.inl q, cap₂⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
      rw [List.getElem?_eq_getElem hmLen]
      exact congrArg some hgetm
    have htrue := getElem?_true_of_lt_takeWhile hmLt hgetm?
    have hfalse : good (⟨Sum.inl q, cap₂⟩ :
        Sigma (duplexSpongeChallengeOracle StmtIn U)) = false := by
      simp [good, bad, eagerDetNarrowEntryGood]
    rw [hfalse] at htrue
    cases htrue
  obtain ⟨hb₂, _hprefix₂, hbEntry₂⟩ :=
    DuplexSpongeFS.basePrefix_of_getElem?_not_redundant (StmtIn := StmtIn) (U := U)
      raw₂ hget₂ hnr₂
  let b₂ := (getBaseTrace (raw₂.take (List.takeWhile good raw₂).length)).length
  have hbEntry₂? : bt₂[b₂]? =
      some (⟨.inl q, cap₂⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
    change (getBaseTrace raw₂)[b₂]? =
      some (⟨Sum.inl q, cap₂⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
    rw [List.getElem?_eq_getElem hb₂]
    exact congrArg some hbEntry₂
  have hprefixHash₁ :=
    spongeDetTrace_hashQuery_basePrefix_eq_takeWhile
      (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
      (U := U) (δ := δ) V maliciousProver fam₁ hq₁
  change bt₁.take j = getBaseTrace (raw₁.takeWhile good) at hprefixHash₁
  have hprefixLen₁ : (getBaseTrace (raw₁.takeWhile good)).length = j := by
    rw [← hprefixHash₁, List.length_take]
    rw [min_eq_left (Nat.le_of_lt hbt₁jLen)]
  have hbaseTakeEq : getBaseTrace (raw₁.takeWhile good) =
      getBaseTrace (raw₂.takeWhile good) := by
    rw [hlock.1]
  have hb₂eqj : b₂ = j := by
    change (getBaseTrace (raw₂.take (List.takeWhile good raw₂).length)).length = j
    rw [take_length_takeWhile raw₂]
    rw [← hbaseTakeEq]
    exact hprefixLen₁
  have hq₂ : hashQueryAt bt₂ j = some q := by
    unfold hashQueryAt
    rw [← hb₂eqj]
    rw [hbEntry₂?]
    rfl
  have hprefixHash₂ :=
    spongeDetTrace_hashQuery_basePrefix_eq_takeWhile
      (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
      (U := U) (δ := δ) V maliciousProver fam₂ hq₂
  change bt₂.take j = getBaseTrace (raw₂.takeWhile good) at hprefixHash₂
  have hbtPrefix : bt₁.take j = bt₂.take j := by
    calc
      bt₁.take j = getBaseTrace (raw₁.takeWhile good) := hprefixHash₁
      _ = getBaseTrace (raw₂.takeWhile good) := hbaseTakeEq
      _ = bt₂.take j := hprefixHash₂.symm
  have htargetEq := priorCapacityTargetAt_eq_of_take_eq
    (StmtIn := StmtIn) (U := U) hbtPrefix i
  have htarget₂ : priorCapacityTargetAt bt₂ j i = some c := by
    rw [← htargetEq]
    exact htarget₁
  change priorCapacityTargetAt bt₂ j i = some c ∧ hashQueryAt bt₂ j = some q
  exact ⟨htarget₂, hq₂⟩

/- **Joint hash-freshness predicate** for a Lemma-5.8 trace experiment `(init, spongeImpl)`:
each hash (`.inl`) answer is a *fresh uniform* draw in `Σ^c`, **independent of the length-`j`
prefix**.  Phrased in the joint form needed for the per-pair bound: for `j' < j`, slot `k`, and any
*fixed* target capacity `c`, the joint event "`j`-th base answer is a hash entry with output `c`
**and** the `k`-th cap at `j'` is `c`" has probability `≤ (prob the `j'`-cap is `c`)/|Σ|^c`.
The current canonical route packages this as `hashFreshHitAt`, a finite-list hit event against
`priorCapacityTargets`.

This is the exact probabilistic content that differs between the two sides: the **sponge** side gets
it from `h ← D_ROM` (uniform random function, product-independent of `p`), the **sigma** side from
`d2sHandleHashQuery`'s lazy uniform sampling.  (Marginal freshness alone would *not* suffice — a
hash output fully correlated with the target can still be marginally uniform; the joint form
encodes the needed independence.) -/

/-- Sponge hash atom from the deterministic prefix/update invariant.

This theorem isolates the probability-theory part of the paper's `E_h` line: after expanding the
sponge experiment to `(h, p)`, the bad atom is bounded by applying adaptive random-function
freshness to the coordinate read by base index `j`.  The only experiment-specific assumption is
that the target readout and the charged hash query are stable when the answer at that charged
coordinate is patched. -/
lemma sponge_hashTargetAtom_first_le_of_update_invariant
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (j : ℕ) (i : Fin (2 * j)) (c : Vector U SpongeSize.C)
    (hinv : ∀ (p : Equiv.Perm (CanonicalSpongeState U))
      (g : StmtIn → Vector U SpongeSize.C) (q : StmtIn) (v : Vector U SpongeSize.C),
      let tr₁ :=
        spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver (Function.update g q v, p)
      let tr₀ :=
        spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver (g, p)
      (priorCapacityTargetAt (getBaseTrace (tr₁.1 ++ tr₁.2)) j i = some c ∧
          hashQueryAt (getBaseTrace (tr₁.1 ++ tr₁.2)) j = some q) ↔
        (priorCapacityTargetAt (getBaseTrace (tr₀.1 ++ tr₀.2)) j i = some c ∧
          hashQueryAt (getBaseTrace (tr₀.1 ++ tr₀.2)) j = some q)) :
    Pr[ fun tr =>
        E_first_at (tr.1 ++ tr.2) j ∧
          hashOutCapAt (getBaseTrace (tr.1 ++ tr.2)) j = some c ∧
          priorCapacityTargetAt (getBaseTrace (tr.1 ++ tr.2)) j i = some c |
        lemma5_8SpongeTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n)
          (pSpec := pSpec) (U := U) (δ := δ) (initSponge := (D_𝔖 StmtIn U).sample)
          (implSponge := (D_𝔖 StmtIn U).eagerImpl) V maliciousProver]
      ≤ Pr[ fun tr =>
          priorCapacityTargetAt (getBaseTrace (tr.1 ++ tr.2)) j i = some c |
          lemma5_8SpongeTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n)
            (pSpec := pSpec) (U := U) (δ := δ) (initSponge := (D_𝔖 StmtIn U).sample)
            (implSponge := (D_𝔖 StmtIn U).eagerImpl) V maliciousProver]
        / capacitySpaceSize (U := U) := by
  classical
  let exp := lemma5_8SpongeTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n)
    (pSpec := pSpec) (U := U) (δ := δ) (initSponge := (D_𝔖 StmtIn U).sample)
    (implSponge := (D_𝔖 StmtIn U).eagerImpl) V maliciousProver
  let det := spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
    (U := U) (δ := δ) V maliciousProver
  let Qleft : QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
      QueryLog (duplexSpongeChallengeOracle StmtIn U) → Prop :=
    fun tr => E_first_at (tr.1 ++ tr.2) j ∧
      hashOutCapAt (getBaseTrace (tr.1 ++ tr.2)) j = some c ∧
      priorCapacityTargetAt (getBaseTrace (tr.1 ++ tr.2)) j i = some c
  let Qtarget : QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
      QueryLog (duplexSpongeChallengeOracle StmtIn U) → Prop :=
    fun tr => priorCapacityTargetAt (getBaseTrace (tr.1 ++ tr.2)) j i = some c
  have hLeftMap :
      Pr[ Qleft | exp] =
        Pr[ Qleft ∘ det | (D_𝔖 StmtIn U).sample] := by
    exact probEvent_lemma5_8SpongeTraceDist_eq_map
      (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
      (U := U) (δ := δ) V maliciousProver Qleft
  have hTargetMap :
      Pr[ Qtarget | exp] =
        Pr[ Qtarget ∘ det | (D_𝔖 StmtIn U).sample] := by
    exact probEvent_lemma5_8SpongeTraceDist_eq_map
      (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
      (U := U) (δ := δ) V maliciousProver Qtarget
  rw [hLeftMap, hTargetMap]
  let sampleP : ProbComp (Equiv.Perm (CanonicalSpongeState U)) :=
    ($ᵗ (Equiv.Perm (CanonicalSpongeState U)))
  rw [show (D_𝔖 StmtIn U).sample =
      (do
        let h ← $ᵗ (OracleReduction.OracleFamily (StmtIn →ₒ Vector U SpongeSize.C))
        let p ← sampleP
        pure (h, p)) by rfl]
  let P : (StmtIn → Vector U SpongeSize.C) × Equiv.Perm (CanonicalSpongeState U) → Prop :=
    fun hp => Qtarget (det hp)
  let read : (StmtIn → Vector U SpongeSize.C) × Equiv.Perm (CanonicalSpongeState U) →
      Option StmtIn :=
    fun hp => hashQueryAt (getBaseTrace ((det hp).1 ++ (det hp).2)) j
  calc
    Pr[ Qleft ∘ det |
        (do
          let h ← $ᵗ (OracleReduction.OracleFamily (StmtIn →ₒ Vector U SpongeSize.C))
          let p ← sampleP
          pure (h, p)) ]
        ≤ Pr[ fun hp => P hp ∧ ∃ q : StmtIn, read hp = some q ∧ hp.1 q = c |
            (do
              let h ← $ᵗ (StmtIn → Vector U SpongeSize.C)
              let p ← sampleP
              pure (h, p)) ] := by
          apply probEvent_mono
          intro hp _ hAtom
          rcases hp with ⟨h, p⟩
          rcases hAtom with ⟨_hFirst, hout, htarget⟩
          obtain ⟨q, hq⟩ := exists_hashQueryAt_of_hashOutCapAt hout
          dsimp [det] at hout htarget hq
          have houtTable := spongeDetTrace_hashQuery_output_eq
            (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
            (U := U) (δ := δ) V maliciousProver h p j q hq
          have hval : h q = c := by
            rw [hout] at houtTable
            injection houtTable with hcap
            exact hcap.symm
          exact ⟨htarget, q, hq, hval⟩
    _ ≤ Pr[ fun hp => P hp |
            (do
              let h ← $ᵗ (StmtIn → Vector U SpongeSize.C)
              let p ← sampleP
              pure (h, p)) ] /
          (Fintype.card (Vector U SpongeSize.C) : ℝ≥0∞) := by
          exact probEvent_uniformFn_prod_freshOptionalCoord_le
            (side := sampleP) (P := P) (read := read) (c := c)
            (by
              intro p g q v
              exact hinv p g q v)
    _ = Pr[ fun hp => P hp |
            (do
              let h ← $ᵗ (OracleReduction.OracleFamily (StmtIn →ₒ Vector U SpongeSize.C))
              let p ← sampleP
              pure (h, p)) ] / capacitySpaceSize (U := U) := by
          have hcapacityCard :
              (@Fintype.card (Vector U SpongeSize.C) Vector.instFintype : ℝ≥0∞) =
                capacitySpaceSize (U := U) := by
            have hcardVec :
                @Fintype.card (Vector U SpongeSize.C) Vector.instFintype =
                  Fintype.card (Fin SpongeSize.C → U) := by
              exact Fintype.card_congr
                (Equiv.rootVectorEquivFin (α := U) (n := SpongeSize.C))
            rw [hcardVec, Fintype.card_fun, Fintype.card_fin, capacitySpaceSize, Nat.cast_pow]
          rw [hcapacityCard]

/-- Sponge hash atom freshness.  At a first bad index, the hash answer capacity at `j` is fresh
relative to each fixed prior capacity-target readout.  This is the experiment-specific
ROM-causality obligation; the finite `2*j` counting is handled by
`sponge_hashFreshHit_first_le`. -/
lemma sponge_hashTargetAtom_first_le
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (j : ℕ) (i : Fin (2 * j)) (c : Vector U SpongeSize.C) :
    Pr[ fun tr =>
        E_first_at (tr.1 ++ tr.2) j ∧
          hashOutCapAt (getBaseTrace (tr.1 ++ tr.2)) j = some c ∧
          priorCapacityTargetAt (getBaseTrace (tr.1 ++ tr.2)) j i = some c |
        lemma5_8SpongeTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n)
          (pSpec := pSpec) (U := U) (δ := δ) (initSponge := (D_𝔖 StmtIn U).sample)
          (implSponge := (D_𝔖 StmtIn U).eagerImpl) V maliciousProver]
      ≤ Pr[ fun tr =>
          priorCapacityTargetAt (getBaseTrace (tr.1 ++ tr.2)) j i = some c |
          lemma5_8SpongeTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n)
            (pSpec := pSpec) (U := U) (δ := δ) (initSponge := (D_𝔖 StmtIn U).sample)
            (implSponge := (D_𝔖 StmtIn U).eagerImpl) V maliciousProver]
        / capacitySpaceSize (U := U) := by
  exact sponge_hashTargetAtom_first_le_of_update_invariant
    (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
    (U := U) (δ := δ) V maliciousProver j i c (by
      intro p g q v
      let fam₁ : (D_𝔖 StmtIn U).Carrier := (Function.update g q v, p)
      let fam₀ : (D_𝔖 StmtIn U).Carrier := (g, p)
      constructor
      · intro h
        exact sponge_hashTarget_hashQuery_transfer_of_agree_off_hash
          (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
          (U := U) (δ := δ) V maliciousProver fam₁ fam₀ q j i c (by
            intro dom hbad
            cases dom with
            | inl q' =>
                have hneq : q' ≠ q := by
                  intro hq'
                  subst q'
                  simp at hbad
                change Function.update g q v q' = g q'
                rw [Function.update_apply, if_neg hneq]
            | inr permDom =>
                cases permDom <;> simp [fam₁, fam₀, spongeAnswer]) h
      · intro h
        exact sponge_hashTarget_hashQuery_transfer_of_agree_off_hash
          (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
          (U := U) (δ := δ) V maliciousProver fam₀ fam₁ q j i c (by
            intro dom hbad
            cases dom with
            | inl q' =>
                have hneq : q' ≠ q := by
                  intro hq'
                  subst q'
                  simp at hbad
                change g q' = Function.update g q v q'
                rw [Function.update_apply, if_neg hneq]
            | inr permDom =>
                cases permDom <;> simp [fam₁, fam₀, spongeAnswer]) h)

/-- Sponge trace core gap: The probability that a fresh hash query hits a prior
target capacity at index `j` is bounded by `2j/|Σ|^c`, since there are at most `2j` targets. -/
lemma sponge_hashFreshHit_first_le
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) (j : ℕ) :
    Pr[ fun tr => E_first_at (tr.1 ++ tr.2) j ∧ hashFreshHitAt (getBaseTrace (tr.1 ++ tr.2)) j |
        lemma5_8SpongeTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n)
          (pSpec := pSpec) (U := U) (δ := δ) (initSponge := (D_𝔖 StmtIn U).sample)
          (implSponge := (D_𝔖 StmtIn U).eagerImpl) V maliciousProver]
      ≤ (2 * (j : ℝ≥0∞)) / capacitySpaceSize (U := U) := by
  let exp := lemma5_8SpongeTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n)
    (pSpec := pSpec) (U := U) (δ := δ) (initSponge := (D_𝔖 StmtIn U).sample)
    (implSponge := (D_𝔖 StmtIn U).eagerImpl) V maliciousProver
  let P : QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
      QueryLog (duplexSpongeChallengeOracle StmtIn U) → Prop :=
    fun tr => E_first_at (tr.1 ++ tr.2) j
  let fresh : QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
      QueryLog (duplexSpongeChallengeOracle StmtIn U) → Option (Vector U SpongeSize.C) :=
    fun tr => hashOutCapAt (getBaseTrace (tr.1 ++ tr.2)) j
  let target : Fin (2 * j) →
      QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
        QueryLog (duplexSpongeChallengeOracle StmtIn U) → Option (Vector U SpongeSize.C) :=
    fun i tr => priorCapacityTargetAt (getBaseTrace (tr.1 ++ tr.2)) j i
  have hHit :
      Pr[ fun tr => E_first_at (tr.1 ++ tr.2) j ∧
          hashFreshHitAt (getBaseTrace (tr.1 ++ tr.2)) j | exp]
        ≤ Pr[ fun tr => P tr ∧ ∃ i : Fin (2 * j), ∃ c : Vector U SpongeSize.C,
          fresh tr = some c ∧ target i tr = some c | exp] := by
    apply probEvent_mono
    intro tr _htr h
    obtain ⟨hFirst, hFresh⟩ := h
    obtain ⟨i, c, hout, htarget⟩ := hashFreshHitAt_imp_exists_target hFresh
    exact ⟨hFirst, i, c, hout, htarget⟩
  have hBound :
      Pr[ fun tr => P tr ∧ ∃ i : Fin (2 * j), ∃ c : Vector U SpongeSize.C,
          fresh tr = some c ∧ target i tr = some c | exp]
        ≤ ((2 * j : ℕ) : ℝ≥0∞) / capacitySpaceSize (U := U) := by
    exact probEvent_pred_fresh_hits_fin_targets_le exp P fresh (2 * j) target
      (capacitySpaceSize (U := U)) (by
        intro i c
        exact sponge_hashTargetAtom_first_le
          (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
          (U := U) (δ := δ) V maliciousProver j i c)
  calc
    Pr[ fun tr => E_first_at (tr.1 ++ tr.2) j ∧
        hashFreshHitAt (getBaseTrace (tr.1 ++ tr.2)) j | exp]
        ≤ Pr[ fun tr => P tr ∧ ∃ i : Fin (2 * j), ∃ c : Vector U SpongeSize.C,
          fresh tr = some c ∧ target i tr = some c | exp] := hHit
    _ ≤ ((2 * j : ℕ) : ℝ≥0∞) / capacitySpaceSize (U := U) := hBound
    _ = (2 * (j : ℝ≥0∞)) / capacitySpaceSize (U := U) := by
      rw [Nat.cast_mul]
      norm_num

/-- Sponge `E_h` bound, refined to the earliest bad index. -/
lemma lemma5_8_sponge_E_h_first_at
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) (j : ℕ) :
    Pr[ fun tr => E_first_at (tr.1 ++ tr.2) j ∧ E_h_at (tr.1 ++ tr.2) j |
        lemma5_8SpongeTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n)
          (pSpec := pSpec) (U := U) (δ := δ) (initSponge := (D_𝔖 StmtIn U).sample)
          (implSponge := (D_𝔖 StmtIn U).eagerImpl) V maliciousProver]
      ≤ (2 * (j : ℝ≥0∞)) / capacitySpaceSize (U := U) := by
  let exp := lemma5_8SpongeTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n)
    (pSpec := pSpec) (U := U) (δ := δ) (initSponge := (D_𝔖 StmtIn U).sample)
    (implSponge := (D_𝔖 StmtIn U).eagerImpl) V maliciousProver
  change Pr[ fun tr => E_first_at (tr.1 ++ tr.2) j ∧ E_h_at (tr.1 ++ tr.2) j | exp]
      ≤ (2 * (j : ℝ≥0∞)) / capacitySpaceSize (U := U)
  calc
    Pr[ fun tr => E_first_at (tr.1 ++ tr.2) j ∧ E_h_at (tr.1 ++ tr.2) j | exp]
      ≤ Pr[ fun tr =>
          E_first_at (tr.1 ++ tr.2) j ∧ hashFreshHitAt (getBaseTrace (tr.1 ++ tr.2)) j |
          exp] := by
      apply probEvent_mono
      intro tr _ h
      rcases h with ⟨hFirst, hEh⟩
      exact ⟨hFirst, E_h_at_imp_hashFreshHitAt _ _ hEh⟩
    _ ≤ (2 * (j : ℝ≥0∞)) / capacitySpaceSize (U := U) :=
      sponge_hashFreshHit_first_le V maliciousProver j

end HashCollisionReduction

end PerIndexCollisionBounds

end BadEventDS

end DuplexSpongeFS
