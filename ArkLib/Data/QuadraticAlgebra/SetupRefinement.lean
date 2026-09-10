/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.QuadraticAlgebra.SetupMachine

/-!
# Same-run quadratic setup correctness

Every base, search, coordinate-enumeration and prefix instruction retains its parent wrapper
charge. Quadratic values are allocated individually. Field certification and sample embeddings
are derived from the actual returned parameter and materialized output.
-/

@[expose] public section

namespace QuadraticAlgebra.SetupMachine

variable {q : ℕ}

private theorem embed_add (c e : ZMod.EnumerationMachine.Cost) :
    embed (c + e) = embed c + embed e := by rfl
private theorem embed_total (c : ZMod.EnumerationMachine.Cost) :
    (embed c).total = EnumerationMachine.totalCost c := by
  simp [embed, ZMod.NonsquareSearchMachine.Cost.total, EnumerationMachine.totalCost]

private theorem charge_total (n k d o : ℕ) : (charge n k d o).total = n + k + 1 + d + o := by
  simp [charge, ZMod.NonsquareSearchMachine.Cost.total]

/-- Exact proof-only vector for the wrappers of `k` delegated instructions. -/
def wrappers (k : ℕ) : Cost := ⟨0, 0, 0, 0, 0, k, 2 * k, 0⟩

private theorem wrappers_succ (k : ℕ) (c e : Cost) :
    wrappers (k + 1) + (c + e) = (wrapper + c) + (wrappers k + e) := by
  ext <;> simp [wrappers, wrapper, charge, ZMod.NonsquareSearchMachine.cost_add,
    Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem wrappers_total (k : ℕ) : (wrappers k).total = 3 * k := by
  simp [wrappers, ZMod.NonsquareSearchMachine.Cost.total]
  omega

private theorem lift_base (L fuel : ℕ) (s : ZMod.EnumerationMachine.Configuration q) :
    ∃ k ≤ fuel, Trace L k (.base s) (wrappers k + embed (ZMod.EnumerationMachine.runFuel fuel s).2)
      (.base (ZMod.EnumerationMachine.runFuel fuel s).1) := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, by
      simpa [wrappers, ZMod.EnumerationMachine.runFuel, embed]
        using (Trace.nil (.base s))⟩
  | succ fuel ih =>
      cases hs : ZMod.EnumerationMachine.step s with
      | none => exact ⟨0, Nat.zero_le _, by
          simpa [wrappers, ZMod.EnumerationMachine.runFuel, hs, embed]
            using (Trace.nil (.base s))⟩
      | some z =>
          obtain ⟨k, hk, ht⟩ := ih z.1
          exact ⟨k + 1, Nat.succ_le_succ hk, by
            simpa only [ZMod.EnumerationMachine.runFuel, hs, embed_add, wrappers_succ] using
              Trace.cons (Step.base hs) ht⟩

private theorem lift_search (L fuel : ℕ) (bs : List (ZMod q))
    (s : ZMod.NonsquareSearchMachine.Configuration q) :
    ∃ k ≤ fuel, Trace L k (.search bs s)
      (wrappers k + (ZMod.NonsquareSearchMachine.runFuel fuel s).2)
      (.search bs (ZMod.NonsquareSearchMachine.runFuel fuel s).1) := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, by
      simpa [wrappers, ZMod.NonsquareSearchMachine.runFuel]
        using (Trace.nil (.search bs s))⟩
  | succ fuel ih =>
      cases hs : ZMod.NonsquareSearchMachine.step s with
      | none => exact ⟨0, Nat.zero_le _, by
          simpa [wrappers, ZMod.NonsquareSearchMachine.runFuel, hs]
            using (Trace.nil (.search bs s))⟩
      | some z =>
          obtain ⟨k, hk, ht⟩ := ih z.1
          exact ⟨k + 1, Nat.succ_le_succ hk, by
            simpa only [ZMod.NonsquareSearchMachine.runFuel, hs, wrappers_succ] using
              Trace.cons (Step.search hs) ht⟩

private theorem lift_pairs (L fuel : ℕ) (a : ZMod q) (bs : List (ZMod q))
    (s : EnumerationMachine.Configuration q) :
    ∃ k ≤ fuel, Trace L k (.pairs a bs s) (wrappers k + embed (EnumerationMachine.runFuel fuel s).2)
      (.pairs a bs (EnumerationMachine.runFuel fuel s).1) := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, by
      simpa [wrappers, EnumerationMachine.runFuel, embed]
        using (Trace.nil (.pairs a bs s))⟩
  | succ fuel ih =>
      cases hs : EnumerationMachine.step s with
      | none => exact ⟨0, Nat.zero_le _, by
          simpa [wrappers, EnumerationMachine.runFuel, hs, embed]
            using (Trace.nil (.pairs a bs s))⟩
      | some z =>
          obtain ⟨k, hk, ht⟩ := ih z.1
          exact ⟨k + 1, Nat.succ_le_succ hk, by
            simpa only [EnumerationMachine.runFuel, hs, embed_add, wrappers_succ] using
              Trace.cons (Step.pairs hs) ht⟩

private theorem lift_prefix (L fuel : ℕ) (a : ZMod q) (bs : List (ZMod q))
    (alphabet : List (Element q a)) (n : ℕ) (s : List.PrefixMachine.Configuration (Element q a)) :
    ∃ k ≤ fuel, Trace L k (.prefix a bs alphabet n s)
      (wrappers k + (List.PrefixMachine.runFuel fuel s).2)
      (.prefix a bs alphabet n (List.PrefixMachine.runFuel fuel s).1) := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, by
      simpa [wrappers, List.PrefixMachine.runFuel]
        using (Trace.nil (.prefix a bs alphabet n s))⟩
  | succ fuel ih =>
      cases hs : List.PrefixMachine.step s with
      | none => exact ⟨0, Nat.zero_le _, by
          simpa [wrappers, List.PrefixMachine.runFuel, hs]
            using (Trace.nil (.prefix a bs alphabet n s))⟩
      | some z =>
          obtain ⟨k, hk, ht⟩ := ih z.1
          exact ⟨k + 1, Nat.succ_le_succ hk, by
            simpa only [List.PrefixMachine.runFuel, hs, wrappers_succ] using
              Trace.cons (Step.prefix hs) ht⟩

private theorem base_ready (L : ℕ) (hq : 0 < q) :
    ∃ bs k c, Trace L k (.base .start) c (.search bs .start) ∧
      bs.length = q ∧ bs.Nodup ∧ (∀ x : ZMod q, x ∈ bs) ∧
      k + c.total ≤ 16 * (4 * q + 3) + 5 := by
  obtain ⟨bs, hr, hl, hn, ha⟩ := ZMod.EnumerationMachine.enumeration_correct q hq
  obtain ⟨k, hk, ht⟩ := lift_base L (4 * q + 3) .start
  rw [hr] at ht
  refine ⟨bs, k + 1, (wrappers k + embed (ZMod.EnumerationMachine.enumerationCost q)) +
    charge 0 0 3 0, ht.trans (Trace.cons Step.based (Trace.nil _)), hl, hn, ha, ?_⟩
  simp only [ZMod.NonsquareSearchMachine.total_add, wrappers_total, charge_total, embed_total]
  simp only [EnumerationMachine.totalCost, ZMod.EnumerationMachine.enumerationCost]
  omega

private theorem parameter_ready (L : ℕ) (bs : List (ZMod q)) (hq : q.Prime) (hodd : q ≠ 2) :
    ∃ a k c, Trace L k (.search bs .start) c (.pairs a bs .start) ∧ ¬IsSquare a ∧
      k + c.total ≤ 16 * ZMod.NonsquareSearchMachine.searchFuel q + 6 := by
  obtain ⟨a, ha, hn, _⟩ := ZMod.NonsquareSearchMachine.search_correct q hq hodd
  rw [ZMod.NonsquareSearchMachine.search_eq_spec] at ha
  obtain ⟨c, hr, hc⟩ := ZMod.NonsquareSearchMachine.search_runFuel q
  rw [ha] at hr
  obtain ⟨k, hk, ht⟩ := lift_search L (ZMod.NonsquareSearchMachine.searchFuel q) bs .start
  rw [hr] at ht
  refine ⟨a, k + 1, (wrappers k + c) + charge 0 0 4 0,
    ht.trans (Trace.cons Step.parameter (Trace.nil _)), hn, ?_⟩
  simp only [ZMod.NonsquareSearchMachine.total_add, wrappers_total, charge_total]
  omega

private theorem pairs_ready (L : ℕ) (a : ZMod q) (bs : List (ZMod q)) (hq : 0 < q) :
    ∃ ps k c, Trace L k (.pairs a bs .start) c (.decode a bs ps [] 0) ∧
      ps.length = q ^ 2 ∧ ps.Nodup ∧ (∀ p : ZMod q × ZMod q, p ∈ ps) ∧
      k + c.total ≤ 16 * EnumerationMachine.enumerationFuel q + 8 := by
  obtain ⟨ps, c, hr, hl, hn, ha, hc⟩ := EnumerationMachine.enumeration_correct q hq
  obtain ⟨k, hk, ht⟩ := lift_pairs L (EnumerationMachine.enumerationFuel q) a bs .start
  rw [hr] at ht
  refine ⟨ps, k + 1, (wrappers k + embed c) + charge 0 2 4 0,
    ht.trans (Trace.cons Step.paired (Trace.nil _)), hl, hn, ha, ?_⟩
  simp only [ZMod.NonsquareSearchMachine.total_add, wrappers_total, charge_total, embed_total]
  unfold EnumerationMachine.enumerationFuel at hk ⊢
  omega

private theorem reverse_ready (L : ℕ) (a : ZMod q) (bs : List (ZMod q))
    (pre out : List (Element q a)) (n : ℕ) :
    ∃ k c, Trace L k (.reverse a bs pre out n) c
      (.prefix a bs (pre.reverse ++ out) n (.scan L (pre.reverse ++ out) [] 0)) ∧
      k + c.total ≤ 7 * pre.length + 9 := by
  induction pre generalizing out with
  | nil =>
      refine ⟨1, charge 0 2 5 0, Trace.cons Step.reversed (Trace.nil _), ?_⟩
      simp [charge_total]
  | cons z pre ih =>
      obtain ⟨k, c, ht, hc⟩ := ih (z :: out)
      refine ⟨k + 1, charge 0 0 5 0 + c, ?_, ?_⟩
      · simpa [List.reverse_cons, List.append_assoc] using Trace.cons Step.reverse ht
      · simp only [ZMod.NonsquareSearchMachine.total_add, charge_total, List.length_cons]
        omega

/-- All quadratic objects and list cells are allocated by actual transitions. -/
theorem decode_ready (L : ℕ) (a : ZMod q) (bs : List (ZMod q)) (ps : List (ZMod q × ZMod q))
    (pre : List (Element q a)) (n : ℕ) :
    ∃ k c, Trace L k (.decode a bs ps pre n) c
      (.prefix a bs (pre.reverse ++ ps.map (EnumerationMachine.decode a)) (n + ps.length)
        (.scan L (pre.reverse ++ ps.map (EnumerationMachine.decode a)) [] 0)) ∧
      k + c.total ≤ 23 * ps.length + 7 * pre.length + 14 := by
  induction ps generalizing pre n with
  | nil =>
      obtain ⟨k, c, ht, hc⟩ := reverse_ready L a bs pre [] n
      refine ⟨k + 1, charge 0 0 3 0 + c, ?_, ?_⟩
      · simpa using Trace.cons Step.decoded ht
      · simp only [ZMod.NonsquareSearchMachine.total_add, charge_total]
        omega
  | cons p ps ih =>
      obtain ⟨k, c, ht, hc⟩ := ih (EnumerationMachine.decode a p :: pre) (n + 1)
      refine ⟨k + 1 + 1, charge 0 0 6 0 + (charge 1 0 5 0 + c), ?_, ?_⟩
      · simpa [EnumerationMachine.decode, List.reverse_cons, List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          Trace.cons Step.decode (Trace.cons Step.save ht)
      · simp only [ZMod.NonsquareSearchMachine.total_add, charge_total, List.length_cons] at hc ⊢
        omega

private theorem prefix_ready (L : ℕ) (a : ZMod q) (bs : List (ZMod q))
    (alphabet : List (Element q a)) (n : ℕ) (hL : L ≤ alphabet.length) :
    ∃ k c, Trace L k (.prefix a bs alphabet n (.scan L alphabet [] 0)) c
      (.done (some ⟨a, ⟨bs, alphabet, alphabet.take L, q, n, L⟩⟩)) ∧
      k + c.total ≤ 5 * List.PrefixMachine.budget L + 13 := by
  obtain ⟨c, hr, hc⟩ := List.PrefixMachine.evaluation_runFuel L alphabet hL
  obtain ⟨k, hk, ht⟩ :=
    lift_prefix L (List.PrefixMachine.budget L) a bs alphabet n (.scan L alphabet [] 0)
  rw [hr] at ht
  refine ⟨k + 1, (wrappers k + c) + charge 0 0 10 1,
    ht.trans (Trace.cons Step.prepared (Trace.nil _)), ?_⟩
  simp only [ZMod.NonsquareSearchMachine.total_add, wrappers_total, charge_total]
  omega

/-- Polynomial bound for both execution length and the complete primitive ledger. -/
def budget (q L : ℕ) : ℕ :=
  16 * ((4 * q + 3) + ZMod.NonsquareSearchMachine.searchFuel q +
    EnumerationMachine.enumerationFuel q) + 23 * q ^ 2 + 5 * List.PrefixMachine.budget L + 60

/-- The bound is quadratic in the base size and linear in the sample count. -/
theorem budget_eq (q L : ℕ) : budget q L = 167 * q ^ 2 + 176 * q + 90 * L + 248 := by
  simp only [budget, ZMod.NonsquareSearchMachine.searchFuel,
    EnumerationMachine.enumerationFuel, List.PrefixMachine.budget]
  ring

/-- Integrity and completeness of the actual materialized output. -/
structure Correct (L : ℕ) (a : ZMod q) (data : Prepared q a) : Prop where
  nonsquare : ¬IsSquare a
  base_count : data.baseCount = q
  base_length : data.base.length = data.baseCount
  base_nodup : data.base.Nodup
  base_complete : ∀ x, x ∈ data.base
  extension_count : data.extensionCount = q ^ 2
  extension_length : data.alphabet.length = data.extensionCount
  extension_nodup : data.alphabet.Nodup
  extension_complete : ∀ x, x ∈ data.alphabet
  sample_count : data.sampleCount = L
  sample_length : data.samples.length = data.sampleCount
  sample_nodup : data.samples.Nodup
  samples_prefix : data.samples = data.alphabet.take L
  samples_embedding : ∃ points : Fin L ↪ Element q a, data.samples = List.ofFn points

/-- One trace performs the search, both enumerations, allocations and sample traversal. -/
theorem preparation_trace (L : ℕ) (hq : q.Prime) (hodd : q ≠ 2) (hL : L ≤ q ^ 2) :
    ∃ (a : ZMod q) (data : Prepared q a) (k : ℕ) (c : Cost),
      Trace L k (.base .start) c (.done (some ⟨a, data⟩)) ∧
      Correct L a data ∧ k + c.total ≤ budget q L := by
  obtain ⟨bs, kb, cb, hb, hbl, hbn, hba, hbc⟩ := base_ready L hq.pos
  obtain ⟨a, ks, cs, hs, ha, hsc⟩ := parameter_ready L bs hq hodd
  obtain ⟨ps, kp, cp, hp, hpl, hpn, hpa, hpc⟩ := pairs_ready L a bs hq.pos
  obtain ⟨kd, cd, hd, hdc⟩ := decode_ready L a bs ps [] 0
  simp only [List.reverse_nil, List.nil_append, Nat.zero_add] at hd
  let alphabet := ps.map (EnumerationMachine.decode a)
  have hal : alphabet.length = q ^ 2 := by simp [alphabet, hpl]
  have han : alphabet.Nodup := hpn.map (EnumerationMachine.decode_injective a)
  have haa : ∀ x, x ∈ alphabet := by
    intro x
    obtain ⟨p, rfl⟩ := EnumerationMachine.decode_surjective a x
    exact List.mem_map.mpr ⟨p, hpa p, rfl⟩
  have hLa : L ≤ alphabet.length := by omega
  obtain ⟨kr, cr, hr, hrc⟩ := prefix_ready L a bs alphabet ps.length hLa
  refine ⟨a, ⟨bs, alphabet, alphabet.take L, q, ps.length, L⟩,
    kb + (ks + (kp + (kd + kr))), cb + (cs + (cp + (cd + cr))),
    hb.trans (hs.trans (hp.trans (hd.trans hr))), ?_, ?_⟩
  · exact ⟨ha, rfl, hbl, hbn, hba, hpl, List.length_map _, han, haa, rfl,
      List.length_take_of_le hLa, (List.take_sublist L alphabet).nodup han, rfl,
      List.PrefixMachine.prefix_embedding L alphabet han hLa⟩
  · simp only [ZMod.NonsquareSearchMachine.total_add]
    simp only [List.length_nil, Nat.mul_zero, Nat.add_zero, hpl] at hdc
    unfold budget
    omega

/-- Prime odd setup succeeds in the same bounded run with its entire ledger charged. -/
theorem setup_correct (L : ℕ) (hq : q.Prime) (hodd : q ≠ 2) (hL : L ≤ q ^ 2) :
    ∃ (a : ZMod q) (data : Prepared q a) (c : Cost),
      runFuel L (budget q L) (.base .start) = (.done (some ⟨a, data⟩), c) ∧
      Correct L a data ∧ c.total ≤ budget q L := by
  obtain ⟨a, data, k, c, ht, hd, hc⟩ := preparation_trace L hq hodd hL
  have he := ht.runFuel_done (budget q L - k)
  rw [show k + (budget q L - k) = budget q L by omega] at he
  exact ⟨a, data, c, he, hd, by omega⟩

/-- Proof-only certification uses the parameter actually found by the search. -/
abbrev certifiedField (hq : q.Prime) (a : ZMod q) (ha : ¬IsSquare a) : Field (Element q a) := by
  letI : Fact q.Prime := ⟨hq⟩
  exact QuadraticAlgebra.fieldOfNonsquare a ha

end QuadraticAlgebra.SetupMachine
