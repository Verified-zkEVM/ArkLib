/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.SampleProduct

/-!
# Fixed-history permutation reprogramming for the H₀--H₁ coupling

The H₀--H₁ lazy-sampling proof will reprogram an eager permutation at a fresh forward
input `x` so that its output is the coupled H₁ proposal `y`.  This file records only
the finite change-of-variables core for one *fixed* exposed history: if the proposal
is uniform, the reprogrammed full permutation still has the uniform marginal.

This is not a deferred-decision theorem for an adaptive execution.  In particular, it
does not prove the conditional permutation law after a history whose answers have
already been revealed, it does not compose several steps, and it does not complete
either marginal after the first stop.  Those obligations belong to the single live
H₀/H₁ joint executor that consumes these local maps.
-/

noncomputable section

open OracleComp

namespace DuplexSpongeFS

namespace KeyLemma

/-- Reprogram the forward image of `x` to `y` by swapping the old and new images. -/
def forwardReprogram {α : Type} [DecidableEq α] (x : α)
    (pair : Equiv.Perm α × α) : Equiv.Perm α :=
  pair.1.trans (Equiv.swap (pair.1 x) pair.2)

/-- The auxiliary old image makes forward reprogramming a bijection on the sampling space.
The first component is the reprogrammed permutation; the second remembers its former image
at `x`. -/
def forwardReprogramWithOldImage {α : Type} [DecidableEq α] (x : α)
    (pair : Equiv.Perm α × α) :
    Equiv.Perm α × α :=
  (forwardReprogram x pair, pair.1 x)

/-- The programmed forward input receives exactly the requested image. -/
lemma forwardReprogram_apply_programmed {α : Type} [DecidableEq α]
    (x y : α) (p : Equiv.Perm α) :
    forwardReprogram x (p, y) x = y := by
  simp [forwardReprogram, Equiv.trans_apply]

/-- A forward reprogram leaves an earlier mapping unchanged whenever neither its input nor its
image is one of the two swapped values. -/
lemma forwardReprogram_apply_eq_of_ne {α : Type} [DecidableEq α]
    (x y state : α) (p : Equiv.Perm α)
    (hstate : state ≠ x) (himage : p state ≠ y) :
    forwardReprogram x (p, y) state = p state := by
  unfold forwardReprogram
  rw [Equiv.trans_apply]
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    exact hstate (p.injective h)
  · exact himage

/-- A forward reprogram also leaves an earlier inverse answer unchanged outside the two swapped
images. -/
lemma forwardReprogram_symm_apply_eq_of_ne {α : Type} [DecidableEq α]
    (x y output : α) (p : Equiv.Perm α)
    (holdImage : output ≠ p x) (hnewImage : output ≠ y) :
    (forwardReprogram x (p, y)).symm output = p.symm output := by
  unfold forwardReprogram
  rw [Equiv.symm_trans_apply]
  change p.symm ((Equiv.swap (p x) y) output) = p.symm output
  congr 1
  exact Equiv.swap_apply_of_ne_of_ne holdImage hnewImage

/-- A fresh forward reprogram preserves every already-realized forward table entry.  This is the
partial-bijection invariant used by the H₀/H₁ coupling: `entries` may be the normalized table of
all previously exposed permutation pairs, while `x` and `y` are respectively fresh for its domain
and range. -/
lemma forwardReprogram_preserves_forward_table {α : Type} [DecidableEq α]
    (x y : α) (p : Equiv.Perm α) (entries : List (α × α))
    (hrealizes : ∀ entry ∈ entries, p entry.1 = entry.2)
    (hfreshInput : ∀ entry ∈ entries, entry.1 ≠ x)
    (hfreshOutput : ∀ entry ∈ entries, entry.2 ≠ y) :
    ∀ entry ∈ entries, forwardReprogram x (p, y) entry.1 = entry.2 := by
  intro entry hentry
  rw [forwardReprogram_apply_eq_of_ne x y entry.1 p
    (hfreshInput entry hentry)]
  · exact hrealizes entry hentry
  · rw [hrealizes entry hentry]
    exact hfreshOutput entry hentry

/-- A fresh forward reprogram also preserves every already-realized inverse table entry.  The
same domain/range freshness is written in the inverse table's natural `(output, input)` order. -/
lemma forwardReprogram_preserves_inverse_table {α : Type} [DecidableEq α]
    (x y : α) (p : Equiv.Perm α) (entries : List (α × α))
    (hrealizes : ∀ entry ∈ entries, p entry.2 = entry.1)
    (hfreshInput : ∀ entry ∈ entries, entry.2 ≠ x)
    (hfreshOutput : ∀ entry ∈ entries, entry.1 ≠ y) :
    ∀ entry ∈ entries, (forwardReprogram x (p, y)).symm entry.1 = entry.2 := by
  intro entry hentry
  have holdImage : entry.1 ≠ p x := by
    intro hEq
    apply hfreshInput entry hentry
    apply p.injective
    rw [hrealizes entry hentry, hEq]
  rw [forwardReprogram_symm_apply_eq_of_ne x y entry.1 p holdImage
    (hfreshOutput entry hentry)]
  apply p.injective
  rw [p.apply_symm_apply, hrealizes entry hentry]

/-- The exact change of variables behind deferred forward permutation programming. -/
noncomputable def forwardReprogramEquiv {α : Type} [DecidableEq α] (x : α) :
    (Equiv.Perm α × α) ≃ (Equiv.Perm α × α) where
  toFun := forwardReprogramWithOldImage x
  invFun := fun pair =>
    (pair.1.trans (Equiv.swap pair.2 (pair.1 x)), pair.1 x)
  left_inv := by
    intro pair
    rcases pair with ⟨p, y⟩
    apply Prod.ext
    · ext state
      simp [forwardReprogramWithOldImage, forwardReprogram, Equiv.trans_apply]
    · simp [forwardReprogramWithOldImage, forwardReprogram, Equiv.trans_apply]
  right_inv := by
    intro pair
    rcases pair with ⟨p, oldImage⟩
    apply Prod.ext
    · ext state
      simp [forwardReprogramWithOldImage, forwardReprogram, Equiv.trans_apply]
    · simp [forwardReprogramWithOldImage, forwardReprogram, Equiv.trans_apply]

/-- Sampling an eager permutation and a uniform proposed image, then programming that image at
`x`, leaves the eager-permutation marginal exactly uniform.  This is the one-step marginal
completion fact required after every fresh H₁ forward proposal. -/
theorem evalDist_forwardReprogram_uniform
    {α : Type} [Finite α] [DecidableEq α] [Nonempty α]
    [SampleableType α] [SampleableType (Equiv.Perm α)]
    [SampleableType (Equiv.Perm α × α)]
    (x : α) :
    evalDist
        (forwardReprogram x <$> ($ᵗ (Equiv.Perm α × α))) =
      evalDist ($ᵗ (Equiv.Perm α)) := by
  let reprogram := forwardReprogramEquiv x
  have hReprogram :
      evalDist (reprogram <$> ($ᵗ (Equiv.Perm α × α))) =
        evalDist ($ᵗ (Equiv.Perm α × α)) :=
    evalDist_map_bijective_uniform_cross
      (α := Equiv.Perm α × α) (β := Equiv.Perm α × α)
      reprogram reprogram.bijective
  calc
    evalDist (forwardReprogram x <$> ($ᵗ (Equiv.Perm α × α))) =
        evalDist (Prod.fst <$> (reprogram <$> ($ᵗ (Equiv.Perm α × α)))) := by
          congr 1
          simp only [Functor.map_map]
          rfl
    _ = evalDist (Prod.fst <$> ($ᵗ (Equiv.Perm α × α))) :=
      evalDist_map_eq_of_evalDist_eq hReprogram Prod.fst
    _ = evalDist ($ᵗ (Equiv.Perm α)) :=
      evalDist_map_fst_uniformSample_prod

/-- Reprogram the inverse image of `y` to `x` by swapping the old and new preimages. -/
def inverseReprogram {α : Type} [DecidableEq α] (y : α)
    (pair : Equiv.Perm α × α) : Equiv.Perm α :=
  (Equiv.swap (pair.1.symm y) pair.2).trans pair.1

/-- The old preimage makes inverse reprogramming a bijection on the sampling space. -/
def inverseReprogramWithOldPreimage {α : Type} [DecidableEq α] (y : α)
    (pair : Equiv.Perm α × α) : Equiv.Perm α × α :=
  (inverseReprogram y pair, pair.1.symm y)

/-- The programmed inverse input receives exactly the requested image. -/
lemma inverseReprogram_apply_programmed {α : Type} [DecidableEq α]
    (y x : α) (p : Equiv.Perm α) :
    inverseReprogram y (p, x) x = y := by
  simp [inverseReprogram, Equiv.trans_apply]

/-- Equivalently, the programmed inverse query returns the requested preimage. -/
lemma inverseReprogram_symm_apply_programmed {α : Type} [DecidableEq α]
    (y x : α) (p : Equiv.Perm α) :
    (inverseReprogram y (p, x)).symm y = x := by
  apply (inverseReprogram y (p, x)).injective
  rw [inverseReprogram_apply_programmed]
  exact (inverseReprogram y (p, x)).apply_symm_apply y

/-- An inverse reprogram leaves an earlier mapping unchanged whenever neither its input nor its
image is one of the two swapped values. -/
lemma inverseReprogram_apply_eq_of_ne {α : Type} [DecidableEq α]
    (y x state : α) (p : Equiv.Perm α)
    (hstate : state ≠ x) (himage : p state ≠ y) :
    inverseReprogram y (p, x) state = p state := by
  unfold inverseReprogram
  change p ((Equiv.swap (p.symm y) x) state) = p state
  congr 1
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    apply himage
    rw [h, p.apply_symm_apply]
  · exact hstate

/-- An inverse reprogram also leaves an earlier inverse answer unchanged outside the two swapped
preimages. -/
lemma inverseReprogram_symm_apply_eq_of_ne {α : Type} [DecidableEq α]
    (y x output : α) (p : Equiv.Perm α)
    (holdImage : output ≠ y) (hnewPreimage : p.symm output ≠ x) :
    (inverseReprogram y (p, x)).symm output = p.symm output := by
  unfold inverseReprogram
  rw [Equiv.symm_trans_apply]
  change (Equiv.swap (p.symm y) x) (p.symm output) = p.symm output
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    apply holdImage
    exact p.symm.injective h
  · exact hnewPreimage

/-- A fresh inverse reprogram preserves every already-realized forward table entry. -/
lemma inverseReprogram_preserves_forward_table {α : Type} [DecidableEq α]
    (y x : α) (p : Equiv.Perm α) (entries : List (α × α))
    (hrealizes : ∀ entry ∈ entries, p entry.1 = entry.2)
    (hfreshInput : ∀ entry ∈ entries, entry.1 ≠ x)
    (hfreshOutput : ∀ entry ∈ entries, entry.2 ≠ y) :
    ∀ entry ∈ entries, inverseReprogram y (p, x) entry.1 = entry.2 := by
  intro entry hentry
  rw [inverseReprogram_apply_eq_of_ne y x entry.1 p
    (hfreshInput entry hentry)]
  · exact hrealizes entry hentry
  · rw [hrealizes entry hentry]
    exact hfreshOutput entry hentry

/-- A fresh inverse reprogram preserves every already-realized inverse table entry. -/
lemma inverseReprogram_preserves_inverse_table {α : Type} [DecidableEq α]
    (y x : α) (p : Equiv.Perm α) (entries : List (α × α))
    (hrealizes : ∀ entry ∈ entries, p entry.2 = entry.1)
    (hfreshInput : ∀ entry ∈ entries, entry.2 ≠ x)
    (hfreshOutput : ∀ entry ∈ entries, entry.1 ≠ y) :
    ∀ entry ∈ entries, (inverseReprogram y (p, x)).symm entry.1 = entry.2 := by
  intro entry hentry
  rw [inverseReprogram_symm_apply_eq_of_ne y x entry.1 p
    (hfreshOutput entry hentry)]
  · apply p.injective
    rw [p.apply_symm_apply, hrealizes entry hentry]
  · intro hEq
    apply hfreshInput entry hentry
    calc
      entry.2 = p.symm (p entry.2) := (p.symm_apply_apply entry.2).symm
      _ = p.symm entry.1 := by rw [hrealizes entry hentry]
      _ = x := hEq

/-- The exact change of variables behind deferred inverse permutation programming. -/
noncomputable def inverseReprogramEquiv {α : Type} [DecidableEq α] (y : α) :
    (Equiv.Perm α × α) ≃ (Equiv.Perm α × α) where
  toFun := inverseReprogramWithOldPreimage y
  invFun := fun pair =>
    ((Equiv.swap pair.2 (pair.1.symm y)).trans pair.1, pair.1.symm y)
  left_inv := by
    intro pair
    rcases pair with ⟨p, x⟩
    apply Prod.ext
    · ext state
      simp [inverseReprogramWithOldPreimage, inverseReprogram, Equiv.trans_apply]
    · simp [inverseReprogramWithOldPreimage, inverseReprogram]
  right_inv := by
    intro pair
    rcases pair with ⟨p, oldPreimage⟩
    apply Prod.ext
    · ext state
      simp [inverseReprogramWithOldPreimage, inverseReprogram, Equiv.trans_apply]
    · simp [inverseReprogramWithOldPreimage, inverseReprogram]

/-- Sampling an eager permutation and a uniform proposed preimage, then programming that
preimage at `y`, leaves the eager-permutation marginal exactly uniform. -/
theorem evalDist_inverseReprogram_uniform
    {α : Type} [Finite α] [DecidableEq α] [Nonempty α]
    [SampleableType α] [SampleableType (Equiv.Perm α)]
    [SampleableType (Equiv.Perm α × α)]
    (y : α) :
    evalDist
        (inverseReprogram y <$> ($ᵗ (Equiv.Perm α × α))) =
      evalDist ($ᵗ (Equiv.Perm α)) := by
  let reprogram := inverseReprogramEquiv y
  have hReprogram :
      evalDist (reprogram <$> ($ᵗ (Equiv.Perm α × α))) =
        evalDist ($ᵗ (Equiv.Perm α × α)) :=
    evalDist_map_bijective_uniform_cross
      (α := Equiv.Perm α × α) (β := Equiv.Perm α × α)
      reprogram reprogram.bijective
  calc
    evalDist (inverseReprogram y <$> ($ᵗ (Equiv.Perm α × α))) =
        evalDist (Prod.fst <$> (reprogram <$> ($ᵗ (Equiv.Perm α × α)))) := by
          congr 1
          simp only [Functor.map_map]
          rfl
    _ = evalDist (Prod.fst <$> ($ᵗ (Equiv.Perm α × α))) :=
      evalDist_map_eq_of_evalDist_eq hReprogram Prod.fst
    _ = evalDist ($ᵗ (Equiv.Perm α)) :=
      evalDist_map_fst_uniformSample_prod

/-! ### Deferred programming relative to an exposed history

The unconditional swap lemmas above are insufficient after an adaptive history: programming a
new output that was already exposed would retroactively change an H₀ answer.  The following
change of variables is the correct one-step kernel.  It programs only when the H₁ proposal lies
outside the *actual permutation image* of the exposed input history; otherwise the paired run
stops and leaves H₀'s permutation unchanged.  The auxiliary component is respectively the old
image or the already-exposed proposal, which makes the whole case split bijective.
-/

/-- The image of an exposed input history under a permutation. -/
def permutationHistoryImage {α : Type} [DecidableEq α]
    (history : Finset α) (p : Equiv.Perm α) : Finset α :=
  history.image p

/-- The paired forward step's H₀ permutation.  A proposal already in the exposed image is the
first-stop branch and does not modify H₀; otherwise the unexposed input is swap-programmed. -/
def forwardHistoryReprogram {α : Type} [DecidableEq α]
    (history : Finset α) (x : α) (pair : Equiv.Perm α × α) : Equiv.Perm α :=
  if pair.2 ∈ permutationHistoryImage history pair.1 then pair.1
  else forwardReprogram x pair

/-- The auxiliary value that makes `forwardHistoryReprogram` a bijective change of variables.
On the stopping branch it is the already-exposed proposal; on the continuing branch it is the
old image at the newly exposed input. -/
def forwardHistoryReprogramWithAux {α : Type} [DecidableEq α]
    (history : Finset α) (x : α) (pair : Equiv.Perm α × α) :
    Equiv.Perm α × α :=
  if pair.2 ∈ permutationHistoryImage history pair.1 then pair
  else (forwardReprogram x pair, pair.1 x)

/-- Swap-programming an unexposed input with a new output leaves the complete exposed range
unchanged. -/
lemma permutationHistoryImage_forwardReprogram_eq
    {α : Type} [DecidableEq α]
    (history : Finset α) (x y : α) (p : Equiv.Perm α)
    (hx : x ∉ history)
    (hy : y ∉ permutationHistoryImage history p) :
    permutationHistoryImage history (forwardReprogram x (p, y)) =
      permutationHistoryImage history p := by
  apply Finset.image_congr
  intro state hState
  apply forwardReprogram_apply_eq_of_ne x y state p
  · exact fun hEq => hx (hEq ▸ hState)
  · intro hEq
    apply hy
    exact Finset.mem_image.mpr ⟨state, hState, hEq⟩

/-- At an input outside the exposed history, the old image is outside its exposed range. -/
lemma apply_not_mem_permutationHistoryImage
    {α : Type} [DecidableEq α]
    (history : Finset α) (x : α) (p : Equiv.Perm α)
    (hx : x ∉ history) :
    p x ∉ permutationHistoryImage history p := by
  intro hImage
  obtain ⟨state, hState, hEq⟩ := Finset.mem_image.mp hImage
  exact hx ((p.injective hEq) ▸ hState)

/-- Invert the history-aware forward programming change of variables.  The auxiliary component
identifies the stopping branch exactly when it is already in the exposed image. -/
def forwardHistoryReprogramWithAuxInv {α : Type} [DecidableEq α]
    (history : Finset α) (x : α) (pair : Equiv.Perm α × α) :
    Equiv.Perm α × α :=
  if pair.2 ∈ permutationHistoryImage history pair.1 then pair
  else (pair.1.trans (Equiv.swap pair.2 (pair.1 x)), pair.1 x)

/-- The forward history-aware programming map is a true finite change of variables.  This is
what permits the paired simulator to expose a fresh H₁ proposal, preserve every old H₀ answer on
the continuing branch, and still retain the exact uniform H₀ permutation marginal. -/
noncomputable def forwardHistoryReprogramEquiv {α : Type} [DecidableEq α]
    (history : Finset α) (x : α) (hx : x ∉ history) :
    (Equiv.Perm α × α) ≃ (Equiv.Perm α × α) where
  toFun := forwardHistoryReprogramWithAux history x
  invFun := forwardHistoryReprogramWithAuxInv history x
  left_inv := by
    intro pair
    rcases pair with ⟨p, y⟩
    by_cases hy : y ∈ permutationHistoryImage history p
    · simp [forwardHistoryReprogramWithAux, forwardHistoryReprogramWithAuxInv, hy]
    · have hImage :
          permutationHistoryImage history (forwardReprogram x (p, y)) =
            permutationHistoryImage history p :=
        permutationHistoryImage_forwardReprogram_eq history x y p hx hy
      have hOldImage : p x ∉ permutationHistoryImage history (forwardReprogram x (p, y)) := by
        rw [hImage]
        exact apply_not_mem_permutationHistoryImage history x p hx
      simp only [forwardHistoryReprogramWithAux, hy, ↓reduceIte]
      simp only [forwardHistoryReprogramWithAuxInv, hOldImage, ↓reduceIte]
      apply Prod.ext
      · ext state
        simp [forwardReprogram, Equiv.trans_apply]
      · exact forwardReprogram_apply_programmed x y p
  right_inv := by
    intro pair
    rcases pair with ⟨p, oldImage⟩
    by_cases hOldImage : oldImage ∈ permutationHistoryImage history p
    · simp [forwardHistoryReprogramWithAux, forwardHistoryReprogramWithAuxInv, hOldImage]
    · let original : Equiv.Perm α :=
        p.trans (Equiv.swap oldImage (p x))
      have hOriginalImage :
          permutationHistoryImage history original = permutationHistoryImage history p := by
        dsimp only [original]
        rw [Equiv.swap_comm oldImage (p x)]
        exact permutationHistoryImage_forwardReprogram_eq history x oldImage p hx hOldImage
      have hProgrammed : p x ∉ permutationHistoryImage history original := by
        rw [hOriginalImage]
        exact apply_not_mem_permutationHistoryImage history x p hx
      simp only [forwardHistoryReprogramWithAuxInv, hOldImage, ↓reduceIte]
      change forwardHistoryReprogramWithAux history x (original, p x) = (p, oldImage)
      simp only [forwardHistoryReprogramWithAux, hProgrammed, ↓reduceIte]
      apply Prod.ext
      · ext state
        simp [original, forwardReprogram, Equiv.trans_apply]
      · simp [original, Equiv.trans_apply]

/-- The permutation component of the history-aware equivalence is exactly the programmed
permutation used by the coupled forward step. -/
lemma forwardHistoryReprogramEquiv_fst {α : Type} [DecidableEq α]
    (history : Finset α) (x : α) (hx : x ∉ history)
    (pair : Equiv.Perm α × α) :
    (forwardHistoryReprogramEquiv history x hx pair).1 =
      forwardHistoryReprogram history x pair := by
  rcases pair with ⟨p, y⟩
  by_cases hy : y ∈ permutationHistoryImage history p <;>
    simp [forwardHistoryReprogramEquiv, forwardHistoryReprogramWithAux,
      forwardHistoryReprogram, hy]

/-- A history-aware forward step preserves every previously exposed forward answer.  This is the
pointwise form used by the paired-execution induction: even on a newly programmed step, the
fresh input and fresh output conditions prevent either swapped value from occurring in `history`. -/
lemma forwardHistoryReprogram_preserves_history {α : Type} [DecidableEq α]
    (history : Finset α) (x : α) (p : Equiv.Perm α) (y state : α)
    (hx : x ∉ history) (hState : state ∈ history) :
    forwardHistoryReprogram history x (p, y) state = p state := by
  by_cases hy : y ∈ permutationHistoryImage history p
  · simp [forwardHistoryReprogram, hy]
  · rw [forwardHistoryReprogram, if_neg hy]
    apply forwardReprogram_apply_eq_of_ne x y state p
    · exact fun hEq => hx (hEq ▸ hState)
    · intro hEq
      exact hy (Finset.mem_image.mpr ⟨state, hState, hEq⟩)

/-- For a history fixed independently of the sampled pair, the history-aware forward kernel
retains an exact uniform permutation marginal.  The output proposal is retained as an auxiliary
value precisely on the stopping branch; on the continuing branch the auxiliary is the overwritten
old image.  This is a local change of variables only: a live coupling still needs its separate
conditional-history and post-stop-completion proof. -/
theorem evalDist_forwardHistoryReprogram_uniform
    {α : Type} [Finite α] [DecidableEq α] [Nonempty α]
    [SampleableType α] [SampleableType (Equiv.Perm α)]
    [SampleableType (Equiv.Perm α × α)]
    (history : Finset α) (x : α) (hx : x ∉ history) :
    evalDist
        (forwardHistoryReprogram history x <$> ($ᵗ (Equiv.Perm α × α))) =
      evalDist ($ᵗ (Equiv.Perm α)) := by
  let reprogram := forwardHistoryReprogramEquiv history x hx
  have hReprogram :
      evalDist (reprogram <$> ($ᵗ (Equiv.Perm α × α))) =
        evalDist ($ᵗ (Equiv.Perm α × α)) :=
    evalDist_map_bijective_uniform_cross
      (α := Equiv.Perm α × α) (β := Equiv.Perm α × α)
      reprogram reprogram.bijective
  calc
    evalDist
        (forwardHistoryReprogram history x <$> ($ᵗ (Equiv.Perm α × α))) =
        evalDist (Prod.fst <$> (reprogram <$> ($ᵗ (Equiv.Perm α × α)))) := by
          congr 1
          simp only [Functor.map_map]
          congr 1
          funext a
          rcases a with ⟨p, y⟩
          by_cases hy : y ∈ permutationHistoryImage history p <;>
            simp [reprogram, forwardHistoryReprogramEquiv,
              forwardHistoryReprogramWithAux, forwardHistoryReprogram, hy]
    _ = evalDist (Prod.fst <$> ($ᵗ (Equiv.Perm α × α))) :=
      evalDist_map_eq_of_evalDist_eq hReprogram Prod.fst
    _ = evalDist ($ᵗ (Equiv.Perm α)) :=
      evalDist_map_fst_uniformSample_prod

/-- Invert a full permutation while retaining an explicit equivalence of the permutation space.
This transports the forward history kernel to its inverse-query dual. -/
noncomputable def permutationSymmEquiv {α : Type} :
    Equiv.Perm α ≃ Equiv.Perm α where
  toFun := fun p => p.symm
  invFun := fun p => p.symm
  left_inv := by
    intro p
    exact p.symm_symm
  right_inv := by
    intro p
    exact p.symm_symm

/-- Apply `permutationSymmEquiv` to the permutation component of a sampled pair. -/
noncomputable def permutationPairSymmEquiv {α : Type} :
    (Equiv.Perm α × α) ≃ (Equiv.Perm α × α) :=
  Equiv.prodCongr permutationSymmEquiv (Equiv.refl α)

/-- The inverse-query dual of `forwardHistoryReprogram`.  Here `history` records exposed output
states.  Passing to the inverse permutation turns an inverse query at `y` with proposed preimage
into exactly a forward query at `y`; this definition therefore has the same explicit stop versus
fresh-programming split as the forward kernel. -/
def inverseHistoryReprogram {α : Type} [DecidableEq α]
    (history : Finset α) (y : α) (pair : Equiv.Perm α × α) : Equiv.Perm α :=
  (forwardHistoryReprogram history y (pair.1.symm, pair.2)).symm

/-- The inverse history kernel with the auxiliary old preimage/stopping proposal retained. -/
def inverseHistoryReprogramWithAux {α : Type} [DecidableEq α]
    (history : Finset α) (y : α) (pair : Equiv.Perm α × α) :
    Equiv.Perm α × α :=
  let result := forwardHistoryReprogramWithAux history y (pair.1.symm, pair.2)
  (result.1.symm, result.2)

/-- A history-aware inverse step preserves every previously exposed inverse answer.  It is the
dual of `forwardHistoryReprogram_preserves_history` under permutation inversion. -/
lemma inverseHistoryReprogram_symm_preserves_history {α : Type} [DecidableEq α]
    (history : Finset α) (y : α) (p : Equiv.Perm α) (x output : α)
    (hy : y ∉ history) (hOutput : output ∈ history) :
    (inverseHistoryReprogram history y (p, x)).symm output = p.symm output := by
  change forwardHistoryReprogram history y (p.symm, x) output = p.symm output
  exact forwardHistoryReprogram_preserves_history history y p.symm x output hy hOutput

/-- The inverse history kernel is a fixed-history change of variables: invert the permutation,
apply the forward history equivalence, and invert the resulting permutation back. -/
noncomputable def inverseHistoryReprogramEquiv {α : Type} [DecidableEq α]
    (history : Finset α) (y : α) (hy : y ∉ history) :
    (Equiv.Perm α × α) ≃ (Equiv.Perm α × α) :=
  (permutationPairSymmEquiv.trans
    (forwardHistoryReprogramEquiv history y hy)).trans permutationPairSymmEquiv

/-- For a fixed history, the inverse history-aware programming kernel retains an exact uniform
permutation marginal.  It is the local inverse companion of
`evalDist_forwardHistoryReprogram_uniform`; it is not yet an adaptive lazy-permutation
completion theorem. -/
theorem evalDist_inverseHistoryReprogram_uniform
    {α : Type} [Finite α] [DecidableEq α] [Nonempty α]
    [SampleableType α] [SampleableType (Equiv.Perm α)]
    [SampleableType (Equiv.Perm α × α)]
    (history : Finset α) (y : α) (hy : y ∉ history) :
    evalDist
        (inverseHistoryReprogram history y <$> ($ᵗ (Equiv.Perm α × α))) =
      evalDist ($ᵗ (Equiv.Perm α)) := by
  let reprogram := inverseHistoryReprogramEquiv history y hy
  have hReprogram :
      evalDist (reprogram <$> ($ᵗ (Equiv.Perm α × α))) =
        evalDist ($ᵗ (Equiv.Perm α × α)) :=
    evalDist_map_bijective_uniform_cross
      (α := Equiv.Perm α × α) (β := Equiv.Perm α × α)
      reprogram reprogram.bijective
  calc
    evalDist
        (inverseHistoryReprogram history y <$> ($ᵗ (Equiv.Perm α × α))) =
        evalDist (Prod.fst <$> (reprogram <$> ($ᵗ (Equiv.Perm α × α)))) := by
          congr 1
          simp only [Functor.map_map]
          congr 1
          funext a
          rcases a with ⟨p, x⟩
          dsimp [reprogram, inverseHistoryReprogramEquiv, permutationPairSymmEquiv,
            permutationSymmEquiv, inverseHistoryReprogram]
          rw [forwardHistoryReprogramEquiv_fst]
    _ = evalDist (Prod.fst <$> ($ᵗ (Equiv.Perm α × α))) :=
      evalDist_map_eq_of_evalDist_eq hReprogram Prod.fst
    _ = evalDist ($ᵗ (Equiv.Perm α)) :=
      evalDist_map_fst_uniformSample_prod

end KeyLemma

end DuplexSpongeFS
