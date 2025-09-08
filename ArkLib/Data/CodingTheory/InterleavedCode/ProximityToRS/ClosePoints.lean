/-
Close points on an affine line with respect to Reed–Solomon codes,
and basic cardinality links to scalars producing such points.
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.InterleavedCode.Defs
import Mathlib.Tactic

noncomputable section

open Code

namespace ProximityToRS

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
The set of points on an affine line, which are within distance `e`
from a Reed-Solomon code.
-/
def closePtsOnAffineLine (u v : ι → F) (deg : ℕ) (α : ι ↪ F) (e : ℕ) : Finset (ι → F) :=
  by
    classical
    let fFintype : Fintype F := Fintype.ofFinite F
    exact Finset.univ.filter
      (fun x : (ι → F) => x ∈ Affine.line u v ∧ distFromCode x (ReedSolomon.code α deg) ≤ e)

/--
The number of points on an affine line which are within distance `e`
from a Reed-Solomon code.
-/
def numberOfClosePts (u v : ι → F) (deg : ℕ) (α : ι ↪ F) (e : ℕ) : ℕ :=
  (closePtsOnAffineLine u v deg α e).card

/-- Cardinality link: the number of close points on the affine line is bounded by the
number of good scalars. -/
lemma card_closePts_le_card_good
  {u v : ι → F} {deg : ℕ} {α : ι ↪ F} {e : ℕ} :
  (closePtsOnAffineLine u v deg α e).card ≤
    Nat.card {a : F // Code.distFromCode (u + a • v) (ReedSolomon.code α deg) ≤ e} := by
  classical
  -- Domain of scalars that map to close points on the affine line
  let G := {a : F // Code.distFromCode (u + a • v) (ReedSolomon.code α deg) ≤ e}
  -- Target subtype of elements of the close-points Finset
  let s := closePtsOnAffineLine u v deg α e
  let S := {x : (ι → F) // x ∈ s}
  -- Map good scalars to close points via a ↦ u + a•v, landing in the subtype S
  let φ : G → S := fun a => by
    refine ⟨u + a.1 • v, ?_⟩
    -- Membership in the filtered Finset is straightforward
    have hxLine : (u + a.1 • v) ∈ Affine.line u v := ⟨a.1, rfl⟩
    have hxDist : distFromCode (u + a.1 • v) (ReedSolomon.code α deg) ≤ e := a.2
    have : (u + a.1 • v) ∈ closePtsOnAffineLine u v deg α e := by
      classical
      simp [closePtsOnAffineLine, hxLine, hxDist]
    simpa [s] using this
  -- Surjection: every element in S corresponds to some a ∈ G
  have hsurj_φ : Function.Surjective φ := by
    intro y
    rcases y with ⟨y, hy⟩
    -- From membership in s, extract a witness a with y = u + a•v and the distance bound
    have hy' : y ∈ closePtsOnAffineLine u v deg α e := by simpa [s] using hy
    have : y ∈ Affine.line u v ∧ distFromCode y (ReedSolomon.code α deg) ≤ e := by
      classical
      simpa [closePtsOnAffineLine] using (Finset.mem_filter.mp hy')
    rcases this with ⟨hyLine, hydist⟩
    rcases hyLine with ⟨a, rfl⟩
    exact ⟨⟨a, hydist⟩, rfl⟩
  -- Hence, card(S) ≤ card(G)
  have h_card_S_le : Nat.card S ≤ Nat.card G :=
    Finite.card_le_of_surjective φ hsurj_φ
  -- And card(s) ≤ card(S) since s.attach ⊆ univ
  have h_card_s_le_S : s.card ≤ Nat.card S := by
    -- s.card = (s.attach).card ≤ (univ : Finset S).card = Fintype.card S
    have hsubset : (s.attach : Finset S) ⊆ (Finset.univ : Finset S) := by exact Finset.subset_univ _
    have hmono := Finset.card_mono hsubset
    -- (univ : Finset S).card = Fintype.card S
    have huniv : (Finset.univ : Finset S).card = Fintype.card S := by
      classical
      simp
    have hattach : (s.attach : Finset S).card = s.card := by
      classical
      simp [Finset.card_attach]
    simpa [hattach, huniv] using hmono
  -- Chain the inequalities
  exact le_trans h_card_s_le_S h_card_S_le

-- A version expressed with `numberOfClosePts` for convenient use at call sites.
lemma numberOfClosePts_le_card_good
  {u v : ι → F} {deg : ℕ} {α : ι ↪ F} {e : ℕ} :
  numberOfClosePts u v deg α e ≤
    Nat.card {a : F // Code.distFromCode (u + a • v) (ReedSolomon.code α deg) ≤ e} := by
  classical
  simpa [numberOfClosePts] using
    (card_closePts_le_card_good (u := u) (v := v) (deg := deg) (α := α) (e := e))

end ProximityToRS
