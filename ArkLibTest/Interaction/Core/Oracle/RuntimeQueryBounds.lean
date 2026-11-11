/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibTest.Interaction.Core.Oracle.HiddenBitFixture
import ArkLibTest.Interaction.Core.Support
import VCVio.OracleComp.QueryTracking.QueryBound.Simulation

/-! Access certificates for the hidden-bit composition of
`ArkLibTest.Interaction.Core.Oracle.HiddenBitFixture`. The prefix exports its input slot and its
decision makes one dummy request. The suffix decision reads the export as a pad and reveals the
hidden bit. Oracle access is typing: the export is a map over the prefix resources, which on the
only prefix path are the inputs alone, and the suffix decision routed by `suffixRoute` queries only
the reveal request and the input slot of the composed resources. -/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle Interaction.TwoParty.Lens
  OracleComp OracleSpec
open Interaction.Core.HiddenBitFixture

namespace Interaction.Core.RuntimeQueryBoundsTests

/-- The only shape path of the prefix. -/
abbrev firstPath : Path bitFirst := ⟨⟨⟩, ⟨⟩⟩

/-- The shape path of the composition on which the prover guesses `guess`. -/
abbrev combinedPath (guess : Bool) : Path bitCombined := ⟨⟨⟩, guess, ⟨⟩⟩

/-- The export returned by the prefix. -/
abbrev exportMap (v : View bitFirst firstPath) := bitPrefix.outputMap () firstPath v

-- RuntimeQueryBounds 2, restated: names are retired. The export's only query is the input slot
-- `.inl ()` of the prefix resources.
example (v : View bitFirst firstPath) :
    (exportMap v).impl ⟨(), ()⟩ = liftM (firstResources.spec.query (.inl ⟨(), ()⟩)) := rfl

-- RuntimeQueryBounds 1, access part, restated: the export is typed over the prefix resources,
-- which have no message slot on the only prefix path, so it reads the inputs alone; its query is
-- the input slot. The cost part is in `QueryCost.lean`.
example : IsEmpty (oracleIdx bitFirst firstPath) := inferInstanceAs (IsEmpty PEmpty)

/-- The prefix export queries only its input oracle. -/
theorem export_access (v : View bitFirst firstPath) :
    AllQueriesSatisfy ((exportMap v).impl ⟨(), ()⟩) (fun q => q = .inl ⟨(), ()⟩) :=
  (allQueriesSatisfy_query_iff (spec := firstResources.spec) (.inl ⟨(), ()⟩) _).mpr rfl

-- RuntimeQueryBounds 3, restated: the prefix output map is the embedding of the input slot, and
-- the prefix decision makes the dummy request and accepts.
example (v : View bitFirst firstPath) :
    exportMap v = OracleMap.fst _ _ := rfl

example (v : View bitFirst firstPath) : (bitPrefix.decide () firstPath v).run = (do
    let _ : Bool ← liftM ((bitAmbient + firstResources.spec).query (.inl false))
    pure (some ())) := rfl

/-- The suffix decision reads the pad from the export, reveals the hidden bit and claims
`hidden ^^ pad`. -/
theorem suffix_decide (guess : Bool) (v : View bitSecond ⟨guess, ⟨⟩⟩) :
    (bitSuffix.decide () ⟨guess, ⟨⟩⟩ v).run = (do
      let pad : Bool ← liftM ((bitAmbient + (secondResources guess).spec).query
        (.inr (.inl ⟨(), ()⟩)))
      let hidden : Bool ← liftM ((bitAmbient + (secondResources guess).spec).query (.inl true))
      pure (some (hidden ^^ pad))) := rfl

-- RuntimeQueryBounds 4, restated: the suffix decision unfolds to the pad and reveal queries
-- (`suffix_decide`), and the suffix output data is `guess ^^ pad`, with the pad read from the
-- export.
example (guess : Bool) (v : View bitSecond ⟨guess, ⟨⟩⟩)
    (x : (secondResources guess).Data) :
    (bitSuffix.outputMap () ⟨guess, ⟨⟩⟩ v).f x () = (guess ^^ (show Bool from x.1 ())) :=
  rfl

/-- The suffix may request only the reveal, and may query only the export slot. -/
abbrev suffixAllowed (p : Path bitSecond) :
    (bitAmbient + (pathResources bits bitSecond p).spec).Domain → Prop
  | .inl request => request = true
  | .inr q => q = .inl ⟨(), ()⟩

-- RuntimeQueryBounds 5, restated: the ambient permission is kept; the suffix's resource queries
-- go to the export slot, and the suffix resources have no other slot on any path.
/-- The suffix decision queries only its export oracle and the reveal request. -/
theorem suffix_access (p : Path bitSecond) (v : View bitSecond p) :
    AllQueriesSatisfy (bitSuffix.decide () p v).run (suffixAllowed p) := by
  rcases p with ⟨guess, ⟨⟩⟩
  rw [suffix_decide]
  exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨rfl, fun _ =>
    (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨rfl, fun _ => allQueriesSatisfy_pure _ _⟩⟩

example (guess : Bool) : IsEmpty (oracleIdx bitSecond ⟨guess, ⟨⟩⟩) :=
  inferInstanceAs (IsEmpty PEmpty)

/-- The suffix route of the composition, with ambient requests kept. -/
abbrev routeSuffix (p : Path bitCombined) (v : View bitCombined p) :=
  (OracleVerifier.suffixRoute bitPrefix () p v).withAmbient bitAmbient

/-- The suffix decision with its resource queries routed into the composed resources. -/
def routedSuffix (p : Path bitCombined) (v : View bitCombined p) :
    OracleComp (bitAmbient + (pathResources bits bitCombined p).spec) (Option Bool) :=
  simulateQ (routeSuffix p v)
    (bitSuffix.decide () (Path.split bitFirst (fun _ => bitSecond) p).2
      (View.split bitFirst (fun _ => bitSecond) p v).2).run

/-- The routed export query is the input-slot query of the composed resources. -/
theorem routeSuffix_export (guess : Bool) (v : View bitCombined (combinedPath guess)) :
    routeSuffix (combinedPath guess) v (.inr (.inl ⟨(), ()⟩)) =
      liftM ((bitAmbient + (pathResources bits bitCombined
        (combinedPath guess)).spec).query (.inr (.inl ⟨(), ()⟩))) := rfl

/-- The raw permissions: only the reveal request, and only the input slot. -/
abbrev rawAllowed (p : Path bitCombined) :
    (bitAmbient + (pathResources bits bitCombined p).spec).Domain → Prop
  | .inl request => request = true
  | .inr q => q = .inl ⟨(), ()⟩

-- RuntimeQueryBounds 8, restated: on every composed path and view, the routed suffix decision
-- satisfies the raw permissions: the ambient permission is kept, and the export query becomes the
-- input-slot query.
/-- The routed suffix decision queries only the input oracle and the reveal request. -/
theorem routed_suffix_access (p : Path bitCombined) (v : View bitCombined p) :
    AllQueriesSatisfy (routedSuffix p v) (rawAllowed p) := by
  rcases p with ⟨⟨⟩, guess, ⟨⟩⟩
  refine (suffix_access _ _).simulateQ fun q allowed => ?_
  rcases q with request | (⟨i, q⟩ | ⟨i, q⟩)
  · exact (allQueriesSatisfy_query_iff _ _).mpr allowed
  · cases i
    cases q
    exact (routeSuffix_export guess v).symm ▸
      (allQueriesSatisfy_query_iff (spec := bitAmbient +
        (pathResources bits bitCombined (combinedPath guess)).spec)
        (.inr (.inl ⟨(), ()⟩)) _).mpr rfl
  · exact i.elim

end Interaction.Core.RuntimeQueryBoundsTests
