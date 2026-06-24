/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.OracleReduction.Basic
import ArkLib.Interaction.Reduction
import ArkLib.Interaction.Choreo

open Interaction.TwoParty

/-!
# Schnorr's Σ-Protocol — Two Views

A 3-round public-coin proof of knowledge of discrete logarithm, written twice against ArkLib's
two interactive frameworks:

1. `State.*` — ArkLib's flat `Prover` / `Verifier` / `Reduction` schema (in
   `ArkLib/OracleReduction/Basic.lean`) with an explicit `PrvState : Fin (n + 1) → Type`
   family and case-splits on round indices.
2. `Interactive.*` — ArkLib's `Interaction.Prover` / `Interaction.Verifier` /
   `Interaction.Reduction` wrappers (in `ArkLib/Interaction/Reduction.lean`) over VCVio's
   paired `StrategyOver` fibers. The protocol is a `Spec` (free monad over
   `Spec.basePFunctor`); the prover/verifier inhabit focal/counterpart fibers
   that definitionally unfold to iterated-monad forms. State threads through via
   lexical scope; no `PrvState` family, no case-split on round indices.

Both target the same Σ-protocol:

  Round 0  (P → V) : `R = r • g`     where `r ← $ᵗ F`     (commitment)
  Round 1  (V → P) : `c ← $ᵗ F`                            (random challenge)
  Round 2  (P → V) : `z = r + c · sk`                      (response)
  Verifier accepts iff `z • g = R + c • pk`.

## Setup

- `F` : scalar field (sampleable, decidable equality)
- `G` : additive group acted on by `F` via `Module F G`
- `g : G` : public generator
- Statement `pk : G`, witness `sk : F`, relation `sk • g = pk`
-/

namespace Schnorr

variable (F : Type) [Field F] [Sampleable F]
variable (G : Type) [AddCommGroup G] [Module F G] [DecidableEq G]
variable (g : G)

/-- The discrete-log relation: `sk` is the discrete log of `pk` w.r.t. generator `g`. -/
@[reducible, simp]
def relIn : Set (G × F) := { ⟨pk, sk⟩ | sk • g = pk }

/-- Trivial output relation (acceptance is encoded via the verifier returning `pure ()`). -/
@[reducible, simp]
def relOut : Set (Unit × Unit) := Set.univ

/-! ## State-based view: ArkLib's flat `Prover` / `Verifier` / `Reduction` schema. -/

namespace State

open OracleComp OracleSpec ProtocolSpec

/-- The 3-round Schnorr protocol specification:
    `(P → V : G), (V → P : F), (P → V : F)`. -/
@[reducible]
def pSpec : ProtocolSpec 3 :=
  ⟨!v[.P_to_V, .V_to_P, .P_to_V], !v[G, F, F]⟩

instance : ∀ i, SampleableType ((pSpec F G).Challenge i)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => inferInstanceAs (SampleableType F)
  | ⟨2, h⟩ => nomatch h

instance : ∀ i, VCVCompatible ((pSpec F G).Challenge i)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => inferInstanceAs (VCVCompatible F)
  | ⟨2, h⟩ => nomatch h

/-- The honest Schnorr prover, state-based.

  - State 0 : `(pk, sk)`         — input context
  - State 1 : `(sk, r)`          — secret + sampled randomness
  - State 2 : `z`                — fully-formed response
  - State 3 : `Unit`

  Sampling happens in round 0 via `$ᵗ F`; everything else is pure. -/
@[inline, specialize]
def prover : Prover unifSpec G F Unit Unit (pSpec F G) where
  PrvState
  | 0 => G × F
  | 1 => F × F
  | 2 => F
  | 3 => Unit
  input := id
  sendMessage
  | ⟨0, _⟩ => fun (_pk, sk) => do
      let r ← $ᵗ F
      pure (r • g, (sk, r))
  | ⟨1, h⟩ => nomatch h
  | ⟨2, _⟩ => fun z => pure (z, ())
  receiveChallenge
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun (sk, r) => pure (fun (c : F) => r + c * sk)
  | ⟨2, h⟩ => nomatch h
  output := fun () => pure ((), ())

/-- The honest Schnorr verifier, state-based.

  Pure algebraic check `z • g = R + c • pk`; no oracle queries needed. The result lives in
  `OptionT (OracleComp unifSpec) Unit`, so rejection is `failure`. -/
@[inline, specialize]
def verifier : Verifier unifSpec G Unit (pSpec F G) where
  verify := fun pk tr =>
    let R : G := tr 0
    let c : F := tr 1
    let z : F := tr 2
    if z • g = R + c • pk then pure () else failure

/-- Schnorr's Σ-protocol packaged as an ArkLib `Reduction`. -/
@[inline, specialize]
def reduction : Reduction unifSpec G F Unit Unit (pSpec F G) where
  prover := prover F G g
  verifier := verifier F G g

end State

/-! ## Interactive view: ArkLib's `Interaction.Prover` / `Interaction.Verifier` /
  `Interaction.Reduction` wrappers over paired `StrategyOver` fibers.

  The protocol shape is a real W-type (free monad over `Spec.basePFunctor`); the prover and
  verifier inhabit focal and counterpart strategy fibers, wrapped by ArkLib's
  `Interaction.Prover`/`Verifier` abbrevs with the standard `(SharedIn,
  StatementIn, WitnessIn, StatementOut, WitnessOut)` indexing. -/

namespace Interactive

open Interaction OracleComp OracleSpec

/-- Schnorr's 3-round interaction tree, as a `Spec`:
    `node G (fun _ => node F (fun _ => node F (fun _ => done)))`. -/
def spec : Spec :=
  .node G fun _ => .node F fun _ => .node F fun _ => .done

/-- Per-node sender / receiver assignment from the prover's perspective:
    sender, receiver, sender. -/
def proverRoles : RoleDecoration (spec F G) :=
  ⟨.sender, fun _ => ⟨.receiver, fun _ => ⟨.sender, fun _ => ⟨⟩⟩⟩⟩

/-- The honest Schnorr prover as an `Interaction.Prover` over `OracleComp unifSpec`.

  Indexing follows the top-level convention from `ArkLib/Interaction/Reduction.lean`:
  `SharedIn := G` carries the public key, `StatementIn := PUnit`, `WitnessIn := F` the secret key.
  The output type at `.done` is `HonestProverOutput (Option Unit) PUnit`.

  After unfolding the focal strategy fiber on the role decoration, the underlying strategy has type
  `m ((R : G) × ((c : F) → m (m ((z : F) × (Option Unit × PUnit)))))` for
  `m = OracleComp unifSpec`. -/
@[inline, specialize]
def prover :
    Prover (OracleComp unifSpec) G
      (fun _ => spec F G) (fun _ => proverRoles F G)
      (fun _ => PUnit) (fun _ => F)
      (fun _ _ => Option Unit) (fun _ _ => PUnit) :=
  fun _pk _ sk => pure (do
    let r ← $ᵗ F
    pure ⟨r • g, fun (c : F) => pure (pure ⟨r + c * sk, (some (), PUnit.unit)⟩)⟩)

/-- The honest Schnorr verifier as an `Interaction.Verifier` over `OracleComp unifSpec`.

  `StatementOut := Option Unit` carries the accept / reject decision (`some ()` accepts,
  `none` rejects). After unfolding the counterpart strategy fiber, the underlying type is
  `(R : G) → m (m ((c : F) × ((z : F) → m (Option Unit))))` for `m = OracleComp unifSpec`. -/
@[inline, specialize]
def verifier :
    Verifier (OracleComp unifSpec) G
      (fun _ => spec F G) (fun _ => proverRoles F G)
      (fun _ => PUnit) (fun _ _ => Option Unit) :=
  fun pk _ (R : G) => pure (do
    let c ← $ᵗ F
    pure ⟨c, fun (z : F) =>
      pure (if z • g = R + c • pk then some () else none)⟩)

/-- Schnorr written once as a scoped two-party choreography.

The scoped choreography core keeps public messages in continuation scope, so the
verifier can refer to `R`, `c`, and `z` without manually packing them into local
state names such as `pkAndR`. Private prover state is unpacked by pattern at the
next prover action, instead of being projected from an ad-hoc tuple name. -/
def schnorrChoreo :
    Choreo.Scoped.Program (OracleComp unifSpec)
      F G (Option Unit × PUnit) (Option Unit) :=
  choreo_begin
  prover_send[G] R from sk => do
    let r ← $ᵗ F
    send (r • g : G) keeping ((sk, r) : F × F)
  ;;
  verifier_send[F] c from pk => do
    let c ← $ᵗ F
    send c keeping pk
  ;;
  prover_send[F] z from ⟨sk, r⟩ =>
    send (r + c * sk) keeping ()
  ;;
  choreo_end
    prover _pfinal => (accept, ()) ;;
    verifier pk => if z • g = R + c • pk then accept else reject

/-- The choreography produces the same interaction tree as the hand-written
Schnorr `spec`. -/
example : (schnorrChoreo F G g).spec = spec F G := rfl

/-- The choreography produces the same prover-perspective roles as
`proverRoles`. -/
example : (schnorrChoreo F G g).roles = proverRoles F G := rfl

/-- Honest Schnorr prover projected from the choreography. -/
@[inline, specialize]
def proverFromChoreo :
    Prover (OracleComp unifSpec) G
      (fun _ => spec F G) (fun _ => proverRoles F G)
      (fun _ => PUnit) (fun _ => F)
      (fun _ _ => Option Unit) (fun _ _ => PUnit) :=
  fun _pk _ sk => (schnorrChoreo F G g).prover sk

/-- Honest Schnorr verifier projected from the choreography. -/
@[inline, specialize]
def verifierFromChoreo :
    Verifier (OracleComp unifSpec) G
      (fun _ => spec F G) (fun _ => proverRoles F G)
      (fun _ => PUnit) (fun _ _ => Option Unit) :=
  fun pk _ => (schnorrChoreo F G g).verifier pk

/-- Schnorr packaged as a reduction via the choreography. -/
@[inline, specialize]
def reductionFromChoreo :
    Reduction (OracleComp unifSpec) G
      (fun _ => spec F G) (fun _ => proverRoles F G)
      (fun _ => PUnit) (fun _ => F)
      (fun _ _ => Option Unit) (fun _ _ => PUnit) where
  prover := proverFromChoreo F G g
  verifier := verifierFromChoreo F G g

/-- Schnorr's Σ-protocol packaged as an `Interaction.Reduction`. -/
@[inline, specialize]
def reduction :
    Reduction (OracleComp unifSpec) G
      (fun _ => spec F G) (fun _ => proverRoles F G)
      (fun _ => PUnit) (fun _ => F)
      (fun _ _ => Option Unit) (fun _ _ => PUnit) where
  prover := prover F G g
  verifier := fun pk stmt => verifier F G g pk stmt

/-- The projected prover is propositionally the same as the hand-written prover. -/
theorem proverFromChoreo_eq_prover : proverFromChoreo F G g = prover F G g := by
  funext pk stmt sk
  simp only [proverFromChoreo, prover, schnorrChoreo, Choreo.Scoped.proverSendConst,
    Choreo.Scoped.verifierSendConst, Choreo.Scoped.done, bind_pure_comp,
    map_pure, Functor.map_map]
  rfl

/-- The projected verifier is propositionally the same as the hand-written verifier. -/
theorem verifierFromChoreo_eq_verifier : verifierFromChoreo F G g = verifier F G g := by
  funext pk stmt R
  simp only [verifierFromChoreo, verifier, schnorrChoreo, Choreo.Scoped.proverSendConst,
    Choreo.Scoped.verifierSendConst, Choreo.Scoped.done, bind_pure_comp,
    Functor.map_map]
  rfl

/-- The projected reduction is propositionally the same as the hand-written reduction. -/
theorem reductionFromChoreo_eq_reduction : reductionFromChoreo F G g = reduction F G g := by
  simp only [reductionFromChoreo, reduction, proverFromChoreo_eq_prover,
    verifierFromChoreo_eq_verifier]

/-! ### Type-unfolding checks

The paired `StrategyOver` fibers unfold on a concrete role decoration by `rfl`.
The two `example`s below pin down exactly the iterated-monad shapes asserted in
the docstrings of `prover` and `verifier`. -/

example :
    Spec.StrategyOver (pairedSyntax (OracleComp unifSpec))
      Interaction.TwoParty.Participant.focal (spec F G) (proverRoles F G)
      (fun _ => HonestProverOutput (Option Unit) PUnit) =
      OracleComp unifSpec ((_ : G) ×
        ((_ : F) → OracleComp unifSpec (OracleComp unifSpec
          ((_ : F) × (Option Unit × PUnit))))) := rfl

example :
    Spec.StrategyOver (pairedSyntax (OracleComp unifSpec))
      Interaction.TwoParty.Participant.counterpart (spec F G) (proverRoles F G)
      (fun _ => Option Unit) =
      ((_ : G) → OracleComp unifSpec (OracleComp unifSpec ((_ : F) ×
        ((_ : F) → OracleComp unifSpec (Option Unit))))) := rfl

end Interactive

end Schnorr
