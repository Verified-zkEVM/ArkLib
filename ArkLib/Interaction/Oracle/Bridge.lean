/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Core

/-!
# Bridge: Interaction.Spec + OracleDecoration → Oracle.Spec

Structural conversion from the W-type-based
`Interaction.Spec + RoleDecoration + OracleDecoration` to the new
`Interaction.Oracle.Spec` inductive.

## Main definitions

- `Interaction.Oracle.Spec.ofInteractionSpec` — convert an `Interaction.Spec`
  with `RoleDecoration` and `OracleDecoration` into an `Oracle.Spec`.
  At sender nodes the continuation is treated as constant (picking a
  representative via a provided default-element function).
- `Interaction.Oracle.Spec.ofRoleDecoration` — convert a `RoleDecoration`
  to `Spec.RoleDeco`.
- `Interaction.Oracle.Spec.ofOracleDecoration` — convert an
  `OracleDecoration` to `Spec.OracleDeco`.

## Implementation notes

The bridge requires a `senderDefault` function to pick a representative
element at each sender node (since oracle message types may not have
`Inhabited` instances). In practice, all oracle message types are nonempty,
so any such function suffices.

Verifier and reduction conversions (from `OracleVerifier`/`OracleReduction`
to `Oracle.Verifier`/`Oracle.Reduction`) are deferred. The output types need
to be re-indexed from `Interaction.Spec.Transcript` to
`Oracle.Spec.PublicTranscript`, which requires careful coherence proofs. In
practice, consumers should construct `Oracle.Spec`-based reductions natively
rather than converting from the old representation.
-/

open OracleComp OracleSpec
open Interaction.TwoParty

namespace Interaction.Oracle.Spec

/-- Convert an `Interaction.Spec + RoleDecoration + OracleDecoration` into an
`Oracle.Spec`.

At sender nodes, the continuation `rest x` is structurally required to be
constant by `OracleDecoration` (oracle messages don't branch). We pick the
representative using the `senderDefault` function.

At receiver nodes, the continuation genuinely depends on the message, so
`.public` is used. -/
noncomputable def ofInteractionSpec
    (senderDefault : ∀ (X : Type), OracleInterface X → X) :
    (spec : Interaction.Spec) → (roles : RoleDecoration spec) →
    OracleDecoration spec roles → Oracle.Spec
  | .done, _, _ => .done
  | .node X rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩ =>
      let x₀ := senderDefault X oi
      .oracle X (ofInteractionSpec senderDefault (rest x₀) (rRest x₀) (odRest x₀))
  | .node X rest, ⟨.receiver, rRest⟩, odFn =>
      .«public» X (fun x =>
        ofInteractionSpec senderDefault (rest x) (rRest x) (odFn x))

/-- Convert a `RoleDecoration` to `RoleDeco` on the resulting `Oracle.Spec`.
Only receiver nodes carry role information in `Oracle.Spec`; sender nodes
are structurally `.sender` by construction. -/
noncomputable def ofRoleDecoration
    (senderDefault : ∀ (X : Type), OracleInterface X → X) :
    (spec : Interaction.Spec) → (roles : RoleDecoration spec) →
    (od : OracleDecoration spec roles) →
    RoleDeco (ofInteractionSpec senderDefault spec roles od)
  | .done, _, _ => ⟨⟩
  | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩ =>
      let x₀ := senderDefault _ oi
      ofRoleDecoration senderDefault (rest x₀) (rRest x₀) (odRest x₀)
  | .node _ rest, ⟨.receiver, rRest⟩, odFn =>
      ⟨.receiver, fun x =>
        ofRoleDecoration senderDefault (rest x) (rRest x) (odFn x)⟩

/-- Convert an `OracleDecoration` to `OracleDeco` on the resulting
`Oracle.Spec`. The `OracleInterface` at each sender node becomes the
`.oracle` node's interface. -/
noncomputable def ofOracleDecoration
    (senderDefault : ∀ (X : Type), OracleInterface X → X) :
    (spec : Interaction.Spec) → (roles : RoleDecoration spec) →
    (od : OracleDecoration spec roles) →
    OracleDeco (ofInteractionSpec senderDefault spec roles od)
  | .done, _, _ => ⟨⟩
  | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩ =>
      let x₀ := senderDefault _ oi
      ⟨oi, ofOracleDecoration senderDefault (rest x₀) (rRest x₀) (odRest x₀)⟩
  | .node _ rest, ⟨.receiver, rRest⟩, odFn =>
      fun x => ofOracleDecoration senderDefault (rest x) (rRest x) (odFn x)

end Interaction.Oracle.Spec
