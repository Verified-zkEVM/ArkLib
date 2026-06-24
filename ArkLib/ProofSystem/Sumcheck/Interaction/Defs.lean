/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.Basic.Replicate
import PolyFun.Interaction.TwoParty.Compose
import ArkLib.Interaction.Reduction
import ArkLib.Interaction.RoleChain
import ArkLib.ProofSystem.Sumcheck.Interaction.CompPoly

open Interaction.TwoParty

/-!
# Sum-Check Interaction: Shared Definitions

This module defines the shared algebraic core for the sum-check interaction stack,
using CompPoly types throughout.

## Overview

The sum-check protocol verifies a claim of the form

  `∑ x ∈ D^n, poly(x) = target`

where `poly : CMvDegreeLE R n deg` is a computable multivariate polynomial over `n` variables
with individual degree at most `deg`, `D` is a finite evaluation domain, and `target : R` is
the claimed sum.

A single round of sum-check is a two-message interaction:
1. **Prover → Verifier**: the prover sends the *round polynomial*, a `CDegreeLE R deg`
   univariate polynomial obtained by keeping one variable free and summing the rest over `D`.
2. **Verifier → Prover**: the verifier replies with a random field challenge `r_i`.

After round `i`, the target is updated to `p_i(r_i)`. The public *stage state*
(`RoundClaim R`) carries only this target; challenge history lives in the chained transcript.

## Main Definitions

- `RoundClaim R`: the public per-round claim (target value).
- `underlyingRoundSpec R deg`: the plain `Interaction.Spec` projection for one round.
- `underlyingRoundRoles R deg`: the corresponding plain role decoration.
- `underlyingRoleChain`: the `n`-round plain `RoleChain` projection.
- `advance`: updates the claim after a round (`target ↦ poly.eval(challenge)`).
- `roundCheck`: the per-round sum check (computable `Bool`).
- `RoundCheckProp`: propositional version of `roundCheck`.
- `fullSum`: the full sum `∑_{x ∈ D^n} poly(x)` that sum-check verifies.
- `PolyStmt` / `PolyFamily`: the fixed original polynomial oracle statement.
- `underlyingSpec` / `underlyingRoles`: the `n`-round replicated plain interaction surface.
- `challengePrefix`: extract the verifier challenges already present in a
  replicated-round transcript.
-/

namespace Sumcheck

open Interaction CompPoly CPoly

/-- The fixed polynomial oracle statement with `numVars` variables. -/
abbrev PolyStmt (R : Type) [BEq R] [CommSemiring R] [LawfulBEq R]
    (deg : ℕ) (numVars : ℕ) :=
  CMvDegreeLE R numVars deg

/-- The singleton oracle family carrying the original sum-check polynomial. -/
abbrev PolyFamily (R : Type) [BEq R] [CommSemiring R] [LawfulBEq R]
    (deg : ℕ) (numVars : ℕ) : Unit → Type :=
  fun _ => PolyStmt R deg numVars

section

variable (R : Type) [BEq R] [CommSemiring R] [LawfulBEq R] (deg : ℕ)

/-- The public claim at each round of sum-check: just the target sum value. -/
abbrev RoundClaim := R

/-- Terminal public output of an `n`-round sum-check: the verifier challenge
point together with the claimed value of the original polynomial at that point.

Rejection is represented by wrapping this in `Option`. -/
structure FinalClaim (numVars : Nat) where
  point : Fin numVars → R
  value : R

/-! ## Single-round interaction shape -/

/-- The plain `Interaction.Spec` projection for a single round: prover sends a
degree-bounded univariate polynomial (`CDegreeLE R deg`), then verifier sends a
field element challenge. -/
def underlyingRoundSpec : Spec :=
  .node (CDegreeLE R deg) fun _ =>
    .node R fun _ =>
      .done

/-- Plain role decoration for a single round: prover (sender) sends first,
verifier (receiver) sends second. -/
def underlyingRoundRoles : RoleDecoration (underlyingRoundSpec R deg) :=
  ⟨.sender, fun _ => ⟨.receiver, fun _ => ⟨⟩⟩⟩

/-- The plain `n`-round role chain for sum-check. The protocol shape is
constant; stateful information belongs to the parties, not the chain. -/
def underlyingRoleChain (n : Nat) : Spec.RoleChain n :=
  Spec.RoleChain.replicate (underlyingRoundSpec R deg) (underlyingRoundRoles R deg) n

/-- The plain `n`-round interaction projection for sum-check. -/
abbrev underlyingSpec (n : Nat) : Spec :=
  Spec.RoleChain.toSpec n (underlyingRoleChain R deg n)

/-- The role decoration for the plain `n`-round replicated interaction projection. -/
abbrev underlyingRoles (n : Nat) : RoleDecoration (underlyingSpec R deg n) :=
  Spec.RoleChain.toRoles n (underlyingRoleChain R deg n)

/-- Extract the polynomial from a single-round transcript. -/
abbrev underlyingRoundPoly (tr : Spec.Transcript (underlyingRoundSpec R deg)) :
    CDegreeLE R deg :=
  tr.1

/-- Extract the challenge from a single-round transcript. -/
abbrev underlyingRoundChallenge (tr : Spec.Transcript (underlyingRoundSpec R deg)) :
    R :=
  tr.2.1

/-- Extract the `i`-th round transcript from an `n`-round transcript. -/
def underlyingRoundTranscript (n : Nat)
    (tr : Spec.Transcript (underlyingSpec R deg n)) (i : Fin n) :
    Spec.Transcript (underlyingRoundSpec R deg) :=
  match n with
  | 0 => i.elim0
  | n + 1 =>
      let split := Spec.RoleChain.splitTranscript n (underlyingRoleChain R deg (n + 1)) tr
      Fin.cases split.1
        (fun i => underlyingRoundTranscript n split.2 i)
        i

/-- Extract the prefix of verifier challenges from an `n`-round replicated
transcript. -/
def challengePrefix (n : Nat) (tr : Spec.Transcript (underlyingSpec R deg n)) :
    Fin n → R :=
  fun i => underlyingRoundChallenge R deg (underlyingRoundTranscript R deg n tr i)

/-- Advance the public claim after one round: evaluate the sent polynomial at the challenge.
This is the state chain `advance` function. The new target is `poly.eval(challenge)`. -/
def advance
    (_ : Nat) (_ : RoundClaim R) (tr : Spec.Transcript (underlyingRoundSpec R deg)) :
    RoundClaim R :=
  CPolynomial.eval (underlyingRoundChallenge R deg tr) (underlyingRoundPoly R deg tr).1

/-! ## Per-round sum check -/

/-- The per-round sum check: verify that the univariate polynomial's evaluations over the
domain `D` sum to the claimed target. This is the defining check of sum-check. -/
def roundCheck {m_dom : ℕ} (D : Fin m_dom → R) (target : RoundClaim R)
    (poly : CDegreeLE R deg) : Bool :=
  ((Finset.univ : Finset (Fin m_dom)).sum fun j => CPolynomial.eval (D j) poly.1) == target

/-- Propositional version of `roundCheck`: the polynomial's evaluations over `D`
sum to the target. -/
def RoundCheckProp {m_dom : ℕ} (D : Fin m_dom → R) (target : RoundClaim R)
    (poly : CDegreeLE R deg) : Prop :=
  ((Finset.univ : Finset (Fin m_dom)).sum fun j => CPolynomial.eval (D j) poly.1) = target

/-- The full sum `∑_{z ∈ D^n} poly(D ∘ z)` of a multivariate polynomial over the product domain.
This is the claimed quantity in sum-check: the protocol verifies `fullSum D poly = target`. -/
def fullSum {n : ℕ} {m_dom : ℕ} (D : Fin m_dom → R) (poly : PolyStmt R deg n) : R :=
  (Finset.univ : Finset (Fin n → Fin m_dom)).sum fun z =>
    CMvPolynomial.eval (D ∘ z) poly.1

/-- Replay the verifier's current claim across an `n`-round replicated
sum-check transcript. Later rounds are ignored once a check fails. -/
def statementResult {m_dom : Nat} (D : Fin m_dom → R) :
    (n : Nat) → RoundClaim R → Spec.Transcript (underlyingSpec R deg n) → Option (RoundClaim R)
| 0, target, _ => some target
| n + 1, target, tr =>
    let ⟨tr₁, trRest⟩ := Spec.RoleChain.splitTranscript n
      (underlyingRoleChain R deg (n + 1)) tr
    if roundCheck R deg D target (underlyingRoundPoly R deg tr₁) then
      statementResult D n (advance R deg 0 target tr₁) trRest
    else
      none

end

end Sumcheck

