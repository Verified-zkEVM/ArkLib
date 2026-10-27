/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.Logup.Interaction.Source
import ArkLib.ProofSystem.Logup.Interaction.Config
import ArkLib.Data.Probability.KoalaBear
import Lean.Compiler.IR

/-!
# Actual retained Q source over a nontrivial base/challenge extension

The base table [0,1] is evaluated at the non-base generator theta of KoalaBear.Ext6. With the
arbitrary helper [0,1], scalar reconstruction is theta cubed; changing the actual retained helper
to zero changes that answer. The Boolean row zero is a denominator pole for alpha zero, so this
also exercises the unconditional realization contract. No honest-helper premise is supplied.
-/

open _root_.Interaction.Oracle OracleComp OracleSpec CompPoly

namespace Logup.Interaction.SourceTest

abbrev Base := KoalaBear.Field
abbrev Challenge := KoalaBear.Ext6

def embedding : Base →+* Challenge := algebraMap Base Challenge

def data (_ : Fin 2 × Fin 1) : CMlPolynomialEval Base 1 := #v[0, 1]
def helpers : Vector (CMlPolynomialEval Challenge 1) 1 := #v[#v[0, 1]]
def cfg : Config 1 1 1 := (Config.create? 1 1 1).get (by decide)
def groups : Vector (List (Fin 1)) 1 := cfg.groups

abbrev originalAccess := (inputFamily embedding 1 1).spec.toPFunctor

def originalHandler : QueryImpl (ofPFunctor originalAccess) Id :=
  (inputFamily embedding 1 1).behaviorOfRealizations data

def originalView : VirtualOracle (ofPFunctor originalAccess) (inputFamily embedding 1 1) :=
  VirtualOracle.id (inputFamily embedding 1 1)

abbrev retainedAccess := Access.extend originalAccess (helperInterface (E := Challenge) 1 1)

def retainedHandler (msg : Vector (CMlPolynomialEval Challenge 1) 1) :
    QueryImpl (ofPFunctor retainedAccess) Id :=
  Access.extendImpl originalAccess (helperInterface (E := Challenge) 1 1) originalHandler msg

def recorder (msg : Vector (CMlPolynomialEval Challenge 1) 1) :
    QueryImpl (ofPFunctor retainedAccess) (StateM (List Nat)) := fun q => do
  let tag := match q with
    | .inl t => t.1.1.val
    | .inr t => 2 + t.1.val
  modify (· ++ [tag])
  return retainedHandler msg q

def observed (msg : Vector (CMlPolynomialEval Challenge 1) 1) : Challenge × List Nat :=
  (simulateQ (recorder msg) (queryQ embedding 1 1 1 groups 0 (fun _ => 0) (fun _ => 1)
    originalAccess originalView (fun _ => KoalaBear.ext6Gen))).run []

def observedCoeffs (msg : Vector (CMlPolynomialEval Challenge 1) 1) :
    Vector Base 6 × List Nat :=
  (KoalaBear.Ext6.coeffsEquiv.symm (observed msg).1, (observed msg).2)

theorem original_realizes : originalView.eval originalHandler =
    (inputFamily embedding 1 1).behaviorOfRealizations data :=
  VirtualOracle.eval_id originalHandler

theorem group_bound : ∀ k : Fin 1, groups[k.val].length ≤ 1 := cfg.length_group_le

theorem source_realizes (msg : Vector (CMlPolynomialEval Challenge 1) 1) :
    (qView embedding 1 1 1 groups 0 (fun _ => 0) (fun _ => 1) 1
      originalAccess originalView).eval (retainedHandler msg) =
    (Sumcheck.Interaction.MultivariateRound.polynomialFamily Challenge 1 3).behaviorOfRealizations
      (fun _ => qPolynomial embedding 1 1 1 groups 0 (fun _ => 0) (fun _ => 1) 1
        group_bound data msg) :=
  qView_realizes embedding 1 1 1 groups 0 (fun _ => 0) (fun _ => 1) 1 group_bound
    originalAccess originalView originalHandler data original_realizes msg

namespace ZeroRows

def cfg : Config 0 1 1 := (Config.create? 0 1 1).get (by decide)
def groups : Vector (List (Fin 1)) 1 := cfg.groups

def data (i : Fin 2 × Fin 1) : CMlPolynomialEval Base 0 :=
  if i.1 = 0 then #v[3] else #v[2]

def helpers : Vector (CMlPolynomialEval Challenge 0) 1 := #v[#v[7]]
abbrev originalAccess := (inputFamily embedding 0 1).spec.toPFunctor

def originalHandler : QueryImpl (ofPFunctor originalAccess) Id :=
  (inputFamily embedding 0 1).behaviorOfRealizations data

def originalView : VirtualOracle (ofPFunctor originalAccess) (inputFamily embedding 0 1) :=
  VirtualOracle.id (inputFamily embedding 0 1)

abbrev retainedAccess := Access.extend originalAccess (helperInterface (E := Challenge) 0 1)
def retainedHandler : QueryImpl (ofPFunctor retainedAccess) Id :=
  Access.extendImpl originalAccess (helperInterface (E := Challenge) 0 1) originalHandler helpers

def recorder : QueryImpl (ofPFunctor retainedAccess) (StateM (List Nat)) := fun q => do
  let tag := match q with
    | .inl t => t.1.1.val
    | .inr t => 2 + t.1.val
  modify (· ++ [tag])
  return retainedHandler q

/-- At the pole alpha=value=3, arbitrary helper7 gives Q=7+5*(7*0-2)=-3. -/
def observed : Challenge × List Nat :=
  (simulateQ recorder (queryQ embedding 0 1 1 groups 3 Fin.elim0 (fun _ => 5)
    originalAccess originalView Fin.elim0)).run []

theorem source_realizes :
    (qView embedding 0 1 1 groups 3 Fin.elim0 (fun _ => 5) 1
      originalAccess originalView).eval retainedHandler =
    (Sumcheck.Interaction.MultivariateRound.polynomialFamily Challenge 0 3).behaviorOfRealizations
      (fun _ => qPolynomial embedding 0 1 1 groups 3 Fin.elim0 (fun _ => 5) 1
        cfg.length_group_le data helpers) :=
  qView_realizes embedding 0 1 1 groups 3 Fin.elim0 (fun _ => 5) 1 cfg.length_group_le
    originalAccess originalView originalHandler data (VirtualOracle.eval_id originalHandler) helpers

end ZeroRows

open Lean Elab Command

run_cmd do
  unless observedCoeffs helpers == (#v[0, 0, 0, 1, 0, 0], [0, 1, 2]) do
    throwError "retained Ext6 Q source changed theta cubed or its ordered queries"
  unless observedCoeffs #v[#v[0, 0]] == (#v[0, -1, 1, 0, 0, 0], [0, 1, 2]) do
    throwError "Q source substituted an earlier input for the actual changed helper"
  unless ZeroRows.observed == (-3, [0, 1, 2]) do
    throwError "zero-variable Q source changed its pole semantics or retained source queries"
  for name in #[``baseTableInterface, ``inputFamily, ``helperInterface, ``queryInput,
      ``queryHelper, ``queryQ, ``qView, ``embedding, ``originalHandler,
      ``recorder, ``observed, ``observedCoeffs, ``ZeroRows.observed] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing source or external extension-field caller IR: {name}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``CMlPolynomialEval.eval₂Mle_eq_MvPolynomial_MLE,
      ``eval₂Mle_eq_tablePolynomial, ``queryQ_eval, ``qView_realizes,
      ``original_realizes, ``source_realizes, ``ZeroRows.source_realizes] do
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do
      throwError "unexpected axioms in `{name}`: {axioms}"

end Logup.Interaction.SourceTest
