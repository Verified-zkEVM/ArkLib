/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.Logup.Lookup.Tuple.Completeness
import ArkLib.Interaction.Oracle.LoggedExecution
import ArkLib.Data.Probability.KoalaBear
import Mathlib.Algebra.Field.ZMod
import Lean.Compiler.IR

/-! # Genuine tuple witnesses, colliding fingerprints and actual coefficient-source completeness -/

open Interaction.Oracle OracleComp OracleSpec CompPoly Logup.Lookup Logup.Lookup.Tuple
open Logup.Lookup.Tuple.Honest
open scoped BigOperators ENNReal ProbabilityTheory
open Lean Elab Command
namespace LogupTupleHonestTest
namespace Small
abbrev F := ZMod 17
instance : Fact (Nat.Prime 17) := ⟨by decide⟩
def f : F →+* F := RingHom.id F
def cfg : Config F 1 1 3 1 := (Config.create? F 1 1 3 1 17).get (by decide)
def schema : TaggedTuple.Schema F 2 2 :=
  (TaggedTuple.Schema.mk? #v[2, 1] #v[2, 3]).get (by decide)
def layout : ProviderLayout 2 3 := (ProviderLayout.create? 2 3 #[0, 1, 1]).get (by decide)
def keys : Vector (CMlPolynomialEval schema.Key 1) 4 :=
  #v[#v[⟨0, #v[0, 1]⟩, ⟨1, #v[0]⟩],
    #v[⟨0, #v[0, 1]⟩, ⟨0, #v[0, 0]⟩],
    #v[⟨1, #v[0]⟩, ⟨1, #v[0]⟩],
    #v[⟨1, #v[0]⟩, ⟨1, #v[0]⟩]]
def prepared : PreparedProvider schema layout 1 1 :=
  PreparedProvider.prepare schema layout keys (by decide)
def indices : Vector (Fin 6) 2 := #v[0, 2]
theorem valid : ValidIndices prepared.keyData indices := by unfold ValidIndices; decide
theorem duplicate_valid : ValidIndices prepared.keyData #v[0, 3] := by unfold ValidIndices; decide
abbrev access := (coefficientFamily f 1 1 3 2).spec.toPFunctor
def impl : QueryImpl (ofPFunctor access) Id :=
  (coefficientFamily f 1 1 3 2).behaviorOfRealizations
    (fun sj => prepared.coefficientTable sj.1 sj.2)
def view := VirtualOracle.id (coefficientFamily f 1 1 3 2)
theorem realizes : view.eval impl = (coefficientFamily f 1 1 3 2).behaviorOfRealizations
    (fun sj => prepared.coefficientTable sj.1 sj.2) := VirtualOracle.eval_id impl

def build := Logup.Prover.Honest.pureBuilder (E := F) cfg.weighted.groups
  cfg.weighted.length_group_le

theorem hash_A (beta : F) : schema.fingerprint f beta ⟨0, #v[0, 1]⟩ =
    2 * beta ^ 2 + beta := by
  rw [TaggedTuple.Schema.fingerprint_eq_sum]
  change (2 : F) * beta ^ 2 + (∑ j : Fin 2, (#v[0, 1] : Vector F 2)[j.val] * beta ^ j.val) = _
  simp [Fin.sum_univ_succ]

theorem hash_C (beta : F) : schema.fingerprint f beta ⟨0, #v[0, 0]⟩ = 2 * beta ^ 2 := by
  rw [TaggedTuple.Schema.fingerprint_eq_sum]
  change (2 : F) * beta ^ 2 + (∑ j : Fin 2, (#v[0, 0] : Vector F 2)[j.val] * beta ^ j.val) = _
  simp [Fin.sum_univ_succ]

theorem hash_B (beta : F) : schema.fingerprint f beta ⟨1, #v[0]⟩ = 3 * beta ^ 2 := by
  rw [TaggedTuple.Schema.fingerprint_eq_sum]
  change (3 : F) * beta ^ 2 + (∑ j : Fin 1, (#v[0] : Vector F 1)[j.val] * beta ^ j.val) = _
  simp

theorem offPole_collisions (beta : F) (hbeta : beta = 0 ∨ beta = 1) :
    (5 : F) ∉ Logup.Lookup.Honest.tableSupport (RingHom.id F)
      (prepared.fingerprintData f beta) := by
  rw [Logup.Lookup.Honest.mem_tableSupport]
  rintro ⟨piece, row, heq⟩
  simp only [PreparedProvider.fingerprintData, Vector.get_eq_getElem,
    Vector.getElem_map, RingHom.id_apply] at heq
  fin_cases piece <;> fin_cases row
  all_goals
    first
    | change schema.fingerprint f beta ⟨0, #v[0, 1]⟩ = 5 at heq
      rw [hash_A] at heq
    | change schema.fingerprint f beta ⟨0, #v[0, 0]⟩ = 5 at heq
      rw [hash_C] at heq
    | change schema.fingerprint f beta ⟨1, #v[0]⟩ = 5 at heq
      rw [hash_B] at heq
  all_goals rcases hbeta with rfl | rfl
  all_goals first
    | exact (show (0 : F) ≠ 5 by decide) heq
    | exact (show (2 : F) ≠ 5 by decide) heq
    | exact (show (3 : F) ≠ 5 by decide) heq

def uniform : ProbComp Bool := Tuple.uniformExecute f 1 1 3 2 1 cfg access view impl
  (proverWith f cfg prepared indices unifSpec build)

theorem failure : Pr{let accepted ← uniform}[accepted = false] ≤ (6 : ℝ≥0∞) / 17 := by
  unfold uniform
  have h := uniformExecute_proverWith_failure_le_rows f cfg prepared indices valid build
    (Logup.Prover.Honest.pureBuilder_correct (E := F) _ _) access view impl realizes
  simpa only [Nat.reducePow, Nat.reduceMul, Nat.cast_ofNat, ZMod.card] using h

theorem success : (11 : ℝ≥0∞) / 17 ≤ Pr{let accepted ← uniform}[accepted = true] := by
  unfold uniform
  have h := uniformExecute_proverWith_success_ge_rows f cfg prepared indices valid build
    (Logup.Prover.Honest.pureBuilder_correct (E := F) _ _) access view impl realizes
  have harith : (11 : ℝ≥0∞) / 17 = 1 - 6 / 17 := by
    have hself : (17 : ℝ≥0∞) / 17 = 1 := ENNReal.div_self (by norm_num) (by norm_num)
    rw [← hself, ← ENNReal.sub_div (by intros; norm_num)]
    congr 1
    exact_mod_cast (show (11 : Nat) = 17 - 6 by rfl)
  rw [harith]
  simpa only [Nat.reducePow, Nat.reduceMul, Nat.cast_ofNat, ZMod.card] using h

theorem total : Pr{let _ ← uniform}[True] = 1 :=
  uniformExecute_proverWith_total f cfg prepared indices build access view impl

abbrev combined := Tuple.protocol f 1 1 3 1
abbrev ambient : OracleSpec (Fin 4) := Fin 4 →ₒ F
def event (i : Fin 4) : OracleComp ambient F := liftM (ambient.query i)
def joint : OracleComp ambient ((Fin 1 → F) × (Fin 4 → F)) := do
  let z ← event 2
  return (fun _ => z, ![4, 9, 6, 3])
def logger (beta alpha : F) : QueryImpl ambient (StateM (List Nat)) := fun i => do
  modify (· ++ [i.val])
  return ![beta, alpha, 2, 5] i
abbrev Result := LoggedResult combined.tree combined.oracles access (fun _ => Unit) (fun _ => Bool)
def run (witness : Vector (Fin 6) 2) : OracleComp ambient Result := executeStrategiesLogged
  ambient combined.tree combined.roles combined.oracles access impl
  (proverWith f cfg prepared witness ambient build)
  (Tuple.verifier f 1 1 3 2 1 cfg ambient (event 0) (event 1) joint (event 3) access view)
set_option backward.isDefEq.respectTransparency false in
def pathData (path : combined.tree.ExecutionPath) :
    Vector (CMlPolynomialEval F 1) 3 × F × CPolynomial.Raw F :=
  (path.1, path.2.1, path.2.2.2.2.2.1.val.val)

def summarize (result : Result × List Nat) :
    Bool × (Vector (CMlPolynomialEval F 1) 3 × F × CPolynomial.Raw F) × Nat × List Nat :=
  (result.1.verifierOut, pathData result.1.path, result.1.sourceLog.length, result.2)
def summary (beta alpha : F) (witness : Vector (Fin 6) 2 := indices) :
    Bool × (Vector (CMlPolynomialEval F 1) 3 × F × CPolynomial.Raw F) × Nat × List Nat :=
  summarize ((simulateQ (logger beta alpha) (run witness)).run [])

/-- Both collision challenges have supported completeness for arbitrary later draw programs. -/
theorem supported (beta : F) (hbeta : beta = 0 ∨ beta = 1)
    (jointDraw : OracleComp ambient ((Fin 1 → F) × (Fin 4 → F)))
    (roundDraw : OracleComp ambient F) :
    ∀ accepted ∈ support (Tuple.execute f 1 1 3 2 1 cfg ambient (pure beta) (pure 5)
      jointDraw roundDraw access view impl
      (proverWith f cfg prepared indices ambient build)), accepted = true := by
  apply execute_proverWith_support_completeness f cfg prepared indices valid ambient build
    (Logup.Prover.Honest.pureBuilder_correct (E := F) _ _) (pure beta) (pure 5) _
    jointDraw roundDraw access view impl realizes
  intro b hb alpha ha
  have hbeq : b = beta := by simpa only [support_pure, Set.mem_singleton_iff] using hb
  have haeq : alpha = 5 := by simpa only [support_pure, Set.mem_singleton_iff] using ha
  subst b
  subst alpha
  exact offPole_collisions beta hbeta
end Small

namespace ZeroRound
abbrev F := Small.F
def f : F →+* F := RingHom.id F
def cfg : Config F 0 1 2 1 := (Config.create? F 0 1 2 1 17).get (by decide)
def schema : TaggedTuple.Schema F 2 0 :=
  (TaggedTuple.Schema.mk? #v[0, 0] #v[0, 1]).get (by decide)
def layout : ProviderLayout 2 2 := (ProviderLayout.create? 2 2 #[0, 1]).get (by decide)
def keys : Vector (CMlPolynomialEval schema.Key 0) 3 :=
  #v[#v[⟨0, #v[]⟩], #v[⟨0, #v[]⟩], #v[⟨1, #v[]⟩]]
def prepared : PreparedProvider schema layout 0 1 :=
  PreparedProvider.prepare schema layout keys (by decide)
def indices : Vector (Fin 2) 1 := #v[0]
theorem valid : ValidIndices prepared.keyData indices := by unfold ValidIndices; decide
abbrev access := (coefficientFamily f 0 1 2 0).spec.toPFunctor
def impl : QueryImpl (ofPFunctor access) Id :=
  (coefficientFamily f 0 1 2 0).behaviorOfRealizations
    (fun sj => prepared.coefficientTable sj.1 sj.2)
def view := VirtualOracle.id (coefficientFamily f 0 1 2 0)
def build := Logup.Prover.Honest.pureBuilder (E := F) cfg.weighted.groups
  cfg.weighted.length_group_le
abbrev ambient := Small.ambient
def joint : OracleComp ambient ((Fin 0 → F) × (Fin 3 → F)) := do
  let a ← Small.event 2
  return (Fin.elim0, ![a, 9, 6])
def run : OracleComp ambient Bool := Tuple.execute f 0 1 2 0 1 cfg ambient
  (Small.event 0) (Small.event 1) joint (Small.event 3) access view impl
  (proverWith f cfg prepared indices ambient build)
def summary (beta alpha : F) : Bool × List Nat :=
  (simulateQ (Small.logger beta alpha) run).run []
end ZeroRound

namespace Extension
abbrev B := KoalaBear.Field
abbrev E := KoalaBear.Ext6
def f : B →+* E := algebraMap B E
def cfg : Config B 1 1 3 1 := (Config.create? B 1 1 3 1 KoalaBear.fieldSize).get (by decide)
def schema : TaggedTuple.Schema B 2 2 :=
  (TaggedTuple.Schema.mk? #v[2, 1] #v[2, 3]).get (by decide)
def keys : Vector (CMlPolynomialEval schema.Key 1) 4 :=
  #v[#v[⟨0, #v[0, 1]⟩, ⟨1, #v[0]⟩],
    #v[⟨0, #v[0, 1]⟩, ⟨0, #v[0, 0]⟩],
    #v[⟨1, #v[0]⟩, ⟨1, #v[0]⟩],
    #v[⟨1, #v[0]⟩, ⟨1, #v[0]⟩]]
def prepared : PreparedProvider schema Small.layout 1 1 :=
  PreparedProvider.prepare schema Small.layout keys (by decide)
theorem valid : ValidIndices prepared.keyData Small.indices := by unfold ValidIndices; decide
abbrev access := (coefficientFamily f 1 1 3 2).spec.toPFunctor
def impl : QueryImpl (ofPFunctor access) Id :=
  (coefficientFamily f 1 1 3 2).behaviorOfRealizations
    (fun sj => prepared.coefficientTable sj.1 sj.2)
def view := VirtualOracle.id (coefficientFamily f 1 1 3 2)
theorem realizes : view.eval impl = (coefficientFamily f 1 1 3 2).behaviorOfRealizations
    (fun sj => prepared.coefficientTable sj.1 sj.2) := VirtualOracle.eval_id impl

def build := Logup.Prover.Honest.pureBuilder (E := E) cfg.weighted.groups
  cfg.weighted.length_group_le
abbrev ambient : OracleSpec Unit := Unit →ₒ E
def round : OracleComp ambient E := liftM (ambient.query ())
def logger : QueryImpl ambient (StateM Nat) := fun _ => do
  modify (· + 1)
  return KoalaBear.ext6Gen
def run : OracleComp ambient Bool := Tuple.execute f 1 1 3 2 1 cfg ambient
  (pure KoalaBear.ext6Gen) (pure 2)
  (pure ((fun _ => KoalaBear.ext6Gen), ![KoalaBear.ext6Gen, 1, KoalaBear.ext6Gen ^ 2, 3]))
  round access view impl (proverWith f cfg prepared Small.indices ambient build)
def summary : Bool × Nat := (simulateQ logger run).run 0

def uniform : ProbComp Bool := Tuple.uniformExecute f 1 1 3 2 1 cfg access view impl
  (proverWith f cfg prepared Small.indices unifSpec build)
theorem total : Pr{let _ ← uniform}[True] = 1 :=
  uniformExecute_proverWith_total f cfg prepared Small.indices build access view impl
end Extension

run_cmd do
  let mu : Vector (CMlPolynomialEval Small.F 1) 3 := #v[#v[1, 0], #v[1, 0], #v[0, 0]]
  unless Small.summary 0 5 == (true, (mu, 0, #[10, 14]), 22, [0, 1, 2, 3]) do
    throwError "true tuple lookup failed at beta0 collision or lost actual prefix/source routing"
  unless Small.summary 1 5 == (true, (mu, 1, #[8, 14, 16, 5]), 22, [0, 1, 2, 3]) do
    throwError "true tuple lookup failed at beta1 collision or changed its actual cubic"
  unless Small.summary 1 2 == (true, (mu, 1, #[1, 6, 2, 7]), 22, [0, 1, 2, 3]) do
    throwError "unused table pole caused a retry or changed actual retained-helper reconstruction"
  unless Small.summary 0 0 == (false, (mu, 0, #[6, 14, 6]), 2, [0, 1, 2]) do
    throwError "active-pole abort drew a native challenge or skipped actual first-round checks"
  unless Small.summary 1 5 #v[0, 3] ==
      (true, (#v[#v[1, 0], #v[0, 1], #v[0, 0]], 1, #[0, 13, 16, 5]), 22, [0, 1, 2, 3]) do
    throwError "a different valid duplicate table position was canonicalized or lost"
  for beta in List.finRange 17 do
    unless ZeroRound.summary beta.val 2 == (true, [0, 1, 2]) do
      throwError "width0/tag0 honest tuple did not accept every beta without native rounds"
  unless ZeroRound.summary 0 1 == (true, [0, 1, 2]) &&
      ZeroRound.summary 0 0 == (false, [0, 1, 2]) do
    throwError "zero-round actual terminal authentication lost active/unused table-pole distinction"
  unless Extension.summary == (true, 1) do
    throwError "genuine base-to-Ext6 tuple source/ordinary honest endpoint failed at theta"

run_cmd do
  for name in #[``proverWith, ``Small.run, ``Small.pathData, ``Small.summarize,
      ``Small.summary, ``Small.uniform, ``ZeroRound.run, ``Extension.run, ``Extension.uniform] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing ordinary tuple honest executable IR: {name}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``validIndices_fingerprintData, ``execute_proverWith_eq,
      ``valueSupport_weighted_eq_tableSupport, ``uniformExecute_proverWith_eq,
      ``execute_proverWith_support_completeness, ``uniformExecute_proverWith_failure_le_rows,
      ``uniformExecute_proverWith_success_ge_rows, ``uniformExecute_proverWith_total,
      ``Small.valid, ``Small.duplicate_valid, ``Small.realizes, ``Small.hash_A, ``Small.hash_C,
      ``Small.hash_B, ``Small.offPole_collisions, ``Small.failure, ``Small.success, ``Small.total,
      ``Small.supported, ``ZeroRound.valid, ``Extension.valid, ``Extension.realizes,
      ``Extension.total] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "tuple honest completeness has an unexpected axiom: {name}"
end LogupTupleHonestTest
