/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.ProtocolSpec.SeqCompose
import ArkLibTest.Data.Fin.Tuple.Lemmas

/-!
# Compiled reads of composed protocol specifications

Read challenge instances and transcripts through append and sequential composition.
-/

open ProtocolSpec

namespace ArkLibTest.SeqComposeCompiled

/-- One challenge round, from `Fin 7`. -/
abbrev chal : ProtocolSpec 1 := ⟨fun _ => .V_to_P, fun _ => Fin 7⟩

instance : ∀ i, Inhabited (chal.Challenge i) := fun _ => ⟨3⟩

/-- The number of rounds of `chals k`, as the appends add it up. -/
def len : ℕ → ℕ
  | 0 => 0
  | k + 1 => 1 + len k

/-- `k` challenge rounds, each prepended to the rest. -/
def chals : (k : ℕ) → ProtocolSpec (len k)
  | 0 => !p[]
  | k + 1 => chal ++ₚ chals k

/-- Every round of `chals k` is a challenge. -/
theorem chals_dir : ∀ (k : ℕ) (i : Fin (len k)), (chals k).dir i = .V_to_P
  | 0, i => i.elim0
  | k + 1, i => by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact Fin.vappend_left _ _ j
    · exact (Fin.vappend_right _ _ j).trans (chals_dir k j)

/-- Every round of `chals k` is from `Fin 7`. -/
theorem chals_type : ∀ (k : ℕ) (i : Fin (len k)), (chals k).Type i = Fin 7
  | 0, i => i.elim0
  | k + 1, i => by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact Fin.vappend_left _ _ j
    · exact (Fin.vappend_right _ _ j).trans (chals_type k j)

/-- The challenges' defaults of `chals k`, by the instance of `++ₚ` at every round. -/
@[instance_reducible]
def chalsDefault : (k : ℕ) → ∀ i, Inhabited ((chals k).Challenge i)
  | 0 => fun i => i.1.elim0
  | k + 1 => instInhabitedChallengeAppend (pSpec₁ := chal) (pSpec₂ := chals k)
      (h₂ := chalsDefault k)

/-- A transcript of `chals k`: round `i` holds `k - 1 - i`, modulo `7`. -/
def chalsTranscript : (k : ℕ) → (chals k).FullTranscript
  | 0 => fun i => i.elim0
  | k + 1 => (fun _ => Fin.ofNat 7 k : chal.FullTranscript) ++ₜ chalsTranscript k

/-- `k` challenge rounds, composed by `seqCompose`. -/
abbrev seqChals (k : ℕ) := seqCompose fun _ : Fin k => chal

/-- Every round of `seqChals k` is a challenge. -/
theorem seqChals_dir (k : ℕ) (i : Fin k) : (seqChals k).dir (Fin.embedSum i 0) = .V_to_P :=
  Fin.vflatten_embedSum (fun _ : Fin k => chal.dir) i 0

/-- Every round of `seqChals k` is from `Fin 7`. -/
theorem seqChals_type (k : ℕ) (i : Fin k) : (seqChals k).Type (Fin.embedSum i 0) = Fin 7 :=
  Fin.vflatten_embedSum (fun _ : Fin k => chal.Type) i 0

/-- A transcript of `seqChals k`: round `i` holds `i`, modulo `7`. -/
def seqTranscript (k : ℕ) : (seqChals k).FullTranscript :=
  FullTranscript.seqCompose fun i => (fun _ => Fin.ofNat 7 i.val : chal.FullTranscript)

/-- The challenge defaults of `chals k`, in order. -/
def chalsDefaults (k : ℕ) : List (Fin 7) :=
  List.ofFn fun i => cast (chals_type k i) (@default _ (chalsDefault k ⟨i, chals_dir k i⟩))

/-- The entries of `chalsTranscript k`, in order. -/
def chalsEntries (k : ℕ) : List (Fin 7) :=
  List.ofFn fun i => cast (chals_type k i) (chalsTranscript k i)

/-- The challenge defaults of `seqChals k`, in order. -/
def seqDefaults (k : ℕ) : List (Fin 7) :=
  List.ofFn fun i : Fin k => cast (seqChals_type k i)
    (@default _ (instInhabitedChallengeSeqCompose (pSpec := fun _ : Fin k => chal)
      ⟨Fin.embedSum i 0, seqChals_dir k i⟩))

/-- The entries of `seqTranscript k`, in order. -/
def seqEntries (k : ℕ) : List (Fin 7) :=
  List.ofFn fun i : Fin k => cast (seqChals_type k i) (seqTranscript k (Fin.embedSum i 0))

-- These ordinary callers require generated code, which reads every round by comparisons.
private def compiledChecks : IO Unit := do
  unless chalsDefaults 40 = List.replicate 40 3 do
    throw (IO.userError "Incorrect challenge defaults of prepended rounds")
  unless chalsEntries 40 = (List.range 40).reverse.map (Fin.ofNat 7) do
    throw (IO.userError "Incorrect entries of prepended transcripts")
  unless seqDefaults 40 = List.replicate 40 3 do
    throw (IO.userError "Incorrect challenge defaults of a sequential composition")
  unless seqEntries 40 = (List.range 40).map (Fin.ofNat 7) do
    throw (IO.userError "Incorrect entries of a sequentially composed transcript")
  IO.println "Compiled protocol specification checks passed."

-- The registrations are checked first, so that a missing one fails at once instead of running
-- the recursive definitions.
/-- info: Compiled protocol specification checks passed. -/
#guard_msgs in
#eval show Lean.Meta.MetaM Unit from do
  ArkLibTest.FinTupleCompiledForms.checkCompiledForms
  compiledChecks

end ArkLibTest.SeqComposeCompiled
