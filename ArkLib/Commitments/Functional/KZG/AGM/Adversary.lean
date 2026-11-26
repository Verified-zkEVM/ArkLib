/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Commitments.Functional.KZG.Security
public import VCVio.CryptoFoundations.GroupModel.Interaction

/-!
# Algebraic KZG adversaries

Two source sorts receive the committer and verifier keys. Uniform sampling supplies all coins;
it adds no group inputs. Decoding forgets explanations, while extraction reads coefficients.

References: [KZG10TR]; Fuchsbauer, Kiltz, and Loss, *The Algebraic Group Model and its
Applications*, CRYPTO 2018.
-/

@[expose] public section

open OracleComp OracleSpec GroupModel.Interaction

namespace KZG.AGM

abbrev Group (G₁ G₂ : Type) : Bool → Type
  | false => G₁
  | true => G₂

instance {G₁ G₂ : Type} [AddMonoid G₁] [AddMonoid G₂] (s : Bool) :
    AddMonoid (Group G₁ G₂ s) := by cases s <;> dsimp [Group] <;> infer_instance

instance {F G₁ G₂ : Type} [SMul F G₁] [SMul F G₂] (s : Bool) :
    SMul F (Group G₁ G₂ s) := by cases s <;> dsimp [Group] <;> infer_instance

def groupInputs {G₁ G₂ : Type} (xs : List G₁) (ys : List G₂) : Groups (Group G₁ G₂)
  | false => xs
  | true => ys

abbrev Adversary (F G₁ G₂ D : Type) [Zero F] [AddMonoid G₁] [AddMonoid G₂]
    [SMul F G₁] [SMul F G₂] :=
  GroupModel.Interaction.Adversary F (Group G₁ G₂) Unit ℕ (fun k => Fin (k + 1)) D

abbrev Output (F G₁ G₂ D : Type) := Explained F D (Group G₁ G₂)

def initialInput {G₁ G₂ : Type} {n : ℕ} (ck : Fin (n + 1) → G₁) (vk : Fin 2 → G₂) :
    Message Unit (Group G₁ G₂) := ⟨(), groupInputs (List.ofFn ck) (List.ofFn vk)⟩

/-- Coins are forwarded to `unifSpec`; no group elements are returned. -/
def oracle {G₁ G₂ : Type} :
    QueryImpl (plainSpec (Group G₁ G₂) ℕ (fun k => Fin (k + 1))) ProbComp :=
  fun q => do
    let r ← unifSpec.query q.data
    return ⟨r, groupInputs [] []⟩

variable {F G₁ G₂ D : Type} [Field F] [AddCommGroup G₁] [Module F G₁]
  [AddCommGroup G₂] [Module F G₂] {n : ℕ}

/-- Execute the adversary with its original uniform coins. -/
def run (A : Adversary F G₁ G₂ D) (ck : Fin (n + 1) → G₁) (vk : Fin 2 → G₂) :
    ProbComp (Output F G₁ G₂ D) :=
  simulateQ (fun q => oracle q.value) (A.main (initialInput ck vk))

/-- Every reachable output is explained over exactly the initial keys. -/
theorem run_valid (A : Adversary F G₁ G₂ D) (ck : Fin (n + 1) → G₁) (vk : Fin 2 → G₂)
    (out : Output F G₁ G₂ D) (hout : out ∈ support (run A ck vk)) :
    out.Valid (initialInput ck vk).groups := by
  have h := A.algebraic (initialInput ck vk)
  unfold run at hout
  generalize A.main (initialInput ck vk) = program at h hout
  induction program using OracleComp.inductionOn with
  | pure x =>
      simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at hout
      subst out
      exact h
  | query_bind q next ih =>
      change IsAlgebraic (Reply := fun k => Fin (k + 1)) (initialInput ck vk).groups
        (liftM ((explainedSpec F (Group G₁ G₂) ℕ (fun k => Fin (k + 1))).query q) >>= next) at h
      obtain ⟨_, hn⟩ := (isAlgebraic_query (Reply := fun k => Fin (k + 1)) _ q next).mp h
      simp only [simulateQ_bind, simulateQ_spec_query, oracle, bind_assoc, pure_bind] at hout
      rw [mem_support_bind_iff] at hout
      obtain ⟨r, _, hr⟩ := hout
      apply ih _ ?_ hr
      have hb : extend (initialInput ck vk).groups (groupInputs [] []) =
          (initialInput ck vk).groups := by
        funext s
        cases s <;> simp [extend, groupInputs]
      simpa only [hb] using hn ⟨r, groupInputs [] []⟩

/-- Read a group output, defaulting to zero when the adversary omits it. -/
def point (out : Output F G₁ G₂ D) (i : ℕ) : G₁ :=
  (out.value.groups false)[i]?.getD 0

/-- Read an explanation as a coefficient vector, padding missing entries with zero.
In particular, the extractor `coefficients out 0` only reads the commitment's coefficients. -/
def coefficients (out : Output F G₁ G₂ D) (i : ℕ) : Fin (n + 1) → F :=
  fun j => (((out.coefficients false)[i]?).getD [])[j.val]?.getD 0

private theorem evaluate_ofFn (cs : List F) (ck : Fin (n + 1) → G₁) :
    GroupModel.Interaction.evaluate cs (List.ofFn ck) =
      commit ck (fun j => cs[j.val]?.getD 0) := by
  unfold GroupModel.Interaction.evaluate
  have hm : (List.ofFn ck).mapIdx (fun i g => cs[i]?.getD 0 • g) =
      List.ofFn (fun j : Fin (n + 1) => cs[j.val]?.getD 0 • ck j) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_mapIdx, List.getElem_ofFn]
  rw [hm, List.sum_ofFn]
  rfl

/-- Each decoded group element equals the commitment to its decoded explanation. -/
theorem point_eq_commit (out : Output F G₁ G₂ D) (ck : Fin (n + 1) → G₁)
    (vk : Fin 2 → G₂) (h : out.Valid (initialInput ck vk).groups) (i : ℕ) :
    point out i = commit ck (coefficients out i) := by
  have hh := h false
  change List.Forall₂ (fun g cs => cs.length = (List.ofFn ck).length ∧
    GroupModel.Interaction.evaluate cs (List.ofFn ck) = g) _ _ at hh
  unfold point coefficients
  generalize out.value.groups false = gs at hh ⊢
  generalize out.coefficients false = css at hh ⊢
  induction hh generalizing i with
  | nil => simp [commit]
  | @cons g cs gs css hc ht ih =>
      cases i with
      | zero => simpa using (hc.2.symm.trans (evaluate_ofFn cs ck))
      | succ i => simpa using ih i

/-- Pair ordinary claims with the corresponding explained proof points. -/
def openings (claims : D → List (F × F)) (out : Output F G₁ G₂ D) :
    List (FunctionBinding.Opening F G₁) :=
  List.ofFn fun i : Fin (claims out.value.data).length =>
    let zv := (claims out.value.data)[i]
    (zv.1, zv.2, point out (i.val + 1))

/-- Drop explanations to obtain the existing function-binding adversary. -/
def toFunctionBindingAdversary (A : Adversary F G₁ G₂ (List (F × F))) :
    FunctionBindingAdversary F G₁ G₂ n :=
  fun ck vk => (fun out => (point out 0, openings id out)) <$> run A ck vk

/-- The two evaluation-binding claims share their evaluation point. -/
def evalClaims (d : F × F × F) : List (F × F) := [(d.1, d.2.1), (d.1, d.2.2)]

/-- Drop explanations to obtain the existing evaluation-binding adversary. -/
def toEvalBindingAdversary (A : Adversary F G₁ G₂ (F × F × F)) :
    EvalBindingAdversary F G₁ G₂ n :=
  fun ck vk => (fun out => (point out 0, out.value.data.1, out.value.data.2.1,
    point out 1, out.value.data.2.2, point out 2)) <$> run A ck vk

end KZG.AGM
