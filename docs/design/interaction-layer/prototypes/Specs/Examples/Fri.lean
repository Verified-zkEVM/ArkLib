/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Specs.Examples.Branching
import Mathlib.Algebra.Field.ZMod

/-!
# FRI as a specification

This module writes FRI with a domain that halves each round.

* `friSpec F k l ω`: the domain `D_j` of round `j` has `2^(k+1-j)` points `ω^(2^j · s)`, indexed
  by `s`. The word `f₀` on `D_0` is an input oracle.
  * The block `fold` has `k` rounds. In round `i` the verifier samples `α_i`, and the prover sends
    the folded word `f_{i+1}` on `D_{i+1}`, of size `2^(k-i)`, as an oracle message.
  * The verifier samples `α_k`, and the prover sends the final constant `c`, the fold of `f_k`.
  * The block `query` has `l` rounds. Each samples a position `t` of `D_0`. The block
    `consistency` then reads `a_i = f_i(x)` and `b_i = f_i(-x)` for the pair above `t` in each
    round `i < k` and checks `fold`: `2x · f_{i+1}(x²) = x (a_i + b_i) + α_i (a_i − b_i)`. Round
    `0` reads the input oracle `f₀`. The check `final` tests the same relation for `f_k` against
    `c`.
* `fri_tree`: the tree is `k` pairs of a challenge and an oracle word, the challenge `α_k`, the
  message `c` and `l` challenges. Lean proves it by `rfl`.
* `fri_verdict_isSome`: if the input oracle holds the witness word, `ω ≠ 0` and `2 ≠ 0`, the
  verdict accepts every honest transcript. The proof applies `Spec.verdict_isSome`, the generic
  block lemma `roundsGo_complete` with the invariant `FoldInv`, and the identity `fold_check`.
* The tests read `f_1`, `c` and the second query position by their label paths and check the
  labels and the expanded TeX of the checks.

What is not proved: soundness, and that `ω` has order `2^(k+1)`. Honest acceptance does not need
the order, since the honest prover and the checks use the same index maps (`loJ`, `loI`, `hiI`,
`ptI`).

## Design choices

* The checks contain no division: `2x · f'(x²) = x (a + b) + α (a − b)` is the fold
  `f'(x²) = (a + b)/2 + α (a − b)/(2x)` multiplied by `2x`. *Why:* the formula language has no
  division. The two forms agree when `2x ≠ 0`, which is why the theorem assumes `ω ≠ 0` and
  `2 ≠ 0`.
* The index maps `lo`, `hi` and `pt` are named functions in the formulas. Their printed names do
  not carry the round, since the name of a function in a formula is a fixed string.
* The checks write the arity-2 fold directly instead of calling ArkLib's
  `RoundConsistency.roundConsistencyCheck`. *Why:* that check interpolates an arbitrary list of
  points over ArkLib's FFT domains, so as a named function it would hide the fold relation in the
  figure, and completeness would need its Lagrange-interpolation lemmas.
* The values of the check `final` have the names `a_k`, `b_k`, `x_k` and `f_k`, built with
  `ixCount`: the folded figure prints the index as the symbol `k`, and the expanded figure prints
  the number (`a_{2}` when `k = 2`). *Why:* inside a round, the folded figure prints a round index
  as an offset from the innermost open round, so `ix "a" k` would print as an offset from the
  index of the query round.
* The state of the fold block (`FoldState`) keeps the challenges and the handles of all words, so
  a query round can read every round oracle.
-/

set_option linter.hashCommand false

namespace Specs
open Interaction PFunctor FreeM Interaction.TwoParty.Lens Interaction.Oracle OracleComp
  OracleSpec

namespace Fri

section Fri

variable {F : Type} [Field F] [DecidableEq F] [TypeName F] {k : ℕ}

/-- The default answer of a handle over a field. -/
local instance : Inhabited F := ⟨0⟩

/-! ## Words and folding -/

/-- The size `2^(k+1-j)` of the evaluation domain `D_j` of round `j`. -/
abbrev size (k j : ℕ) : ℕ := 2 ^ (k + 1 - j)

/-- The word of round `j`: its values on `D_j = {ω^(2^j · t) : t < 2^(k+1-j)}`, indexed by `t`. -/
abbrev Word (F : Type) (k j : ℕ) : Type := Fin (size k j) → F

instance {j : ℕ} : TypeName (Word F k j) :=
  ⟨TypeName.name F ++ "^{" ++ toString (size k j) ++ "}"⟩

/-- The index `t mod 2^(k-i)` of the query position `t` in the domain of round `i + 1`. -/
def loJ (k i : ℕ) (t : Fin (size k 0)) : Fin (size k (i + 1)) :=
  ⟨t.val % size k (i + 1), Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- The lower index of the pair in `D_i` that folds to `loJ k i t`. -/
def loI (k i : ℕ) (t : Fin (size k 0)) : Fin (size k i) :=
  ⟨(loJ k i t).val % size k i, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- The upper index of the pair in `D_i` that folds to `loJ k i t`: the point `-x`. -/
def hiI (k i : ℕ) (t : Fin (size k 0)) : Fin (size k i) :=
  ⟨((loJ k i t).val + size k (i + 1)) % size k i, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- The point `x = ω^(2^i · loJ k i t)` of `D_i` at the lower index. -/
def ptI (ω : F) (k i : ℕ) (t : Fin (size k 0)) : F := ω ^ (2 ^ i * (loJ k i t).val)

/-- One folding step with challenge `α`: `f'(x²) = (f(x) + f(-x)) / 2 + α (f(x) - f(-x)) / (2x)`,
the even part plus `α` times the odd part. -/
def foldStep (ω : F) (k i : ℕ) (g : Word F k i) (α : F) : Word F k (i + 1) := fun j =>
  let a := g ⟨j.val % size k i, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  let b := g ⟨(j.val + size k (i + 1)) % size k i, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  let x := ω ^ (2 ^ i * j.val)
  (a + b) / 2 + α * (a - b) / (2 * x)

/-- The honest word of round `i`: `f_0` folded with the challenges `α_0, …, α_{i-1}`. -/
def honestWord (ω : F) (k : ℕ) : (i : ℕ) → (Fin i → F) → Word F k 0 → Word F k i
  | 0, _, f => f
  | i + 1, as, f => foldStep ω k i (honestWord ω k i (Fin.init as) f) (as (Fin.last i))

/-! ## The specification -/

/-- The verifier's state after `i` folding rounds: the challenges `α_{<i}` and the handles of the
words `f_0, …, f_i`. -/
structure FoldState (F : Type) (k i : ℕ) where
  /-- The folding challenges so far. -/
  as : Fin i → F
  /-- The handles of the words so far. -/
  fs : (j : Fin (i + 1)) → OHdl (ix "f" j) (Fin (size k j)) F

/-- The handle of the word `f_i`. -/
def FoldState.f {i : ℕ} (st : FoldState F k i) (j : ℕ) (h : j ≤ i) :
    OHdl (ix "f" j) (Fin (size k j)) F :=
  st.fs ⟨j, by omega⟩

variable {In : OracleBundle} {T : Type}

/-- Folding round `i`: the verifier samples `α_i`, and the prover sends the folded word
`f_{i+1}` as an oracle. -/
noncomputable def foldRound (ω : F) {t : OracleProtocol} {ks : Skel} (i : ℕ) (_ : i < k)
    (st : FoldState F k i) (next : FoldState F k (i + 1) → Desc In (Word F k 0) T t ks) :=
  challenge (ix "\\alpha" i) F fun α =>
  oracle (ix "f" (i + 1)) (Word F k (i + 1)) F "\\mathsf{fold}"
    (fun w => honestWord ω k (i + 1) (Fin.snoc st.as α.val) w) fun f =>
  next ⟨Fin.snoc st.as α.val,
    Fin.snoc (α := fun j : Fin (i + 2) => OHdl (ix "f" j) (Fin (size k j)) F) st.fs f⟩

/-- Consistency round `i` of a query at position `t`: the verifier reads `f_i` at the pair
`x, -x` of `D_i` above `loJ k i t` and checks the fold against `f_{i+1}`, without division. -/
noncomputable def checkRound (ω : F) (st : FoldState F k k) (t : Val "t" (Fin (size k 0)))
    {W : Type} {tr : OracleProtocol} {ks : Skel} (i : ℕ) (hi : i < k) (_ : Unit)
    (next : Unit → Desc In W T tr ks) :=
  compute (ix "a" i) F ⟪st.f i hi.le, t⟫
    (fun f t => Fml.query f (Fml.app "lo" (loI k i) (Fml.var t))) fun a =>
  compute (ix "b" i) F ⟪st.f i hi.le, t⟫
    (fun f t => Fml.query f (Fml.app "hi" (hiI k i) (Fml.var t))) fun b =>
  compute (ix "x" i) F ⟪t⟫ (fun t => Fml.app "pt" (ptI ω k i) (Fml.var t)) fun x =>
  check "fold" ⟪st.f (i + 1) hi, (⟨st.as ⟨i, hi⟩⟩ : Val (ix "\\alpha" i) F), a, b, x, t⟫
    (fun f α a b x t => 2 * Fml.var x * Fml.query f (Fml.app "lo" (loJ k i) (Fml.var t)) ='
      Fml.var x * (Fml.var a + Fml.var b) + Fml.var α * (Fml.var a - Fml.var b)) <|
  next ()

/-- Query round `j`: the verifier samples a position `t`, checks every fold along it, and checks
the last fold against the final constant `c`. -/
noncomputable def queryRound (ω : F) (l : ℕ) (st : FoldState F k k)
    (αk : Val (ix "\\alpha" k) F) (c : Val "c" F) {W : Type} {tr : OracleProtocol} {ks : Skel}
    (j : ℕ) (_ : j < l) (_ : Unit) (next : Unit → Desc In W T tr ks) :=
  challenge "t" (Fin (size k 0)) fun t =>
  rounds "consistency" k () (checkRound ω st t) (countName := "k") (tree := fun _ _ => tr)
    fun _ =>
  compute (ixCount "a" k "k") F
      ⟪(⟨(st.f k le_rfl).ref⟩ : OHdl (ixCount "f" k "k") (Fin (size k k)) F), t⟫
    (fun f t => Fml.query f (Fml.app "lo" (loI k k) (Fml.var t))) fun a =>
  compute (ixCount "b" k "k") F
      ⟪(⟨(st.f k le_rfl).ref⟩ : OHdl (ixCount "f" k "k") (Fin (size k k)) F), t⟫
    (fun f t => Fml.query f (Fml.app "hi" (hiI k k) (Fml.var t))) fun b =>
  compute (ixCount "x" k "k") F ⟪t⟫ (fun t => Fml.app "pt" (ptI ω k k) (Fml.var t)) fun x =>
  check "final" ⟪c, (⟨αk.val⟩ : Val (ixCount "\\alpha" k "k") F), a, b, x⟫
    (fun c α a b x => 2 * Fml.var x * Fml.var c ='
      Fml.var x * (Fml.var a + Fml.var b) + Fml.var α * (Fml.var a - Fml.var b)) <|
  next ()

variable (F) in
/-- FRI with `k + 1` folds and `l` queries over the domain `D_0` of size `2^(k+1)` generated by
`ω`. -/
noncomputable def friSpec (k l : ℕ) (ω : F) :=
  Spec.mk (In := OracleBundle.ofInst (Word F k 0)) (W := Word F k 0) (T := Unit)
    fun _ : Unit =>
  input (ix "f" 0) (Fin (size k 0)) F (TypeName.name (Word F k 0)) (fun q => q) (fun _ => rfl)
    fun f0 =>
  rounds "fold" k (⟨Fin.elim0,
      Fin.cons (α := fun j : Fin 1 => OHdl (ix "f" j) (Fin (size k j)) F) f0 fun i => i.elim0⟩ :
      FoldState F k 0)
    (foldRound ω) (countName := "k") fun st =>
  challenge (ix "\\alpha" k) F fun αk =>
  message "c" F "\\mathsf{fold}"
    (fun w => foldStep ω k k (honestWord ω k k st.as w) αk.val ⟨0, Nat.two_pow_pos _⟩) fun c =>
  rounds "query" l () (queryRound ω l st αk c) (countName := "l") fun _ =>
  done ()

variable (F) in
/-- The expected tree: `k` rounds of a challenge and an oracle word, the last challenge, the final
constant and `l` query challenges. -/
noncomputable abbrev friTree (k l : ℕ) : OracleProtocol :=
  roundsTree (fun i t => .liftBind (.challenge F) fun _ =>
      .liftBind (.oracle (Word F k (i + 1)) inferInstance) fun _ => t)
    (.liftBind (.challenge F) fun _ => .liftBind (.message F) fun _ =>
      roundsTree (fun _ t => .liftBind (.challenge (Fin (size k 0))) fun _ => t) (.pure ⟨⟩) 0 l)
    0 k

/-- The tree of the specification is the expected tree. -/
theorem fri_tree (k l : ℕ) (ω : F) : (friSpec F k l ω).tree = friTree F k l := rfl

/-! ## Honest acceptance -/

omit [DecidableEq F] [TypeName F] in
/-- The fold identity behind the check: `2x · f'(x²) = x (f(x) + f(-x)) + α (f(x) - f(-x))` when
`f' = foldStep … f α`, `x ≠ 0` and `2 ≠ 0`. -/
theorem fold_check (ω : F) (hω : ω ≠ 0) (h2 : (2 : F) ≠ 0) {i : ℕ} (g : Word F k i) (α : F)
    (t : Fin (size k 0)) :
    2 * ptI ω k i t * foldStep ω k i g α (loJ k i t) =
      ptI ω k i t * (g (loI k i t) + g (hiI k i t)) + α * (g (loI k i t) - g (hiI k i t)) := by
  have hx : ω ^ (2 ^ i * (loJ k i t).val) ≠ 0 := pow_ne_zero _ hω
  simp only [foldStep, ptI, loI, hiI]
  field_simp

/-- The last fold reads position `0`: the domain of round `k + 1` has one point. -/
theorem loJ_last (t : Fin (size k 0)) : loJ k k t = ⟨0, Nat.two_pow_pos _⟩ := by
  ext
  simp [loJ, size, Nat.mod_one]

/-- The first `j` challenges of `as`. -/
def pre {i : ℕ} (as : Fin i → F) (j : ℕ) (hj : j ≤ i) : Fin j → F := fun l => as ⟨l, by omega⟩

omit [Field F] [DecidableEq F] [TypeName F] in
theorem pre_snoc {i : ℕ} (as : Fin i → F) (α : F) (j : ℕ) (hj : j ≤ i) :
    pre (Fin.snoc as α) j (by omega) = pre as j hj := by
  funext l
  simp only [pre, Fin.snoc, show (l : ℕ) < i by omega, dite_true, cast_eq]
  rfl

/-- The invariant of the fold block before round `i`: the next level is `i + 1`, the handle of
`f_j` reads level `j`, and level `j` answers with the honest word of round `j`. -/
def FoldInv (ω : F) (w : Word F k 0) (i : ℕ) (st : FoldState F k i) (env : Handlers Id)
    (ℓ : ℕ) : Prop :=
  ℓ = i + 1 ∧ (∀ j, st.fs j = ⟨⟨j, default⟩⟩) ∧
    ∀ j (hj : j ≤ i) (q : Fin (size k j)),
      (env.find (default : F) j q).run = honestWord ω k j (pre st.as j hj) w q

/-- **Honest acceptance.** If the input oracle holds the witness word, `ω ≠ 0` and `2 ≠ 0`, the
verdict accepts every transcript of the honest prover. -/
theorem fri_verdict_isSome (l : ℕ) (ω : F) (hω : ω ≠ 0) (h2 : (2 : F) ≠ 0) (w : Word F k 0)
    (data : (OracleBundle.ofInst (Word F k 0)).Data) (hdata : data = w)
    (tr : (friSpec F k l ω).Tr)
    (hh : ((friSpec F k l ω).desc ()).Honest w ((OracleBundle.ofInst (Word F k 0)).answer data)
      tr .empty 0) :
    ((friSpec F k l ω).verdict () data tr).isSome := by
  subst hdata
  refine Spec.verdict_isSome _ () data data tr ?_ hh
  unfold friSpec
  erw [Desc.Complete.eq_7]
  refine roundsGo_complete "fold" k "k" _ (foldRound ω) _ _ _ _ data _ (FoldInv ω data) ?_ ?_ k 0
    (by omega) _ _ _ ?_
  · intro t' ks' i hi st next' env ℓ hI hnext'
    obtain ⟨hℓ, hfs, hfind⟩ := hI
    subst hℓ
    erw [Desc.Complete.eq_4]
    intro α
    erw [Desc.Complete.eq_3]
    refine hnext' _ _ _ ⟨rfl, fun j => ?_, fun j hj q => ?_⟩
    · induction j using Fin.lastCases with
      | last => simp
      | cast j => simp [hfs]
    · rcases Nat.lt_or_ge j (i + 1) with hj' | hj'
      · rw [Handlers.find_ext_ne _ (by omega), pre_snoc _ _ _ (by omega)]
        exact hfind j (by omega) q
      · obtain rfl : j = i + 1 := by omega
        rw [Handlers.find_ext_self]
        rfl
  · intro st env ℓ hI
    erw [Desc.Complete.eq_4]
    intro αk
    erw [Desc.Complete.eq_2]
    refine roundsGo_complete "query" l "l" _ (queryRound ω l st ⟨αk⟩ _) _ _ _ _ data _
      (fun _ _ env' ℓ' => FoldInv ω data k st env' ℓ') ?_ ?_ l 0 (by omega) _ _ _ hI
    · intro t' ks' j hj _ next' env' ℓ' hI' hnext'
      unfold queryRound
      erw [Desc.Complete.eq_4]
      intro t
      refine roundsGo_complete "consistency" k "k" _ (checkRound ω st ⟨t⟩) _ _ _ _ data _
        (fun _ _ env'' ℓ'' => FoldInv ω data k st env'' ℓ'') ?_ ?_ k 0 (by omega) _ _ _ hI'
      · intro t'' ks'' i hi _ next'' env'' ℓ'' hI'' hnext''
        unfold checkRound
        erw [Desc.Complete.eq_6, Desc.Complete.eq_6, Desc.Complete.eq_6, Desc.Complete.eq_5]
        refine ⟨?_, hnext'' _ _ _ hI''⟩
        obtain ⟨-, hfs, hfind⟩ := hI''
        have hf : ∀ j (hj : j ≤ k), st.f j hj = ⟨⟨j, default⟩⟩ := fun j _ => hfs _
        simp only [hf]
        refine decide_eq_true ?_
        change 2 * ptI ω k i t * (env''.find (default : F) (i + 1) (loJ k i t)).run =
          ptI ω k i t * ((env''.find (default : F) i (loI k i t)).run +
            (env''.find (default : F) i (hiI k i t)).run) +
          st.as ⟨i, hi⟩ * ((env''.find (default : F) i (loI k i t)).run -
            (env''.find (default : F) i (hiI k i t)).run)
        rw [hfind (i + 1) hi, hfind i hi.le, hfind i hi.le]
        exact fold_check ω hω h2 _ _ t
      · intro _ env'' ℓ'' hI''
        erw [Desc.Complete.eq_6, Desc.Complete.eq_6, Desc.Complete.eq_6, Desc.Complete.eq_5]
        refine ⟨?_, hnext' _ _ _ hI''⟩
        obtain ⟨-, hfs, hfind⟩ := hI''
        have hf : ∀ j (hj : j ≤ k), st.f j hj = ⟨⟨j, default⟩⟩ := fun j _ => hfs _
        simp only [hf]
        refine decide_eq_true ?_
        change 2 * ptI ω k k t * foldStep ω k k (honestWord ω k k st.as data) αk
            ⟨0, Nat.two_pow_pos _⟩ =
          ptI ω k k t * ((env''.find (default : F) k (loI k k t)).run +
            (env''.find (default : F) k (hiI k k t)).run) +
          αk * ((env''.find (default : F) k (loI k k t)).run -
            (env''.find (default : F) k (hiI k k t)).run)
        rw [hfind k le_rfl, hfind k le_rfl]
        have h := fold_check ω hω h2 (honestWord ω k k st.as data) αk t
        rw [loJ_last] at h
        exact h
    · intro _ _ _ _
      trivial
  · refine ⟨rfl, fun j => ?_, fun j hj q => ?_⟩
    · rw [Fin.fin_one_eq_zero j]
      rfl
    · obtain rfl : j = 0 := by omega
      rw [Handlers.find_ext_self]
      rfl

end Fri

section Tests

/-- The field `𝔽₁₇`, in which `2` has order `8`. -/
instance : Fact (Nat.Prime 17) := ⟨by decide⟩
instance : TypeName (ZMod 17) := ⟨"\\mathbb{F}_{17}"⟩

/-- The word `f_1` of the fold block by its label path. -/
example (tr : (friSpec (ZMod 17) 2 3 2).Tr) : tr⟦fold, 1, f⟧ = tr.2.2.2.1 := rfl
/-- The final constant. -/
example (tr : (friSpec (ZMod 17) 2 3 2).Tr) : tr⟦c⟧ = tr.2.2.2.2.2.1 := rfl
/-- The position of the second query. -/
example (tr : (friSpec (ZMod 17) 2 3 2).Tr) : tr⟦query, 1, t⟧ = tr.2.2.2.2.2.2.2.1 := rfl

/-- The labels and the expanded TeX of the checks. -/
def checkTex (ks : Skel) : List (String × String) :=
  ks.checks.map fun (c : String × Syn) => (c.1, c.2.tex Mode.expanded)

/-! With `k = 2` and `l = 3`: each of the three queries checks two folds and the final constant. -/
#guard (checkTex (friSpec (ZMod 17) 2 3 2).skeleton).map (·.1) ==
  ["fold", "fold", "final", "fold", "fold", "final", "fold", "fold", "final"]

#guard (checkTex (friSpec (ZMod 17) 2 3 2).skeleton).take 3 ==
  [("fold", "2 \\cdot x_{0} \\cdot f_{1}(\\mathrm{lo}(t)) = x_{0} \\cdot (a_{0} + b_{0}) + \
      \\alpha_{0} \\cdot (a_{0} - b_{0})"),
   ("fold", "2 \\cdot x_{1} \\cdot f_{2}(\\mathrm{lo}(t)) = x_{1} \\cdot (a_{1} + b_{1}) + \
      \\alpha_{1} \\cdot (a_{1} - b_{1})"),
   ("final", "2 \\cdot x_{2} \\cdot c = x_{2} \\cdot (a_{2} + b_{2}) + \
      \\alpha_{2} \\cdot (a_{2} - b_{2})")]

/-! The folded figure prints the final check with the symbol `k`. -/
#guard ((friSpec (ZMod 17) 2 3 2).skeleton.checks.lookup "final").map
    (·.tex { folded := true }) == some
  "2 \\cdot x_{k} \\cdot c = x_{k} \\cdot (a_{k} + b_{k}) + \
    \\alpha_{k} \\cdot (a_{k} - b_{k})"

end Tests

#print axioms fold_check
#print axioms loJ_last
#print axioms fri_tree
#print axioms fri_verdict_isSome

end Fri

end Specs
