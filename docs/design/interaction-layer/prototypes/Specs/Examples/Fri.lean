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
  * The loop `fold` has `k` rounds over the round variable `i`. In round `i` the verifier samples
    `α_i`, and the prover sends the folded word `f_{i+1}` on `D_{i+1}`, of size `2^(k-i)`, as an
    oracle message.
  * The verifier samples `α_k`, and the prover sends the final constant `c`, the fold of `f_k`.
  * The loop `query` has `l` rounds over the round variable `j`. Each samples a position `t_j` of
    `D_0`. The nested loop `consistency` then reads `a_i = f_i(x_i)` and `b_i = f_i(-x_i)` for the
    pair above `t_j` in each round `i < k` and checks `fold`:
    `2x_i · f_{i+1}(x_i²) = x_i (a_i + b_i) + α_i (a_i − b_i)`. Round `0` reads the input oracle
    `f₀`. The check `final` tests the same relation for `f_k` against `c`.
* `fri_tree`: the tree is `k` pairs of a challenge and an oracle word, the challenge `α_k`, the
  message `c` and `l` challenges. Lean proves it by `rfl`.
* `fri_erase`: the erased skeleton, which the JSON and the folded figure read, is the same for all
  numbers of folds `k` and queries `l`. Lean proves it by `rfl`.
* `fri_verdict_isSome`: if the input oracle holds the witness word, `ω ≠ 0` and `2 ≠ 0`, the
  verdict accepts every honest transcript. The proof applies `Spec.verdict_isSome`, the generic
  loop lemma `rounds_complete` for each of the three loops with the invariant `FoldInv`, and the
  identity `fold_check`.
* The tests read `f_1`, `c` and the second query position by their label paths, and check the
  folded and expanded TeX of the two checks.

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
* Every name in a loop body is symbolic: `α_i`, `f_{i+1}`, `a_i` over the round variable `i`, and
  `t_j` over the query loop's variable `j`. The values of the check `final` and the challenge
  `α_k` use the count symbol `k` (`iv "a" (v := "k")`). *Why:* `rounds` requires a round's
  skeleton to be the same in every round, and the expanded figure prints each symbol as its value
  (`a_{2}` when `k = 2`). The nested loops have different round variables, so the expanded figure
  binds both.
* The printed types that depend on the round or the counts are symbolic strings
  (`𝔽^{2^{k-i}}`, `[2^{k+1}]`). *Why:* a type's `TypeName` prints the number, which would make the
  skeleton depend on `i` and `k`. These strings are annotation text, so the expanded figure prints
  them unchanged.
* The consistency loop passes its round skeleton `checkSkel` explicitly, built from the formulas of
  round `0`. *Why:* the formulas (`fmlA`, `fmlB`, `fmlX`, `fmlFold`) have hole types that mention
  the round (`f_i` answers queries in `Fin (2^(k+1-i))`), so `rounds` cannot infer the skeleton by
  unification. Their syntax keeps only the names of the index maps, so every round's skeleton
  evaluates to `checkSkel`, and Lean checks that by evaluation.
* The state of the fold loop (`FoldState`) keeps the challenges and the references of all words,
  and `FoldState.f` names a word's handle as the reading round needs (`f_i`, `f_{i+1}` or
  `f_k`). *Why:* a query round reads every round oracle, under a name relative to its own round
  variable.
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
  /-- The references of the words so far. -/
  fs : (j : Fin (i + 1)) → Ref (Fin (size k j)) F

/-- The handle of the word `f_j`, under the name `nm` that the reading round gives it. -/
def FoldState.f {i : ℕ} (st : FoldState F k i) (nm : Name) (j : ℕ) (h : j ≤ i) :
    OHdl nm (Fin (size k j)) F :=
  ⟨st.fs ⟨j, by omega⟩⟩

variable {In : OracleBundle} {T : Type}

/-- Folding round `i`: the verifier samples `α_i`, and the prover sends the folded word
`f_{i+1}` as an oracle. -/
noncomputable def foldRound (ω : F) {t : OracleProtocol} {ks : Skel} (i : ℕ) (_ : i < k)
    (st : FoldState F k i) (next : FoldState F k (i + 1) → Desc In (Word F k 0) T t ks) :=
  challenge (iv "\\alpha") F fun α =>
  oracle (iv "f" 1) (Word F k (i + 1)) F "\\mathsf{fold}" (ty := TypeName.name F ++ "^{2^{k-i}}")
    (fun w => honestWord ω k (i + 1) (Fin.snoc st.as α.val) w) fun f =>
  next ⟨Fin.snoc st.as α.val,
    Fin.snoc (α := fun j : Fin (i + 2) => Ref (Fin (size k j)) F) st.fs f.ref⟩

/-- The query position `t_j` of query round `j`. -/
abbrev tName : Name := iv "t" (v := "j")

/-- The value `a_i = f_i(lo(t_j))` of consistency round `i`. -/
def fmlA (k i : ℕ) :
    Closed [.orc (iv "f") (Fin (size k i)) F, .val tName (Fin (size k 0))] F :=
  ⟨fun f t => Fml.query f (Fml.app "lo" (loI k i) (Fml.var t))⟩

/-- The value `b_i = f_i(hi(t_j))` of consistency round `i`. -/
def fmlB (k i : ℕ) :
    Closed [.orc (iv "f") (Fin (size k i)) F, .val tName (Fin (size k 0))] F :=
  ⟨fun f t => Fml.query f (Fml.app "hi" (hiI k i) (Fml.var t))⟩

/-- The point `x_i = pt(t_j)` of consistency round `i`. -/
def fmlX (ω : F) (k i : ℕ) : Closed [.val tName (Fin (size k 0))] F :=
  ⟨fun t => Fml.app "pt" (ptI ω k i) (Fml.var t)⟩

/-- The check `fold` of consistency round `i`: `2x · f_{i+1}(lo(t)) = x (a + b) + α (a − b)`. -/
def fmlFold (k i : ℕ) :
    Closed [.orc (iv "f" 1) (Fin (size k (i + 1))) F, .val (iv "\\alpha") F, .val (iv "a") F,
      .val (iv "b") F, .val (iv "x") F, .val tName (Fin (size k 0))] Bool :=
  ⟨fun f α a b x t => 2 * Fml.var x * Fml.query f (Fml.app "lo" (loJ k i) (Fml.var t)) ='
      Fml.var x * (Fml.var a + Fml.var b) + Fml.var α * (Fml.var a - Fml.var b)⟩

variable (F) in
/-- The skeleton of a consistency round followed by `ks`, from the formulas of round `0`. Every
round has this skeleton, since the syntax of a function application keeps only its name. `rounds`
cannot infer it, because the hole types of round `i` mention `i` (the domain `D_i` has its own
size), so `checkRound`'s loop passes it as `G`, and Lean checks each round against it by
evaluation. -/
def checkSkel (ω : F) (k : ℕ) (ks : Skel) : Skel :=
  .cons (.let_ (iv "a") (TypeName.name F) (fmlA (F := F) k 0).syntax "") <|
  .cons (.let_ (iv "b") (TypeName.name F) (fmlB (F := F) k 0).syntax "") <|
  .cons (.let_ (iv "x") (TypeName.name F) (fmlX ω k 0).syntax "") <|
  .cons (.check "fold" (fmlFold (F := F) k 0).syntax "") ks

/-- Consistency round `i` of a query at position `t`: the verifier reads `f_i` at the pair
`x, -x` of `D_i` above `loJ k i t` and checks the fold against `f_{i+1}`, without division. -/
noncomputable def checkRound (ω : F) (st : FoldState F k k) (t : Val tName (Fin (size k 0)))
    {W : Type} {tr : OracleProtocol} {ks : Skel} (i : ℕ) (hi : i < k) (_ : Unit)
    (next : Unit → Desc In W T tr ks) :=
  compute (iv "a") F ⟪st.f (iv "f") i hi.le, t⟫ (fmlA k i).fml fun a =>
  compute (iv "b") F ⟪st.f (iv "f") i hi.le, t⟫ (fmlB k i).fml fun b =>
  compute (iv "x") F ⟪t⟫ (fmlX ω k i).fml fun x =>
  check "fold" ⟪st.f (iv "f" 1) (i + 1) hi, (⟨st.as ⟨i, hi⟩⟩ : Val (iv "\\alpha") F), a, b, x, t⟫
    (fmlFold k i).fml <|
  next ()

/-- Query round `j`: the verifier samples a position `t`, checks every fold along it, and checks
the last fold against the final constant `c`. -/
noncomputable def queryRound (ω : F) (l : ℕ) (st : FoldState F k k)
    (αk : Val (iv "\\alpha" (v := "k")) F) (c : Val "c" F) {W : Type} {tr : OracleProtocol}
    {ks : Skel} (j : ℕ) (_ : j < l) (_ : Unit) (next : Unit → Desc In W T tr ks) :=
  challenge tName (Fin (size k 0)) (ty := "[2^{k+1}]") fun t =>
  rounds "consistency" k () (G := checkSkel F ω k) (checkRound ω st t) (countName := "k")
    (tree := fun _ _ => tr) fun _ =>
  compute (iv "a" (v := "k")) F ⟪st.f (iv "f" (v := "k")) k le_rfl, t⟫
    (fun f t => Fml.query f (Fml.app "lo" (loI k k) (Fml.var t))) fun a =>
  compute (iv "b" (v := "k")) F ⟪st.f (iv "f" (v := "k")) k le_rfl, t⟫
    (fun f t => Fml.query f (Fml.app "hi" (hiI k k) (Fml.var t))) fun b =>
  compute (iv "x" (v := "k")) F ⟪t⟫ (fun t => Fml.app "pt" (ptI ω k k) (Fml.var t)) fun x =>
  check "final" ⟪c, αk, a, b, x⟫
    (fun c α a b x => 2 * Fml.var x * Fml.var c ='
      Fml.var x * (Fml.var a + Fml.var b) + Fml.var α * (Fml.var a - Fml.var b)) <|
  next ()

variable (F) in
/-- FRI with `k + 1` folds and `l` queries over the domain `D_0` of size `2^(k+1)` generated by
`ω`. -/
noncomputable def friSpec (k l : ℕ) (ω : F) :=
  Spec.mk (In := OracleBundle.ofInst (Word F k 0)) (W := Word F k 0) (T := Unit)
    fun _ : Unit =>
  input (ix "f" 0) (Fin (size k 0)) F (TypeName.name F ++ "^{2^{k+1}}") (fun q => q)
    (fun _ => rfl) fun f0 =>
  rounds "fold" k (⟨Fin.elim0,
      Fin.cons (α := fun j : Fin 1 => Ref (Fin (size k j)) F) f0.ref fun i => i.elim0⟩ :
      FoldState F k 0)
    (foldRound ω) (countName := "k") fun st =>
  challenge (iv "\\alpha" (v := "k")) F fun αk =>
  message "c" F "\\mathsf{fold}"
    (fun w => foldStep ω k k (honestWord ω k k st.as w) αk.val ⟨0, Nat.two_pow_pos _⟩) fun c =>
  rounds "query" l () (queryRound ω l st αk c) (countName := "l") (var := "j") fun _ =>
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

/-- The erased skeleton of the specification, which the JSON and the folded figure read, does not
depend on the numbers of folds and queries. -/
theorem fri_erase (k l k' l' : ℕ) (ω : F) :
    (friSpec F k l ω).skeleton.erase = (friSpec F k' l' ω).skeleton.erase := rfl

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
  ℓ = i + 1 ∧ (∀ j, st.fs j = ⟨j.val, default⟩) ∧
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
  refine rounds_complete _ _ _ (foldRound ω) _ _ _ _ _ _ _ _ data _ (FoldInv ω data) ?_ ?_ _ _ ?_
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
    refine rounds_complete _ _ _ (queryRound ω l st ⟨αk⟩ _) _ _ _ _ _ _ _ _ data _
      (fun _ _ env' ℓ' => FoldInv ω data k st env' ℓ') ?_ ?_ _ _ hI
    · intro t' ks' j hj _ next' env' ℓ' hI' hnext'
      unfold queryRound
      erw [Desc.Complete.eq_4]
      intro t
      refine rounds_complete (G := checkSkel F ω k) _ _ _ (checkRound ω st ⟨t⟩) _ _ _ _ _ _ _ _
        data _
        (fun _ _ env'' ℓ'' => FoldInv ω data k st env'' ℓ'') ?_ ?_ _ _ hI'
      · intro t'' ks'' i hi _ next'' env'' ℓ'' hI'' hnext''
        unfold checkRound
        erw [Desc.Complete.eq_6, Desc.Complete.eq_6, Desc.Complete.eq_6, Desc.Complete.eq_5]
        refine ⟨?_, hnext'' _ _ _ hI''⟩
        obtain ⟨-, hfs, hfind⟩ := hI''
        have hf : ∀ nm j (hj : j ≤ k), st.f nm j hj = ⟨⟨j, default⟩⟩ :=
          fun _ _ _ => congrArg OHdl.mk (hfs _)
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
        have hf : ∀ nm j (hj : j ≤ k), st.f nm j hj = ⟨⟨j, default⟩⟩ :=
          fun _ _ _ => congrArg OHdl.mk (hfs _)
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
/-- The last folding challenge `α_2`, after the fold block, by its subscript. With the base alone
the accessor reads `α_0`. -/
example (tr : (friSpec (ZMod 17) 2 3 2).Tr) : tr⟦"\\alpha_2"⟧ = tr.2.2.2.2.1 := rfl
example (tr : (friSpec (ZMod 17) 2 3 2).Tr) : tr⟦"\\alpha"⟧ = tr⟦fold, 0, "\\alpha"⟧ := rfl
/-- The position of the second query. -/
example (tr : (friSpec (ZMod 17) 2 3 2).Tr) : tr⟦query, 1, t⟧ = tr.2.2.2.2.2.2.2.1 := rfl

/-- The labels and the TeX of the checks in the mode `m`. -/
def checkTex (ks : Skel) (m : Mode) : List (String × String) :=
  ks.checks.map fun (c : String × Syn) => (c.1, c.2.tex m)

/-! The skeleton lists the checks of each loop body once: `fold` from the consistency loop and
`final` after it. Folded, they print over the round variables `i`, `j` and the count `k`. -/
#guard checkTex (friSpec (ZMod 17) 2 3 2).skeleton { folded := true } ==
  [("fold", "2 \\cdot x_{i} \\cdot f_{i+1}(\\mathrm{lo}(t_{j})) = x_{i} \\cdot (a_{i} + b_{i}) + \
      \\alpha_{i} \\cdot (a_{i} - b_{i})"),
   ("final", "2 \\cdot x_{k} \\cdot c = x_{k} \\cdot (a_{k} + b_{k}) + \
      \\alpha_{k} \\cdot (a_{k} - b_{k})")]

/-! Expanded in consistency round `0` of query round `1` with `k = 2`. -/
#guard checkTex (friSpec (ZMod 17) 2 3 2).skeleton
    (((Mode.expanded.bind "k" 2).bind "j" 1).bind "i" 0) ==
  [("fold", "2 \\cdot x_{0} \\cdot f_{1}(\\mathrm{lo}(t_{1})) = x_{0} \\cdot (a_{0} + b_{0}) + \
      \\alpha_{0} \\cdot (a_{0} - b_{0})"),
   ("final", "2 \\cdot x_{2} \\cdot c = x_{2} \\cdot (a_{2} + b_{2}) + \
      \\alpha_{2} \\cdot (a_{2} - b_{2})")]

end Tests

#print axioms fold_check
#print axioms loJ_last
#print axioms fri_tree
#print axioms fri_erase
#print axioms fri_verdict_isSome

end Fri

end Specs
