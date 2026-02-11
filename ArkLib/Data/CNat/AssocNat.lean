/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5c0bcc8c-887f-4393-9fb0-e71b319d1cde

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem zero_mul {a : AssocNat} : 0 * a = 0

- theorem succ_mul {a b : AssocNat} : (succ a) * b = a * b + b

- theorem mul_add {a b c : AssocNat} : a * (b + c) = a * b + a * c

- @[simp] theorem one_mul {a : AssocNat} : 1 * a = a

- private theorem toNat_mulNat (a : AssocNat) (k : Nat) : toNat (mulNat a k) = toNat a * k

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

import Mathlib
import ArkLib.Data.Classes.ToNat


import Mathlib.Tactic.GeneralizeProofs

namespace Harmonic.GeneralizeProofs
-- Harmonic `generalize_proofs` tactic

open Lean Meta Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
def mkLambdaFVarsUsedOnly' (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut e := e
  let mut fvars' : List Expr := []
  for i' in [0:fvars.size] do
    let fvar := fvars[fvars.size - i' - 1]!
    e ← mkLambdaFVars #[fvar] e (usedOnly := false) (usedLetOnly := false)
    match e with
    | .letE _ _ v b _ => e := b.instantiate1 v
    | .lam _ _ _b _ => fvars' := fvar :: fvars'
    | _ => unreachable!
  return (fvars'.toArray, e)

partial def abstractProofs' (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  if (← read).depth ≤ (← read).config.maxDepth then MAbs.withRecurse <| visit (← instantiateMVars e) ty?
  else return e
where
  visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    if (← read).config.debug then
      if let some ty := ty? then
        unless ← isDefEq (← inferType e) ty do
          throwError "visit: type of{indentD e}\nis not{indentD ty}"
    if e.isAtomic then
      return e
    else
      checkCache (e, ty?) fun _ ↦ do
        if ← isProof e then
          visitProof e ty?
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none) (usedOnly := false) (usedLetOnly := false)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              let ty'? ←
                if let some ty := ty? then
                  let .forallE _ _ tyB _ ← pure ty
                    | throwError "Expecting forall in abstractProofs .lam"
                  pure <| some <| tyB.instantiate1 x
                else
                  pure none
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?) (usedOnly := false) (usedLetOnly := false)
          | .letE n t v b _ =>
            let t' ← visit t none
            withLetDecl n t' (← visit v t') fun x ↦ MAbs.withLocal x do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty?) (usedLetOnly := false)
          | .app .. =>
            e.withApp fun f args ↦ do
              let f' ← visit f none
              let argTys ← appArgExpectedTypes f' args ty?
              let mut args' := #[]
              for arg in args, argTy in argTys do
                args' := args'.push <| ← visit arg argTy
              return mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty?)
          | .proj _ _ b => return e.updateProj! (← visit b none)
          | _           => unreachable!
  visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    let eOrig := e
    let fvars := (← read).fvars
    let e := e.withApp' fun f args => f.beta args
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then return e
    let e ←
      if let some ty := ty? then
        if (← read).config.debug then
          unless ← isDefEq ty (← inferType e) do
            throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
        mkExpectedTypeHint e ty
      else pure e
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
        throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
          fvars: {fvars}"
    let (fvars', pf) ← mkLambdaFVarsUsedOnly' fvars e
    if !(← read).config.abstract && !fvars'.isEmpty then
      return eOrig
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
        throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
          fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
    let pfTy ← instantiateMVars (← inferType pf)
    let pfTy ← abstractProofs' pfTy none
    if let some pf' ← MAbs.findProof? pfTy then
      return mkAppN pf' fvars'
    MAbs.insertProof pfTy pf
    return mkAppN pf fvars'
partial def withGeneralizedProofs' {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToFVar := (← get).propToFVar
  let (e, generalizations) ← MGen.runMAbs <| abstractProofs' e ty?
  let rec
    go [Inhabited α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
        withLocalDeclD (← mkFreshUserName `pf) ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToFVar := propToFVar.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.get?
          modify fun s => { s with propToFVar }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)

partial def generalizeProofsCore'
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) := go g 0 #[]
where
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      let fvar := rfvars[i]
      if fvars.contains fvar then
        let tgt ← instantiateMVars <| ← g.getType
        let ty := (if tgt.isLet then tgt.letType! else tgt.bindingDomain!).cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          let tgt' := Expr.forallE tgt.letName! ty tgt.letBody! .default
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToFVar.get? ty then
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              MGen.insertFVar t' (.fvar fvar')
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b _ =>
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            withGeneralizedProofs' v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g' (usedOnly := false) (usedLetOnly := false)) (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      withGeneralizedProofs' (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)

end GeneralizeProofs

open Lean Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
partial def generalizeProofs'
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : Config := {}) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { propToFVar := ← initialPropToFVar }
    GeneralizeProofs.generalizeProofsCore' g fvars rfvars target |>.run config |>.run' s

elab (name := generalizeProofsElab'') "generalize_proofs" config?:(Parser.Tactic.config)?
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let config ← elabConfig (mkOptionalNode config?)
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← generalizeProofs' g fvars target config
    g.withContext do
      let mut lctx ← getLCtx
      for h in hs, fvar in pfs do
        if let `(binderIdent| $s:ident) := h then
          lctx := lctx.setUserName fvar.fvarId! s.getId
        Expr.addLocalVarInfoForBinderIdent fvar h
      Meta.withLCtx lctx (← Meta.getLocalInstances) do
        let g' ← Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign g'
        return g'.mvarId!

end Harmonic

/-!
# Alternate representation of `Nat` with definitional associativity

We define `AssocNat`, following the (Zulip comment by Trebor
Huang)[https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Nat.20add.20is.20not.20associative/near/396000000].

It's mostly a curiosity for now. The motivation is that one could define `Fin` on `AssocNat`, so
that one can define an append operation on `Fin n → α` (fin vectors) that is definitionally
associative.
-/

/-
AssocNat: natural numbers represented by endomorphisms of `Nat`
that commute with `Nat.succ`.

• The data is just `Nat → Nat`.
• The commuting-with-succ proof lives in `Prop`, so it is erased
  by the kernel; two values that differ only in that proof are
  definitionally equal (`Prop` is a definitional subsingleton).
• "Addition'' is composition, whose associativity is judgmental
  (`rfl`) in lambda calculus.
-/

/-- A natural number as a successor-preserving endomap of `Nat`. This allows addition to be
defined as composition, which is definitionally associative.

TODO: figure out compiler optimization for this representation.
-/
@[ext]
structure AssocNat where
  toFun : Nat → Nat
  presSucc : ∀ n, toFun (n.succ) = (toFun n).succ

attribute [simp] AssocNat.presSucc

instance : CoeFun AssocNat (fun _ => Nat → Nat) := ⟨AssocNat.toFun⟩

namespace AssocNat

/-- `0` is the identity function `ℕ → ℕ`. -/
@[inline] def zero : AssocNat :=
  ⟨id, by intro n; rfl⟩

/-- `1` is the successor of `0`, defined as `Nat.succ`. -/
@[inline] def one : AssocNat :=
  ⟨Nat.succ, by intro n; rfl⟩

/-- Addition on `AssocNat` is just function composition. -/
@[inline] def add (a b : AssocNat) : AssocNat :=
  ⟨a ∘ b, by intro n; simp [Function.comp]⟩

/-- Successor on `AssocNat`, defined as addition by `1` on the right to ensure that
`n.succ = n + 1` holds definitionally. -/
@[inline] def succ (n : AssocNat) : AssocNat :=
  add n one

/-- Convert a `k : Nat` into an `AssocNat`, which is the function `λ m, m + k`. -/
@[inline] def ofNat (k : Nat) : AssocNat :=
  ⟨fun m => m + k, fun m => Nat.succ_add m k⟩

/-- Convert a `k : Nat` into an `AssocNat`, which is the function `λ m, k + m`. -/
@[inline] def ofNat' (k : Nat) : AssocNat :=
  ⟨fun m => k + m, fun m => Nat.add_assoc k m 1⟩

/-- Evaluate an `AssocNat` at `0` to recover a `Nat`. -/
@[inline] def toNat (t : AssocNat) : Nat := t 0

/-- Predecessor of `AssocNat`. -/
@[inline] def pred : AssocNat → AssocNat :=
  fun a => match a.toNat with
  | 0 => zero
  | Nat.succ k => ofNat k

/-- Truncated subtraction on `AssocNat`, implemented by recursion on the **second** argument.
    This mirrors the definition of `Nat.sub`, so we get the same definitional equalities:

    • `a - 0 = a` (rfl)
    • `(succ a) - (succ b) = a - b` (rfl)

    Internally we recurse on `toNat b`, updating the running constant.  The resulting
    endomap is always of the form `λ m, (c - k) + m`, so it is successor‐preserving. -/
def subNat (c : AssocNat) : Nat → AssocNat
| 0            => c -- c - 0 = c
| Nat.succ k   => pred (subNat c k)

-- c - (k + 1) = (c - k).pred?

/-- Truncated subtraction on `AssocNat`, defined as `subAux` on the `toNat` of the arguments. -/
def sub (a b : AssocNat) : AssocNat :=
  subNat a b.toNat

/-- Multiplication on `AssocNat`, obtained by *iterating* `a + _` on the **second** argument.
    This gives the usual judgmental equalities

    • `a * 0 = 0`  (rfl)
    • `a * (succ k) = a + a * k` (rfl)
    • in particular `a * 2 = a + a` (rfl).

    We implement it by a simple `Nat.rec` on `toNat b`. -/
def mulNat (a : AssocNat) : Nat → AssocNat
| 0            => zero
| Nat.succ k   => add a (mulNat a k)

def mul (a b : AssocNat) : AssocNat :=
  mulNat a b.toNat

instance : Zero AssocNat where
  zero := zero

instance : One AssocNat where
  one := one

instance : Add AssocNat where
  add := add

instance : Sub AssocNat where
  sub := sub

instance : Mul AssocNat where
  mul := mul

instance : ToNat AssocNat where
  toNat := toNat

/-- `a + 0 = a` holds definitionally. -/
@[simp] theorem add_zero {a : AssocNat} : a + 0 = a := rfl

/-- `0 + a = a` holds definitionally. -/
@[simp] theorem zero_add {a : AssocNat} : 0 + a = a := rfl

/-- Composition is definitionally associative. -/
theorem add_assoc (a b c : AssocNat) : (a + b) + c = a + (b + c) := rfl

/-- `a * 0 = 0` holds definitionally. -/
@[simp] theorem mul_zero {a : AssocNat} : a * 0 = 0 := rfl

/-- `0 * a = 0` holds only propositionally. -/
theorem zero_mul {a : AssocNat} : 0 * a = 0 := by
  change mul zero a = zero
  ext n
  simp [mul, zero]
  induction h : a.toNat with
  | zero => simp [zero, mulNat, toNat]
  | succ n ih => simp [mulNat, toNat, ih, h]; (
  exact Nat.recOn n rfl fun n ih => by aesop;)

/-- `a * 1 = a` holds definitionally. -/
@[simp] theorem mul_one {a : AssocNat} : a * 1 = a := rfl

-- /-- `a * (succ b) = a + a * b` holds only propositionally. -/
-- theorem mul_succ {a b : AssocNat} : a * (succ b) = a + a * b := by
--   dsimp

/-- `(succ a) * b = a * b + b` holds only propositionally. -/
theorem succ_mul {a b : AssocNat} : (succ a) * b = a * b + b := by
  -- By definition of multiplication in `AssocNat`, we can prove this using induction on `b`.
  have h_mul_ind : ∀ (a : AssocNat) (k : Nat), (a + 1) * AssocNat.ofNat k = a * AssocNat.ofNat k + AssocNat.ofNat k := by
    -- By definition of multiplication in `AssocNat`, we can prove this using induction on `k`.
    intro a k
    induction' k with k ih;
    · exact?;
    · -- By definition of multiplication in `AssocNat`, we have:
      have h_mul_def : ∀ (a : AssocNat) (k : Nat), a * AssocNat.ofNat (k + 1) = a + a * AssocNat.ofNat k := by
        exact?;
      simp_all +decide [ add_comm, add_left_comm, add_assoc ];
      congr! 1;
      ext m;
      exact?;
  -- By definition of `AssocNat`, we know that `b = AssocNat.ofNat b.toNat`.
  have h_b : b = AssocNat.ofNat b.toNat := by
    ext m;
    induction m <;> simp_all +decide [ AssocNat.ofNat ];
    rfl;
  exact h_b ▸ h_mul_ind a _

/-- `a * (b + c) = a * b + a * c` holds only propositionally. -/
theorem mul_add {a b c : AssocNat} : a * (b + c) = a * b + a * c := by
  -- By definition of multiplication, we can rewrite the left-hand side as $a * (b + c)$.
  have h_mul : a * (b + c) = mulNat a (b.toNat + c.toNat) := by
    -- By definition of `toNat`, we know that `toNat (b + c) = b.toNat + c.toNat`.
    have h_toNat : toNat (b + c) = b.toNat + c.toNat := by
      have h_succ : ∀ m, b.toFun m = b.toFun 0 + m := by
        exact fun m => by induction m <;> simp +arith +decide [ * ] ;
      exact h_succ _;
    exact h_toNat ▸ rfl;
  -- We can prove this by induction on `b.toNat`.
  have h_ind : ∀ n : Nat, ∀ a b : AssocNat, mulNat a (n + b.toNat) = mulNat a n + mulNat a b.toNat := by
    intros n a b; induction' n with n ih generalizing a b <;> simp_all +decide [ Nat.succ_add ] ;
    · exact?;
    · convert congr_arg ( fun x => a + x ) ( ih a b ) using 1
  generalize_proofs at *; (
  exact h_mul.trans ( h_ind _ _ _ ))

/-- `1 * a = a` holds only propositionally. -/
@[simp] theorem one_mul {a : AssocNat} : 1 * a = a := by
  change mul one a = a
  ext n
  simp [mul, one]
  induction h : a.toNat with
  | zero => simp [zero, mulNat, toNat]; simp [toNat] at h; (
  -- By induction on $n$, we can show that $a.toFun n = n$ for all $n$.
  have h_ind : ∀ n, a.toFun n = n := by
    intro n; induction n <;> aesop;
  rw [ h_ind ])
  | succ n ih => simp [mulNat, toNat, ih, h]; (
  -- By definition of `toNat`, we know that `a.toNat = n + 1` implies `a = Nat.succ n`.
  have h_eq : a = ⟨fun m => m + (n + 1), fun m => Nat.succ_add m (n + 1)⟩ := by
    -- By induction on $m$, we can show that $a(m) = m + (n + 1)$ for all $m$.
    have h_ind : ∀ m, a m = m + (n + 1) := by
      intro m; induction m <;> simp_all +arith +decide;
      exact h;
    cases a ; aesop;
  -- Substitute h_eq into the goal and simplify.
  rw [h_eq]
  simp [Nat.succ_eq_add_one];
  induction' n with n ih;
  · exact?;
  · induction' n + 1 with n ih <;> simp_all +arith +decide [ Nat.succ_eq_add_one ];
    · exact?;
    · exact?)

/-- `toNat` commutes with successor. -/
@[simp] theorem toNat_succ (t : AssocNat) : toNat (succ t) = (toNat t).succ := by
  simp [succ, toNat, add, one]

/-- Extensionality theorem for `AssocNat`, defined as equality of the endomaps evaluated at `0`. -/
@[ext]
theorem ext' {a b : AssocNat} (h : a 0 = b 0) : a = b := by
  ext m
  induction m with
  | zero => simp [h]
  | succ m ih => simp [ih]

/-- `ofNat` commutes with successor (pointwise equality of functions). -/
@[simp] theorem ofNat_succ (n : Nat) : ofNat n.succ = succ (ofNat n) := by
  ext
  simp [ofNat, succ, one, add, Nat.add_comm]

/-- Every endomap commuting with `Nat.succ` is addition by a constant. -/
theorem toFun_eq_const_plus (t : AssocNat) : ∀ m : Nat, t m = t 0 + m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih => simp [ih, Nat.add_assoc]

/-- `toNat` turns composition into addition. -/
@[simp] theorem toNat_add (a b : AssocNat) : toNat (add a b) = toNat a + toNat b := by
  -- (a ∘ b) 0 = a (b 0)
  dsimp [toNat, add, Function.comp]
  have := toFun_eq_const_plus a (b 0)
  simpa using this

-- /-- `toNat` turns subtraction into truncated subtraction. -/
-- private theorem toNat_subNat (c : AssocNat) (k : Nat) : toNat (subNat c k) = c - k := by
--   induction k with
--   | zero => simp [subNat, toNat]; sorry
--   | succ k ih => sorry

-- @[simp] theorem toNat_sub (a b : AssocNat) : toNat (sub a b) = toNat a - toNat b := by
--   dsimp [sub]
--   exact toNat_subAux (toNat a) (toNat b)

/-- `toNat` turns multiplication into multiplication. -/
private theorem toNat_mulNat (a : AssocNat) (k : Nat) : toNat (mulNat a k) = toNat a * k := by
  induction k with
  | zero => simp [mulNat, toNat, zero]
  | succ k ih =>
  convert congr_arg₂ ( · + · ) rfl ih using 1;
  convert toNat_add a ( a.mulNat k ) using 1;
  ring

@[simp] theorem toNat_mul (a b : AssocNat) : toNat (mul a b) = toNat a * toNat b := by
  dsimp [mul]
  exact toNat_mulNat a (toNat b)

/-- `ofNat` respects addition (pointwise equality of functions). -/
@[simp] theorem ofNat_add (n m : Nat) : ofNat (n + m) = add (ofNat n) (ofNat m) := by
  ext
  simp [ofNat, add, Nat.add_comm, Nat.add_left_comm]

/-- `toNat` is the left inverse of `ofNat`. -/
@[simp] theorem toNat_ofNat (n : Nat) : toNat (ofNat n) = n := by
  simp [toNat, ofNat]

/-- `ofNat` is the right inverse of `toNat`. -/
@[simp] theorem ofNat_toNat (t : AssocNat) : ofNat (toNat t) = t := by
  ext
  simp [ofNat, toNat]

/-- The explicit equivalence `Nat ≃ AssocNat`. -/
@[simps] def equivNat : Nat ≃ AssocNat where
  toFun := ofNat
  invFun := toNat
  left_inv := by
    intro n; simp
  right_inv := by
    intro t; simp

/-- Less-than relation on `AssocNat`, defined directly without going through `Nat`. -/
instance : LT AssocNat where
  lt a b := a 0 < b 0

/-- Less-equal relation on `AssocNat`. -/
instance : LE AssocNat where
  le a b := a 0 ≤ b 0

/-- The less-than relation is well-defined (does not depend on choice of representative). -/
theorem lt_iff_toNat_lt (a b : AssocNat) : a < b ↔ toNat a < toNat b := by
  rfl

/-- The less-equal relation is well-defined. -/
theorem le_iff_toNat_le (a b : AssocNat) : a ≤ b ↔ toNat a ≤ toNat b := by
  rfl

/-- `AssocNat` has decidable equality. -/
instance : DecidableEq AssocNat := by
  intro a b
  by_cases h : a 0 = b 0
  · right; exact ext' h
  · left; intro heq; exact h (by rw [heq])

-- /-- `AssocNat` forms a linear order. -/
-- instance : LinearOrder AssocNat := sorry

end AssocNat

-- -----------------------------------------------------------------
-- AssocFin: finite types based on AssocNat
-- -----------------------------------------------------------------

/-- `AssocFin n` is the type of `AssocNat` numbers less than `n`. -/
@[ext]
structure AssocFin (n : AssocNat) where
  val : AssocNat
  isLt : val < n

attribute [simp] AssocFin.isLt

namespace AssocFin

variable {n : AssocNat}

instance : CoeFun (AssocFin n) (fun _ => Nat → Nat) := ⟨fun f => f.val.toFun⟩

/-- The value of an `AssocFin` as an `AssocNat`. -/
def toAssocNat (f : AssocFin n) : AssocNat := f.val

/-- Convert an `AssocFin` to a regular `Fin` via the isomorphism. -/
def toFin (f : AssocFin n) : Fin (AssocNat.toNat n) :=
  ⟨AssocNat.toNat f.val, f.isLt⟩

/-- Convert a regular `Fin` to an `AssocFin` via the isomorphism. -/
def ofFin {n : AssocNat} (f : Fin (AssocNat.toNat n)) : AssocFin n :=
  ⟨AssocNat.ofNat f.val, by simp [AssocNat.lt_iff_toNat_lt, AssocNat.toNat_ofNat]⟩

/-- `AssocFin 0` is empty. -/
instance : IsEmpty (AssocFin AssocNat.zero) := by
  constructor
  intro f
  have : f.val.toNat < 0 := f.isLt
  exact Nat.not_lt_zero _ this

/-- `AssocFin` has decidable equality. -/
instance (n : AssocNat) : DecidableEq (AssocFin n) := by
  intro a b
  by_cases h : a.val = b.val
  · right; exact AssocFin.ext h
  · left; intro heq; exact h (by rw [heq])

end AssocFin