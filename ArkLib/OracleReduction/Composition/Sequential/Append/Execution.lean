/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Composition.Sequential.Append.StateFunction

/-!
  # Sequential Composition: Execution

  Running an appended prover / verifier / reduction. The main result is `Prover.append_run`,
  which decomposes `(P₁.append P₂).run` into the two component runs; it is supported by the
  transport ladder in the `AppendRunHelpers` section below.
-/

open OracleComp OracleSpec SubSpec

universe u v

open ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

section Execution

/-! ## Helper lemmas for `Prover.append_run`

The appended prover `P₁.append P₂` is defined by a three-way `dif` on the round index (below the
seam / at the seam / above the seam), and each branch transports its state along a type equality.
Reasoning about `runToRound` therefore forces us to work up to `HEq`.  The lemmas below build the
transport ladder that `Prover.append_run` needs; they are all `private`, since they exist only to
serve that proof and the security proofs later in this file.
-/

section AppendRunHelpers

variable {P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
    {P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}

/-! ### Transport helpers -/

private theorem heq_eqMpr {α β : Sort u} (h : α = β) (b : β) : HEq (Eq.mpr h b) b := by subst h; rfl

private theorem heq_eqMp' {α β : Sort u} (h : α = β) (a : α) : HEq (Eq.mp h a) a := by subst h; rfl

private theorem heq_bind {M : Type → Type} [Monad M] {α α' β β' : Type} (hα : α = α') (hβ : β = β')
    {x : M α} {x' : M α'} (hx : HEq x x') {f : α → M β} {f' : α' → M β'} (hf : HEq f f') :
    HEq (x >>= f) (x' >>= f') := by
  subst hα; subst hβ
  obtain rfl := eq_of_heq hx
  obtain rfl := eq_of_heq hf
  rfl

private theorem heq_liftM {ι' : Type} {superSpec : OracleSpec ι'} [oSpec ⊂ₒ superSpec]
    {α α' : Type} (hα : α = α')
    {x : OracleComp oSpec α} {x' : OracleComp oSpec α'} (hx : HEq x x') :
    HEq (liftM x : OracleComp superSpec α) (liftM x' : OracleComp superSpec α') := by
  subst hα
  obtain rfl := eq_of_heq hx
  rfl

private theorem heq_pure {M : Type → Type} [Monad M] {α α' : Type} (hα : α = α')
    {a : α} {a' : α'} (h : HEq a a') : HEq (pure a : M α) (pure a' : M α') := by
  subst hα; obtain rfl := eq_of_heq h; rfl

private theorem heq_prod {A A' B B' : Type} (hA : A = A') (hB : B = B')
    {a : A} {a' : A'} (ha : HEq a a') {b : B} {b' : B'} (hb : HEq b b') :
    HEq ((a, b) : A × B) ((a', b') : A' × B') := by
  subst hA; subst hB; obtain rfl := eq_of_heq ha; obtain rfl := eq_of_heq hb; rfl

private theorem heq_fst {A A' B B' : Type} (hA : A = A') (hB : B = B') {x : A × B} {x' : A' × B'}
    (h : HEq x x') : HEq x.1 x'.1 := by
  subst hA; subst hB; obtain rfl := eq_of_heq h; rfl

private theorem heq_snd {A A' B B' : Type} (hA : A = A') (hB : B = B') {x : A × B} {x' : A' × B'}
    (h : HEq x x') : HEq x.2 x'.2 := by
  subst hA; subst hB; obtain rfl := eq_of_heq h; rfl

private theorem heq_fun' {α α' β β' : Type} (hα : α = α') (hβ : β = β')
    {f : α → β} {f' : α' → β'}
    (h : ∀ (a : α) (a' : α'), HEq a a' → HEq (f a) (f' a')) : HEq f f' := by
  subst hα; subst hβ
  exact heq_of_eq (funext fun a => eq_of_heq (h a a HEq.rfl))

private theorem heq_app {A A' B B' : Type} (hA : A = A') (hB : B = B')
    {f : A → B} {f' : A' → B'} (hf : HEq f f') {a : A} {a' : A'} (ha : HEq a a') :
    HEq (f a) (f' a') := by
  subst hA; subst hB; obtain rfl := eq_of_heq hf; obtain rfl := eq_of_heq ha; rfl

private theorem heq_pi {α : Sort u} {β β' : α → Sort v} (hβ : β = β')
    {f : (a : α) → β a} {g : (a : α) → β' a} (h : ∀ a, HEq (f a) (g a)) : HEq f g := by
  subst hβ; exact heq_of_eq (funext fun a => eq_of_heq (h a))

private theorem heq_dapply {α : Sort u} {β β' : α → Sort v} (hβ : β = β')
    {f : (a : α) → β a} {g : (a : α) → β' a} (h : HEq f g) (a : α) : HEq (f a) (g a) := by
  subst hβ; obtain rfl := eq_of_heq h; rfl

/-! ### `Transcript.concat` computation rules -/

private theorem concat_apply_lt {N : ℕ} {pSpec : ProtocolSpec N} {k : Fin N}
    (T : pSpec.Transcript k.castSucc) (msg : pSpec.«Type» k) (i : ℕ) (hi : i < k.val)
    (hi' : i < (k.succ : Fin (N + 1)).val) :
    HEq (T.concat msg ⟨i, hi'⟩) (T ⟨i, hi⟩) := by
  unfold Transcript.concat Fin.snoc
  rw [dif_pos hi]
  exact cast_heq _ _

private theorem concat_apply_last {N : ℕ} {pSpec : ProtocolSpec N} {k : Fin N}
    (T : pSpec.Transcript k.castSucc) (msg : pSpec.«Type» k) (i : ℕ) (hik : i = k.val)
    (hi' : i < (k.succ : Fin (N + 1)).val) :
    HEq (T.concat msg ⟨i, hi'⟩) msg := by
  subst hik
  unfold Transcript.concat Fin.snoc
  rw [dif_neg (Nat.lt_irrefl k.val)]
  exact cast_heq _ _

/-! ### The combined prover's state family -/

private theorem prvState_left (k : Fin (m + n + 1)) (j : Fin (m + 1)) (hkj : k.val = j.val) :
    (P₁.append P₂).PrvState k = P₁.PrvState j := by
  change (Fin.append (m := m + 1) P₁.PrvState (Fin.tail P₂.PrvState)
    ∘ Fin.cast (by omega)) k = P₁.PrvState j
  have hcast : Fin.cast (show m + n + 1 = m + 1 + n by omega) k = Fin.castAdd n j := by
    ext; simpa using hkj
  simp only [Function.comp_apply, hcast, Fin.append_left]

private theorem prvState_right (k : Fin (m + n + 1)) (j : Fin (n + 1)) (hk : m < k.val)
    (hkj : k.val = m + j.val) :
    (P₁.append P₂).PrvState k = P₂.PrvState j := by
  change (Fin.append (m := m + 1) P₁.PrvState (Fin.tail P₂.PrvState)
    ∘ Fin.cast (by omega)) k = P₂.PrvState j
  have hcast : Fin.cast (show m + n + 1 = m + 1 + n by omega) k
      = Fin.natAdd (m + 1) ⟨j.val - 1, by omega⟩ := by
    ext; simp; omega
  simp only [Function.comp_apply, hcast, Fin.append_right, Fin.tail]
  congr 1
  ext; simp; omega

/-! ### Round behaviour below the seam -/

private theorem append_sendMessage_left (i : Fin (m + n)) (hi : i.val < m)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir i = .P_to_V)
    (hDir₁ : pSpec₁.dir ⟨i.val, hi⟩ = .P_to_V)
    (state : (P₁.append P₂).PrvState i.castSucc)
    (state₁ : P₁.PrvState (⟨i.val, hi⟩ : Fin m).castSucc)
    (hst : HEq state state₁) :
    HEq ((P₁.append P₂).sendMessage ⟨i, hDir⟩ state)
        (P₁.sendMessage ⟨⟨i.val, hi⟩, hDir₁⟩ state₁) := by
  conv_lhs => unfold Prover.append
  dsimp only
  rw [dif_pos hi]
  refine (heq_eqMpr _ _).trans (heq_of_eq ?_)
  congr 1
  exact eq_of_heq ((heq_eqMp' _ _).trans hst)

private theorem append_receiveChallenge_left (i : Fin (m + n)) (hi : i.val < m)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir i = .V_to_P)
    (hDir₁ : pSpec₁.dir ⟨i.val, hi⟩ = .V_to_P)
    (state : (P₁.append P₂).PrvState i.castSucc)
    (state₁ : P₁.PrvState (⟨i.val, hi⟩ : Fin m).castSucc)
    (hst : HEq state state₁) :
    HEq ((P₁.append P₂).receiveChallenge ⟨i, hDir⟩ state)
        (P₁.receiveChallenge ⟨⟨i.val, hi⟩, hDir₁⟩ state₁) := by
  conv_lhs => unfold Prover.append
  dsimp only
  rw [dif_pos hi]
  refine (heq_eqMpr _ _).trans (heq_of_eq ?_)
  congr 1
  exact eq_of_heq ((heq_eqMp' _ _).trans hst)

/-! ### Transcript payload types -/

/-- The two `Type` families a left-index transcript ranges over are equal. -/
private theorem transcript_family_left (k : ℕ) (hk : k ≤ m) (h1 : k ≤ m + n) :
    (fun i : Fin k => (pSpec₁ ++ₚ pSpec₂).«Type» (Fin.castLE h1 i))
      = (fun i : Fin k => pSpec₁.«Type» (Fin.castLE hk i)) := by
  funext i
  have hcast : Fin.castLE h1 i = Fin.castAdd n (Fin.castLE hk i) := by ext; simp
  rw [hcast, append_Type_castAdd]

private theorem transcript_left_type_eq (k : Fin (m + n + 1)) (j : Fin (m + 1))
    (hkj : k.val = j.val) :
    (pSpec₁ ++ₚ pSpec₂).Transcript k = pSpec₁.Transcript j := by
  obtain ⟨kv, hk⟩ := k
  obtain ⟨jv, hjv⟩ := j
  dsimp only at hkj
  subst hkj
  change ((i : Fin kv) → (pSpec₁ ++ₚ pSpec₂).«Type» (Fin.castLE (by omega) i))
    = ((i : Fin kv) → pSpec₁.«Type» (Fin.castLE (by omega) i))
  refine congrArg (fun F : Fin kv → Type => (i : Fin kv) → F i) ?_
  exact transcript_family_left kv (by omega) (by omega)

/-- `Transcript.concat` is compatible with the left-append transport. -/
private theorem heq_concat_left (j : Fin (m + n)) (hj : j.val < m)
    {msg : (pSpec₁ ++ₚ pSpec₂).«Type» j} {msg₁ : pSpec₁.«Type» ⟨j.val, hj⟩} (hmsg : HEq msg msg₁)
    {tr : (pSpec₁ ++ₚ pSpec₂).Transcript j.castSucc}
    {tr₁ : pSpec₁.Transcript (⟨j.val, hj⟩ : Fin m).castSucc} (htr : HEq tr tr₁) :
    HEq (Transcript.concat msg tr) (Transcript.concat msg₁ tr₁) := by
  refine heq_pi (transcript_family_left (j.val + 1) (by omega) (by omega)) (fun i => ?_)
  rcases Nat.lt_or_ge i.val j.val with h | h
  · refine (concat_apply_lt tr msg i.val h i.isLt).trans ?_
    refine HEq.trans ?_ (concat_apply_lt tr₁ msg₁ i.val h i.isLt).symm
    exact heq_dapply (transcript_family_left j.val (by omega) (by omega)) htr ⟨i.val, h⟩
  · have hi : i.val = j.val := by have := i.isLt; omega
    exact ((concat_apply_last tr msg i.val hi i.isLt).trans hmsg).trans
      (concat_apply_last tr₁ msg₁ i.val hi i.isLt).symm

/-! ### `processRound` only sees its input through a bind -/

private theorem processRound_eq_bind {N : ℕ} {pSpec : ProtocolSpec N} (j : Fin N)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec)
    (cur : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript j.castSucc × P.PrvState j.castSucc)) :
    P.processRound j cur = cur >>= fun x => P.processRound j (pure x) := by
  unfold Prover.processRound
  simp [pure_bind]

/-! ### Lift coherence: the two-step lift agrees with the direct lift -/

private theorem liftAppendLeft_liftM {α : Type} (oa : OracleComp oSpec α) :
    (liftAppendLeft pSpec₂ (liftM oa : OracleComp (oSpec + [pSpec₁.Challenge]ₒ) α))
      = (liftM oa : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α) := by
  unfold liftAppendLeft
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    simp [ih]
    congr 1

/-- Lifting a left-component challenge query into the appended protocol queries the
left-injected index and transports the response back. -/
private theorem liftAppendLeft_getChallenge (i : ChallengeIdx pSpec₁) :
    liftAppendLeft pSpec₂
        ((liftM (pSpec₁.getChallenge i)) :
          OracleComp (oSpec + [pSpec₁.Challenge]ₒ) (pSpec₁.Challenge i))
      = cast (challenge_append_inl (pSpec₂ := pSpec₂) i) <$>
          ((liftM ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inl i))) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl i))) := by
  unfold liftAppendLeft
  rfl

/-! ### Next rung (the 4-way split is done; the two real branches remain) -/

private theorem append_processRound_left_pure (j : Fin (m + n)) (hj : j.val < m)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript j.castSucc)
    (st : (P₁.append P₂).PrvState j.castSucc)
    (tr₁ : pSpec₁.Transcript (⟨j.val, hj⟩ : Fin m).castSucc)
    (st₁ : P₁.PrvState (⟨j.val, hj⟩ : Fin m).castSucc)
    (htr : HEq tr tr₁) (hst : HEq st st₁) :
    HEq ((P₁.append P₂).processRound j (pure ⟨tr, st⟩))
        (liftAppendLeft pSpec₂ (P₁.processRound ⟨j.val, hj⟩ (pure ⟨tr₁, st₁⟩))) := by
  have hdir : Fin.vappend pSpec₁.dir pSpec₂.dir j = pSpec₁.dir ⟨j.val, hj⟩ :=
    Fin.vappend_left_of_lt _ _ j hj
  unfold Prover.processRound liftAppendLeft
  simp only [pure_bind]
  split <;> rename_i hA <;> split <;> rename_i hB
  · -- both V_to_P
    simp only [liftM_bind, liftM_pure, liftAppendLeft_liftM, liftAppendLeft_getChallenge,
      bind_map_left]
    have hChal : (pSpec₁ ++ₚ pSpec₂).Challenge (⟨j, hA⟩ : ChallengeIdx (pSpec₁ ++ₚ pSpec₂))
        = pSpec₁.Challenge ⟨⟨j.val, hj⟩, hB⟩ :=
      challenge_append_inl (pSpec₂ := pSpec₂) ⟨⟨j.val, hj⟩, hB⟩
    have hStS : (P₁.append P₂).PrvState j.succ = P₁.PrvState (⟨j.val, hj⟩ : Fin m).succ :=
      prvState_left _ _ rfl
    have hTrS : (pSpec₁ ++ₚ pSpec₂).Transcript j.succ
        = pSpec₁.Transcript (⟨j.val, hj⟩ : Fin m).succ :=
      transcript_left_type_eq _ _ rfl
    have hPairOut : ((pSpec₁ ++ₚ pSpec₂).Transcript j.succ × (P₁.append P₂).PrvState j.succ)
        = (pSpec₁.Transcript (⟨j.val, hj⟩ : Fin m).succ
            × P₁.PrvState (⟨j.val, hj⟩ : Fin m).succ) :=
      congrArg₂ Prod hTrS hStS
    have hMOut : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
          ((pSpec₁ ++ₚ pSpec₂).Transcript j.succ × (P₁.append P₂).PrvState j.succ)
        = OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
          (pSpec₁.Transcript (⟨j.val, hj⟩ : Fin m).succ
            × P₁.PrvState (⟨j.val, hj⟩ : Fin m).succ) :=
      congrArg _ hPairOut
    have hFun : ((pSpec₁ ++ₚ pSpec₂).Challenge (⟨j, hA⟩ : ChallengeIdx (pSpec₁ ++ₚ pSpec₂))
          → (P₁.append P₂).PrvState j.succ)
        = (pSpec₁.Challenge ⟨⟨j.val, hj⟩, hB⟩ → P₁.PrvState (⟨j.val, hj⟩ : Fin m).succ) :=
      congrArg₂ (fun X Y => X → Y) hChal hStS
    have hMFun : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
          ((pSpec₁ ++ₚ pSpec₂).Challenge (⟨j, hA⟩ : ChallengeIdx (pSpec₁ ++ₚ pSpec₂))
            → (P₁.append P₂).PrvState j.succ)
        = OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
          (pSpec₁.Challenge ⟨⟨j.val, hj⟩, hB⟩ → P₁.PrvState (⟨j.val, hj⟩ : Fin m).succ) :=
      congrArg _ hFun
    refine heq_bind rfl hPairOut HEq.rfl ?_
    refine heq_fun' rfl hMOut ?_
    intro c c' hc
    obtain rfl := eq_of_heq hc
    refine heq_bind hFun hPairOut ?_ ?_
    · exact heq_liftM hFun (append_receiveChallenge_left j hj hA hB st st₁ hst)
    · refine heq_fun' hFun hMOut ?_
      intro f f' hf
      exact heq_pure hPairOut
        (heq_prod hTrS hStS
          (heq_concat_left j hj (cast_heq hChal c).symm htr)
          (heq_app hChal hStS hf (cast_heq hChal c).symm))
  · rw [hdir, hB] at hA; exact absurd hA (by simp)
  · rw [hdir, hB] at hA; exact absurd hA (by simp)
  · -- both P_to_V
    simp only [liftM_bind, liftM_pure, liftAppendLeft_liftM]
    have hMsg : (pSpec₁ ++ₚ pSpec₂).«Type» j = pSpec₁.«Type» ⟨j.val, hj⟩ :=
      calc (pSpec₁ ++ₚ pSpec₂).«Type» j
          = (pSpec₁ ++ₚ pSpec₂).«Type» (Fin.castAdd n (⟨j.val, hj⟩ : Fin m)) :=
            congrArg _ (Fin.ext rfl).symm
        _ = pSpec₁.«Type» ⟨j.val, hj⟩ := append_Type_castAdd _
    have hStS : (P₁.append P₂).PrvState j.succ = P₁.PrvState (⟨j.val, hj⟩ : Fin m).succ :=
      prvState_left _ _ rfl
    have hTrS : (pSpec₁ ++ₚ pSpec₂).Transcript j.succ
        = pSpec₁.Transcript (⟨j.val, hj⟩ : Fin m).succ :=
      transcript_left_type_eq _ _ rfl
    have hPairIn : ((pSpec₁ ++ₚ pSpec₂).Message ⟨j, hA⟩ × (P₁.append P₂).PrvState j.succ)
        = (pSpec₁.Message ⟨⟨j.val, hj⟩, hB⟩ × P₁.PrvState (⟨j.val, hj⟩ : Fin m).succ) :=
      congrArg₂ Prod hMsg hStS
    have hPairOut : ((pSpec₁ ++ₚ pSpec₂).Transcript j.succ × (P₁.append P₂).PrvState j.succ)
        = (pSpec₁.Transcript (⟨j.val, hj⟩ : Fin m).succ
            × P₁.PrvState (⟨j.val, hj⟩ : Fin m).succ) :=
      congrArg₂ Prod hTrS hStS
    refine heq_bind hPairIn hPairOut ?_ ?_
    · exact heq_liftM hPairIn (append_sendMessage_left j hj hA hB st st₁ hst)
    · have hMOut : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            ((pSpec₁ ++ₚ pSpec₂).Transcript j.succ × (P₁.append P₂).PrvState j.succ)
          = OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            (pSpec₁.Transcript (⟨j.val, hj⟩ : Fin m).succ
              × P₁.PrvState (⟨j.val, hj⟩ : Fin m).succ) :=
        congrArg _ hPairOut
      refine heq_fun' hPairIn hMOut ?_
      intro x x' hx
      exact heq_pure hPairOut
        (heq_prod hTrS hStS (heq_concat_left j hj (heq_fst hMsg hStS hx) htr)
          (heq_snd hMsg hStS hx))

/-! ### Running up to a round below the seam -/

private theorem append_input (ctxIn : Stmt₁ × Wit₁) :
    HEq ((P₁.append P₂).input ctxIn) (P₁.input ctxIn) := by
  conv_lhs => unfold Prover.append
  dsimp only
  exact heq_eqMpr _ _

private theorem heq_default_transcript :
    HEq (default : (pSpec₁ ++ₚ pSpec₂).Transcript 0) (default : pSpec₁.Transcript 0) := by
  refine heq_pi (transcript_family_left 0 (by omega) (by omega)) (fun i => ?_)
  exact Fin.elim0 i

/-- The payload type of `runToRound` below the seam. -/
private theorem payload_left_eq (k : Fin (m + n + 1)) (j : Fin (m + 1)) (hkj : k.val = j.val) :
    ((pSpec₁ ++ₚ pSpec₂).Transcript k × (P₁.append P₂).PrvState k)
      = (pSpec₁.Transcript j × P₁.PrvState j) :=
  congrArg₂ Prod (transcript_left_type_eq k j hkj) (prvState_left k j hkj)

private theorem append_runToRound_left (stmt : Stmt₁) (wit : Wit₁) (j : Fin (m + 1)) :
    ∀ (k : Fin (m + n + 1)), k.val = j.val →
      HEq ((P₁.append P₂).runToRound k stmt wit)
          (liftAppendLeft pSpec₂ (P₁.runToRound j stmt wit)) := by
  induction j using Fin.induction with
  | zero =>
    intro k hk
    obtain rfl : k = 0 := Fin.ext (by simpa using hk)
    unfold Prover.runToRound
    simp only [Fin.induction_zero, liftAppendLeft]
    exact heq_pure (payload_left_eq 0 0 (by simp))
      (heq_prod (transcript_left_type_eq 0 0 (by simp)) (prvState_left 0 0 (by simp))
        heq_default_transcript (append_input _))
  | succ i ih =>
    intro k hk
    have hle : m ≤ m + n := Nat.le_add_right m n
    obtain rfl : k = (Fin.castLE hle i).succ := by
      refine Fin.ext ?_
      have := i.isLt
      simpa using hk
    unfold Prover.runToRound
    simp only [Fin.induction_succ]
    rw [processRound_eq_bind (P := P₁.append P₂), processRound_eq_bind (P := P₁)]
    simp only [liftM_bind]
    refine heq_bind (payload_left_eq _ _ (by simp)) (payload_left_eq _ _ (by simp))
      (ih _ (by simp)) ?_
    refine heq_fun' (payload_left_eq _ _ (by simp))
      (congrArg _ (payload_left_eq _ _ (by simp))) ?_
    intro x x' hx
    exact append_processRound_left_pure (Fin.castLE hle i) i.isLt
      x.1 x.2 x'.1 x'.2
      (heq_fst (transcript_left_type_eq _ _ (by simp)) (prvState_left _ _ (by simp)) hx)
      (heq_snd (transcript_left_type_eq _ _ (by simp)) (prvState_left _ _ (by simp)) hx)

/-! ### The seam round `m`, and rounds above it -/

private theorem heq_dcast {α : Sort u} {β : α → Sort v} [DCast α β] {a a' : α} (h : a = a')
    (b : β a) :
    HEq (dcast h b) b := by
  subst h; rw [dcast_eq]

private theorem append_sendMessage_seam (i : Fin (m + n)) (him : i.val = m) (hn : 0 < n)
    (outputFn : P₁.PrvState (Fin.last m) → Stmt₂ × Wit₂)
    (hOutput : P₁.output = fun st => pure (outputFn st))
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir i = .P_to_V)
    (hDir₂ : pSpec₂.dir ⟨0, hn⟩ = .P_to_V)
    (state : (P₁.append P₂).PrvState i.castSucc)
    (state₁ : P₁.PrvState (Fin.last m)) (hst : HEq state state₁) :
    HEq ((P₁.append P₂).sendMessage ⟨i, hDir⟩ state)
        (P₂.sendMessage ⟨⟨0, hn⟩, hDir₂⟩ (P₂.input (outputFn state₁))) := by
  conv_lhs => unfold Prover.append
  dsimp only
  rw [dif_neg (by omega : ¬ i.val < m), dif_pos him]
  refine (heq_eqMpr _ _).trans (heq_of_eq ?_)
  rw [hOutput]
  simp only [pure_bind]
  exact congrArg (fun z => P₂.sendMessage ⟨⟨0, hn⟩, hDir₂⟩ (P₂.input (outputFn z)))
    (eq_of_heq ((heq_eqMp' _ _).trans hst))

private theorem append_receiveChallenge_seam (i : Fin (m + n)) (him : i.val = m) (hn : 0 < n)
    (outputFn : P₁.PrvState (Fin.last m) → Stmt₂ × Wit₂)
    (hOutput : P₁.output = fun st => pure (outputFn st))
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir i = .V_to_P)
    (hDir₂ : pSpec₂.dir ⟨0, hn⟩ = .V_to_P)
    (state : (P₁.append P₂).PrvState i.castSucc)
    (state₁ : P₁.PrvState (Fin.last m)) (hst : HEq state state₁) :
    HEq ((P₁.append P₂).receiveChallenge ⟨i, hDir⟩ state)
        (P₂.receiveChallenge ⟨⟨0, hn⟩, hDir₂⟩ (P₂.input (outputFn state₁))) := by
  conv_lhs => unfold Prover.append
  dsimp only
  rw [dif_neg (by omega : ¬ i.val < m), dif_pos him]
  refine (heq_eqMpr _ _).trans (heq_of_eq ?_)
  rw [hOutput]
  simp only [pure_bind]
  exact congrArg (fun z => P₂.receiveChallenge ⟨⟨0, hn⟩, hDir₂⟩ (P₂.input (outputFn z)))
    (eq_of_heq ((heq_eqMp' _ _).trans hst))

private theorem append_sendMessage_right (i : Fin (m + n)) (hi : m < i.val) (hik : i.val - m < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir i = .P_to_V)
    (hDir₂ : pSpec₂.dir ⟨i.val - m, hik⟩ = .P_to_V)
    (state : (P₁.append P₂).PrvState i.castSucc)
    (state₂ : P₂.PrvState (⟨i.val - m, hik⟩ : Fin n).castSucc) (hst : HEq state state₂) :
    HEq ((P₁.append P₂).sendMessage ⟨i, hDir⟩ state)
        (P₂.sendMessage ⟨⟨i.val - m, hik⟩, hDir₂⟩ state₂) := by
  conv_lhs => unfold Prover.append
  dsimp only
  rw [dif_neg (by omega : ¬ i.val < m), dif_neg (by omega : ¬ i.val = m)]
  refine (heq_eqMpr _ _).trans (heq_of_eq ?_)
  congr 1
  exact eq_of_heq ((heq_dcast _ _).trans ((heq_eqMp' _ _).trans hst))

private theorem append_receiveChallenge_right (i : Fin (m + n)) (hi : m < i.val)
    (hik : i.val - m < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir i = .V_to_P)
    (hDir₂ : pSpec₂.dir ⟨i.val - m, hik⟩ = .V_to_P)
    (state : (P₁.append P₂).PrvState i.castSucc)
    (state₂ : P₂.PrvState (⟨i.val - m, hik⟩ : Fin n).castSucc) (hst : HEq state state₂) :
    HEq ((P₁.append P₂).receiveChallenge ⟨i, hDir⟩ state)
        (P₂.receiveChallenge ⟨⟨i.val - m, hik⟩, hDir₂⟩ state₂) := by
  conv_lhs => unfold Prover.append
  dsimp only
  rw [dif_neg (by omega : ¬ i.val < m), dif_neg (by omega : ¬ i.val = m)]
  refine (heq_eqMpr _ _).trans (heq_of_eq ?_)
  congr 1
  exact eq_of_heq ((heq_dcast _ _).trans ((heq_eqMp' _ _).trans hst))

/-- `append_sendMessage_right` stated at an explicit `pSpec₂` round index. -/
private theorem append_sendMessage_right' (i : Fin (m + n)) (l : Fin n) (hil : i.val = m + l.val)
    (hl : 0 < l.val)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir i = .P_to_V) (hDir₂ : pSpec₂.dir l = .P_to_V)
    (state : (P₁.append P₂).PrvState i.castSucc) (state₂ : P₂.PrvState l.castSucc)
    (hst : HEq state state₂) :
    HEq ((P₁.append P₂).sendMessage ⟨i, hDir⟩ state) (P₂.sendMessage ⟨l, hDir₂⟩ state₂) := by
  have hik : i.val - m < n := by have := i.isLt; omega
  obtain rfl : l = ⟨i.val - m, hik⟩ := Fin.ext (show l.val = i.val - m by omega)
  exact append_sendMessage_right i (by omega) hik hDir hDir₂ state state₂ hst

/-- `append_receiveChallenge_right` stated at an explicit `pSpec₂` round index. -/
private theorem append_receiveChallenge_right' (i : Fin (m + n)) (l : Fin n)
    (hil : i.val = m + l.val)
    (hl : 0 < l.val)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir i = .V_to_P) (hDir₂ : pSpec₂.dir l = .V_to_P)
    (state : (P₁.append P₂).PrvState i.castSucc) (state₂ : P₂.PrvState l.castSucc)
    (hst : HEq state state₂) :
    HEq ((P₁.append P₂).receiveChallenge ⟨i, hDir⟩ state)
        (P₂.receiveChallenge ⟨l, hDir₂⟩ state₂) := by
  have hik : i.val - m < n := by have := i.isLt; omega
  obtain rfl : l = ⟨i.val - m, hik⟩ := Fin.ext (show l.val = i.val - m by omega)
  exact append_receiveChallenge_right i (by omega) hik hDir hDir₂ state state₂ hst

/-! ### Combining a full left transcript with a partial right transcript -/

private theorem append_Type_lt (i : Fin (m + n)) (h : i.val < m) :
    (pSpec₁ ++ₚ pSpec₂).«Type» i = pSpec₁.«Type» ⟨i.val, h⟩ :=
  calc (pSpec₁ ++ₚ pSpec₂).«Type» i
      = (pSpec₁ ++ₚ pSpec₂).«Type» (Fin.castAdd n (⟨i.val, h⟩ : Fin m)) :=
        congrArg _ (Fin.ext rfl).symm
    _ = pSpec₁.«Type» ⟨i.val, h⟩ := append_Type_castAdd _

private theorem append_Type_ge (i : Fin (m + n)) (h2 : i.val - m < n) (h : m ≤ i.val) :
    (pSpec₁ ++ₚ pSpec₂).«Type» i = pSpec₂.«Type» ⟨i.val - m, h2⟩ :=
  calc (pSpec₁ ++ₚ pSpec₂).«Type» i
      = (pSpec₁ ++ₚ pSpec₂).«Type» (Fin.natAdd m (⟨i.val - m, h2⟩ : Fin n)) :=
        congrArg _ (Fin.ext (show m + (i.val - m) = i.val by omega)).symm
    _ = pSpec₂.«Type» ⟨i.val - m, h2⟩ := append_Type_natAdd _

/-- Glue a complete `pSpec₁` transcript onto a partial `pSpec₂` transcript. -/
private def concatLR {k : Fin (m + n + 1)} {l : Fin (n + 1)} (hkl : k.val = m + l.val)
    (tr₁ : pSpec₁.FullTranscript) (tr₂ : pSpec₂.Transcript l) :
    (pSpec₁ ++ₚ pSpec₂).Transcript k := fun i =>
  have hi : i.val < k.val := i.isLt
  have hl : l.val < n + 1 := l.isLt
  have hk : k.val ≤ m + n := by have := k.isLt; omega
  if h : i.val < m then
    cast (append_Type_lt (pSpec₂ := pSpec₂) (Fin.castLE hk i) h).symm (tr₁ ⟨i.val, h⟩)
  else
    cast (append_Type_ge (pSpec₁ := pSpec₁) (Fin.castLE hk i)
        (show i.val - m < n by omega) (show m ≤ i.val by omega)).symm
      (tr₂ ⟨i.val - m, by omega⟩)

private theorem concatLR_apply_lt {k : Fin (m + n + 1)} {l : Fin (n + 1)} (hkl : k.val = m + l.val)
    (tr₁ : pSpec₁.FullTranscript) (tr₂ : pSpec₂.Transcript l)
    (i : Fin k.val) (h : i.val < m) :
    HEq (concatLR hkl tr₁ tr₂ i) (tr₁ ⟨i.val, h⟩) := by
  unfold concatLR
  rw [dif_pos h]
  exact cast_heq _ _

private theorem concatLR_apply_ge {k : Fin (m + n + 1)} {l : Fin (n + 1)} (hkl : k.val = m + l.val)
    (tr₁ : pSpec₁.FullTranscript) (tr₂ : pSpec₂.Transcript l)
    (i : Fin k.val) (h : ¬ i.val < m) (h2 : i.val - m < l.val) :
    HEq (concatLR hkl tr₁ tr₂ i) (tr₂ ⟨i.val - m, h2⟩) := by
  unfold concatLR
  rw [dif_neg h]
  exact cast_heq _ _

/-- The empty transcript at round `0` of a non-empty protocol. -/
private def emptyTranscript {N : ℕ} {pSpec : ProtocolSpec N} (hN : 0 < N) :
    pSpec.Transcript (⟨0, hN⟩ : Fin N).castSucc := fun z => Fin.elim0 z

/-- Gluing at the seam: extending the left transcript by the first `pSpec₂` message. -/
private theorem concatLR_seam (hjlt : m < m + n) (hn : 0 < n)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, hjlt⟩ : Fin (m + n)).castSucc)
    (tr₁ : pSpec₁.FullTranscript) (htr : HEq tr tr₁)
    (msg : (pSpec₁ ++ₚ pSpec₂).«Type» ⟨m, hjlt⟩) (msg₂ : pSpec₂.«Type» ⟨0, hn⟩)
    (hmsg : HEq msg msg₂)
    (hkl : ((⟨m, hjlt⟩ : Fin (m + n)).succ : Fin (m + n + 1)).val
      = m + ((⟨0, hn⟩ : Fin n).succ).val) :
    Transcript.concat msg tr
      = concatLR hkl tr₁ (Transcript.concat msg₂ (emptyTranscript hn)) := by
  funext i
  have hi : i.val < m + 1 := i.isLt
  refine eq_of_heq ?_
  rcases Nat.lt_or_ge i.val m with h | h
  · refine (concat_apply_lt tr msg i.val h i.isLt).trans ?_
    refine HEq.trans ?_ (concatLR_apply_lt hkl tr₁ _ i h).symm
    have hfam := transcript_family_left (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) m
      (le_refl m) (Nat.le_add_right m n)
    exact heq_dapply hfam htr ⟨i.val, h⟩
  · refine (concat_apply_last tr msg i.val (show i.val = m by omega) i.isLt).trans ?_
    refine HEq.trans hmsg ?_
    refine HEq.trans ?_
      (concatLR_apply_ge hkl tr₁ _ i (show ¬ i.val < m by omega)
        (show i.val - m < 0 + 1 by omega)).symm
    exact (concat_apply_last (emptyTranscript hn) msg₂ (i.val - m)
      (show i.val - m = 0 by omega) (show i.val - m < 0 + 1 by omega)).symm

/-- Gluing above the seam: extending by a later `pSpec₂` message. -/
private theorem concatLR_step (j : Fin (m + n)) (l : Fin n) (hjl : j.val = m + l.val)
    (tr₁ : pSpec₁.FullTranscript) (tr₂ : pSpec₂.Transcript l.castSucc)
    (msg : (pSpec₁ ++ₚ pSpec₂).«Type» j) (msg₂ : pSpec₂.«Type» l) (hmsg : HEq msg msg₂)
    (hkl : (j.castSucc : Fin (m + n + 1)).val = m + (l.castSucc).val)
    (hkl' : (j.succ : Fin (m + n + 1)).val = m + (l.succ).val) :
    Transcript.concat msg (concatLR hkl tr₁ tr₂)
      = concatLR hkl' tr₁ (Transcript.concat msg₂ tr₂) := by
  funext i
  have hi : i.val < j.val + 1 := i.isLt
  refine eq_of_heq ?_
  rcases Nat.lt_or_ge i.val m with h | h
  · refine (concat_apply_lt _ msg i.val (show i.val < j.val by omega) i.isLt).trans ?_
    refine (concatLR_apply_lt hkl tr₁ tr₂ ⟨i.val, show i.val < j.val by omega⟩ h).trans ?_
    exact (concatLR_apply_lt hkl' tr₁ _ i h).symm
  · rcases Nat.lt_or_ge i.val j.val with h2 | h2
    · refine (concat_apply_lt _ msg i.val h2 i.isLt).trans ?_
      refine (concatLR_apply_ge hkl tr₁ tr₂ ⟨i.val, show i.val < j.val by omega⟩
        (show ¬ i.val < m by omega) (show i.val - m < l.val by omega)).trans ?_
      refine HEq.trans ?_
        (concatLR_apply_ge hkl' tr₁ _ i (show ¬ i.val < m by omega)
          (show i.val - m < l.val + 1 by omega)).symm
      exact (concat_apply_lt tr₂ msg₂ (i.val - m) (show i.val - m < l.val by omega)
        (show i.val - m < l.val + 1 by omega)).symm
    · refine (concat_apply_last _ msg i.val (show i.val = j.val by omega) i.isLt).trans ?_
      refine HEq.trans hmsg ?_
      refine HEq.trans ?_
        (concatLR_apply_ge hkl' tr₁ _ i (show ¬ i.val < m by omega)
          (show i.val - m < l.val + 1 by omega)).symm
      exact (concat_apply_last tr₂ msg₂ (i.val - m) (show i.val - m = l.val by omega)
        (show i.val - m < l.val + 1 by omega)).symm

/-! ### Right-hand lifts -/

private theorem liftAppendRight_liftM {α : Type} (oa : OracleComp oSpec α) :
    (liftAppendRight pSpec₁ (liftM oa : OracleComp (oSpec + [pSpec₂.Challenge]ₒ) α))
      = (liftM oa : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α) := by
  unfold liftAppendRight
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    simp [ih]
    congr 1

private theorem liftAppendRight_getChallenge (i : ChallengeIdx pSpec₂) :
    liftAppendRight pSpec₁
        ((liftM (pSpec₂.getChallenge i)) :
          OracleComp (oSpec + [pSpec₂.Challenge]ₒ) (pSpec₂.Challenge i))
      = cast (challenge_append_inr (pSpec₁ := pSpec₁) i) <$>
          ((liftM ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr i))) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i))) := by
  unfold liftAppendRight
  rfl

/-! ### `processRound` above the seam -/

private theorem append_processRound_right_pure (l : Fin n) (hl : 0 < l.val)
    (tr₁ : pSpec₁.FullTranscript) (tr₂ : pSpec₂.Transcript l.castSucc)
    (st : (P₁.append P₂).PrvState (Fin.natAdd m l).castSucc) (st₂ : P₂.PrvState l.castSucc)
    (hst : HEq st st₂)
    (hkl : ((Fin.natAdd m l).castSucc : Fin (m + n + 1)).val = m + (l.castSucc).val)
    (hkl' : ((Fin.natAdd m l).succ : Fin (m + n + 1)).val = m + (l.succ).val) :
    HEq ((P₁.append P₂).processRound (Fin.natAdd m l) (pure ⟨concatLR hkl tr₁ tr₂, st⟩))
        ((fun p => ((concatLR hkl' tr₁ p.1 : (pSpec₁ ++ₚ pSpec₂).Transcript (Fin.natAdd m l).succ),
            p.2)) <$>
          liftAppendRight pSpec₁ (P₂.processRound l (pure ⟨tr₂, st₂⟩))) := by
  have hil : (Fin.natAdd m l).val = m + l.val := rfl
  have hlt : (Fin.natAdd m l).val - m < n := show m + l.val - m < n by have := l.isLt; omega
  have hidx : (⟨(Fin.natAdd m l).val - m, hlt⟩ : Fin n) = l :=
    Fin.ext (show m + l.val - m = l.val by omega)
  have hdir : Fin.vappend pSpec₁.dir pSpec₂.dir (Fin.natAdd m l) = pSpec₂.dir l := by
    rw [Fin.vappend_right_of_not_lt _ _ _ (show ¬ m + l.val < m by omega), hidx]
  have hStS : (P₁.append P₂).PrvState (Fin.natAdd m l).succ = P₂.PrvState l.succ :=
    prvState_right ((Fin.natAdd m l).succ) l.succ (show m < m + l.val + 1 by omega)
      (show m + l.val + 1 = m + (l.val + 1) by omega)
  unfold Prover.processRound liftAppendRight
  simp only [pure_bind]
  split <;> rename_i hA <;> split <;> rename_i hB
  · -- V_to_P
    simp only [liftM_bind, liftM_pure, liftAppendRight_liftM, liftAppendRight_getChallenge,
      map_bind, map_pure, bind_map_left]
    have hChal : (pSpec₁ ++ₚ pSpec₂).Challenge
          (⟨Fin.natAdd m l, hA⟩ : ChallengeIdx (pSpec₁ ++ₚ pSpec₂))
        = pSpec₂.Challenge ⟨l, hB⟩ :=
      challenge_append_inr (pSpec₁ := pSpec₁) ⟨l, hB⟩
    have hFun : ((pSpec₁ ++ₚ pSpec₂).Challenge
          (⟨Fin.natAdd m l, hA⟩ : ChallengeIdx (pSpec₁ ++ₚ pSpec₂))
          → (P₁.append P₂).PrvState (Fin.natAdd m l).succ)
        = (pSpec₂.Challenge ⟨l, hB⟩ → P₂.PrvState l.succ) :=
      congrArg₂ (fun X Y => X → Y) hChal hStS
    refine heq_bind rfl (congrArg₂ Prod rfl hStS) HEq.rfl ?_
    refine heq_fun' rfl (congrArg _ (congrArg₂ Prod rfl hStS)) ?_
    intro c c' hc
    obtain rfl := eq_of_heq hc
    refine heq_bind hFun (congrArg₂ Prod rfl hStS) ?_ ?_
    · exact heq_liftM hFun
        (append_receiveChallenge_right' (Fin.natAdd m l) l hil hl hA hB st st₂ hst)
    · refine heq_fun' hFun (congrArg _ (congrArg₂ Prod rfl hStS)) ?_
      intro f f' hf
      refine heq_pure (congrArg₂ Prod rfl hStS) ?_
      refine heq_prod rfl hStS ?_ (heq_app hChal hStS hf (cast_heq hChal c).symm)
      exact heq_of_eq (concatLR_step (Fin.natAdd m l) l (by simp) tr₁ tr₂ c
        (cast hChal c) (cast_heq hChal c).symm hkl hkl')
  · rw [hdir, hB] at hA; exact absurd hA (by simp)
  · rw [hdir, hB] at hA; exact absurd hA (by simp)
  · -- P_to_V
    simp only [liftM_bind, liftM_pure, liftAppendRight_liftM, map_bind, map_pure]
    have hMsgIdx : (pSpec₁ ++ₚ pSpec₂).Message
          (⟨Fin.natAdd m l, hA⟩ : MessageIdx (pSpec₁ ++ₚ pSpec₂))
        = pSpec₂.Message ⟨l, hB⟩ := append_Type_natAdd _
    have hPairIn : ((pSpec₁ ++ₚ pSpec₂).Message
          (⟨Fin.natAdd m l, hA⟩ : MessageIdx (pSpec₁ ++ₚ pSpec₂))
          × (P₁.append P₂).PrvState (Fin.natAdd m l).succ)
        = (pSpec₂.Message ⟨l, hB⟩ × P₂.PrvState l.succ) :=
      congrArg₂ Prod hMsgIdx hStS
    refine heq_bind hPairIn (congrArg₂ Prod rfl hStS) ?_ ?_
    · exact heq_liftM hPairIn
        (append_sendMessage_right' (Fin.natAdd m l) l hil hl hA hB st st₂ hst)
    · refine heq_fun' hPairIn (congrArg _ (congrArg₂ Prod rfl hStS)) ?_
      intro x x' hx
      refine heq_pure (congrArg₂ Prod rfl hStS) ?_
      refine heq_prod rfl hStS ?_ (heq_snd hMsgIdx hStS hx)
      exact heq_of_eq (concatLR_step (Fin.natAdd m l) l (by simp) tr₁ tr₂ x.1 x'.1
        (heq_fst hMsgIdx hStS hx) hkl hkl')

/-! ### `processRound` at the seam -/

private theorem append_processRound_seam_pure (hjlt : m < m + n) (hn : 0 < n)
    (outputFn : P₁.PrvState (Fin.last m) → Stmt₂ × Wit₂)
    (hOutput : P₁.output = fun st => pure (outputFn st))
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, hjlt⟩ : Fin (m + n)).castSucc)
    (tr₁ : pSpec₁.FullTranscript) (htr : HEq tr tr₁)
    (st : (P₁.append P₂).PrvState (⟨m, hjlt⟩ : Fin (m + n)).castSucc)
    (st₁ : P₁.PrvState (Fin.last m)) (hst : HEq st st₁)
    (hkl : ((⟨m, hjlt⟩ : Fin (m + n)).succ : Fin (m + n + 1)).val
      = m + ((⟨0, hn⟩ : Fin n).succ).val) :
    HEq ((P₁.append P₂).processRound ⟨m, hjlt⟩ (pure ⟨tr, st⟩))
        ((fun p => ((concatLR hkl tr₁ p.1 :
              (pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, hjlt⟩ : Fin (m + n)).succ), p.2)) <$>
          liftAppendRight pSpec₁
            (P₂.processRound ⟨0, hn⟩ (pure ⟨emptyTranscript hn, P₂.input (outputFn st₁)⟩))) := by
  have hdir : Fin.vappend pSpec₁.dir pSpec₂.dir ⟨m, hjlt⟩ = pSpec₂.dir ⟨0, hn⟩ := by
    rw [Fin.vappend_right_of_not_lt _ _ _ (show ¬ m < m by omega)]
    congr 1
    exact Fin.ext (show m - m = 0 by omega)
  have hMsg : (pSpec₁ ++ₚ pSpec₂).«Type» (⟨m, hjlt⟩ : Fin (m + n)) = pSpec₂.«Type» ⟨0, hn⟩ :=
    (append_Type_ge (⟨m, hjlt⟩ : Fin (m + n)) (show m - m < n by omega)
      (show m ≤ m by omega)).trans (congrArg pSpec₂.«Type» (Fin.ext (show m - m = 0 by omega)))
  have hStS : (P₁.append P₂).PrvState (⟨m, hjlt⟩ : Fin (m + n)).succ
      = P₂.PrvState (⟨0, hn⟩ : Fin n).succ :=
    prvState_right _ _ (show m < m + 1 by omega) (show m + 1 = m + (0 + 1) by omega)
  have hβ : (((pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, hjlt⟩ : Fin (m + n)).succ)
        × (P₁.append P₂).PrvState (⟨m, hjlt⟩ : Fin (m + n)).succ)
      = (((pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, hjlt⟩ : Fin (m + n)).succ)
        × P₂.PrvState (⟨0, hn⟩ : Fin n).succ) := congrArg₂ Prod rfl hStS
  unfold Prover.processRound liftAppendRight
  simp only [pure_bind]
  split <;> rename_i hA <;> split <;> rename_i hB
  · -- V_to_P
    simp only [liftM_bind, liftM_pure, liftAppendRight_liftM, liftAppendRight_getChallenge,
      map_bind, map_pure, bind_map_left]
    have hChal : (pSpec₁ ++ₚ pSpec₂).Challenge
          (⟨⟨m, hjlt⟩, hA⟩ : ChallengeIdx (pSpec₁ ++ₚ pSpec₂))
        = pSpec₂.Challenge ⟨⟨0, hn⟩, hB⟩ := hMsg
    have hFun : ((pSpec₁ ++ₚ pSpec₂).Challenge
          (⟨⟨m, hjlt⟩, hA⟩ : ChallengeIdx (pSpec₁ ++ₚ pSpec₂))
          → (P₁.append P₂).PrvState (⟨m, hjlt⟩ : Fin (m + n)).succ)
        = (pSpec₂.Challenge ⟨⟨0, hn⟩, hB⟩ → P₂.PrvState (⟨0, hn⟩ : Fin n).succ) :=
      congrArg₂ (fun X Y => X → Y) hChal hStS
    refine heq_bind rfl hβ HEq.rfl ?_
    refine heq_fun' rfl (congrArg _ hβ) ?_
    intro c c' hc
    obtain rfl := eq_of_heq hc
    refine heq_bind hFun hβ ?_ ?_
    · exact heq_liftM hFun
        (append_receiveChallenge_seam ⟨m, hjlt⟩ rfl hn outputFn hOutput hA hB st st₁ hst)
    · refine heq_fun' hFun (congrArg _ hβ) ?_
      intro f f' hf
      refine heq_pure hβ ?_
      refine heq_prod rfl hStS ?_ (heq_app hChal hStS hf (cast_heq hChal c).symm)
      exact heq_of_eq (concatLR_seam hjlt hn tr tr₁ htr c (cast hChal c)
        (cast_heq hChal c).symm hkl)
  · rw [hdir, hB] at hA; exact absurd hA (by simp)
  · rw [hdir, hB] at hA; exact absurd hA (by simp)
  · -- P_to_V
    simp only [liftM_bind, liftM_pure, liftAppendRight_liftM, map_bind, map_pure]
    have hMsgIdx : (pSpec₁ ++ₚ pSpec₂).Message
          (⟨⟨m, hjlt⟩, hA⟩ : MessageIdx (pSpec₁ ++ₚ pSpec₂))
        = pSpec₂.Message ⟨⟨0, hn⟩, hB⟩ := hMsg
    have hα : ((pSpec₁ ++ₚ pSpec₂).Message (⟨⟨m, hjlt⟩, hA⟩ : MessageIdx (pSpec₁ ++ₚ pSpec₂))
          × (P₁.append P₂).PrvState (⟨m, hjlt⟩ : Fin (m + n)).succ)
        = (pSpec₂.Message ⟨⟨0, hn⟩, hB⟩ × P₂.PrvState (⟨0, hn⟩ : Fin n).succ) :=
      congrArg₂ Prod hMsgIdx hStS
    refine heq_bind hα hβ ?_ ?_
    · exact heq_liftM hα
        (append_sendMessage_seam ⟨m, hjlt⟩ rfl hn outputFn hOutput hA hB st st₁ hst)
    · refine heq_fun' hα (congrArg _ hβ) ?_
      intro x x' hx
      refine heq_pure hβ ?_
      refine heq_prod rfl hStS ?_ (heq_snd hMsgIdx hStS hx)
      exact heq_of_eq (concatLR_seam hjlt hn tr tr₁ htr x.1 x'.1
        (heq_fst hMsgIdx hStS hx) hkl)

/-! ### Running past the seam -/

private theorem runToRound_succ_bind {N : ℕ} {pSpec : ProtocolSpec N}
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec) (j : Fin N) (stmt : Stmt₁) (wit : Wit₁) :
    P.runToRound j.succ stmt wit
      = P.runToRound j.castSucc stmt wit >>= fun x => P.processRound j (pure x) := by
  rw [Prover.runToRound_succ, processRound_eq_bind]

private theorem runToRound_castSucc_zero (hl : 0 < n) (s : Stmt₂) (w : Wit₂) :
    P₂.runToRound ((⟨0, hl⟩ : Fin n).castSucc) s w
      = pure ⟨emptyTranscript hl, P₂.input (s, w)⟩ := rfl


/-- The un-glued right-hand run: the left half's result paired with the second prover's
partial run.  Gluing is applied by an outer `map`, which is what makes the induction compose. -/
private def rightRun (outputFn : P₁.PrvState (Fin.last m) → Stmt₂ × Wit₂)
    (stmt : Stmt₁) (wit : Wit₁) (l : Fin (n + 1)) :
    OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      (pSpec₁.FullTranscript × (pSpec₂.Transcript l × P₂.PrvState l)) := do
  let p₁ ← liftAppendLeft pSpec₂ (P₁.runToRound (Fin.last m) stmt wit)
  let p₂ ← liftAppendRight pSpec₁
    (P₂.runToRound l (outputFn p₁.2).1 (outputFn p₁.2).2)
  pure (p₁.1, p₂)

private theorem append_runToRound_right (hn : 0 < n)
    (outputFn : P₁.PrvState (Fin.last m) → Stmt₂ × Wit₂)
    (hOutput : P₁.output = fun st => pure (outputFn st))
    (stmt : Stmt₁) (wit : Wit₁) :
    ∀ (l : ℕ) (_hl : l < n) (k : Fin (m + n + 1)) (l' : Fin (n + 1))
      (hkl : k.val = m + l'.val) (_hl' : l'.val = l + 1),
      HEq ((P₁.append P₂).runToRound k stmt wit)
          ((fun q : pSpec₁.FullTranscript × (pSpec₂.Transcript l' × P₂.PrvState l') =>
              ((concatLR hkl q.1 q.2.1 : (pSpec₁ ++ₚ pSpec₂).Transcript k), q.2.2))
            <$> rightRun (P₂ := P₂) outputFn stmt wit l') := by
  intro l
  induction l with
  | zero =>
    intro hl k l' hkl hl'
    obtain rfl : l' = (⟨0, hl⟩ : Fin n).succ := Fin.ext (by simpa using hl')
    have hjlt : m < m + n := Nat.lt_add_of_pos_right hn
    obtain rfl : k = (⟨m, hjlt⟩ : Fin (m + n)).succ := Fin.ext (by simpa using hkl)
    have hStS : (P₁.append P₂).PrvState (⟨m, hjlt⟩ : Fin (m + n)).succ
        = P₂.PrvState (⟨0, hl⟩ : Fin n).succ :=
      prvState_right _ _ (show m < m + 1 by omega) (show m + 1 = m + (0 + 1) by omega)
    have hβ : (((pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, hjlt⟩ : Fin (m + n)).succ)
          × (P₁.append P₂).PrvState (⟨m, hjlt⟩ : Fin (m + n)).succ)
        = (((pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, hjlt⟩ : Fin (m + n)).succ)
          × P₂.PrvState (⟨0, hl⟩ : Fin n).succ) := congrArg₂ Prod rfl hStS
    unfold rightRun
    simp only [Prover.runToRound_succ, runToRound_castSucc_zero, map_bind, map_pure]
    rw [processRound_eq_bind]
    refine heq_bind (payload_left_eq _ (Fin.last m) (by simp)) hβ
      (append_runToRound_left stmt wit (Fin.last m) _ (by simp)) ?_
    refine heq_fun' (payload_left_eq _ (Fin.last m) (by simp)) (congrArg _ hβ) ?_
    intro x p₁ hx
    refine HEq.trans (append_processRound_seam_pure hjlt hl outputFn hOutput x.1 p₁.1
      (heq_fst (transcript_left_type_eq _ (Fin.last m) (by simp))
        (prvState_left _ (Fin.last m) (by simp)) hx) x.2 p₁.2
      (heq_snd (transcript_left_type_eq _ (Fin.last m) (by simp))
        (prvState_left _ (Fin.last m) (by simp)) hx) hkl) ?_
    refine heq_of_eq ?_
    first
      | rfl
      | simp only [map_bind, map_pure]
      | (rw [map_eq_bind_pure_comp]; rfl)
  | succ l ih =>
    intro hl k l' hkl hl'
    obtain rfl : l' = (⟨l + 1, hl⟩ : Fin n).succ := Fin.ext (by simpa using hl')
    have hlt' : l < n := by omega
    obtain rfl : k = (Fin.natAdd m (⟨l + 1, hl⟩ : Fin n)).succ :=
      Fin.ext (show k.val = m + (l + 1) + 1 by omega)
    have hkl' : ((Fin.natAdd m (⟨l + 1, hl⟩ : Fin n)).castSucc : Fin (m + n + 1)).val
        = m + ((⟨l + 1, hl⟩ : Fin n).castSucc : Fin (n + 1)).val := rfl
    have hStS : (P₁.append P₂).PrvState (Fin.natAdd m (⟨l + 1, hl⟩ : Fin n)).castSucc
        = P₂.PrvState ((⟨l + 1, hl⟩ : Fin n).castSucc) :=
      prvState_right _ _ (show m < m + (l + 1) by omega)
        (show m + (l + 1) = m + (l + 1) by omega)
    have hα : (((pSpec₁ ++ₚ pSpec₂).Transcript
            (Fin.natAdd m (⟨l + 1, hl⟩ : Fin n)).castSucc)
          × (P₁.append P₂).PrvState (Fin.natAdd m (⟨l + 1, hl⟩ : Fin n)).castSucc)
        = (((pSpec₁ ++ₚ pSpec₂).Transcript (Fin.natAdd m (⟨l + 1, hl⟩ : Fin n)).castSucc)
          × P₂.PrvState ((⟨l + 1, hl⟩ : Fin n).castSucc)) := congrArg₂ Prod rfl hStS
    have hf : HEq (fun x => (P₁.append P₂).processRound (Fin.natAdd m (⟨l + 1, hl⟩ : Fin n))
          (pure x))
        (fun x' : ((pSpec₁ ++ₚ pSpec₂).Transcript
              (Fin.natAdd m (⟨l + 1, hl⟩ : Fin n)).castSucc
            × P₂.PrvState ((⟨l + 1, hl⟩ : Fin n).castSucc)) =>
          (P₁.append P₂).processRound (Fin.natAdd m (⟨l + 1, hl⟩ : Fin n))
            (pure (x'.1, cast hStS.symm x'.2))) := by
      refine heq_fun' hα rfl ?_
      intro x x' hx
      have h1 : x.1 = x'.1 := eq_of_heq (heq_fst rfl hStS hx)
      have h2 : x.2 = cast hStS.symm x'.2 :=
        eq_of_heq ((heq_snd rfl hStS hx).trans (cast_heq hStS.symm x'.2).symm)
      refine heq_of_eq (congrArg _ (congrArg _ ?_))
      rw [← h1, ← h2]
    rw [Prover.runToRound_succ, processRound_eq_bind]
    refine HEq.trans
      (heq_bind hα rfl (ih hlt' _ ((⟨l + 1, hl⟩ : Fin n).castSucc) hkl' (by simp)) hf) ?_
    have hStS' : (P₁.append P₂).PrvState (Fin.natAdd m (⟨l + 1, hl⟩ : Fin n)).succ
        = P₂.PrvState ((⟨l + 1, hl⟩ : Fin n).succ) :=
      prvState_right _ _ (show m < m + (l + 1) + 1 by omega)
        (show m + (l + 1) + 1 = m + (l + 1 + 1) by omega)
    have hβ' : (((pSpec₁ ++ₚ pSpec₂).Transcript
            (Fin.natAdd m (⟨l + 1, hl⟩ : Fin n)).succ)
          × (P₁.append P₂).PrvState (Fin.natAdd m (⟨l + 1, hl⟩ : Fin n)).succ)
        = (((pSpec₁ ++ₚ pSpec₂).Transcript (Fin.natAdd m (⟨l + 1, hl⟩ : Fin n)).succ)
          × P₂.PrvState ((⟨l + 1, hl⟩ : Fin n).succ)) := congrArg₂ Prod rfl hStS'
    have hstep : HEq
        (fun q : pSpec₁.FullTranscript × (pSpec₂.Transcript ((⟨l + 1, hl⟩ : Fin n).castSucc)
            × P₂.PrvState ((⟨l + 1, hl⟩ : Fin n).castSucc)) =>
          (P₁.append P₂).processRound (Fin.natAdd m (⟨l + 1, hl⟩ : Fin n))
            (pure (concatLR hkl' q.1 q.2.1, cast hStS.symm q.2.2)))
        (fun q : pSpec₁.FullTranscript × (pSpec₂.Transcript ((⟨l + 1, hl⟩ : Fin n).castSucc)
            × P₂.PrvState ((⟨l + 1, hl⟩ : Fin n).castSucc)) =>
          ((fun p => ((concatLR hkl q.1 p.1 : (pSpec₁ ++ₚ pSpec₂).Transcript
                (Fin.natAdd m (⟨l + 1, hl⟩ : Fin n)).succ), p.2)) <$>
            liftAppendRight pSpec₁
              (P₂.processRound (⟨l + 1, hl⟩ : Fin n) (pure q.2)))) := by
      refine heq_fun' rfl (congrArg _ hβ') ?_
      intro q q' hq
      obtain rfl := eq_of_heq hq
      exact append_processRound_right_pure (⟨l + 1, hl⟩ : Fin n) (Nat.succ_pos l) q.1 q.2.1
        (cast hStS.symm q.2.2) q.2.2 (cast_heq _ _) rfl rfl
    simp only [bind_map_left]
    refine HEq.trans (heq_bind rfl hβ' HEq.rfl hstep) ?_
    refine heq_of_eq ?_
    simp only [rightRun, runToRound_succ_bind, liftM_bind, bind_assoc,
      map_eq_bind_pure_comp, pure_bind]
    rfl

/-! ### Output, and the final transcript identity -/

private theorem append_output_pos (hn : n ≠ 0)
    (state : (P₁.append P₂).PrvState (Fin.last (m + n)))
    (state₂ : P₂.PrvState (Fin.last n)) (hst : HEq state state₂) :
    (P₁.append P₂).output state = P₂.output state₂ := by
  conv_lhs => unfold Prover.append
  dsimp only
  rw [dif_neg hn]
  exact congrArg P₂.output
    (eq_of_heq ((heq_dcast _ _).trans ((heq_eqMp' _ _).trans hst)))

private theorem concatLR_last (hkl : (Fin.last (m + n)).val = m + (Fin.last n).val)
    (tr₁ : pSpec₁.FullTranscript) (tr₂ : pSpec₂.FullTranscript) :
    concatLR hkl tr₁ tr₂ = tr₁ ++ₜ tr₂ := by
  funext i
  refine eq_of_heq ?_
  rcases Nat.lt_or_ge i.val m with h | h
  · refine (concatLR_apply_lt hkl tr₁ tr₂ i h).trans ?_
    exact (Fin.happend_heq_left tr₁ tr₂ ⟨i.val, by have := i.isLt; omega⟩ h).symm
  · refine (concatLR_apply_ge hkl tr₁ tr₂ i (show ¬ i.val < m by omega)
      (show i.val - m < n by have := i.isLt; omega)).trans ?_
    exact (Fin.happend_heq_right tr₁ tr₂ ⟨i.val, by have := i.isLt; omega⟩
      (show ¬ i.val < m by omega)).symm

/-! ### Assembly -/

private theorem append_run_pos (hn : 0 < n)
    (outputFn : P₁.PrvState (Fin.last m) → Stmt₂ × Wit₂)
    (hOutput : P₁.output = fun st => pure (outputFn st))
    (stmt : Stmt₁) (wit : Wit₁) :
    (P₁.append P₂).run stmt wit
      = (rightRun (P₂ := P₂) outputFn stmt wit (Fin.last n) >>= fun q =>
          ((liftM (P₂.output q.2.2) :
              OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Stmt₃ × Wit₃))
            >>= fun ctx =>
            pure ((q.1 ++ₜ q.2.1 : (pSpec₁ ++ₚ pSpec₂).FullTranscript), ctx))) := by
  have hkl : (Fin.last (m + n)).val = m + (Fin.last n).val := by simp
  have hStS : (P₁.append P₂).PrvState (Fin.last (m + n)) = P₂.PrvState (Fin.last n) :=
    prvState_right _ _ (by simp; omega) (by simp)
  have hα : (((pSpec₁ ++ₚ pSpec₂).Transcript (Fin.last (m + n)))
        × (P₁.append P₂).PrvState (Fin.last (m + n)))
      = (((pSpec₁ ++ₚ pSpec₂).Transcript (Fin.last (m + n))) × P₂.PrvState (Fin.last n)) :=
    congrArg₂ Prod rfl hStS
  have key := append_runToRound_right (P₁ := P₁) (P₂ := P₂) hn outputFn hOutput stmt wit
    (n - 1) (by omega)
    (Fin.last (m + n)) (Fin.last n) hkl (by simp; omega)
  have hf : HEq
      (fun p : ((pSpec₁ ++ₚ pSpec₂).Transcript (Fin.last (m + n))
          × (P₁.append P₂).PrvState (Fin.last (m + n))) =>
        ((liftM ((P₁.append P₂).output p.2) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Stmt₃ × Wit₃))
          >>= fun ctx => pure ((p.1 : (pSpec₁ ++ₚ pSpec₂).FullTranscript), ctx)))
      (fun p : ((pSpec₁ ++ₚ pSpec₂).Transcript (Fin.last (m + n))
          × P₂.PrvState (Fin.last n)) =>
        ((liftM (P₂.output p.2) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Stmt₃ × Wit₃))
          >>= fun ctx => pure ((p.1 : (pSpec₁ ++ₚ pSpec₂).FullTranscript), ctx))) := by
    refine heq_fun' hα rfl ?_
    intro p p' hp
    refine heq_of_eq ?_
    have h1 : p.1 = p'.1 := eq_of_heq (heq_fst rfl hStS hp)
    have h2 : (P₁.append P₂).output p.2 = P₂.output p'.2 :=
      append_output_pos (by omega) p.2 p'.2 (heq_snd rfl hStS hp)
    rw [h1, h2]
  refine eq_of_heq ?_
  unfold Prover.run
  refine HEq.trans (heq_bind hα rfl key hf) ?_
  refine HEq.trans (heq_of_eq (bind_map_left _ _ _)) (heq_of_eq ?_)
  congr 1
  funext q
  refine congrArg (fun t => liftM (P₂.output q.2.2) >>= fun ctx => pure (t, ctx)) ?_
  exact concatLR_last hkl q.1 q.2.1

private theorem runToRound_last_zero {pSpec : ProtocolSpec 0}
    (P : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec) (s : Stmt₂) (w : Wit₂) :
    P.runToRound (Fin.last 0) s w = pure ⟨fun z => Fin.elim0 z, P.input (s, w)⟩ := rfl

private theorem append_output_zero (hn : n = 0)
    (state : (P₁.append P₂).PrvState (Fin.last (m + n)))
    (state₁ : P₁.PrvState (Fin.last m)) (hst : HEq state state₁) :
    (P₁.append P₂).output state
      = (do let ctx ← P₁.output state₁
            P₂.output (dcast (by simp [hn]) (P₂.input ctx))) := by
  conv_lhs => unfold Prover.append
  dsimp only
  rw [dif_pos hn]
  congr 1
  exact congrArg P₁.output (eq_of_heq ((heq_eqMp' _ _).trans hst))

private theorem heq_append_nil (hn : n = 0) (tr₁ : pSpec₁.FullTranscript)
    (tr₂ : pSpec₂.FullTranscript) :
    HEq ((tr₁ ++ₜ tr₂ : (pSpec₁ ++ₚ pSpec₂).FullTranscript)) tr₁ := by
  subst hn
  refine heq_pi (transcript_family_left (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) m
    (le_refl m) (by omega)) ?_
  intro i
  exact Fin.happend_heq_left tr₁ tr₂ i (by have := i.isLt; omega)

end AppendRunHelpers

namespace Prover

variable {P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
    {P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}
    {stmt : Stmt₁} {wit : Wit₁}

-- #print Prover.processRound

-- theorem append_processRound (roundIdx : Fin (m + n)) (stmt : Stmt₁) (wit : Wit₁)
--     (transcript : pSpec₁.FullTranscript) (proveQueryLog : Set (Stmt₁ × Wit₁))
--     (verifyQueryLog : Set (Stmt₂ × Wit₂)) :
--       (P₁.append P₂).processRound roundIdx stmt wit transcript proveQueryLog verifyQueryLog =
--         (P₁.processRound roundIdx stmt wit transcript proveQueryLog verifyQueryLog) ∧
--         (P₂.processRound roundIdx stmt wit transcript proveQueryLog verifyQueryLog) := sorry

-- theorem append_runToRound

-- The challenge-oracle inclusions that `append_run`'s statement lifts along are provided
-- (proved) by `ProtocolSpec.subSpec_challenge_append_left` / `..._right` in
-- `ProtocolSpec/SeqCompose.lean`, with their `LawfulSubSpec` instances and the `@[simp]` lemmas
-- `liftM_getChallenge_append_inl` / `_inr` that compute the lifted challenge query.
--
-- Scope of what lawfulness buys: `support_liftComp` / `mem_support_liftComp_iff` apply directly.
-- `evalDist_liftComp` / `probEvent_liftComp` do NOT apply at this shape — they additionally
-- require `IsUniformSpec` on both specs, and `oSpec` here is arbitrary. The security definitions
-- below measure after `simulateQ pImpl`, so relating the two sides at the distribution level will
-- need `simulateQ_liftM_eq_of_query` plus the fact that `challengeQueryImpl` for the appended
-- protocol, precomposed with the lift, agrees with `challengeQueryImpl` for the component — a
-- `SampleableType`-compatibility fact across the transport that is not yet proved.

/--
States that running an appended prover `P₁.append P₂` with an initial statement `stmt₁` and
witness `wit₁` behaves as expected: it first runs `P₁` to obtain an intermediate statement
`stmt₂`, witness `wit₂`, and transcript `transcript₁`. Then, it runs `P₂` on `stmt₂` and `wit₂`
to produce the final statement `stmt₃`, witness `wit₃`, and transcript `transcript₂`.
The overall output is `stmt₃`, `wit₃`, and the combined transcript `transcript₁ ++ₜ transcript₂`.

**Why the extra hypothesis `[P₁.OutputIsPure]`.** Without it this statement is *false*, so it has
been weakened rather than dropped. The reason is a difference in *when* the first prover's output
step happens on the two sides of the equation:

* `Prover.processRound` always draws a challenge round's challenge from the challenge oracle
  *before* handing it to `receiveChallenge`;
* in `P₁.append P₂`, the seam round (the first round of `pSpec₂`) is precisely where `P₁.output`
  is invoked, from inside that `receiveChallenge`.

So when `pSpec₂` opens with a verifier-to-prover round, the left-hand side draws `pSpec₂`'s first
challenge and only *then* runs `P₁.output`, whereas the right-hand side finishes `P₁.run` —
output included — before `P₂.run` draws anything. If `P₁.output` makes oracle queries of its own,
the two sides issue their queries in a different order, and the two computations genuinely differ.

`Prover.OutputIsPure` says exactly that `P₁.output` makes no oracle queries: it is some plain
function of the prover's final state, wrapped in `pure`. For such an output step the ordering is
immaterial and the identity holds. This covers every prover in the library, whose output step is a
pure read-off of the accumulated state; it excludes only provers that query oracles while
producing their output.
-/
theorem append_run [hPure : P₁.OutputIsPure] (stmt : Stmt₁) (wit : Wit₁) :
    (P₁.append P₂).run stmt wit = (do
      let ⟨transcript₁, stmt₂, wit₂⟩ ← liftAppendLeft pSpec₂ (P₁.run stmt wit)
      let ⟨transcript₂, stmt₃, wit₃⟩ ← liftAppendRight pSpec₁ (P₂.run stmt₂ wit₂)
      return ⟨transcript₁ ++ₜ transcript₂, stmt₃, wit₃⟩) := by
  obtain ⟨outputFn, hOutputPt⟩ := hPure.output_is_pure
  have hOutput : P₁.output = fun st => pure (outputFn st) := funext hOutputPt
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hStS : (P₁.append P₂).PrvState (Fin.last (m + 0)) = P₁.PrvState (Fin.last m) :=
      prvState_left _ _ (by simp)
    have hTr : (pSpec₁ ++ₚ pSpec₂).Transcript (Fin.last (m + 0))
        = pSpec₁.Transcript (Fin.last m) := transcript_left_type_eq _ _ (by simp)
    have hα : (((pSpec₁ ++ₚ pSpec₂).Transcript (Fin.last (m + 0)))
          × (P₁.append P₂).PrvState (Fin.last (m + 0)))
        = (pSpec₁.Transcript (Fin.last m) × P₁.PrvState (Fin.last m)) :=
      congrArg₂ Prod hTr hStS
    have key := append_runToRound_left (P₁ := P₁) (P₂ := P₂) stmt wit (Fin.last m)
      (Fin.last (m + 0)) (by simp)
    have hf : HEq
        (fun p : ((pSpec₁ ++ₚ pSpec₂).Transcript (Fin.last (m + 0))
            × (P₁.append P₂).PrvState (Fin.last (m + 0))) =>
          ((liftM ((P₁.append P₂).output p.2) :
              OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Stmt₃ × Wit₃))
            >>= fun ctx => pure ((p.1 : (pSpec₁ ++ₚ pSpec₂).FullTranscript), ctx)))
        (fun p : (pSpec₁.Transcript (Fin.last m) × P₁.PrvState (Fin.last m)) =>
          ((liftM (P₁.output p.2 >>= fun ctx =>
                P₂.output (dcast (by simp) (P₂.input ctx))) :
              OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Stmt₃ × Wit₃))
            >>= fun ctx => pure ((cast hTr.symm p.1 : (pSpec₁ ++ₚ pSpec₂).FullTranscript),
              ctx))) := by
      refine heq_fun' hα rfl ?_
      intro p p' hp
      refine heq_of_eq ?_
      rw [append_output_zero rfl p.2 p'.2 (heq_snd hTr hStS hp),
        eq_of_heq ((heq_fst hTr hStS hp).trans (cast_heq hTr.symm p'.1).symm)]
      rfl
    refine eq_of_heq ?_
    unfold Prover.run
    refine HEq.trans (heq_bind hα rfl key hf) ?_
    refine heq_of_eq ?_
    simp only [hOutput, liftM_bind, liftM_pure, liftAppendRight_liftM, bind_assoc,
      pure_bind, runToRound_last_zero]
    refine bind_congr (fun p => ?_)
    have hd : (dcast (by simp) (P₂.input (outputFn p.2)) : P₂.PrvState (Fin.last 0))
        = P₂.input (outputFn p.2) := eq_of_heq (heq_dcast _ _)
    have hc : (cast hTr.symm p.1 : (pSpec₁ ++ₚ pSpec₂).FullTranscript)
        = p.1 ++ₜ (fun z => Fin.elim0 z) :=
      eq_of_heq ((cast_heq hTr.symm p.1).trans
        (heq_append_nil rfl p.1 (fun z => Fin.elim0 z)).symm)
    rw [hd, hc]
    rfl
  · rw [append_run_pos hn outputFn hOutput stmt wit]
    unfold rightRun Prover.run
    simp only [hOutput, liftM_bind, liftM_pure, liftAppendRight_liftM, bind_assoc,
      pure_bind]

/-- Purity of the output step is preserved by binary sequential composition of provers.

The appended prover's `output` field (see `Prover.append`) splits on whether the second protocol is
empty: when `pSpec₂` has rounds it is `P₂.output` on the transported final state, and when `pSpec₂`
is empty the seam collapses into the output step, making it `P₁.output`, then `P₂.input`, then
`P₂.output`. Both branches are pure as soon as `P₁` and `P₂` have pure output.

This is the prover-side analogue of `Verifier.IsPure.append`, and it is what lets a chain of binary
appends discharge the `Prover.OutputIsPure` hypothesis of `Prover.append_run` from per-factor
purity. `Prover.instOutputIsPureAppend` below is the instance form, so that nested appends
propagate automatically. -/
theorem OutputIsPure.append (P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (h₁ : P₁.OutputIsPure) (h₂ : P₂.OutputIsPure) :
    (P₁.append P₂).OutputIsPure := by
  obtain ⟨f₁, hf₁⟩ := h₁.output_is_pure
  obtain ⟨f₂, hf₂⟩ := h₂.output_is_pure
  by_cases hn : n = 0
  · subst hn
    refine ⟨fun st =>
      f₂ (dcast (by simp) (P₂.input (f₁ (cast (prvState_left _ _ (by simp)) st)))), fun st => ?_⟩
    rw [append_output_zero rfl st _ (cast_heq _ st).symm, hf₁, pure_bind, hf₂]
  · refine ⟨fun st => f₂ (cast (prvState_right _ _ (by simp; omega) (by simp)) st), fun st => ?_⟩
    rw [append_output_pos hn st _ (cast_heq _ st).symm, hf₂]

/-- Instance form of `Prover.OutputIsPure.append`, so that nested appends discharge the
`Prover.append_run` hypothesis automatically. -/
instance instOutputIsPureAppend [h₁ : P₁.OutputIsPure] [h₂ : P₂.OutputIsPure] :
    (P₁.append P₂).OutputIsPure := OutputIsPure.append P₁ P₂ h₁ h₂

-- TODO: Need to define a function that "extracts" a second prover from the combined prover

end Prover

namespace Verifier

variable {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁} {V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂}
  {stmt : Stmt₁}

/-- Running the sequential composition of two verifiers on a transcript of the combined protocol
  is equivalent to running the first verifier on the first part of the transcript, and the second
  verifier on the second part of the transcript, and returning the final statement. -/
theorem append_run (tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript) :
    (V₁.append V₂).run stmt tr =
        (do
          let stmt₂ ← V₁.run stmt tr.fst
          let stmt₃ ← V₂.run stmt₂ tr.snd
          return stmt₃) := rfl

end Verifier

namespace Reduction

variable {R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
    {R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}
    {stmt : Stmt₁} {wit : Wit₁}

/- Unfortunately this is not true due to sequencing: `(R₁.append R₂).run` runs the two provers
first, then the two verifiers, whereas `R₁.run` and then `R₂.run` runs the first prover and
verifier, then the second prover and verifier.

We need justification to be able to swap the first verifier with the second prover, which would be
true if we interpret / maps this oracle computation (a priori a term of the free monad) into a
commutative monad (such as `Id`, i.e. all oracle queries are answered deterministically, `PMF`, i.e.
all oracle queries are answered probabilistically, `Option`, `ReaderT ρ`, `Set`, `WriterT` into a
commutative monoid, etc.). -/

-- TODO: prove this after VCVio refactor
-- theorem append_run_interp {m : Type → Type} [Monad m] [m.IsCommutative]
--     {interp : OracleImpl oSpec m} : ((R₁.append R₂).run stmt wit).runM interp =
--         (do
--           let ⟨ctx₁, stmt₂, transcript₁⟩ ← liftM (R₁.run stmt wit)
--           let ⟨ctx₂, stmt₃, transcript₂⟩ ← liftM (R₂.run stmt₂ ctx₁.2)
--           return ⟨ctx₂, stmt₃, transcript₁ ++ₜ transcript₂⟩).runM interp := by
--   unfold run append
--   simp [Prover.append_run, Verifier.append_run]
--   sorry

end Reduction

end Execution
