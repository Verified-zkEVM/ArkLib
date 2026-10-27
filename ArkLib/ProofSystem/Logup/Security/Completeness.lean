/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Logup.Prover.Reference
public import ArkLib.ProofSystem.Logup.Interaction.Execution
public import ArkLib.ProofSystem.Logup.Security.InitialSoundness
public import ArkLib.ProofSystem.Sumcheck.Interaction.ComputableCompleteness

-- The concrete prefix specialization unfolds PolyFun's `Focal.splitPrefix`.
import all PolyFun.Interaction.TwoParty.Compose

/-!
# Completeness of the actual weighted LogUp endpoint

A formal prefix substitution identifies folded private-state messages with the existing original
polynomial native honest prover. These proof-only homomorphisms are private; runtime still uses
only tables and coefficient arrays. The exact native interpretation and source realization reuse
existing Sumcheck completeness, including its actual terminal authentication and executable domain.

The message implementation has an explicit formal head-projection contract. The selected
`Prover/Default.lean` construction specializes it to the measured builder; correctness does not
imply an arithmetic cost transfer. Arithmetic and storage bounds live in `Prover/Resources/`.

Balanced mapped fibers give zero helper total for every alpha, including poles. Off-pole alpha
also gives zero local residuals, so every supported full execution accepts. The named uniform
endpoint can fail only on the proof-only support of actual mapped values. No verifier scans this
support or retries. Public abort returns false and retains probability mass.
-/

@[expose] public section

open MvPolynomial Interaction.Oracle OracleComp OracleSpec
namespace Logup.Prover.Honest

variable {R : Type} [CommRing R]

private noncomputable def roundMap {n : Nat} (i : Fin (n + 1)) (v : Fin n → R) :
    MvPolynomial (Fin (n + 1)) R →+* Polynomial R :=
  (Polynomial.mapRingHom (MvPolynomial.eval v)).comp
    (MvPolynomial.finSuccEquivNth R i).toRingHom

private theorem roundMap_eq {n : Nat} (i : Fin (n + 1)) (v : Fin n → R) :
    roundMap i v = eval₂Hom Polynomial.C
      (Fin.insertNth (α := fun _ => Polynomial R) i
        (Polynomial.X : Polynomial R) (Polynomial.C ∘ v)) := by
  ext j : 2
  · simp [roundMap, MvPolynomial.finSuccEquivNth_apply]
  · refine Fin.succAboveCases i ?_ ?_ j
    · simp [roundMap]
    · intro k
      simp [roundMap, MvPolynomial.finSuccEquivNth_apply]

private noncomputable def prefixMap {start count : Nat} (cs : Fin start → R) :
    MvPolynomial (Fin (start + count)) R →+* MvPolynomial (Fin count) R :=
  eval₂Hom C (Fin.append (C ∘ cs) X)

private theorem prefix_roundMap {start r : Nat} (cs : Fin start → R) (suffix : Fin r → R) :
    roundMap (⟨start, by omega⟩ : Fin (start + r + 1)) (Fin.append cs suffix) =
      (roundMap (0 : Fin (r + 1)) suffix).comp (prefixMap cs) := by
  rw [roundMap_eq, roundMap_eq]
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [prefixMap]
  · intro j
    simp only [RingHom.comp_apply, prefixMap, eval₂Hom_X']
    change Fin.insertNth (α := fun _ => Polynomial R)
        (⟨start, by omega⟩ : Fin (start + r + 1)) (Polynomial.X : Polynomial R)
        (Polynomial.C ∘ Fin.append cs suffix) j =
      eval₂Hom Polynomial.C (Fin.insertNth (α := fun _ => Polynomial R)
        (0 : Fin (r + 1)) (Polynomial.X : Polynomial R)
        (Polynomial.C ∘ suffix))
        (Fin.append (C ∘ cs) X j)
    refine Fin.addCases (m := start) (n := r + 1) (fun a => ?_) (fun b => ?_) j
    · have h : (a.castAdd (r + 1) : Fin (start + (r + 1))) < ⟨start, by omega⟩ := by
        exact a.isLt
      rw [Fin.insertNth_apply_below h]
      simp only [eq_rec_constant]
      have hc : (a.castAdd (r + 1)).castPred (by
        apply Fin.ne_of_lt
        change a.val < start + r
        omega) = a.castAdd r := Fin.ext rfl
      rw [hc]
      simp
    · refine Fin.cases ?_ (fun b => ?_) b
      · have hi : (Fin.natAdd start (0 : Fin (r + 1))) =
          (⟨start, by omega⟩ : Fin (start + r + 1)) := Fin.ext (by simp)
        conv_lhs => rw [hi, Fin.insertNth_apply_same]
        simp
      · have h : (⟨start, by omega⟩ : Fin (start + r + 1)) <
            Fin.natAdd start b.succ := by change start < start + (b.val + 1); omega
        rw [Fin.insertNth_apply_above h]
        simp only [eq_rec_constant]
        have hc : (Fin.natAdd start b.succ).pred (by
          apply Fin.ne_of_gt
          change 0 < start + (b.val + 1)
          omega) =
            Fin.natAdd start b := Fin.ext (by simp)
        rw [hc]
        simp

private noncomputable def headMap {count : Nat} (x : R) :
    MvPolynomial (Fin (count + 1)) R →+* MvPolynomial (Fin count) R :=
  (Polynomial.evalRingHom (C x)).comp (MvPolynomial.finSuccEquiv R count).toRingHom

private theorem headMap_eq {count : Nat} (x : R) :
    headMap (count := count) x = eval₂Hom C (Fin.cons (C x) X) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [headMap, MvPolynomial.finSuccEquiv_apply]
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp [headMap, MvPolynomial.finSuccEquiv_X_zero,
      MvPolynomial.finSuccEquiv_X_succ]

private theorem prefixMap_snoc {start count : Nat} (cs : Fin start → R) (x : R) :
    prefixMap (count := count) (Fin.snoc cs x) =
      (headMap x).comp ((prefixMap (count := count + 1) cs).comp
        ((rename (Fin.cast (Nat.succ_add_eq_add_succ start count))).toRingHom)) := by
  rw [headMap_eq]
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [prefixMap]
  · intro j
    simp only [prefixMap, eval₂Hom_X', RingHom.comp_apply]
    have hs : (C : R →+* MvPolynomial (Fin count) R) ∘ Fin.snoc cs x = Fin.snoc (C ∘ cs) (C x) := by
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i <;> simp
    rw [hs, Fin.append_left_snoc]
    simp only [Function.comp_apply]
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, rename_X, eval₂Hom_X']
    change Fin.append (C ∘ cs) (Fin.cons (C x) X)
        (Fin.cast (Nat.succ_add_eq_add_succ start count) j) =
      eval₂Hom C (Fin.cons (C x) X) (Fin.append (C ∘ cs) X
        (Fin.cast (Nat.succ_add_eq_add_succ start count) j))
    generalize hk : Fin.cast (Nat.succ_add_eq_add_succ start count) j = k
    refine Fin.addCases (m := start) (n := count + 1) (fun a => ?_) (fun b => ?_) k
    · simp
    · refine Fin.cases ?_ (fun b => ?_) b <;> simp


private noncomputable def fixedPrefixMap {n start count : Nat}
    (finish : start + count = n) (cs : Fin start → R) :
    MvPolynomial (Fin n) R →+* MvPolynomial (Fin count) R :=
  (prefixMap cs).comp (rename (Fin.cast finish.symm)).toRingHom

private theorem fixedPrefixMap_zero (n : Nat) :
    fixedPrefixMap (show 0 + n = n by omega) (Fin.elim0 : Fin 0 → R) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [fixedPrefixMap, prefixMap]
  · intro j
    simp only [fixedPrefixMap, prefixMap, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, rename_X, eval₂Hom_X', RingHom.id_apply]
    change Fin.append (Fin.elim0 : Fin 0 → MvPolynomial (Fin n) R) X
      (Fin.cast (show n = 0 + n by omega) j) = X j
    rw [Fin.elim0_append]
    exact congrArg X (Fin.ext rfl)

private theorem fixedPrefixMap_snoc {n start count : Nat} (finish : start + (count + 1) = n)
    (cs : Fin start → R) (x : R) :
    fixedPrefixMap (show (start + 1) + count = n by omega) (Fin.snoc cs x) =
      (headMap x).comp (fixedPrefixMap finish cs) := by
  have hcast :
      (rename (R := R) (Fin.cast (Nat.succ_add_eq_add_succ start count))).toRingHom.comp
        (rename (Fin.cast (show (start + 1) + count = n by omega).symm)).toRingHom =
      (rename (Fin.cast finish.symm)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro j
      simp
  simp only [fixedPrefixMap, prefixMap_snoc, RingHom.comp_assoc]
  rw [hcast]


private theorem projectedRoundPolynomial_prefix {start r deg m : Nat} (D : Fin m ↪ R)
    (cs : Fin start → R) (p : R⦃≤ deg⦄[X Fin (start + r + 1)])
    (q : R⦃≤ deg⦄[X Fin (r + 1)]) (hq : q.val = prefixMap cs p.val) :
    Sumcheck.Spec.SingleRound.projectedRoundPolynomial R (start + r + 1) deg D
      ⟨start, by omega⟩ cs p =
    Sumcheck.Spec.SingleRound.projectedRoundPolynomial R (r + 1) deg D
      (⟨0, by omega⟩ : Fin (r + 1)) Fin.elim0 q := by
  classical
  apply Subtype.ext
  simp only [Sumcheck.Spec.SingleRound.projectedRoundPolynomial]
  change (∑ x ∈ (Finset.univ.map D) ^ᶠ (start + r - start),
      roundMap (⟨start, by omega⟩ : Fin (start + r + 1))
        (Sumcheck.Spec.SingleRound.roundSuffix R (start + r) ⟨start, by omega⟩ cs x) p.val) =
    ∑ x ∈ (Finset.univ.map D) ^ᶠ r,
      roundMap (0 : Fin (r + 1))
        (Sumcheck.Spec.SingleRound.roundSuffix R r (⟨0, by omega⟩ : Fin (r + 1)) Fin.elim0 x) q.val
  have hdim : start + r - start = r := Nat.add_sub_cancel_left start r
  let e : (Fin (start + r - start) → R) ≃ (Fin r → R) :=
    { toFun := fun x => x ∘ Fin.cast hdim.symm
      invFun := fun x => x ∘ Fin.cast hdim
      left_inv := fun x => funext fun j => congrArg x (Fin.ext rfl)
      right_inv := fun x => funext fun j => congrArg x (Fin.ext rfl) }
  refine Finset.sum_equiv e ?_ ?_
  · intro x
    simp only [Fintype.mem_piFinset]
    constructor
    · intro h j
      exact h (Fin.cast hdim.symm j)
    · intro h j
      simpa [e, Function.comp_def] using h (Fin.cast hdim j)
  · intro x hx
    have hs : Sumcheck.Spec.SingleRound.roundSuffix R (start + r)
        (⟨start, by omega⟩ : Fin (start + r + 1)) cs x = Fin.append cs (e x) := by
      change (Fin.append cs x ∘ Fin.cast _) = Fin.append cs (e x)
      funext j
      refine Fin.addCases (m := start) (n := r) (fun a => ?_) (fun b => ?_) j
      · change Fin.append cs x (Fin.cast _ (a.castAdd r)) = _
        have hc : Fin.cast (show start + r = start + (start + r - start) by omega) (a.castAdd r) =
            a.castAdd (start + r - start) := Fin.ext rfl
        rw [hc]
        simp
      · change Fin.append cs x (Fin.cast _ (Fin.natAdd start b)) = _
        have hc : Fin.cast (show start + r = start + (start + r - start) by omega)
            (Fin.natAdd start b) = Fin.natAdd start (Fin.cast hdim.symm b) := Fin.ext rfl
        rw [hc]
        simp [e, Function.comp_def]
    have hzero : Sumcheck.Spec.SingleRound.roundSuffix R r
        (⟨0, by omega⟩ : Fin (r + 1)) Fin.elim0 (e x) = e x := by
      change (Fin.append Fin.elim0 (e x) ∘ Fin.cast _) = e x
      rw [Fin.elim0_append]
      funext i
      exact congrArg (e x) (Fin.ext rfl)
    rw [hs, hzero, hq]
    exact congrArg (fun f => f p.val) (prefix_roundMap cs (e x))


private theorem projectedRoundPolynomial_fixedPrefix {n start count deg m : Nat}
    (D : Fin m ↪ R) (finish : start + (count + 1) = n) (cs : Fin start → R)
    (p : R⦃≤ deg⦄[X Fin n]) (q : R⦃≤ deg⦄[X Fin (count + 1)])
    (hq : q.val = fixedPrefixMap finish cs p.val) :
    Sumcheck.Spec.SingleRound.projectedRoundPolynomial R n deg D
      ⟨start, by omega⟩ cs p =
    Sumcheck.Spec.SingleRound.projectedRoundPolynomial R (count + 1) deg D
      (⟨0, by omega⟩ : Fin (count + 1)) Fin.elim0 q := by
  subst n
  apply projectedRoundPolynomial_prefix
  simpa [fixedPrefixMap] using hq


/-- Semantic contract for any executable round-message implementation. -/
def HeadMessageCorrect {E : Type} [CommRing E] [DecidableEq E] [Nontrivial E]
    {T K ell : Nat} (groups : Vector (List (Fin T)) K)
    (build : (r : Nat) → Logup.Prover.State E T K (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2)) : Prop :=
  ∀ r state (small : E⦃≤ ell + 2⦄[X Fin (r + 1)]),
    small.val = State.polynomial groups state →
    Sumcheck.Impl.Representation.toMessage E (ell + 2) (build r state) =
      Sumcheck.Spec.SingleRound.projectedRoundPolynomial E (r + 1) (ell + 2)
        (boolEmbedding E) 0 Fin.elim0 small

/-- The pure coefficient implementation satisfies the existing head-projection specification. -/
theorem pureBuilder_correct {E : Type} [CommRing E] [DecidableEq E] [Nontrivial E]
    {T K ell : Nat} (groups : Vector (List (Fin T)) K)
    (hgroups : ∀ k, (groups.get k).length ≤ ell) :
    HeadMessageCorrect (E := E) groups (pureBuilder groups hgroups) := by
  intro r state small hsmall
  exact RoundCoefficients.message_toMessage groups hgroups state.lambda
    state.denominator state.weight state.helper state.kernel small hsmall

private theorem interpret_nativeWith {E : Type} [CommRing E] [DecidableEq E] [Nontrivial E]
    {T K ell n : Nat} {ι : Type} (ambient : OracleSpec ι)
    (groups : Vector (List (Fin T)) K)
    (build : (r : Nat) → Logup.Prover.State E T K (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2))
    (hbuild : HeadMessageCorrect groups build)
    (count start : Nat) (finish : start + count = n)
    (stmt : Sumcheck.Spec.StatementRound E n ⟨start, by omega⟩)
    (p : E⦃≤ ell + 2⦄[X Fin n]) (state : Logup.Prover.State E T K count)
    (hstate : State.polynomial groups state = fixedPrefixMap finish stmt.challenges p.val)
    (hdegree : ∀ j, (State.polynomial groups state).degreeOf j ≤ ell + 2) :
    Sumcheck.Interaction.Computable.interpretProver E (ell + 2) ambient count
      (nativeWith ambient build count state) =
    Sumcheck.Interaction.Native.honestProver E n (ell + 2) (boolEmbedding E) ambient
      count start finish stmt p := by
  classical
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    let small : E⦃≤ ell + 2⦄[X Fin (count + 1)] :=
      ⟨State.polynomial groups state,
        (MvPolynomial.mem_restrictDegree_iff_degreeOf_le _ _).mpr hdegree⟩
    have hmsg : Sumcheck.Impl.Representation.toMessage E (ell + 2)
        (build count state) =
      Sumcheck.Spec.SingleRound.projectedRoundPolynomial E n (ell + 2) (boolEmbedding E)
        ⟨start, by omega⟩ stmt.challenges p := by
      trans Sumcheck.Spec.SingleRound.projectedRoundPolynomial E (count + 1) (ell + 2)
        (boolEmbedding E) 0 Fin.elim0 small
      · exact hbuild count state small rfl
      · exact (projectedRoundPolynomial_fixedPrefix (boolEmbedding E) finish
          stmt.challenges p small hstate).symm
    simp only [nativeWith, Sumcheck.Interaction.Computable.interpretProver,
      Sumcheck.Interaction.Native.Core.transportProver,
      Sumcheck.Interaction.Native.honestProver, pure_bind]
    rw [hmsg]
    congr 1
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      funext choice
      cases choice with
      | none => rfl
      | some x =>
        change (pure _ >>= fun next => pure
          (Sumcheck.Interaction.Computable.interpretProver E (ell + 2) ambient count next)) = pure _
        simp only [pure_bind]
        congr 1
        apply ih (start + 1) (by omega)
        · rw [State.polynomial_fold]
          change headMap x (State.polynomial groups state) = _
          rw [hstate, fixedPrefixMap_snoc]
          rfl
        · intro j
          rw [State.polynomial_fold]
          exact (MvPolynomial.degreeOf_eval_C_finSuccEquiv _ j x).trans (hdegree j.succ)


private theorem nativeWith_support_completeness
    {E : Type} [CommRing E] [DecidableEq E] [Nontrivial E]
    {T K ell n : Nat} {ι : Type} (ambient : OracleSpec ι)
    (groups : Vector (List (Fin T)) K)
    (build : (r : Nat) → Logup.Prover.State E T K (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2))
    (hbuild : HeadMessageCorrect groups build)
    (challenge : OracleComp ambient E) (domain : List E)
    (hdomain : domain.Perm (Finset.univ.map (boolEmbedding E)).toList)
    (count start : Nat) (finish : start + count = n)
    (A : PFunctor)
    (original : VirtualOracle (ofPFunctor A)
      (Sumcheck.Interaction.MultivariateRound.polynomialFamily E n (ell + 2)))
    (stmt : Sumcheck.Spec.StatementRound E n ⟨start, by omega⟩)
    (impl : QueryImpl (ofPFunctor A) Id)
    (p : E⦃≤ ell + 2⦄[X Fin n]) (state : Logup.Prover.State E T K count)
    (hstate : State.polynomial groups state = fixedPrefixMap finish stmt.challenges p.val)
    (hdegree : ∀ j, (State.polynomial groups state).degreeOf j ≤ ell + 2)
    (horiginal : original.eval impl =
      (Sumcheck.Interaction.MultivariateRound.polynomialFamily E n (ell + 2)).behaviorOfRealizations
        (fun _ => p))
    (hcurrent : Sumcheck.Interaction.MultivariateRound.closedRelation E n (ell + 2)
      (boolEmbedding E)
      ⟨start, by omega⟩ ⟨stmt, original.eval impl⟩) :
    ∀ accepted ∈ support
      (Sumcheck.Interaction.Computable.executeWithFinalCheck E n (ell + 2) ambient challenge
        domain count start finish A original stmt impl
        (nativeWith ambient build count state)), accepted = true := by
  unfold Sumcheck.Interaction.Computable.executeWithFinalCheck
  rw [Sumcheck.Interaction.Native.Core.executeWithFinalCheck_eq_of_domain_perm E n (ell + 2)
    (Sumcheck.Impl.Representation.Message E (ell + 2))
    (Sumcheck.Impl.Representation.evaluate E (ell + 2)) ambient challenge domain
    (Finset.univ.map (boolEmbedding E)).toList hdomain]
  rw [Sumcheck.Interaction.Native.Core.executeWithFinalCheck_eq_execute]
  change ∀ accepted ∈ support (Sumcheck.Interaction.Native.Core.accepts E n (ell + 2) <$>
    Sumcheck.Interaction.Computable.execute E n (ell + 2) ambient challenge
      (Finset.univ.map (boolEmbedding E)).toList count start finish A original stmt impl
      (nativeWith ambient build count state)), accepted = true
  rw [Sumcheck.Interaction.Computable.execute_eq_native,
    interpret_nativeWith ambient groups build hbuild count start finish stmt p state hstate hdegree]
  intro accepted haccepted
  rw [support_map, Set.mem_image] at haccepted
  rcases haccepted with ⟨result, hresult, rfl⟩
  exact (Sumcheck.Interaction.Native.Core.accepts_eq_true_iff E n (ell + 2) result).mpr
    (Sumcheck.Interaction.Native.execute_support_completeness E n (ell + 2) (boolEmbedding E)
      ambient challenge count start finish A original stmt impl p horiginal hcurrent result hresult)


open CompPoly Logup.Interaction
open scoped BigOperators

/-- Balanced mapped fibers and off-pole alpha give the actual prepared-source initial relation. -/
theorem honest_initial_relation {B E : Type} [CommRing B] [Field E] [DecidableEq E]
    {n T ell : Nat} (f : B →+* E) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) (alpha : E)
    (hbalanced : ∀ v,
      ((Finset.univ : Finset (Fin n → Fin 2)).product (Finset.univ : Finset (Fin T))).sumFiber
        (fun p => f ((data (0, p.2)).get (finFunctionFinEquiv p.1)))
        (fun p => f ((data (1, p.2)).get (finFunctionFinEquiv p.1))) v = 0)
    (hoff : ∀ i u, alpha - f ((data (0, i)).get u) ≠ 0)
    (z : Fin n → E) (lambda : Fin (T ⌈/⌉ ell) → E)
    (A : PFunctor) (inputView : VirtualOracle (ofPFunctor A) (inputFamily f n T))
    (impl : QueryImpl (ofPFunctor A) Id)
    (hinput : inputView.eval impl = (inputFamily f n T).behaviorOfRealizations data) :
    Sumcheck.Interaction.MultivariateRound.closedRelation E n (ell + 2) (boolEmbedding E) 0
      ⟨zeroStatement E n,
        (qView f n T (T ⌈/⌉ ell) cfg.groups alpha z lambda ell A inputView).eval
          (Access.extendImpl A (helperInterface (E := E) n (T ⌈/⌉ ell)) impl
            (State.prepare f alpha cfg data).helper)⟩ := by
  unfold zeroStatement
  rw [initial_relation_iff cfg f alpha z lambda A inputView impl data hinput]
  have hres : residualTable cfg f alpha data (State.prepare f alpha cfg data).helper =
      fun _ _ => 0 := by
    funext k u
    exact groupResidual_helpers cfg.groups f alpha data k (finFunctionFinEquiv u)
      (fun i _ => hoff i (finFunctionFinEquiv u))
  have hzero : MvPolynomial.MLE (fun _ : Fin n → Fin 2 => (0 : E)) = 0 := by
    simp [MvPolynomial.MLE]
  simp only [hres, hzero, map_zero, mul_zero,
    Finset.sum_const_zero, add_zero]
  exact sum_helpers_eq_zero cfg f alpha data hbalanced

private theorem boolean_domain_perm {E : Type} [Field E] :
    ([0, 1] : List E).Perm (Finset.univ.map (boolEmbedding E)).toList := by
  classical
  apply List.perm_of_nodup_nodup_toFinset_eq (by simp) (Finset.nodup_toList _)
  rw [Finset.toList_toFinset]
  ext x
  simp [Fin.exists_fin_two, eq_comm]

/-- Every supported prepared native execution accepts after actual final source authentication. -/
theorem native_start_prepare_support_completeness
    {B E : Type} [CommRing B] [Field E] [DecidableEq E]
    {n T ell : Nat} (f : B →+* E) (cfg : Config n T ell)
    (build : (r : Nat) → Logup.Prover.State E T (T ⌈/⌉ ell) (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2))
    (hbuild : HeadMessageCorrect cfg.groups build)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) (alpha : E)
    (hbalanced : ∀ v,
      ((Finset.univ : Finset (Fin n → Fin 2)).product (Finset.univ : Finset (Fin T))).sumFiber
        (fun p => f ((data (0, p.2)).get (finFunctionFinEquiv p.1)))
        (fun p => f ((data (1, p.2)).get (finFunctionFinEquiv p.1))) v = 0)
    (hoff : ∀ i u, alpha - f ((data (0, i)).get u) ≠ 0)
    (z : Fin n → E) (lambda : Fin (T ⌈/⌉ ell) → E)
    {ι : Type} (ambient : OracleSpec ι) (challenge : OracleComp ambient E)
    (A : PFunctor) (inputView : VirtualOracle (ofPFunctor A) (inputFamily f n T))
    (impl : QueryImpl (ofPFunctor A) Id)
    (hinput : inputView.eval impl = (inputFamily f n T).behaviorOfRealizations data) :
    ∀ accepted ∈ support
      (Sumcheck.Interaction.Computable.executeWithFinalCheck E n (ell + 2) ambient challenge
        [0, 1] n 0 (Nat.zero_add n)
        (Access.extend A (helperInterface (E := E) n (T ⌈/⌉ ell)))
        (qView f n T (T ⌈/⌉ ell) cfg.groups alpha z lambda ell A inputView)
        (zeroStatement E n)
        (Access.extendImpl A (helperInterface (E := E) n (T ⌈/⌉ ell)) impl
          (State.prepare f alpha cfg data).helper)
        (nativeWith ambient build n
          (State.start (State.prepare f alpha cfg data) z lambda))), accepted = true := by
  let p := qPolynomial f n T (T ⌈/⌉ ell) cfg.groups alpha z lambda ell cfg.length_group_le
    data (State.prepare f alpha cfg data).helper
  apply nativeWith_support_completeness ambient cfg.groups build hbuild challenge
    [0, 1] boolean_domain_perm n 0 (Nat.zero_add n) _ _ _ _ p
  · change State.polynomial cfg.groups (State.start (State.prepare f alpha cfg data) z lambda) =
      fixedPrefixMap (Nat.zero_add n) (Fin.elim0 : Fin 0 → E) p.val
    rw [fixedPrefixMap_zero, RingHom.id_apply]
    exact State.polynomial_start_prepare f alpha cfg data z lambda
  · intro j
    rw [State.polynomial_start_prepare]
    exact (MvPolynomial.mem_restrictDegree_iff_degreeOf_le _ _).mp p.property j
  · exact qView_realizes f n T (T ⌈/⌉ ell) cfg.groups alpha z lambda ell
      cfg.length_group_le A inputView impl data hinput _
  · exact honest_initial_relation f cfg data alpha hbalanced hoff z lambda A inputView impl hinput

private theorem splitPrefix_honestWith {B E : Type} [CommRing B] [Field E] {n T ell : Nat}
    (f : B →+* E) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) {ι : Type} (ambient : OracleSpec ι)
    (build : (r : Nat) → Logup.Prover.State E T (T ⌈/⌉ ell) (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2)) :
    splitPrefixProver n (T ⌈/⌉ ell) ell ambient (honestWith f cfg data ambient build) =
      fun (alpha : E) => pure (pure ⟨(State.prepare f alpha cfg data).helper,
        fun joint => pure (nativeWith ambient build n
          (State.start (State.prepare f alpha cfg data) joint.1 joint.2))⟩) := by
  rfl


/-- The whole honest endpoint has exactly the actual alpha, joint and native challenge programs. -/
theorem execute_honestWith_eq_binds {B E : Type} [CommRing B] [Field E] [DecidableEq E]
    {n T ell : Nat} (f : B →+* E) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) {ι : Type} (ambient : OracleSpec ι)
    (build : (r : Nat) → Logup.Prover.State E T (T ⌈/⌉ ell) (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2))
    (alphaDraw : OracleComp ambient E)
    (jointDraw : OracleComp ambient ((Fin n → E) × (Fin (T ⌈/⌉ ell) → E)))
    (roundDraw : OracleComp ambient E) (A : PFunctor)
    (inputView : VirtualOracle (ofPFunctor A) (inputFamily f n T))
    (impl : QueryImpl (ofPFunctor A) Id) :
    execute f n T ell cfg ambient alphaDraw jointDraw roundDraw A inputView impl
      (honestWith f cfg data ambient build) = (do
        let alpha ← alphaDraw
        let joint ← jointDraw
        Sumcheck.Interaction.Computable.executeWithFinalCheck E n (ell + 2) ambient roundDraw
          [0, 1] n 0 (Nat.zero_add n) (family (E := E) n ell).spec.toPFunctor
          (VirtualOracle.id (family (E := E) n ell)) (zeroStatement E n)
          ((qView f n T (T ⌈/⌉ ell) cfg.groups alpha joint.1 joint.2 ell A inputView).eval
            (Access.extendImpl A (helperInterface (E := E) n (T ⌈/⌉ ell)) impl
              (State.prepare f alpha cfg data).helper))
          (nativeWith ambient build n
            (State.start (State.prepare f alpha cfg data) joint.1 joint.2))) := by
  have herase : Interaction.StrategyOver.TwoParty.Focal.mapOutput (fun _ _ => (() : Unit))
      (honestWith f cfg data ambient build) = honestWith f cfg data ambient build := by
    change Interaction.StrategyOver.TwoParty.Focal.mapOutput (fun _ => id)
      (honestWith f cfg data ambient build) = _
    exact Interaction.StrategyOver.TwoParty.Focal.mapOutput_id _
  rw [execute_eq_prefix_binds]
  simp only [herase, splitPrefix_honestWith]
  rfl


/-- Every supported whole honest execution accepts when its supported alphas are off-pole. -/
theorem execute_honestWith_support_completeness
    {B E : Type} [CommRing B] [Field E] [DecidableEq E]
    {n T ell : Nat} (f : B →+* E) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n)
    (build : (r : Nat) → Logup.Prover.State E T (T ⌈/⌉ ell) (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2))
    (hbuild : HeadMessageCorrect cfg.groups build)
    (hbalanced : ∀ v,
      ((Finset.univ : Finset (Fin n → Fin 2)).product (Finset.univ : Finset (Fin T))).sumFiber
        (fun p => f ((data (0, p.2)).get (finFunctionFinEquiv p.1)))
        (fun p => f ((data (1, p.2)).get (finFunctionFinEquiv p.1))) v = 0)
    {ι : Type} (ambient : OracleSpec ι) (alphaDraw : OracleComp ambient E)
    (hoff : ∀ alpha ∈ support alphaDraw, ∀ i u, alpha - f ((data (0, i)).get u) ≠ 0)
    (jointDraw : OracleComp ambient ((Fin n → E) × (Fin (T ⌈/⌉ ell) → E)))
    (roundDraw : OracleComp ambient E) (A : PFunctor)
    (inputView : VirtualOracle (ofPFunctor A) (inputFamily f n T))
    (impl : QueryImpl (ofPFunctor A) Id)
    (hinput : inputView.eval impl = (inputFamily f n T).behaviorOfRealizations data) :
    ∀ accepted ∈ support
      (execute f n T ell cfg ambient alphaDraw jointDraw roundDraw A inputView impl
        (honestWith f cfg data ambient build)), accepted = true := by
  rw [execute_honestWith_eq_binds]
  intro accepted haccepted
  obtain ⟨alpha, halpha, haccepted⟩ := support_bind_exists haccepted
  obtain ⟨joint, _, haccepted⟩ := support_bind_exists haccepted
  let p := qPolynomial f n T (T ⌈/⌉ ell) cfg.groups alpha joint.1 joint.2 ell
    cfg.length_group_le data (State.prepare f alpha cfg data).helper
  apply nativeWith_support_completeness ambient cfg.groups build hbuild roundDraw
    [0, 1] boolean_domain_perm n 0 (Nat.zero_add n)
    (family (E := E) n ell).spec.toPFunctor (VirtualOracle.id (family (E := E) n ell))
    (zeroStatement E n) _ p _ _ _ _ _ accepted haccepted
  · change State.polynomial cfg.groups
      (State.start (State.prepare f alpha cfg data) joint.1 joint.2) =
        fixedPrefixMap (Nat.zero_add n) (Fin.elim0 : Fin 0 → E) p.val
    rw [fixedPrefixMap_zero, RingHom.id_apply]
    exact State.polynomial_start_prepare f alpha cfg data joint.1 joint.2
  · intro j
    rw [State.polynomial_start_prepare]
    exact (MvPolynomial.mem_restrictDegree_iff_degreeOf_le _ _).mp p.property j
  · rw [VirtualOracle.eval_id]
    exact qView_realizes f n T (T ⌈/⌉ ell) cfg.groups alpha joint.1 joint.2 ell
      cfg.length_group_le A inputView impl data hinput _
  · rw [VirtualOracle.eval_id]
    exact honest_initial_relation f cfg data alpha hbalanced (hoff alpha halpha)
      joint.1 joint.2 A inputView impl hinput


/-- Finite support of mapped original values, used only in completeness analysis.
The verifier never computes or scans it. -/
def valueSupport {B E : Type} [CommRing B] [Field E] [DecidableEq E]
    {n T : Nat} (f : B →+* E) (data : Fin 2 × Fin T → CMlPolynomialEval B n) : Finset E :=
  ((Finset.univ : Finset (Fin n → Fin 2)).product (Finset.univ : Finset (Fin T))).image
    (fun p => f ((data (0, p.2)).get (finFunctionFinEquiv p.1)))

/-- A mapped scalar is a pole precisely when it occurs in an original value table. -/
theorem mem_valueSupport {B E : Type} [CommRing B] [Field E] [DecidableEq E]
    {n T : Nat} (f : B →+* E) (data : Fin 2 × Fin T → CMlPolynomialEval B n) (alpha : E) :
    alpha ∈ valueSupport f data ↔ ∃ i u, f ((data (0, i)).get u) = alpha := by
  rw [valueSupport, Finset.mem_image]
  constructor
  · rintro ⟨⟨u, i⟩, _, h⟩
    exact ⟨i, finFunctionFinEquiv u, h⟩
  · rintro ⟨i, u, h⟩
    refine ⟨(finFunctionFinEquiv.symm u, i), by simp, ?_⟩
    simpa only [Equiv.apply_symm_apply] using h

/-- All actual denominators are nonzero precisely outside the mapped value support. -/
theorem offPole_iff_not_mem_valueSupport {B E : Type} [CommRing B] [Field E] [DecidableEq E]
    {n T : Nat} (f : B →+* E) (data : Fin 2 × Fin T → CMlPolynomialEval B n) (alpha : E) :
    (∀ i u, alpha - f ((data (0, i)).get u) ≠ 0) ↔ alpha ∉ valueSupport f data := by
  constructor
  · intro h hmem
    obtain ⟨i, u, heq⟩ := (mem_valueSupport f data alpha).mp hmem
    apply h i u
    rw [heq, sub_self]
  · intro hn i u hsub
    apply hn
    exact (mem_valueSupport f data alpha).mpr ⟨i, u, (sub_eq_zero.mp hsub).symm⟩

/-- The distinct mapped support has at most one value per original occurrence. -/
theorem card_valueSupport_le {B E : Type} [CommRing B] [Field E] [DecidableEq E]
    {n T : Nat} (f : B →+* E) (data : Fin 2 × Fin T → CMlPolynomialEval B n) :
    (valueSupport f data).card ≤ T * 2 ^ n := by
  apply Finset.card_image_le.trans
  simp [Nat.mul_comm]

open scoped ProbabilityTheory ENNReal

/-- Failure of the named uniform honest endpoint is bounded by the actual mapped pole fraction. -/
theorem uniformExecute_honestWith_failure_le
    {B E : Type} [CommRing B] [Field E] [DecidableEq E] [Fintype E] [SampleableType E]
    {n T ell : Nat} (f : B →+* E) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n)
    (build : (r : Nat) → Logup.Prover.State E T (T ⌈/⌉ ell) (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2))
    (hbuild : HeadMessageCorrect cfg.groups build)
    (hbalanced : ∀ v,
      ((Finset.univ : Finset (Fin n → Fin 2)).product (Finset.univ : Finset (Fin T))).sumFiber
        (fun p => f ((data (0, p.2)).get (finFunctionFinEquiv p.1)))
        (fun p => f ((data (1, p.2)).get (finFunctionFinEquiv p.1))) v = 0)
    (A : PFunctor) (inputView : VirtualOracle (ofPFunctor A) (inputFamily f n T))
    (impl : QueryImpl (ofPFunctor A) Id)
    (hinput : inputView.eval impl = (inputFamily f n T).behaviorOfRealizations data) :
    Pr{let accepted ← (uniformExecute f n T ell cfg A inputView impl
      (honestWith f cfg data unifSpec build))}[accepted = false] ≤
      ((valueSupport f data).card : ℝ≥0∞) / Fintype.card E := by
  let next (alpha : E) : ProbComp Bool := do
    let joint ← $ᵗ ((Fin n → E) × (Fin (T ⌈/⌉ ell) → E))
    Sumcheck.Interaction.Computable.executeWithFinalCheck E n (ell + 2) unifSpec ($ᵗ E)
      [0, 1] n 0 (Nat.zero_add n) (family (E := E) n ell).spec.toPFunctor
      (VirtualOracle.id (family (E := E) n ell)) (zeroStatement E n)
      ((qView f n T (T ⌈/⌉ ell) cfg.groups alpha joint.1 joint.2 ell A inputView).eval
        (Access.extendImpl A (helperInterface (E := E) n (T ⌈/⌉ ell)) impl
          (State.prepare f alpha cfg data).helper))
      (nativeWith unifSpec build n (State.start (State.prepare f alpha cfg data) joint.1 joint.2))
  have hexec : uniformExecute f n T ell cfg A inputView impl
      (honestWith f cfg data unifSpec build) = ($ᵗ E >>= next) := by
    rw [uniformExecute, execute_honestWith_eq_binds]
  rw [hexec]
  have hbound : Pr{let accepted ← ($ᵗ E >>= next)}[accepted = false] ≤
      Pr{let alpha ← $ᵗ E}[alpha ∈ valueSupport f data] := by
    apply prEvent_bind_le_prEvent_of_forall_eq_zero
    intro alpha halpha
    have hfixed := execute_honestWith_support_completeness f cfg data build hbuild hbalanced
      unifSpec (pure alpha) (fun a ha => by
        have heq : a = alpha := by simpa only [support_pure, Set.mem_singleton_iff] using ha
        subst a
        exact (offPole_iff_not_mem_valueSupport f data alpha).mpr halpha)
      ($ᵗ ((Fin n → E) × (Fin (T ⌈/⌉ ell) → E))) ($ᵗ E) A inputView impl hinput
    rw [execute_honestWith_eq_binds] at hfixed
    change ∀ accepted ∈ support (next alpha), accepted = true at hfixed
    apply prEvent_eq_zero_of_forall_mem_support
    intro accepted haccepted hfalse
    have htrue := hfixed accepted haccepted
    exact Bool.false_ne_true (hfalse.symm.trans htrue)
  apply hbound.trans
  apply le_of_eq
  rw [SampleableType.prEvent_uniformSample]
  have hfilter : Finset.univ.filter (fun x => x ∈ valueSupport f data) = valueSupport f data := by
    ext x
    simp
  rw [hfilter]


/-- The named uniform honest endpoint accepts with probability at least one minus
its pole fraction. -/
theorem uniformExecute_honestWith_success_ge
    {B E : Type} [CommRing B] [Field E] [DecidableEq E] [Fintype E] [SampleableType E]
    {n T ell : Nat} (f : B →+* E) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n)
    (build : (r : Nat) → Logup.Prover.State E T (T ⌈/⌉ ell) (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2))
    (hbuild : HeadMessageCorrect cfg.groups build)
    (hbalanced : ∀ v,
      ((Finset.univ : Finset (Fin n → Fin 2)).product (Finset.univ : Finset (Fin T))).sumFiber
        (fun p => f ((data (0, p.2)).get (finFunctionFinEquiv p.1)))
        (fun p => f ((data (1, p.2)).get (finFunctionFinEquiv p.1))) v = 0)
    (A : PFunctor) (inputView : VirtualOracle (ofPFunctor A) (inputFamily f n T))
    (impl : QueryImpl (ofPFunctor A) Id)
    (hinput : inputView.eval impl = (inputFamily f n T).behaviorOfRealizations data) :
    1 - ((valueSupport f data).card : ℝ≥0∞) / Fintype.card E ≤
      Pr{let accepted ← (uniformExecute f n T ell cfg A inputView impl
        (honestWith f cfg data unifSpec build))}[accepted = true] := by
  have hfail := uniformExecute_honestWith_failure_le f cfg data build hbuild hbalanced
    A inputView impl hinput
  let program := uniformExecute f n T ell cfg A inputView impl
    (honestWith f cfg data unifSpec build)
  have htotal : Pr{let accepted ← program}[accepted = true] =
      1 - Pr{let accepted ← program}[accepted = false] := by
    convert OracleComp.prEvent_not_eq_one_sub program (fun accepted => accepted = false) using 1
    apply prEvent_congr
    intro accepted
    cases accepted <;> simp
  rw [htotal]
  exact tsub_le_tsub_left hfail 1

/-- Every execution retains total probability mass, including public abort returning false. -/
theorem uniformExecute_honestWith_total
    {B E : Type} [CommRing B] [Field E] [DecidableEq E] [SampleableType E]
    {n T ell : Nat} (f : B →+* E) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n)
    (build : (r : Nat) → Logup.Prover.State E T (T ⌈/⌉ ell) (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2))
    (A : PFunctor) (inputView : VirtualOracle (ofPFunctor A) (inputFamily f n T))
    (impl : QueryImpl (ofPFunctor A) Id) :
    Pr{let _ ← (uniformExecute f n T ell cfg A inputView impl
      (honestWith f cfg data unifSpec build))}[True] = 1 :=
  OracleComp.prEvent_true_eq_one _

end Logup.Prover.Honest
