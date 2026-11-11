/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Oracle.Routing
public import ArkLib.Interaction.Core.Security.Soundness
public import VCVio.EvalDist.ProbabilityBounds
public import VCVio.EvalDist.Monad.Disagreement.Measure
public import VCVio.OracleComp.Runtime

/-!
# Composition soundness

An arbitrary focal strategy on an appended interaction splits at the seam into its prefix and
the actual suffix strategy that prefix returns, with its private memory and effects
(`run_appendFlat_splitPrefix`). The seam theorems bound the success of a composed counterpart
`Counterpart.appendFlat c₁ c₂` with arbitrary midpoint outputs: an exceptional event at the
boundary is charged separately, and the suffix error is averaged over the actual boundary
distribution, almost everywhere. The suffix error may include a final action after the whole
interaction.

Passive verifiers decide only at the end. Their composed run is the prefix interaction followed
by a remainder: the suffix interaction and the composed decision (`Verifier.run_eq_bind`,
`OracleVerifier.run_eq_bind`). In the classical experiment the boundary is the prefix
interaction result together with the ambient state, and the suffix premise concerns the
remainder resumed from it. Under a persistent `OracleRuntime` the same decomposition gives the
runtime form through VCVio's `OracleRuntime.run_bind_success_le`.

A corollary starts from the suffix verifier's standalone soundness
(`Verifier.append_soundness_of_standalone`). Because the prefix decision runs after the suffix
interaction, it takes one explicit hypothesis: taking the prefix decision at the boundary leaves
the law of the final verdict unchanged. The hypothesis holds for a prefix decision without ambient
queries (`Verifier.boundaryDecidedRun_eq_of_pure`) and for a stateless ambient implementation
(`Verifier.boundaryDecidedRun_evalDistEq_of_stateless`), which leave the law of the whole run
unchanged. Inadmissible intermediate statements are charged `δ`, giving `ε₁ + δ + ε₂`.
-/

@[expose] public section

universe u uA uS uI wI wJ

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens OracleComp Oracle MeasureTheory
open scoped ENNReal

/-! ## Seam theorems for arbitrary counterparts -/

/-- The actual append boundary: the prefix transcript, the prover's returned suffix strategy and
the counterpart's midpoint output. The continuation carries the prover's private memory and
effects. -/
abbrev AppendBoundary {P : PFunctor.{uA, u}} (l : PFunctor.Lens P rolePoly.{u})
    (m : Type u → Type u) (s₁ : FreeM P PUnit.{u + 1}) (s₂ : Path s₁ → FreeM P PUnit.{u + 1})
    (OutP : PathAlong l (s₁.append s₂) → Type u) (MidC : PathAlong l s₁ → Type u) :=
  (tr : PathAlong l s₁) ×
    Focal l m (s₂ (projectPathAlong l s₁ tr))
      (fun tail => OutP (PathAlong.append l s₁ s₂ tr tail)) × MidC tr

section seam

variable {P : PFunctor.{uA, 0}} {l : PFunctor.Lens P rolePoly.{0}}
  {m : Type → Type} [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
  {s₁ : FreeM P PUnit} {s₂ : Path s₁ → FreeM P PUnit}
  {MidC : PathAlong l s₁ → Type} {OutP OutC : PathAlong l (s₁.append s₂) → Type}

variable (prover : Focal l m (s₁.append s₂) OutP)
  (counterpart₁ : PureEnd l m .counterpart s₁ MidC)
  (counterpart₂ : (tr : PathAlong l s₁) → MidC tr →
    Counterpart l m (s₂ (projectPathAlong l s₁ tr))
      (fun tail => OutC (PathAlong.append l s₁ s₂ tr tail)))
  (Exceptional : AppendBoundary l m s₁ s₂ OutP MidC → Prop)
  (Success : (tr : PathAlong l (s₁.append s₂)) → OutC tr → Prop)

/-- Run `finish` after the whole interaction and bound the success of its returned value.

For this fixed whole prover, the suffix error is averaged over the actual prefix boundaries
outside `Exceptional`, and the probability of `Exceptional` is charged separately. The suffix
premise includes `finish`, which receives the full transcript and both outputs, so it covers a
final verifier action that may query oracles or reject. The premise only holds almost
everywhere. Neither phase nor `finish` must be lossless, and no commutativity of effects is
required. -/
theorem run_appendFlat_soundness_weighted_ae_finish {α : Type}
    (finish : (tr : PathAlong l (s₁.append s₂)) → OutP tr → OutC tr → m α)
    (FinalSuccess : α → Prop) (error : AppendBoundary l m s₁ s₂ OutP MidC → ℝ≥0∞)
    (hsuffix : letI : MeasurableSpace (AppendBoundary l m s₁ s₂ OutP MidC) := ⊤
      ∀ᵐ b ∂𝒟[TwoParty.Lens.run s₁ (Focal.splitPrefix prover) counterpart₁.toStrategy],
        ¬ Exceptional b →
          Pr{let value ← (do
            let result ← TwoParty.Lens.run _ b.2.1 (counterpart₂ b.1 b.2.2)
            finish (PathAlong.append l s₁ s₂ b.1 result.1) result.2.1
              result.2.2)}[FinalSuccess value] ≤ error b) :
    let : MeasurableSpace (AppendBoundary l m s₁ s₂ OutP MidC) := ⊤
    Pr{let value ← (do
      let result ← TwoParty.Lens.run (s₁.append s₂) prover
        (Counterpart.appendFlat counterpart₁ counterpart₂)
      finish result.1 result.2.1 result.2.2)}[FinalSuccess value] ≤
      Pr{let b ← (TwoParty.Lens.run s₁ (Focal.splitPrefix prover)
          counterpart₁.toStrategy)}[Exceptional b] +
        ∫⁻ b in {b | ¬ Exceptional b}, error b
          ∂𝒟[TwoParty.Lens.run s₁ (Focal.splitPrefix prover) counterpart₁.toStrategy] := by
  let : MeasurableSpace (AppendBoundary l m s₁ s₂ OutP MidC) := ⊤
  have execution : (do
      let result ← TwoParty.Lens.run (s₁.append s₂) prover
        (Counterpart.appendFlat counterpart₁ counterpart₂)
      finish result.1 result.2.1 result.2.2) = (do
      let b ← TwoParty.Lens.run s₁ (Focal.splitPrefix prover) counterpart₁.toStrategy
      let result ← TwoParty.Lens.run _ b.2.1 (counterpart₂ b.1 b.2.2)
      finish (PathAlong.append l s₁ s₂ b.1 result.1) result.2.1 result.2.2) := by
    rw [run_appendFlat_splitPrefix]
    simp only [bind_assoc, LawfulMonad.pure_bind]
  rw [execution]
  exact prEvent_bind_le_prEvent_add_lintegral_ae _ _ Exceptional FinalSuccess error hsuffix

/-- For one whole prover, the branch-dependent suffix errors are averaged over its actual prefix
boundaries outside `Exceptional`, and `Exceptional` is charged. The suffix premise only holds
almost everywhere, so it may fail at a structurally supported boundary of zero mass. -/
theorem run_appendFlat_soundness_weighted_ae
    (error : AppendBoundary l m s₁ s₂ OutP MidC → ℝ≥0∞)
    (hsuffix : letI : MeasurableSpace (AppendBoundary l m s₁ s₂ OutP MidC) := ⊤
      ∀ᵐ b ∂𝒟[TwoParty.Lens.run s₁ (Focal.splitPrefix prover) counterpart₁.toStrategy],
        ¬ Exceptional b →
          Pr{let result ← (TwoParty.Lens.run _ b.2.1
            (counterpart₂ b.1 b.2.2))}[Success
              (PathAlong.append l s₁ s₂ b.1 result.1) result.2.2] ≤ error b) :
    let : MeasurableSpace (AppendBoundary l m s₁ s₂ OutP MidC) := ⊤
    Pr{let result ← TwoParty.Lens.run (s₁.append s₂) prover
        (Counterpart.appendFlat counterpart₁ counterpart₂)}[Success result.1 result.2.2] ≤
      Pr{let b ← (TwoParty.Lens.run s₁ (Focal.splitPrefix prover)
          counterpart₁.toStrategy)}[Exceptional b] +
        ∫⁻ b in {b | ¬ Exceptional b}, error b
          ∂𝒟[TwoParty.Lens.run s₁ (Focal.splitPrefix prover) counterpart₁.toStrategy] := by
  let : MeasurableSpace (AppendBoundary l m s₁ s₂ OutP MidC) := ⊤
  have h := run_appendFlat_soundness_weighted_ae_finish prover counterpart₁ counterpart₂
    Exceptional (fun tr _ out => pure (⟨tr, out⟩ : (tr : PathAlong l (s₁.append s₂)) × OutC tr))
    (fun result => Success result.1 result.2) error
    (by simpa only [bind_assoc, LawfulMonad.pure_bind, prEvent_norm] using hsuffix)
  simpa only [bind_assoc, LawfulMonad.pure_bind, prEvent_norm] using h

/-- The weighted bound needs suffix security only at structurally reachable boundaries of this
whole prover's prefix, including the actual returned continuation. Unlike the
almost-everywhere form, this premise also covers supported boundaries of zero mass. -/
theorem run_appendFlat_soundness_weighted_of_support
    [MonadAttach m] [WeaklyLawfulMonadAttach m]
    (error : AppendBoundary l m s₁ s₂ OutP MidC → ℝ≥0∞)
    (hsuffix : ∀ b ∈ support
        (TwoParty.Lens.run s₁ (Focal.splitPrefix prover) counterpart₁.toStrategy),
      ¬ Exceptional b →
        Pr{let result ← (TwoParty.Lens.run _ b.2.1
          (counterpart₂ b.1 b.2.2))}[Success
            (PathAlong.append l s₁ s₂ b.1 result.1) result.2.2] ≤ error b) :
    let : MeasurableSpace (AppendBoundary l m s₁ s₂ OutP MidC) := ⊤
    Pr{let result ← TwoParty.Lens.run (s₁.append s₂) prover
        (Counterpart.appendFlat counterpart₁ counterpart₂)}[Success result.1 result.2.2] ≤
      Pr{let b ← (TwoParty.Lens.run s₁ (Focal.splitPrefix prover)
          counterpart₁.toStrategy)}[Exceptional b] +
        ∫⁻ b in {b | ¬ Exceptional b}, error b
          ∂𝒟[TwoParty.Lens.run s₁ (Focal.splitPrefix prover) counterpart₁.toStrategy] := by
  let : MeasurableSpace (AppendBoundary l m s₁ s₂ OutP MidC) := ⊤
  apply run_appendFlat_soundness_weighted_ae prover counterpart₁ counterpart₂ Exceptional Success
  exact evalDist.ae_of_forall_mem_support _ _ MeasurableSet.of_discrete hsuffix

/-- A fixed whole prover needs a prefix bound only for its own prefix, and a uniform suffix
bound only almost everywhere under that prefix's actual boundary distribution. -/
theorem run_appendFlat_soundness_ae (ε₁ ε₂ : ℝ≥0∞)
    (hprefix : Pr{let b ← (TwoParty.Lens.run s₁ (Focal.splitPrefix prover)
      counterpart₁.toStrategy)}[Exceptional b] ≤ ε₁)
    (hsuffix : letI : MeasurableSpace (AppendBoundary l m s₁ s₂ OutP MidC) := ⊤
      ∀ᵐ b ∂𝒟[TwoParty.Lens.run s₁ (Focal.splitPrefix prover) counterpart₁.toStrategy],
        ¬ Exceptional b →
          Pr{let result ← (TwoParty.Lens.run _ b.2.1
            (counterpart₂ b.1 b.2.2))}[Success
              (PathAlong.append l s₁ s₂ b.1 result.1) result.2.2] ≤ ε₂) :
    Pr{let result ← TwoParty.Lens.run (s₁.append s₂) prover
        (Counterpart.appendFlat counterpart₁ counterpart₂)}[Success result.1 result.2.2] ≤
      ε₁ + ε₂ := by
  let : MeasurableSpace (AppendBoundary l m s₁ s₂ OutP MidC) := ⊤
  refine (run_appendFlat_soundness_weighted_ae prover counterpart₁ counterpart₂ Exceptional
    Success (fun _ => ε₂) hsuffix).trans (add_le_add hprefix ?_)
  rw [setLIntegral_const]
  exact mul_le_of_le_one_right' ((measure_mono (Set.subset_univ _)).trans
    (evalDist_apply_univ_le_one _))

/-- A fixed whole prover needs uniform suffix security only at reachable boundaries. -/
theorem run_appendFlat_soundness_of_support
    [MonadAttach m] [WeaklyLawfulMonadAttach m] (ε₁ ε₂ : ℝ≥0∞)
    (hprefix : Pr{let b ← (TwoParty.Lens.run s₁ (Focal.splitPrefix prover)
      counterpart₁.toStrategy)}[Exceptional b] ≤ ε₁)
    (hsuffix : ∀ b ∈ support
        (TwoParty.Lens.run s₁ (Focal.splitPrefix prover) counterpart₁.toStrategy),
      ¬ Exceptional b →
        Pr{let result ← (TwoParty.Lens.run _ b.2.1
          (counterpart₂ b.1 b.2.2))}[Success
            (PathAlong.append l s₁ s₂ b.1 result.1) result.2.2] ≤ ε₂) :
    Pr{let result ← TwoParty.Lens.run (s₁.append s₂) prover
        (Counterpart.appendFlat counterpart₁ counterpart₂)}[Success result.1 result.2.2] ≤
      ε₁ + ε₂ := by
  let : MeasurableSpace (AppendBoundary l m s₁ s₂ OutP MidC) := ⊤
  apply run_appendFlat_soundness_ae prover counterpart₁ counterpart₂ Exceptional Success
    ε₁ ε₂ hprefix
  exact evalDist.ae_of_forall_mem_support _ _ MeasurableSet.of_discrete hsuffix

/-- A fixed whole prover needs a prefix bound only for its own prefix; the suffix bound covers
every boundary outside `Exceptional`. -/
theorem run_appendFlat_soundness_fixed (ε₁ ε₂ : ℝ≥0∞)
    (hprefix : Pr{let b ← (TwoParty.Lens.run s₁ (Focal.splitPrefix prover)
      counterpart₁.toStrategy)}[Exceptional b] ≤ ε₁)
    (hsuffix : ∀ b, ¬ Exceptional b →
      Pr{let result ← (TwoParty.Lens.run _ b.2.1
        (counterpart₂ b.1 b.2.2))}[Success
          (PathAlong.append l s₁ s₂ b.1 result.1) result.2.2] ≤ ε₂) :
    Pr{let result ← TwoParty.Lens.run (s₁.append s₂) prover
        (Counterpart.appendFlat counterpart₁ counterpart₂)}[Success result.1 result.2.2] ≤
      ε₁ + ε₂ :=
  run_appendFlat_soundness_ae prover counterpart₁ counterpart₂ Exceptional Success ε₁ ε₂ hprefix
    (Filter.Eventually.of_forall hsuffix)

omit prover Exceptional in
/-- Prefix truth transitions and suffix soundness bound the success of the composed counterpart
against every whole prover. Prefix outputs retain arbitrary suffix strategies, so suffix
soundness covers every private continuation the prefix can return. The suffix hypothesis covers
every false prefix transcript and midpoint, reachable or not. -/
theorem run_appendFlat_soundness (prover : Focal l m (s₁.append s₂) OutP)
    (Good : (tr : PathAlong l s₁) → MidC tr → Prop) (ε₁ ε₂ : ℝ≥0∞)
    (hprefix : ∀ strategy : Focal l m s₁ (fun tr => Focal l m (s₂ (projectPathAlong l s₁ tr))
        (fun tail => OutP (PathAlong.append l s₁ s₂ tr tail))),
      Pr{let result ← (TwoParty.Lens.run s₁ strategy
        counterpart₁.toStrategy)}[Good result.1 result.2.2] ≤ ε₁)
    (hsuffix : ∀ (tr : PathAlong l s₁) (mid : MidC tr), ¬ Good tr mid →
      ∀ strategy : Focal l m (s₂ (projectPathAlong l s₁ tr))
          (fun tail => OutP (PathAlong.append l s₁ s₂ tr tail)),
        Pr{let result ← (TwoParty.Lens.run _ strategy
          (counterpart₂ tr mid))}[Success (PathAlong.append l s₁ s₂ tr result.1) result.2.2] ≤ ε₂) :
    Pr{let result ← TwoParty.Lens.run (s₁.append s₂) prover
        (Counterpart.appendFlat counterpart₁ counterpart₂)}[Success result.1 result.2.2] ≤
      ε₁ + ε₂ :=
  run_appendFlat_soundness_fixed prover counterpart₁ counterpart₂ (fun b => Good b.1 b.2.2)
    Success ε₁ ε₂ (hprefix (Focal.splitPrefix prover))
    (fun b hfalse => hsuffix b.1 b.2.2 hfalse b.2.1)

omit prover Exceptional in
/-- If suffix soundness applies only to admissible false midpoints, additionally charge the
probability `δ` of leaving that domain, for `ε₁ + δ + ε₂`. The suffix hypothesis covers every
admissible false prefix transcript and midpoint, reachable or not. -/
theorem run_appendFlat_soundness_of_admissible (prover : Focal l m (s₁.append s₂) OutP)
    (Good Admissible : (tr : PathAlong l s₁) → MidC tr → Prop) (ε₁ δ ε₂ : ℝ≥0∞)
    (hprefix : ∀ strategy : Focal l m s₁ (fun tr => Focal l m (s₂ (projectPathAlong l s₁ tr))
        (fun tail => OutP (PathAlong.append l s₁ s₂ tr tail))),
      Pr{let result ← (TwoParty.Lens.run s₁ strategy
        counterpart₁.toStrategy)}[Good result.1 result.2.2] ≤ ε₁)
    (hadmissible : ∀ strategy : Focal l m s₁ (fun tr =>
        Focal l m (s₂ (projectPathAlong l s₁ tr))
          (fun tail => OutP (PathAlong.append l s₁ s₂ tr tail))),
      Pr{let result ← (TwoParty.Lens.run s₁ strategy
        counterpart₁.toStrategy)}[¬ Admissible result.1 result.2.2] ≤ δ)
    (hsuffix : ∀ (tr : PathAlong l s₁) (mid : MidC tr), ¬ Good tr mid → Admissible tr mid →
      ∀ strategy : Focal l m (s₂ (projectPathAlong l s₁ tr))
          (fun tail => OutP (PathAlong.append l s₁ s₂ tr tail)),
        Pr{let result ← (TwoParty.Lens.run _ strategy
          (counterpart₂ tr mid))}[Success (PathAlong.append l s₁ s₂ tr result.1) result.2.2] ≤ ε₂) :
    Pr{let result ← TwoParty.Lens.run (s₁.append s₂) prover
        (Counterpart.appendFlat counterpart₁ counterpart₂)}[Success result.1 result.2.2] ≤
      ε₁ + δ + ε₂ := by
  classical
  apply run_appendFlat_soundness counterpart₁ counterpart₂ Success prover
    (fun tr mid => Good tr mid ∨ ¬ Admissible tr mid) (ε₁ + δ) ε₂
  · intro strategy
    exact (prEvent_or_le (TwoParty.Lens.run s₁ strategy counterpart₁.toStrategy) _ _).trans
      (add_le_add (hprefix strategy) (hadmissible strategy))
  · intro tr mid hfalse strategy
    exact hsuffix tr mid (fun hgood => hfalse (Or.inl hgood))
      (not_not.mp (fun hbad => hfalse (Or.inr hbad))) strategy

end seam

/-! ## End-decided runs split at the append boundary -/

section runs

variable {ι : Type u} {ambient : OracleSpec.{u, u} ι}

/-- The append boundary of a run: the prefix transcript and the continuation the whole prover
returns, over the full run interface of the appended protocol. -/
abbrev RunBoundary {P : PFunctor.{uA, u}} (l : PFunctor.Lens P rolePoly.{u})
    {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (s₁ : FreeM P PUnit.{u + 1}) (s₂ : Path s₁ → FreeM P PUnit.{u + 1})
    (Out : PathAlong l (s₁.append s₂) → Type u) :=
  AppendBoundary l (OracleComp (ambient + challengeSpec l (s₁.append s₂))) s₁ s₂ Out
    (fun _ => PUnit)

/-- The prefix interaction of a run on an appended protocol. It returns the actual append
boundary: the prefix transcript and the continuation the whole prover returns, which keeps the
prover's private memory. Ambient and challenge queries go to the full run interface. -/
def appendPrefixRun {P : PFunctor.{uA, u}} {l : PFunctor.Lens P rolePoly.{u}}
    {s₁ : FreeM P PUnit.{u + 1}} {s₂ : Path s₁ → FreeM P PUnit.{u + 1}}
    {Out : PathAlong l (s₁.append s₂) → Type u}
    (prover : Prover l ambient (s₁.append s₂) Out) :
    OracleComp (ambient + challengeSpec l (s₁.append s₂)) (RunBoundary l ambient s₁ s₂ Out) :=
  TwoParty.Lens.run s₁
    (Focal.splitPrefix (prover.simulate
      (fun q => liftM ((ambient + challengeSpec l (s₁.append s₂)).query (.inl q)))))
    (sampler l s₁ (prefixDraw l s₁ s₂
      (fun c => liftM ((ambient + challengeSpec l (s₁.append s₂)).query (.inr c)))))

/-- The rest of a plain run after the append boundary: the suffix interaction against the
returned continuation, then the end decision on the whole transcript. -/
def Verifier.suffixRun {s₁ : Protocol.{u}} {s₂ : Path s₁ → Protocol.{u}} {S : Type uS}
    {T : Path (s₁.append s₂) → Type u}
    {Out : PathAlong plainSig (s₁.append s₂) → Type u}
    (V : Verifier ambient (s₁.append s₂) S T) (stmt : S)
    (b : RunBoundary plainSig ambient s₁ s₂ Out) :
    OracleComp (ambient + challengeSpec plainSig (s₁.append s₂))
      (Observation plainSig (s₁.append s₂) Out T) := do
  let ⟨tail, out, _⟩ ← TwoParty.Lens.run _ b.2.1
    (sampler plainSig _ (suffixDraw plainSig s₁ s₂
      (fun c => liftM ((ambient + challengeSpec plainSig (s₁.append s₂)).query (.inr c)))
      (projectPathAlong plainSig s₁ b.1)))
  let tr := PathAlong.append plainSig s₁ s₂ b.1 tail
  let verdict ← OracleComp.liftComp
    (V.decide stmt (projectPathAlong plainSig _ tr) (toPlainView _ tr)).run
    (ambient + challengeSpec plainSig (s₁.append s₂))
  pure ⟨tr, out, verdict⟩

/-- A run on an appended plain protocol is its prefix interaction followed by the rest of the
run at the actual boundary. The verifier is arbitrary, so this covers `Verifier.append`. -/
theorem Verifier.run_eq_bind {s₁ : Protocol.{u}} {s₂ : Path s₁ → Protocol.{u}} {S : Type uS}
    {T : Path (s₁.append s₂) → Type u}
    {Out : PathAlong plainSig (s₁.append s₂) → Type u}
    (V : Verifier ambient (s₁.append s₂) S T) (stmt : S)
    (prover : Prover plainSig ambient (s₁.append s₂) Out) :
    V.run stmt prover = appendPrefixRun prover >>= V.suffixRun stmt := by
  simp only [Verifier.run, appendPrefixRun]
  rw [plainSampler_append_eq, run_splitSampler]
  simp only [bind_assoc]
  exact bind_congr fun _ => bind_congr fun _ => LawfulMonad.pure_bind _ _

/-- The rest of an oracle run after the append boundary: the suffix interaction against the
returned continuation, then the end decision with resources answered from the input data and the
payloads of the whole transcript. -/
def OracleVerifier.suffixRun {s₁ : OracleProtocol.{u}} {s₂ : Path s₁ → OracleProtocol.{u}}
    {I : Type uI} {A : I → Type u} {J : Path (s₁.append s₂) → Type u}
    {B : (p : Path (s₁.append s₂)) → J p → Type u}
    {inputs : OracleFamily.{uI, u, wI} I A}
    {outputs : (p : Path (s₁.append s₂)) → OracleFamily.{u, u, wJ} (J p) (B p)} {S : Type uS}
    {T : Path (s₁.append s₂) → Type u}
    {Out : PathAlong oracleSig (s₁.append s₂) → Type u}
    (V : OracleVerifier ambient (s₁.append s₂) S T inputs outputs) (stmt : S)
    (data : ∀ i, A i)
    (b : RunBoundary oracleSig ambient s₁ s₂ Out) :
    OracleComp (ambient + challengeSpec oracleSig (s₁.append s₂))
      (Observation oracleSig (s₁.append s₂) Out (OracleVerifier.Output T B)) := do
  let ⟨tail, out, _⟩ ← TwoParty.Lens.run _ b.2.1
    (sampler oracleSig _ (suffixDraw oracleSig s₁ s₂
      (fun c => liftM ((ambient + challengeSpec oracleSig (s₁.append s₂)).query (.inr c)))
      (projectPathAlong oracleSig s₁ b.1)))
  let tr := PathAlong.append oracleSig s₁ s₂ b.1 tail
  let p := projectPathAlong oracleSig _ tr
  let view := toView _ tr
  let resources := (data, payloads _ tr)
  let verdict ← simulateQ
    (QueryImpl.addLift
      ((fun q => liftM ((ambient + challengeSpec oracleSig (s₁.append s₂)).query (.inl q))) :
        QueryImpl ambient (OracleComp (ambient + challengeSpec oracleSig (s₁.append s₂))))
      ((pathResources inputs _ p).answer resources))
    (V.decide stmt p view).run
  pure ⟨tr, out, verdict.map fun t => (t, (V.outputMap stmt p view).f resources)⟩

/-- An oracle run on an appended protocol is its prefix interaction followed by the rest of the
run at the actual boundary. The verifier is arbitrary, so this covers `OracleVerifier.append`;
`OracleVerifier.run_append` describes the rest of that run. -/
theorem OracleVerifier.run_eq_bind {s₁ : OracleProtocol.{u}} {s₂ : Path s₁ → OracleProtocol.{u}}
    {I : Type uI} {A : I → Type u} {J : Path (s₁.append s₂) → Type u}
    {B : (p : Path (s₁.append s₂)) → J p → Type u}
    {inputs : OracleFamily.{uI, u, wI} I A}
    {outputs : (p : Path (s₁.append s₂)) → OracleFamily.{u, u, wJ} (J p) (B p)} {S : Type uS}
    {T : Path (s₁.append s₂) → Type u}
    {Out : PathAlong oracleSig (s₁.append s₂) → Type u}
    (V : OracleVerifier ambient (s₁.append s₂) S T inputs outputs) (stmt : S)
    (data : ∀ i, A i) (prover : Prover oracleSig ambient (s₁.append s₂) Out) :
    V.run stmt data prover = appendPrefixRun prover >>= V.suffixRun stmt data := by
  simp only [OracleVerifier.run, appendPrefixRun]
  rw [sampler_append_eq, run_splitSampler]
  simp only [bind_assoc]
  exact bind_congr fun _ => bind_congr fun _ => LawfulMonad.pure_bind _ _

end runs

/-! ## Bounds at a bind -/

section bounds

variable {m : Type → Type} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] {α β : Type}

/-- Bound the success of `mx >>= my` by a true-midpoint error, a false inadmissible-midpoint
error, and the suffix error averaged over false admissible midpoints. The suffix premise only
holds almost everywhere under the actual boundary distribution. -/
theorem prEvent_bind_le_truth_invalid_ae (mx : m α) (my : α → m β)
    (TruthMid Admissible : α → Prop) (Success : β → Prop) (error : α → ℝ≥0∞)
    (εtruth εinvalid : ℝ≥0∞)
    (htruth : Pr{let b ← mx}[TruthMid b] ≤ εtruth)
    (hinvalid : Pr{let b ← mx}[¬ TruthMid b ∧ ¬ Admissible b] ≤ εinvalid)
    (hsuffix : letI : MeasurableSpace α := ⊤
      ∀ᵐ b ∂𝒟[mx], ¬ TruthMid b → Admissible b → Pr{let r ← my b}[Success r] ≤ error b) :
    letI : MeasurableSpace α := ⊤
    Pr{let r ← mx >>= my}[Success r] ≤
      εtruth + εinvalid + ∫⁻ b in {b | ¬ TruthMid b ∧ Admissible b}, error b ∂𝒟[mx] := by
  classical
  let : MeasurableSpace α := ⊤
  have h := prEvent_bind_le_prEvent_add_lintegral_ae mx my
    (fun b => TruthMid b ∨ ¬ Admissible b) Success error
    (hsuffix.mono fun _ h hout => h (fun ht => hout (Or.inl ht))
      (not_not.mp fun ha => hout (Or.inr ha)))
  have hset : {b | ¬ (TruthMid b ∨ ¬ Admissible b)} = {b | ¬ TruthMid b ∧ Admissible b} := by
    ext b
    simp only [Set.mem_ofPred_eq, not_or, not_not]
  rw [hset] at h
  refine h.trans (add_le_add ?_ le_rfl)
  rw [prEvent_congr mx _ (fun b => TruthMid b ∨ (¬ TruthMid b ∧ ¬ Admissible b))
    (fun b => by tauto)]
  exact (prEvent_or_le mx _ _).trans (add_le_add htruth hinvalid)

/-- With a uniform suffix error, the bound is `εtruth + εinvalid + ε`. -/
theorem prEvent_bind_le_truth_invalid_uniform_ae (mx : m α) (my : α → m β)
    (TruthMid Admissible : α → Prop) (Success : β → Prop) (εtruth εinvalid ε : ℝ≥0∞)
    (htruth : Pr{let b ← mx}[TruthMid b] ≤ εtruth)
    (hinvalid : Pr{let b ← mx}[¬ TruthMid b ∧ ¬ Admissible b] ≤ εinvalid)
    (hsuffix : letI : MeasurableSpace α := ⊤
      ∀ᵐ b ∂𝒟[mx], ¬ TruthMid b → Admissible b → Pr{let r ← my b}[Success r] ≤ ε) :
    Pr{let r ← mx >>= my}[Success r] ≤ εtruth + εinvalid + ε := by
  let : MeasurableSpace α := ⊤
  refine (prEvent_bind_le_truth_invalid_ae mx my TruthMid Admissible Success (fun _ => ε)
    εtruth εinvalid htruth hinvalid hsuffix).trans (add_le_add le_rfl ?_)
  rw [setLIntegral_const]
  exact mul_le_of_le_one_right' ((measure_mono (Set.subset_univ _)).trans
    (evalDist_apply_univ_le_one _))

end bounds

/-! ## The experiment split at a bind -/

section experiment

variable {ι κ σ α β : Type} {ambient : OracleSpec ι} {chal : OracleSpec κ}

/-- Run a program in the experiment and keep the ambient state it ends in. -/
def experimentWithState (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (challengeQueryImpl : QueryImpl chal ProbComp) (program : OracleComp (ambient + chal) α) :
    ProbComp (α × σ) := do
  (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
    QueryImpl (ambient + chal) (StateT σ ProbComp)) program).run (← init)

/-- Resume a program in the experiment from a given ambient state. -/
def experimentResume (impl : QueryImpl ambient (StateT σ ProbComp))
    (challengeQueryImpl : QueryImpl chal ProbComp) (state : σ)
    (program : OracleComp (ambient + chal) β) : ProbComp β :=
  (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
    QueryImpl (ambient + chal) (StateT σ ProbComp)) program).run' state

/-- The experiment of `first >>= next` runs `first`, keeps its result and ambient state, and
resumes `next` from that state. -/
theorem experiment_bind (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (challengeQueryImpl : QueryImpl chal ProbComp) (first : OracleComp (ambient + chal) α)
    (next : α → OracleComp (ambient + chal) β) :
    experiment init impl challengeQueryImpl (first >>= next) =
      experimentWithState init impl challengeQueryImpl first >>= fun b =>
        experimentResume impl challengeQueryImpl b.2 (next b.1) := by
  simp only [experiment, experimentWithState, experimentResume, simulateQ_bind,
    StateT.run'_eq, StateT.run_bind, bind_assoc, _root_.map_bind]

end experiment

/-! ## Soundness of end-decided runs on appended protocols -/

section soundness

variable {ι σ : Type} {ambient : OracleSpec ι}

/-- In the experiment, the success of a plain run on an appended protocol is bounded by an
exceptional boundary event and the suffix error averaged over the remaining boundaries. The
boundary is the interaction result together with the ambient state, and the suffix premise is over
the run resumed from it, including the end decision. The premise only holds almost everywhere.
The verifier is arbitrary, so this covers `Verifier.append`. -/
theorem Verifier.append_soundness_weighted_ae {s₁ : Protocol} {s₂ : Path s₁ → Protocol}
    {S : Type uS} {T : Path (s₁.append s₂) → Type} {Out : PathAlong plainSig (s₁.append s₂) → Type}
    (V : Verifier ambient (s₁.append s₂) S T) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec plainSig (s₁.append s₂)) ProbComp) (stmt : S)
    (prover : Prover plainSig ambient (s₁.append s₂) Out)
    (Exceptional : RunBoundary plainSig ambient s₁ s₂ Out × σ → Prop)
    (Success : Observation plainSig (s₁.append s₂) Out T → Prop)
    (error : RunBoundary plainSig ambient s₁ s₂ Out × σ → ℝ≥0∞)
    (hsuffix : letI : MeasurableSpace (RunBoundary plainSig ambient s₁ s₂ Out × σ) := ⊤
      ∀ᵐ b ∂𝒟[experimentWithState init impl challenges (appendPrefixRun prover)],
        ¬ Exceptional b →
          Pr{let obs ← (experimentResume impl challenges b.2
            (V.suffixRun stmt b.1))}[Success obs] ≤ error b) :
    letI : MeasurableSpace (RunBoundary plainSig ambient s₁ s₂ Out × σ) := ⊤
    Pr{let obs ← experiment init impl challenges (V.run stmt prover)}[Success obs] ≤
      Pr{let b ← (experimentWithState init impl challenges
          (appendPrefixRun prover))}[Exceptional b] +
        ∫⁻ b in {b | ¬ Exceptional b}, error b
          ∂𝒟[experimentWithState init impl challenges (appendPrefixRun prover)] := by
  let : MeasurableSpace (RunBoundary plainSig ambient s₁ s₂ Out × σ) := ⊤
  rw [V.run_eq_bind, experiment_bind]
  exact prEvent_bind_le_prEvent_add_lintegral_ae _ _ Exceptional Success error hsuffix

/-- In the experiment, a plain run on an appended protocol succeeds with probability at most
`ε₁ + δ + ε₂`: `ε₁` bounds reaching a good boundary, `δ` bounds leaving the admissible
boundaries, and `ε₂` bounds the resumed run from almost every bad admissible boundary. The
boundary is the interaction result together with the ambient state. -/
theorem Verifier.append_soundness {s₁ : Protocol} {s₂ : Path s₁ → Protocol}
    {S : Type uS} {T : Path (s₁.append s₂) → Type} {Out : PathAlong plainSig (s₁.append s₂) → Type}
    (V : Verifier ambient (s₁.append s₂) S T) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec plainSig (s₁.append s₂)) ProbComp) (stmt : S)
    (prover : Prover plainSig ambient (s₁.append s₂) Out)
    (Good Admissible : RunBoundary plainSig ambient s₁ s₂ Out × σ → Prop)
    (Success : Observation plainSig (s₁.append s₂) Out T → Prop) (ε₁ δ ε₂ : ℝ≥0∞)
    (hprefix : Pr{let b ← (experimentWithState init impl challenges
      (appendPrefixRun prover))}[Good b] ≤ ε₁)
    (hadmissible : Pr{let b ← (experimentWithState init impl challenges
      (appendPrefixRun prover))}[¬ Admissible b] ≤ δ)
    (hsuffix : letI : MeasurableSpace (RunBoundary plainSig ambient s₁ s₂ Out × σ) := ⊤
      ∀ᵐ b ∂𝒟[experimentWithState init impl challenges (appendPrefixRun prover)],
        ¬ Good b → Admissible b →
          Pr{let obs ← (experimentResume impl challenges b.2
            (V.suffixRun stmt b.1))}[Success obs] ≤ ε₂) :
    Pr{let obs ← experiment init impl challenges (V.run stmt prover)}[Success obs] ≤
      ε₁ + δ + ε₂ := by
  rw [V.run_eq_bind, experiment_bind]
  exact prEvent_bind_le_truth_invalid_uniform_ae _ _ Good Admissible Success ε₁ δ ε₂ hprefix
    ((prEvent_mono _ _ _ fun _ h => h.2).trans hadmissible) hsuffix

/-- In the experiment, bound the success of an oracle run on an appended protocol by true
midpoints, false inadmissible midpoints, and the suffix error averaged over false admissible
midpoints. Midpoint truth and admissibility are predicates on the boundary and the ambient state;
they may use the materialized prefix payloads. The suffix premise is over the run resumed from
the boundary, including the end decision, and only holds almost everywhere. The verifier is
arbitrary, so this covers `OracleVerifier.append`. -/
theorem OracleVerifier.append_soundness_weighted_ae {s₁ : OracleProtocol}
    {s₂ : Path s₁ → OracleProtocol}
    {I : Type uI} {A : I → Type} {J : Path (s₁.append s₂) → Type}
    {B : (p : Path (s₁.append s₂)) → J p → Type}
    {inputs : OracleFamily.{uI, 0, wI} I A}
    {outputs : (p : Path (s₁.append s₂)) → OracleFamily.{0, 0, wJ} (J p) (B p)} {S : Type uS}
    {T : Path (s₁.append s₂) → Type}
    {Out : PathAlong oracleSig (s₁.append s₂) → Type}
    (V : OracleVerifier ambient (s₁.append s₂) S T inputs outputs) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec oracleSig (s₁.append s₂)) ProbComp) (stmt : S)
    (data : ∀ i, A i) (prover : Prover oracleSig ambient (s₁.append s₂) Out)
    (TruthMid Admissible : RunBoundary oracleSig ambient s₁ s₂ Out × σ → Prop)
    (Success : Observation oracleSig (s₁.append s₂) Out (OracleVerifier.Output T B) → Prop)
    (error : RunBoundary oracleSig ambient s₁ s₂ Out × σ → ℝ≥0∞) (εtruth εinvalid : ℝ≥0∞)
    (htruth : Pr{let b ← (experimentWithState init impl challenges
      (appendPrefixRun prover))}[TruthMid b] ≤ εtruth)
    (hinvalid : Pr{let b ← (experimentWithState init impl challenges
      (appendPrefixRun prover))}[¬ TruthMid b ∧ ¬ Admissible b] ≤ εinvalid)
    (hsuffix : letI : MeasurableSpace (RunBoundary oracleSig ambient s₁ s₂ Out × σ) := ⊤
      ∀ᵐ b ∂𝒟[experimentWithState init impl challenges (appendPrefixRun prover)],
        ¬ TruthMid b → Admissible b →
          Pr{let obs ← (experimentResume impl challenges b.2
            (V.suffixRun stmt data b.1))}[Success obs] ≤ error b) :
    letI : MeasurableSpace (RunBoundary oracleSig ambient s₁ s₂ Out × σ) := ⊤
    Pr{let obs ← experiment init impl challenges (V.run stmt data prover)}[Success obs] ≤
      εtruth + εinvalid + ∫⁻ b in {b | ¬ TruthMid b ∧ Admissible b}, error b
        ∂𝒟[experimentWithState init impl challenges (appendPrefixRun prover)] := by
  rw [V.run_eq_bind, experiment_bind]
  exact prEvent_bind_le_truth_invalid_ae _ _ TruthMid Admissible Success error εtruth εinvalid
    htruth hinvalid hsuffix

/-- A uniform suffix bound gives the sum of the truth, inadmissibility and suffix errors. -/
theorem OracleVerifier.append_soundness_ae {s₁ : OracleProtocol} {s₂ : Path s₁ → OracleProtocol}
    {I : Type uI} {A : I → Type} {J : Path (s₁.append s₂) → Type}
    {B : (p : Path (s₁.append s₂)) → J p → Type}
    {inputs : OracleFamily.{uI, 0, wI} I A}
    {outputs : (p : Path (s₁.append s₂)) → OracleFamily.{0, 0, wJ} (J p) (B p)} {S : Type uS}
    {T : Path (s₁.append s₂) → Type}
    {Out : PathAlong oracleSig (s₁.append s₂) → Type}
    (V : OracleVerifier ambient (s₁.append s₂) S T inputs outputs) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec oracleSig (s₁.append s₂)) ProbComp) (stmt : S)
    (data : ∀ i, A i) (prover : Prover oracleSig ambient (s₁.append s₂) Out)
    (TruthMid Admissible : RunBoundary oracleSig ambient s₁ s₂ Out × σ → Prop)
    (Success : Observation oracleSig (s₁.append s₂) Out (OracleVerifier.Output T B) → Prop)
    (εtruth εinvalid ε : ℝ≥0∞)
    (htruth : Pr{let b ← (experimentWithState init impl challenges
      (appendPrefixRun prover))}[TruthMid b] ≤ εtruth)
    (hinvalid : Pr{let b ← (experimentWithState init impl challenges
      (appendPrefixRun prover))}[¬ TruthMid b ∧ ¬ Admissible b] ≤ εinvalid)
    (hsuffix : letI : MeasurableSpace (RunBoundary oracleSig ambient s₁ s₂ Out × σ) := ⊤
      ∀ᵐ b ∂𝒟[experimentWithState init impl challenges (appendPrefixRun prover)],
        ¬ TruthMid b → Admissible b →
          Pr{let obs ← (experimentResume impl challenges b.2
            (V.suffixRun stmt data b.1))}[Success obs] ≤ ε) :
    Pr{let obs ← experiment init impl challenges (V.run stmt data prover)}[Success obs] ≤
      εtruth + εinvalid + ε := by
  rw [V.run_eq_bind, experiment_bind]
  exact prEvent_bind_le_truth_invalid_uniform_ae _ _ TruthMid Admissible Success εtruth
    εinvalid ε htruth hinvalid hsuffix

/-- The same bound for the oracle run program itself, under any lawful distribution semantics
of the full run interface. Midpoint predicates are on the boundary alone. -/
theorem OracleVerifier.run_append_soundness_weighted_ae {s₁ : OracleProtocol}
    {s₂ : Path s₁ → OracleProtocol}
    {I : Type uI} {A : I → Type} {J : Path (s₁.append s₂) → Type}
    {B : (p : Path (s₁.append s₂)) → J p → Type}
    {inputs : OracleFamily.{uI, 0, wI} I A}
    {outputs : (p : Path (s₁.append s₂)) → OracleFamily.{0, 0, wJ} (J p) (B p)} {S : Type uS}
    {T : Path (s₁.append s₂) → Type}
    {Out : PathAlong oracleSig (s₁.append s₂) → Type}
    [EvalDistSemantics (OracleComp (ambient + challengeSpec oracleSig (s₁.append s₂)))]
    [LawfulEvalDistSemantics (OracleComp (ambient + challengeSpec oracleSig (s₁.append s₂)))]
    (V : OracleVerifier ambient (s₁.append s₂) S T inputs outputs) (stmt : S)
    (data : ∀ i, A i) (prover : Prover oracleSig ambient (s₁.append s₂) Out)
    (TruthMid Admissible : RunBoundary oracleSig ambient s₁ s₂ Out → Prop)
    (Success : Observation oracleSig (s₁.append s₂) Out (OracleVerifier.Output T B) → Prop)
    (error : RunBoundary oracleSig ambient s₁ s₂ Out → ℝ≥0∞) (εtruth εinvalid : ℝ≥0∞)
    (htruth : Pr{let b ← appendPrefixRun prover}[TruthMid b] ≤ εtruth)
    (hinvalid : Pr{let b ← appendPrefixRun prover}[¬ TruthMid b ∧ ¬ Admissible b] ≤ εinvalid)
    (hsuffix : letI : MeasurableSpace (RunBoundary oracleSig ambient s₁ s₂ Out) := ⊤
      ∀ᵐ b ∂𝒟[appendPrefixRun prover], ¬ TruthMid b → Admissible b →
        Pr{let obs ← V.suffixRun stmt data b}[Success obs] ≤ error b) :
    letI : MeasurableSpace (RunBoundary oracleSig ambient s₁ s₂ Out) := ⊤
    Pr{let obs ← V.run stmt data prover}[Success obs] ≤
      εtruth + εinvalid + ∫⁻ b in {b | ¬ TruthMid b ∧ Admissible b}, error b
        ∂𝒟[appendPrefixRun prover] := by
  rw [V.run_eq_bind]
  exact prEvent_bind_le_truth_invalid_ae _ _ TruthMid Admissible Success error εtruth εinvalid
    htruth hinvalid hsuffix

/-- Runtime form: run the oracle program in a runtime that keeps hidden state and an ordered
trace. The boundary is the runtime's joint prefix result, and the premise is the resumed success
averaged over the non-exceptional boundaries. The whole prover is fixed before setup. -/
theorem OracleVerifier.append_soundness_runtime {s₁ : OracleProtocol}
    {s₂ : Path s₁ → OracleProtocol}
    {I : Type uI} {A : I → Type} {J : Path (s₁.append s₂) → Type}
    {B : (p : Path (s₁.append s₂)) → J p → Type}
    {inputs : OracleFamily.{uI, 0, wI} I A}
    {outputs : (p : Path (s₁.append s₂)) → OracleFamily.{0, 0, wJ} (J p) (B p)} {S : Type uS}
    {T : Path (s₁.append s₂) → Type}
    {Out : PathAlong oracleSig (s₁.append s₂) → Type} {κ : Type} {imports : OracleSpec κ}
    [EvalDistSemantics (OracleComp imports)] [LawfulEvalDistSemantics (OracleComp imports)]
    (runtime : OracleRuntime imports (ambient + challengeSpec oracleSig (s₁.append s₂)))
    (V : OracleVerifier ambient (s₁.append s₂) S T inputs outputs) (stmt : S)
    (data : ∀ i, A i) (prover : Prover oracleSig ambient (s₁.append s₂) Out)
    (Exceptional : RunResult runtime (RunBoundary oracleSig ambient s₁ s₂ Out) → Prop)
    (Success : Observation oracleSig (s₁.append s₂) Out (OracleVerifier.Output T B) → Prop)
    (error : RunResult runtime (RunBoundary oracleSig ambient s₁ s₂ Out) → ℝ≥0∞)
    (hsuffix : letI : MeasurableSpace (RunResult runtime
        (RunBoundary oracleSig ambient s₁ s₂ Out)) := ⊤
      (∫⁻ b in {b | ¬ Exceptional b},
        Pr{let result ← runtime.resume b (V.suffixRun stmt data)}[Success result.output]
          ∂𝒟[runtime.run (appendPrefixRun prover)]) ≤
        ∫⁻ b in {b | ¬ Exceptional b}, error b ∂𝒟[runtime.run (appendPrefixRun prover)]) :
    letI : MeasurableSpace (RunResult runtime (RunBoundary oracleSig ambient s₁ s₂ Out)) := ⊤
    Pr{let result ← runtime.run (V.run stmt data prover)}[Success result.output] ≤
      Pr{let b ← runtime.run (appendPrefixRun prover)}[Exceptional b] +
        ∫⁻ b in {b | ¬ Exceptional b}, error b ∂𝒟[runtime.run (appendPrefixRun prover)] := by
  rw [V.run_eq_bind]
  exact runtime.run_bind_success_le _ _ Exceptional Success error hsuffix

/-- Runtime form for a plain run on an appended protocol. -/
theorem Verifier.append_soundness_runtime {s₁ : Protocol} {s₂ : Path s₁ → Protocol}
    {S : Type uS} {T : Path (s₁.append s₂) → Type}
    {Out : PathAlong plainSig (s₁.append s₂) → Type} {κ : Type}
    {imports : OracleSpec κ}
    [EvalDistSemantics (OracleComp imports)] [LawfulEvalDistSemantics (OracleComp imports)]
    (runtime : OracleRuntime imports (ambient + challengeSpec plainSig (s₁.append s₂)))
    (V : Verifier ambient (s₁.append s₂) S T) (stmt : S)
    (prover : Prover plainSig ambient (s₁.append s₂) Out)
    (Exceptional : RunResult runtime (RunBoundary plainSig ambient s₁ s₂ Out) → Prop)
    (Success : Observation plainSig (s₁.append s₂) Out T → Prop)
    (error : RunResult runtime (RunBoundary plainSig ambient s₁ s₂ Out) → ℝ≥0∞)
    (hsuffix : letI : MeasurableSpace (RunResult runtime
        (RunBoundary plainSig ambient s₁ s₂ Out)) := ⊤
      (∫⁻ b in {b | ¬ Exceptional b},
        Pr{let result ← runtime.resume b (V.suffixRun stmt)}[Success result.output]
          ∂𝒟[runtime.run (appendPrefixRun prover)]) ≤
        ∫⁻ b in {b | ¬ Exceptional b}, error b ∂𝒟[runtime.run (appendPrefixRun prover)]) :
    letI : MeasurableSpace (RunResult runtime (RunBoundary plainSig ambient s₁ s₂ Out)) := ⊤
    Pr{let result ← runtime.run (V.run stmt prover)}[Success result.output] ≤
      Pr{let b ← runtime.run (appendPrefixRun prover)}[Exceptional b] +
        ∫⁻ b in {b | ¬ Exceptional b}, error b ∂𝒟[runtime.run (appendPrefixRun prover)] := by
  rw [V.run_eq_bind]
  exact runtime.run_bind_success_le _ _ Exceptional Success error hsuffix

end soundness

/-! ## Standalone suffix soundness

The corollaries below start from the suffix verifier's standalone soundness. Their one
hypothesis compares the verdict of the end-decided run with that of
`Verifier.boundaryDecidedRun`, which takes the prefix decision at the boundary. The hypothesis
holds when the prefix decision makes no ambient query and when the ambient implementation is
stateless.
-/



section standalone

variable {ι σ : Type} {ambient : OracleSpec ι}

/-- Answer the queries of a standalone prefix run from the run interface of the appended
protocol. -/
def prefixQueries (s₁ : Protocol.{0}) (s₂ : Path s₁ → Protocol) :
    QueryImpl (ambient + challengeSpec plainSig s₁)
      (OracleComp (ambient + challengeSpec plainSig (s₁.append s₂))) :=
  ((fun q => liftM ((ambient + challengeSpec plainSig (s₁.append s₂)).query (.inl q))) :
    QueryImpl ambient (OracleComp (ambient + challengeSpec plainSig (s₁.append s₂)))) +
  prefixDraw (m := OracleComp (ambient + challengeSpec plainSig (s₁.append s₂))) plainSig s₁ s₂
    (fun c => liftM ((ambient + challengeSpec plainSig (s₁.append s₂)).query (.inr c)))

/-- Answer the queries of a standalone suffix run from the run interface of the appended
protocol. -/
def suffixQueries (s₁ : Protocol.{0}) (s₂ : Path s₁ → Protocol) (p : Path s₁) :
    QueryImpl (ambient + challengeSpec plainSig (s₂ p))
      (OracleComp (ambient + challengeSpec plainSig (s₁.append s₂))) :=
  ((fun q => liftM ((ambient + challengeSpec plainSig (s₁.append s₂)).query (.inl q))) :
    QueryImpl ambient (OracleComp (ambient + challengeSpec plainSig (s₁.append s₂)))) +
  suffixDraw (m := OracleComp (ambient + challengeSpec plainSig (s₁.append s₂))) plainSig s₁ s₂
    (fun c => liftM ((ambient + challengeSpec plainSig (s₁.append s₂)).query (.inr c))) p

/-- The run of `V₁.append V₂` with the prefix decision taken at the boundary: the standalone
run of `V₁` against the split prover, then the standalone run of `V₂` against the returned
continuation, on the accepted intermediate statement. Queries go to the run interface of the
appended protocol. -/
def Verifier.boundaryDecidedRun {s₁ : Protocol} {s₂ : Path s₁ → Protocol} {S : Type uS} {T U : Type}
    {Out : PathAlong plainSig (s₁.append s₂) → Type}
    (V₁ : Verifier ambient s₁ S (fun _ => T))
    (V₂ : (p : Path s₁) → Verifier ambient (s₂ p) T (fun _ => U))
    (stmt : S) (prover : Prover plainSig ambient (s₁.append s₂) Out) :
    OracleComp (ambient + challengeSpec plainSig (s₁.append s₂))
      (Observation plainSig (s₁.append s₂) Out (fun _ => U)) := do
  let o ← simulateQ (prefixQueries s₁ s₂) (V₁.run stmt (Focal.splitPrefix prover))
  let r ← simulateQ (suffixQueries s₁ s₂ (projectPathAlong plainSig s₁ o.1))
    ((V₂ _).onAccept.run o.2.2 o.2.1)
  pure ⟨PathAlong.append plainSig s₁ s₂ o.1 r.1, r.2.1, r.2.2⟩

section transfer
variable {κ κ₁ : Type} {chal : OracleSpec κ} {chal₁ : OracleSpec κ₁} {α : Type}

/-- An experiment over a program whose queries are rewritten keeps its law when the rewritten
queries mean the same in both experiments. -/
theorem experimentWithState_simulateQ (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp)) (ch : QueryImpl chal ProbComp)
    (ch₁ : QueryImpl chal₁ ProbComp) (G : QueryImpl (ambient + chal₁) (OracleComp (ambient + chal)))
    (hG : ∀ t, simulateQ (QueryImpl.addLift impl ch : QueryImpl _ (StateT σ ProbComp)) (G t) =
      (QueryImpl.addLift impl ch₁ : QueryImpl _ (StateT σ ProbComp)) t)
    (x : OracleComp (ambient + chal₁) α) :
    experimentWithState init impl ch (simulateQ G x) = experimentWithState init impl ch₁ x := by
  simp only [experimentWithState, QueryImpl.simulateQ_simulateQ_eq_of_apply hG]

/-- Resuming a program whose queries are rewritten from a state is the experiment started in
that state, when the rewritten queries mean the same in both experiments. -/
theorem experimentResume_simulateQ
    (impl : QueryImpl ambient (StateT σ ProbComp)) (ch : QueryImpl chal ProbComp)
    (ch₁ : QueryImpl chal₁ ProbComp) (G : QueryImpl (ambient + chal₁) (OracleComp (ambient + chal)))
    (hG : ∀ t, simulateQ (QueryImpl.addLift impl ch : QueryImpl _ (StateT σ ProbComp)) (G t) =
      (QueryImpl.addLift impl ch₁ : QueryImpl _ (StateT σ ProbComp)) t)
    (state : σ) (x : OracleComp (ambient + chal₁) α) :
    experimentResume impl ch state (simulateQ G x) = experiment (pure state) impl ch₁ x := by
  simp only [experimentResume, experiment, QueryImpl.simulateQ_simulateQ_eq_of_apply hG]
  exact (LawfulMonad.pure_bind _ _).symm

end transfer

/-- The prefix queries of the appended interface mean the restricted challenge draws. -/
theorem simulateQ_prefixQueries {s₁ : Protocol} {s₂ : Path s₁ → Protocol}
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (ch : QueryImpl (challengeSpec plainSig (s₁.append s₂)) ProbComp)
    (t : (ambient + challengeSpec plainSig s₁).Domain) :
    simulateQ (QueryImpl.addLift impl ch : QueryImpl _ (StateT σ ProbComp))
      (prefixQueries s₁ s₂ t) =
      (QueryImpl.addLift impl (prefixDraw plainSig s₁ s₂ ch) :
        QueryImpl _ (StateT σ ProbComp)) t := by
  rcases t with q | c
  · simp only [prefixQueries, QueryImpl.add_apply_inl, simulateQ_spec_query]
    rfl
  · simp only [prefixQueries, QueryImpl.add_apply_inr]
    rw [← prefixDraw_comp plainSig (m' := StateT σ ProbComp)
      (fun x => simulateQ (QueryImpl.addLift impl ch : QueryImpl _ (StateT σ ProbComp)) x)]
    simp only [simulateQ_spec_query, QueryImpl.addLift_def, QueryImpl.add_apply_inr,
      QueryImpl.liftTarget_apply]
    exact prefixDraw_comp plainSig (fun x => liftM x) s₁ s₂ ch c

/-- The suffix queries of the appended interface mean the restricted challenge draws. -/
theorem simulateQ_suffixQueries {s₁ : Protocol} {s₂ : Path s₁ → Protocol}
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (ch : QueryImpl (challengeSpec plainSig (s₁.append s₂)) ProbComp) (p : Path s₁)
    (t : (ambient + challengeSpec plainSig (s₂ p)).Domain) :
    simulateQ (QueryImpl.addLift impl ch : QueryImpl _ (StateT σ ProbComp))
      (suffixQueries s₁ s₂ p t) =
      (QueryImpl.addLift impl (suffixDraw plainSig s₁ s₂ ch p) :
        QueryImpl _ (StateT σ ProbComp)) t := by
  rcases t with q | c
  · simp only [suffixQueries, QueryImpl.add_apply_inl, simulateQ_spec_query]
    rfl
  · simp only [suffixQueries, QueryImpl.add_apply_inr]
    rw [← suffixDraw_comp plainSig (m' := StateT σ ProbComp)
      (fun x => simulateQ (QueryImpl.addLift impl ch : QueryImpl _ (StateT σ ProbComp)) x)]
    simp only [simulateQ_spec_query, QueryImpl.addLift_def, QueryImpl.add_apply_inr,
      QueryImpl.liftTarget_apply]
    exact suffixDraw_comp plainSig (fun x => liftM x) s₁ s₂ ch p c

/-- A run of `V₁.append V₂` is the prefix interaction, the suffix interaction against the
returned continuation, the prefix decision, and the suffix decision on its result. -/
theorem Verifier.append_run_eq {s₁ : Protocol} {s₂ : Path s₁ → Protocol} {S : Type uS} {T U : Type}
    {Out : PathAlong plainSig (s₁.append s₂) → Type}
    (V₁ : Verifier ambient s₁ S (fun _ => T))
    (V₂ : (p : Path s₁) → Verifier ambient (s₂ p) T (fun _ => U))
    (stmt : S) (prover : Prover plainSig ambient (s₁.append s₂) Out) :
    let full := ambient + challengeSpec plainSig (s₁.append s₂)
    let toFull : QueryImpl ambient (OracleComp full) := fun q => liftM (full.query (.inl q))
    let draw : (c : ChallengeNode plainSig (s₁.append s₂)) →
        OracleComp full (challengeSpec plainSig (s₁.append s₂) c) :=
      fun c => liftM (full.query (.inr c))
    (V₁.append V₂).run stmt prover = (do
      let o ← TwoParty.Lens.run s₁ (Prover.simulate toFull (Focal.splitPrefix prover))
        (sampler plainSig s₁ (prefixDraw plainSig s₁ s₂ draw))
      let r ← TwoParty.Lens.run _ (Prover.simulate toFull o.2.1)
        (sampler plainSig _ (suffixDraw plainSig s₁ s₂ draw (projectPathAlong plainSig s₁ o.1)))
      let mid ← liftComp (V₁.decide stmt (projectPathAlong plainSig s₁ o.1)
        (toPlainView s₁ o.1)).run full
      let v ← liftComp ((V₂ _).onAccept.decide mid (projectPathAlong plainSig _ r.1)
        (toPlainView _ r.1)).run full
      pure ⟨PathAlong.append plainSig s₁ s₂ o.1 r.1, r.2.1, v⟩) := by
  intro full toFull draw
  rw [Verifier.run_eq_bind, appendPrefixRun, splitPrefix_simulate]
  conv_lhs => rw [← Strategy.mapOutput_id (sampler plainSig s₁ _), run_mapOutput_mapOutput]
  rw [bind_assoc]
  refine bind_congr fun o => ?_
  rcases o with ⟨tr₁, k, ⟨⟩⟩
  erw [LawfulMonad.pure_bind]
  simp only [Verifier.suffixRun]
  refine bind_congr fun r => ?_
  rcases r with ⟨tail, out, ⟨⟩⟩
  have hd : ((V₁.append V₂).decide stmt
      (projectPathAlong plainSig _ (PathAlong.append plainSig s₁ s₂ tr₁ tail))
      (toPlainView _ (PathAlong.append plainSig s₁ s₂ tr₁ tail))).run =
      (V₁.decide stmt (projectPathAlong plainSig s₁ tr₁) (toPlainView s₁ tr₁) >>= fun mid =>
        (V₂ _).decide mid (projectPathAlong plainSig _ tail) (toPlainView _ tail)).run := by
    rw [Verifier.append_decide]
    exact splitFiber_append plainSig s₁ s₂
      (fun p q v₁ v₂ => (V₁.decide stmt p v₁ >>= fun mid => (V₂ p).decide mid q v₂).run) tr₁ tail
  dsimp only
  rw [hd]
  simp only [OptionT.run_bind, Verifier.onAccept, Option.elimM, liftComp_bind, bind_assoc]
  refine bind_congr fun mid => ?_
  cases mid <;> rfl

/-- A lifted ambient program keeps its ambient queries when the challenge queries are
rerouted. -/
theorem simulateQ_liftComp_inl {κ κ' : Type} {chal : OracleSpec κ} {chal' : OracleSpec κ'}
    (G : QueryImpl chal (OracleComp (ambient + chal'))) {α : Type} (x : OracleComp ambient α) :
    simulateQ (((fun q => liftM ((ambient + chal').query (.inl q))) :
        QueryImpl ambient (OracleComp (ambient + chal'))) + G) (liftComp x (ambient + chal)) =
      liftComp x (ambient + chal') := by
  rw [QueryImpl.simulateQ_add_liftComp_left]
  rfl

/-- The boundary-decided run is the prefix interaction, the prefix decision, the suffix
interaction against the returned continuation, and the suffix decision on its result. -/
theorem Verifier.boundaryDecidedRun_eq {s₁ : Protocol} {s₂ : Path s₁ → Protocol} {S : Type uS}
    {T U : Type}
    {Out : PathAlong plainSig (s₁.append s₂) → Type}
    (V₁ : Verifier ambient s₁ S (fun _ => T))
    (V₂ : (p : Path s₁) → Verifier ambient (s₂ p) T (fun _ => U))
    (stmt : S) (prover : Prover plainSig ambient (s₁.append s₂) Out) :
    let full := ambient + challengeSpec plainSig (s₁.append s₂)
    let toFull : QueryImpl ambient (OracleComp full) := fun q => liftM (full.query (.inl q))
    let draw : (c : ChallengeNode plainSig (s₁.append s₂)) →
        OracleComp full (challengeSpec plainSig (s₁.append s₂) c) :=
      fun c => liftM (full.query (.inr c))
    Verifier.boundaryDecidedRun V₁ V₂ stmt prover = (do
      let o ← TwoParty.Lens.run s₁ (Prover.simulate toFull (Focal.splitPrefix prover))
        (sampler plainSig s₁ (prefixDraw plainSig s₁ s₂ draw))
      let mid ← liftComp (V₁.decide stmt (projectPathAlong plainSig s₁ o.1)
        (toPlainView s₁ o.1)).run full
      let r ← TwoParty.Lens.run _ (Prover.simulate toFull o.2.1)
        (sampler plainSig _ (suffixDraw plainSig s₁ s₂ draw (projectPathAlong plainSig s₁ o.1)))
      let v ← liftComp ((V₂ _).onAccept.decide mid (projectPathAlong plainSig _ r.1)
        (toPlainView _ r.1)).run full
      pure ⟨PathAlong.append plainSig s₁ s₂ o.1 r.1, r.2.1, v⟩) := by
  intro full toFull draw
  simp only [Verifier.boundaryDecidedRun, Verifier.run, simulateQ_bind, simulateQ_pure, bind_assoc]
  rw [simulateQ_run_simulate_sampler]
  simp only [simulateQ_spec_query, prefixQueries, suffixQueries, QueryImpl.add_apply_inl,
    QueryImpl.add_apply_inr, simulateQ_liftComp_inl]
  refine bind_congr fun o => ?_
  refine bind_congr fun mid => ?_
  erw [LawfulMonad.pure_bind]
  rw [simulateQ_run_simulate_sampler]
  simp only [simulateQ_spec_query, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
  refine bind_congr fun r => ?_
  refine bind_congr fun v => ?_
  erw [LawfulMonad.pure_bind]

/-- A prefix decision without ambient queries may be taken at the boundary: the two runs are
equal. -/
theorem Verifier.boundaryDecidedRun_eq_of_pure {s₁ : Protocol} {s₂ : Path s₁ → Protocol}
    {S : Type uS} {T U : Type} {Out : PathAlong plainSig (s₁.append s₂) → Type}
    (V₁ : Verifier ambient s₁ S (fun _ => T))
    (V₂ : (p : Path s₁) → Verifier ambient (s₂ p) T (fun _ => U))
    (stmt : S) (prover : Prover plainSig ambient (s₁.append s₂) Out)
    (hpure : ∀ p v, ∃ r, (V₁.decide stmt p v).run = pure r) :
    (V₁.append V₂).run stmt prover = Verifier.boundaryDecidedRun V₁ V₂ stmt prover := by
  rw [Verifier.append_run_eq, Verifier.boundaryDecidedRun_eq]
  refine bind_congr fun o => ?_
  obtain ⟨r, hr⟩ := hpure (projectPathAlong plainSig s₁ o.1) (toPlainView s₁ o.1)
  rw [hr, liftComp_pure]
  erw [LawfulMonad.pure_bind]
  refine bind_congr fun x => ?_
  erw [LawfulMonad.pure_bind]

/-- With a stateless ambient implementation the prefix decision may be taken at the boundary:
the two experiments are equal in distribution. -/
theorem Verifier.boundaryDecidedRun_evalDistEq_of_stateless
    {s₁ : Protocol} {s₂ : Path s₁ → Protocol}
    {S : Type uS} {T U : Type} {Out : PathAlong plainSig (s₁.append s₂) → Type}
    (V₁ : Verifier ambient s₁ S (fun _ => T))
    (V₂ : (p : Path s₁) → Verifier ambient (s₂ p) T (fun _ => U))
    (stmt : S) (prover : Prover plainSig ambient (s₁.append s₂) Out)
    (init : ProbComp σ) (g : QueryImpl ambient ProbComp)
    (challenges : QueryImpl (challengeSpec plainSig (s₁.append s₂)) ProbComp) :
    experiment init (g.liftTarget (StateT σ ProbComp)) challenges
        ((V₁.append V₂).run stmt prover) =ᵈ
      experiment init (g.liftTarget (StateT σ ProbComp)) challenges
        (Verifier.boundaryDecidedRun V₁ V₂ stmt prover) := by
  rw [Verifier.append_run_eq, Verifier.boundaryDecidedRun_eq, experiment_bind, experiment_bind]
  refine EvalDistEq.bind (EvalDistEq.refl _) fun b => ?_
  simp only [experimentResume, simulateQ_bind, QueryImpl.addLift_def,
    QueryImpl.simulateQ_add_liftComp_left, QueryImpl.liftTarget_self, simulateQ_liftTarget]
  have hswap : ∀ {α β γ : Type} (Y : StateT σ ProbComp β) (A : ProbComp α)
      (Z : β → α → StateT σ ProbComp γ) (state : σ),
      (Y >>= fun r => (liftM A : StateT σ ProbComp α) >>= fun a => Z r a).run' state =ᵈ
        ((liftM A : StateT σ ProbComp α) >>= fun a => Y >>= fun r => Z r a).run' state := by
    intro α β γ Y A Z state
    simp only [StateT.run'_eq, StateT.run_bind, liftM, monadLift, MonadLift.monadLift,
      StateT.run_lift, bind_assoc]
    exact (EvalDistEq.bind_bind_swap (Y.run state) A
      (fun p a => (Z p.1 a).run p.2)).map Prod.fst
  exact hswap _ _ _ _

/-- Composition soundness from the suffix verifier's standalone soundness. The one hypothesis
`hreorder` states that taking the prefix decision at the boundary leaves the law of the final
verdict unchanged; the transcript and the prover output may change in law. A full-observation
equality implies it (`Verifier.append_soundness_of_standalone_of_evalDistEq`), and so do a
prefix decision without ambient queries (`Verifier.append_soundness_of_standalone_of_pure`) and a
stateless ambient implementation (`Verifier.append_soundness_of_standalone_of_stateless`). `ε₁`
bounds the standalone prefix run accepting a true intermediate statement, `δ` bounds it
accepting an inadmissible one, and every suffix verifier is sound with error `ε₂` from every
ambient state. -/
theorem Verifier.append_soundness_of_standalone {s₁ : Protocol} {s₂ : Path s₁ → Protocol}
    {S : Type uS} {T U : Type} {Out : PathAlong plainSig (s₁.append s₂) → Type}
    (V₁ : Verifier ambient s₁ S (fun _ => T))
    (V₂ : (p : Path s₁) → Verifier ambient (s₂ p) T (fun _ => U))
    (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec plainSig (s₁.append s₂)) ProbComp)
    (middle : StatementProblem T) (output : StatementProblem U) (stmt : S)
    (prover : Prover plainSig ambient (s₁.append s₂) Out) (ε₁ δ ε₂ : ℝ≥0∞)
    (hreorder : (fun obs => obs.2.2) <$>
        experiment init impl challenges ((V₁.append V₂).run stmt prover) =ᵈ
      (fun obs => obs.2.2) <$>
        experiment init impl challenges (Verifier.boundaryDecidedRun V₁ V₂ stmt prover))
    (hprefix : Pr{let o ← (experiment init impl (prefixDraw plainSig s₁ s₂ challenges)
      (V₁.run stmt (Focal.splitPrefix prover)))}[∃ t, o.2.2 = some t ∧ middle.language () t] ≤ ε₁)
    (hadmissible : Pr{let o ← (experiment init impl (prefixDraw plainSig s₁ s₂ challenges)
      (V₁.run stmt (Focal.splitPrefix prover)))}[∃ t, o.2.2 = some t ∧
        ¬ middle.admissible () t] ≤ δ)
    (hsuffix : ∀ p state (Out : PathAlong plainSig (s₂ p) → Type),
      letI : MeasurableSpace (Observation plainSig (s₂ p) Out (fun _ => U)) := ⊤
      Core.soundness ((V₂ p).classicalModel (Out := Out) (pure state) impl
        (suffixDraw plainSig s₁ s₂ challenges p)) middle output
        (fun _ => ()) (fun obs => obs.2.2) ε₂) :
    Pr{let obs ← (experiment init impl challenges ((V₁.append V₂).run stmt prover))}[
      ∃ u, obs.2.2 = some u ∧ output.language () u] ≤ ε₁ + δ + ε₂ := by
  have hfst : ∀ {α κ : Type} {chal : OracleSpec κ} (ch : QueryImpl chal ProbComp)
      (x : OracleComp (ambient + chal) α),
      experiment init impl ch x = Prod.fst <$> experimentWithState init impl ch x := by
    intro α κ chal ch x
    simp only [experiment, experimentWithState, StateT.run'_eq, _root_.map_bind]
  have hverdict := hreorder.prEvent_eq (fun v => ∃ u, v = some u ∧ output.language () u)
  rw [prEvent_map, prEvent_map] at hverdict
  rw [hverdict, Verifier.boundaryDecidedRun, experiment_bind,
    experimentWithState_simulateQ init impl challenges _ _
      (simulateQ_prefixQueries impl challenges)]
  refine prEvent_bind_le_truth_invalid_uniform_ae _ _
    (fun b => ∃ t, b.1.2.2 = some t ∧ middle.language () t)
    (fun b => ∀ t, b.1.2.2 = some t → middle.admissible () t) _ ε₁ δ ε₂ ?_ ?_ ?_
  · rw [hfst, prEvent_map] at hprefix
    exact hprefix
  · rw [hfst, prEvent_map] at hadmissible
    refine (prEvent_mono _ _ _ fun b h => ?_).trans hadmissible
    simpa only [not_forall, exists_prop] using h.2
  · refine ae_of_all _ fun b hnot hadm => ?_
    rcases b with ⟨⟨tr₁, next, mid⟩, state⟩
    have hres : ∀ {α β : Type} (f : α → β) (x : OracleComp _ α),
        experimentResume impl challenges state (x >>= fun a => pure (f a)) =
          f <$> experimentResume impl challenges state x := by
      intro α β f x
      rw [show (x >>= fun a => pure (f a)) = f <$> x from (map_eq_bind_pure_comp _ f x).symm]
      simp only [experimentResume, simulateQ_map, StateT.run'_eq, StateT.run_map,
        Functor.map_map]
    dsimp only at hnot hadm ⊢
    rw [hres, prEvent_map, experimentResume_simulateQ impl challenges _ _
      (simulateQ_suffixQueries impl challenges _)]
    cases mid with
    | none =>
      rw [Verifier.onAccept_run_none, experiment_map, prEvent_map]
      simp
    | some t =>
      rw [Verifier.onAccept_run_some]
      have h := hsuffix (projectPathAlong plainSig s₁ tr₁) state
        (fun tail => Out (PathAlong.append plainSig s₁ s₂ tr₁ tail)) t (hadm t rfl)
        (fun hl => hnot ⟨t, rfl, hl⟩) next
      let : MeasurableSpace (Observation plainSig (s₂ (projectPathAlong plainSig s₁ tr₁))
        (fun tail => Out (PathAlong.append plainSig s₁ s₂ tr₁ tail)) (fun _ => U)) := ⊤
      rw [prEvent_eq_evalDist _ _ (measurable_from_top)]
      exact h

/-- Composition soundness from standalone suffix soundness, when taking the prefix decision at
the boundary leaves the law of the whole observation unchanged. -/
theorem Verifier.append_soundness_of_standalone_of_evalDistEq {s₁ : Protocol}
    {s₂ : Path s₁ → Protocol} {S : Type uS} {T U : Type}
    {Out : PathAlong plainSig (s₁.append s₂) → Type}
    (V₁ : Verifier ambient s₁ S (fun _ => T))
    (V₂ : (p : Path s₁) → Verifier ambient (s₂ p) T (fun _ => U))
    (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec plainSig (s₁.append s₂)) ProbComp)
    (middle : StatementProblem T) (output : StatementProblem U) (stmt : S)
    (prover : Prover plainSig ambient (s₁.append s₂) Out) (ε₁ δ ε₂ : ℝ≥0∞)
    (hreorder : experiment init impl challenges ((V₁.append V₂).run stmt prover) =ᵈ
      experiment init impl challenges (Verifier.boundaryDecidedRun V₁ V₂ stmt prover))
    (hprefix : Pr{let o ← (experiment init impl (prefixDraw plainSig s₁ s₂ challenges)
      (V₁.run stmt (Focal.splitPrefix prover)))}[∃ t, o.2.2 = some t ∧ middle.language () t] ≤ ε₁)
    (hadmissible : Pr{let o ← (experiment init impl (prefixDraw plainSig s₁ s₂ challenges)
      (V₁.run stmt (Focal.splitPrefix prover)))}[∃ t, o.2.2 = some t ∧
        ¬ middle.admissible () t] ≤ δ)
    (hsuffix : ∀ p state (Out : PathAlong plainSig (s₂ p) → Type),
      letI : MeasurableSpace (Observation plainSig (s₂ p) Out (fun _ => U)) := ⊤
      Core.soundness ((V₂ p).classicalModel (Out := Out) (pure state) impl
        (suffixDraw plainSig s₁ s₂ challenges p)) middle output
        (fun _ => ()) (fun obs => obs.2.2) ε₂) :
    Pr{let obs ← (experiment init impl challenges ((V₁.append V₂).run stmt prover))}[
      ∃ u, obs.2.2 = some u ∧ output.language () u] ≤ ε₁ + δ + ε₂ :=
  Verifier.append_soundness_of_standalone V₁ V₂ init impl challenges middle output stmt prover
    ε₁ δ ε₂ (hreorder.map _) hprefix hadmissible hsuffix

/-- A prefix decision without ambient queries composes with a standalone-sound suffix at
`ε₁ + δ + ε₂`. -/
theorem Verifier.append_soundness_of_standalone_of_pure {s₁ : Protocol}
    {s₂ : Path s₁ → Protocol} {S : Type uS} {T U : Type}
    {Out : PathAlong plainSig (s₁.append s₂) → Type}
    (V₁ : Verifier ambient s₁ S (fun _ => T))
    (V₂ : (p : Path s₁) → Verifier ambient (s₂ p) T (fun _ => U))
    (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec plainSig (s₁.append s₂)) ProbComp)
    (middle : StatementProblem T) (output : StatementProblem U) (stmt : S)
    (prover : Prover plainSig ambient (s₁.append s₂) Out) (ε₁ δ ε₂ : ℝ≥0∞)
    (hpure : ∀ p v, ∃ r, (V₁.decide stmt p v).run = pure r)
    (hprefix : Pr{let o ← (experiment init impl (prefixDraw plainSig s₁ s₂ challenges)
      (V₁.run stmt (Focal.splitPrefix prover)))}[∃ t, o.2.2 = some t ∧ middle.language () t] ≤ ε₁)
    (hadmissible : Pr{let o ← (experiment init impl (prefixDraw plainSig s₁ s₂ challenges)
      (V₁.run stmt (Focal.splitPrefix prover)))}[∃ t, o.2.2 = some t ∧
        ¬ middle.admissible () t] ≤ δ)
    (hsuffix : ∀ p state (Out : PathAlong plainSig (s₂ p) → Type),
      letI : MeasurableSpace (Observation plainSig (s₂ p) Out (fun _ => U)) := ⊤
      Core.soundness ((V₂ p).classicalModel (Out := Out) (pure state) impl
        (suffixDraw plainSig s₁ s₂ challenges p)) middle output
        (fun _ => ()) (fun obs => obs.2.2) ε₂) :
    Pr{let obs ← (experiment init impl challenges ((V₁.append V₂).run stmt prover))}[
      ∃ u, obs.2.2 = some u ∧ output.language () u] ≤ ε₁ + δ + ε₂ :=
  Verifier.append_soundness_of_standalone V₁ V₂ init impl challenges middle output stmt prover
    ε₁ δ ε₂ (Verifier.boundaryDecidedRun_eq_of_pure V₁ V₂ stmt prover hpure ▸ .refl _) hprefix
    hadmissible hsuffix

/-- Under a stateless ambient implementation any prefix verifier composes with a standalone-sound
suffix at `ε₁ + δ + ε₂`. -/
theorem Verifier.append_soundness_of_standalone_of_stateless {s₁ : Protocol}
    {s₂ : Path s₁ → Protocol} {S : Type uS} {T U : Type}
    {Out : PathAlong plainSig (s₁.append s₂) → Type}
    (V₁ : Verifier ambient s₁ S (fun _ => T))
    (V₂ : (p : Path s₁) → Verifier ambient (s₂ p) T (fun _ => U))
    (init : ProbComp σ) (g : QueryImpl ambient ProbComp)
    (challenges : QueryImpl (challengeSpec plainSig (s₁.append s₂)) ProbComp)
    (middle : StatementProblem T) (output : StatementProblem U) (stmt : S)
    (prover : Prover plainSig ambient (s₁.append s₂) Out) (ε₁ δ ε₂ : ℝ≥0∞)
    (hprefix : Pr{let o ← (experiment init (g.liftTarget (StateT σ ProbComp))
      (prefixDraw plainSig s₁ s₂ challenges) (V₁.run stmt (Focal.splitPrefix prover)))}[∃ t,
        o.2.2 = some t ∧ middle.language () t] ≤ ε₁)
    (hadmissible : Pr{let o ← (experiment init (g.liftTarget (StateT σ ProbComp))
      (prefixDraw plainSig s₁ s₂ challenges) (V₁.run stmt (Focal.splitPrefix prover)))}[∃ t,
        o.2.2 = some t ∧ ¬ middle.admissible () t] ≤ δ)
    (hsuffix : ∀ p state (Out : PathAlong plainSig (s₂ p) → Type),
      letI : MeasurableSpace (Observation plainSig (s₂ p) Out (fun _ => U)) := ⊤
      Core.soundness ((V₂ p).classicalModel (Out := Out) (pure state)
        (g.liftTarget (StateT σ ProbComp))
        (suffixDraw plainSig s₁ s₂ challenges p)) middle output
        (fun _ => ()) (fun obs => obs.2.2) ε₂) :
    Pr{let obs ← (experiment init (g.liftTarget (StateT σ ProbComp)) challenges
      ((V₁.append V₂).run stmt prover))}[∃ u, obs.2.2 = some u ∧ output.language () u] ≤
        ε₁ + δ + ε₂ :=
  Verifier.append_soundness_of_standalone_of_evalDistEq V₁ V₂ init _ challenges middle output
    stmt prover ε₁ δ ε₂ (Verifier.boundaryDecidedRun_evalDistEq_of_stateless V₁ V₂ stmt prover
      init g challenges) hprefix hadmissible hsuffix

end standalone

end Interaction.Core
