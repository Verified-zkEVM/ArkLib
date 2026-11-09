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

A corollary starts from the suffix verifier's standalone soundness. Because the prefix decision
runs after the suffix interaction, it takes one explicit hypothesis: taking the prefix decision at
the boundary leaves the law of the run unchanged. The hypothesis holds for a prefix decision
without ambient queries and for a stateless ambient implementation. Inadmissible intermediate
statements are charged `δ`, giving `ε₁ + δ + ε₂`.
-/

@[expose] public section

universe u uA

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

/-- The sampler of an appended plain protocol is the append of its restricted samplers. -/
theorem plainSampler_append_eq {m : Type u → Type u} [Monad m] [LawfulMonad m]
    (s₁ : Protocol.{u}) (s₂ : Path s₁ → Protocol.{u})
    (draw : (c : ChallengeNode plainSig (s₁.append s₂)) →
      m (challengeSpec plainSig (s₁.append s₂) c)) :
    sampler plainSig (s₁.append s₂) draw = appendSampler s₁ s₂
      (prefixDraw plainSig s₁ s₂ draw) (suffixDraw plainSig s₁ s₂ draw) := by
  rw [appendSampler_eq, combineDraw_prefixDraw_suffixDraw]

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
def Verifier.suffixRun {s₁ : Protocol.{u}} {s₂ : Path s₁ → Protocol.{u}} {S T : Type u}
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
theorem Verifier.run_eq_bind {s₁ : Protocol.{u}} {s₂ : Path s₁ → Protocol.{u}} {S T : Type u}
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
def OracleVerifier.suffixRun {I J : Type u} {A : I → Type u} {B : J → Type u}
    {inputs : OracleFamily.{u, u, u} I A} {outputs : OracleFamily.{u, u, u} J B}
    {s₁ : OracleProtocol.{u}} {s₂ : Path s₁ → OracleProtocol.{u}} {S T : Type u}
    {Out : PathAlong oracleSig (s₁.append s₂) → Type u}
    (V : OracleVerifier ambient (s₁.append s₂) S T inputs outputs) (stmt : S)
    (data : ∀ i, A i)
    (b : RunBoundary oracleSig ambient s₁ s₂ Out) :
    OracleComp (ambient + challengeSpec oracleSig (s₁.append s₂))
      (Observation oracleSig (s₁.append s₂) Out (T × (∀ j, B j))) := do
  let ⟨tail, out, _⟩ ← TwoParty.Lens.run _ b.2.1
    (sampler oracleSig _ (suffixDraw oracleSig s₁ s₂
      (fun c => liftM ((ambient + challengeSpec oracleSig (s₁.append s₂)).query (.inr c)))
      (projectPathAlong oracleSig s₁ b.1)))
  let tr := PathAlong.append oracleSig s₁ s₂ b.1 tail
  let p := projectPathAlong oracleSig _ tr
  let view := toView _ tr
  let resources := sumData data (payloads _ tr)
  let verdict ← simulateQ
    (QueryImpl.addLift
      ((fun q => liftM ((ambient + challengeSpec oracleSig (s₁.append s₂)).query (.inl q))) :
        QueryImpl ambient (OracleComp (ambient + challengeSpec oracleSig (s₁.append s₂))))
      ((sumFamily inputs (pathFamily _ p)).behaviorOfRealizations resources))
    (V.decide stmt p view).run
  pure ⟨tr, out, verdict.map fun t => (t, (V.outputMap stmt p view).f resources)⟩

/-- An oracle run on an appended protocol is its prefix interaction followed by the rest of the
run at the actual boundary. The verifier is arbitrary, so this covers `OracleVerifier.append`;
`OracleVerifier.run_append` describes the rest of that run. -/
theorem OracleVerifier.run_eq_bind {I J : Type u} {A : I → Type u} {B : J → Type u}
    {inputs : OracleFamily.{u, u, u} I A} {outputs : OracleFamily.{u, u, u} J B}
    {s₁ : OracleProtocol.{u}} {s₂ : Path s₁ → OracleProtocol.{u}} {S T : Type u}
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
    {S T : Type} {Out : PathAlong plainSig (s₁.append s₂) → Type}
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
    {S T : Type} {Out : PathAlong plainSig (s₁.append s₂) → Type}
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
theorem OracleVerifier.append_soundness_weighted_ae {I J : Type} {A : I → Type}
    {B : J → Type} {inputs : OracleFamily I A} {outputs : OracleFamily J B}
    {s₁ : OracleProtocol} {s₂ : Path s₁ → OracleProtocol} {S T : Type}
    {Out : PathAlong oracleSig (s₁.append s₂) → Type}
    (V : OracleVerifier ambient (s₁.append s₂) S T inputs outputs) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec oracleSig (s₁.append s₂)) ProbComp) (stmt : S)
    (data : ∀ i, A i) (prover : Prover oracleSig ambient (s₁.append s₂) Out)
    (TruthMid Admissible : RunBoundary oracleSig ambient s₁ s₂ Out × σ → Prop)
    (Success : Observation oracleSig (s₁.append s₂) Out (T × (∀ j, B j)) → Prop)
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
theorem OracleVerifier.append_soundness_ae {I J : Type} {A : I → Type}
    {B : J → Type} {inputs : OracleFamily I A} {outputs : OracleFamily J B}
    {s₁ : OracleProtocol} {s₂ : Path s₁ → OracleProtocol} {S T : Type}
    {Out : PathAlong oracleSig (s₁.append s₂) → Type}
    (V : OracleVerifier ambient (s₁.append s₂) S T inputs outputs) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec oracleSig (s₁.append s₂)) ProbComp) (stmt : S)
    (data : ∀ i, A i) (prover : Prover oracleSig ambient (s₁.append s₂) Out)
    (TruthMid Admissible : RunBoundary oracleSig ambient s₁ s₂ Out × σ → Prop)
    (Success : Observation oracleSig (s₁.append s₂) Out (T × (∀ j, B j)) → Prop)
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
theorem OracleVerifier.run_append_soundness_weighted_ae {I J : Type} {A : I → Type}
    {B : J → Type} {inputs : OracleFamily I A} {outputs : OracleFamily J B}
    {s₁ : OracleProtocol} {s₂ : Path s₁ → OracleProtocol} {S T : Type}
    {Out : PathAlong oracleSig (s₁.append s₂) → Type}
    [EvalDistSemantics (OracleComp (ambient + challengeSpec oracleSig (s₁.append s₂)))]
    [LawfulEvalDistSemantics (OracleComp (ambient + challengeSpec oracleSig (s₁.append s₂)))]
    (V : OracleVerifier ambient (s₁.append s₂) S T inputs outputs) (stmt : S)
    (data : ∀ i, A i) (prover : Prover oracleSig ambient (s₁.append s₂) Out)
    (TruthMid Admissible : RunBoundary oracleSig ambient s₁ s₂ Out → Prop)
    (Success : Observation oracleSig (s₁.append s₂) Out (T × (∀ j, B j)) → Prop)
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
theorem OracleVerifier.append_soundness_runtime {I J : Type} {A : I → Type}
    {B : J → Type} {inputs : OracleFamily I A} {outputs : OracleFamily J B}
    {s₁ : OracleProtocol} {s₂ : Path s₁ → OracleProtocol} {S T : Type}
    {Out : PathAlong oracleSig (s₁.append s₂) → Type} {κ : Type} {imports : OracleSpec κ}
    [EvalDistSemantics (OracleComp imports)] [LawfulEvalDistSemantics (OracleComp imports)]
    (runtime : OracleRuntime imports (ambient + challengeSpec oracleSig (s₁.append s₂)))
    (V : OracleVerifier ambient (s₁.append s₂) S T inputs outputs) (stmt : S)
    (data : ∀ i, A i) (prover : Prover oracleSig ambient (s₁.append s₂) Out)
    (Exceptional : RunResult runtime (RunBoundary oracleSig ambient s₁ s₂ Out) → Prop)
    (Success : Observation oracleSig (s₁.append s₂) Out (T × (∀ j, B j)) → Prop)
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
    {S T : Type} {Out : PathAlong plainSig (s₁.append s₂) → Type} {κ : Type}
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

end Interaction.Core
