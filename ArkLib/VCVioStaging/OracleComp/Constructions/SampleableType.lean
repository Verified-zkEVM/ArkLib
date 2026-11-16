/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import VCVio.EvalDist.EvalDistEq
public import VCVio.EvalDist.FiniteSupport
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Uniform-sampling marginal lemmas

Vector sampling records results in reverse draw order and commutes with monad morphisms.
Its uniform distribution law is shared by the raw D2S and rate-only samplers.

Companions to `SampleableType.prEvent_uniformSample_fst` in VCVio:
- `evalDist_uniformSample_prod_bind` — a uniform pair equals two independent uniform samples;
- `evalDist_uniformSample_pi_comp_injective` — restricting a uniform dependent table along an
  injection is uniform.

Output measures are compared under any measurable structure with measurable singletons, the
convention of `SampleableType.evalDist_uniformSample`; on these finite types that structure is
the discrete one.

These are building blocks for eager-table "patching" arguments, where a uniform function table
is split along a coordinate partition (`Equiv.piEquivPiSubtypeProd`), the blocks are resampled
independently, and the pieces are recombined.  Upstreaming candidates for
`VCVio.OracleComp.Constructions.SampleableType.Measure`.
-/

@[expose] public section

open OracleComp SampleableType

namespace Vector

universe u v w

variable {α : Type u} {M : Type u → Type v} {N : Type u → Type w}

/-- Repeat an action, storing its results in reverse execution order. -/
def replicateRevM [Monad M] (sample : M α) : (m : ℕ) → M (Vector α m)
  | 0 => pure #v[]
  | m + 1 => do
    let a ← sample
    let v ← replicateRevM sample m
    pure (v.push a)

/-- A monad morphism preserves the draw order and every resulting vector entry. -/
lemma map_replicateRevM [Monad M] [Monad N] (F : M →ᵐ N) (sample : M α) (m : ℕ) :
    F (replicateRevM sample m) = replicateRevM (F sample) m := by
  induction m with
  | zero => simp [replicateRevM]
  | succ m ih => simp [replicateRevM, ih]

end Vector

namespace OracleComp

variable {α β : Type}

/-- **A uniform pair is two independent uniform samples.** -/
lemma evalDist_uniformSample_prod_bind [Finite α] [Finite β]
    [SampleableType α] [SampleableType β] [SampleableType (α × β)]
    [MeasurableSpace (α × β)] [MeasurableSingletonClass (α × β)] :
    𝒟[(do let a ← $ᵗ α; let b ← $ᵗ β; return (a, b) : ProbComp (α × β))]
      = 𝒟[$ᵗ (α × β)] := by
  refine (evalDistEq_iff_forall_prEvent_eq_output.mpr fun p => ?_).evalDist_eq
  rw [prEvent_uniformSample_inst_irrel (α := α × β) _ (instSampleableTypeProd α β) (· = p),
    prEvent_uniformSample_prod (fun z => z = p)]
  simp only [prEvent_norm]

/-- **Restricting a uniform dependent table along an injection is uniform.**

For an injection `d : D → D'` between finite index types and a dependent range family
`β : D' → Type`, drawing a uniform dependent table `g : (x' : D') → β x'` and restricting it
along `d` (i.e. `fun x => g (d x)`) yields the uniform distribution on `(x : D) → β (d x)`.

Proof route (no counting): split the table space along membership in `Set.range d`
(`Equiv.piEquivPiSubtypeProd`), reindex the range block by `D` (`Equiv.piCongrLeft` over
`Equiv.ofInjective`), and marginalize with `SampleableType.prEvent_uniformSample_fst`. -/
lemma evalDist_uniformSample_pi_comp_injective
    {D D' : Type} {β : D' → Type}
    (d : D → D') (hd : Function.Injective d)
    [Finite D] [Finite D'] [∀ x', Finite (β x')] [∀ x', Nonempty (β x')]
    [SampleableType ((x' : D') → β x')] [SampleableType ((x : D) → β (d x))]
    [MeasurableSpace ((x : D) → β (d x))] [MeasurableSingletonClass ((x : D) → β (d x))] :
    𝒟[(fun g (x : D) => g (d x)) <$> ($ᵗ ((x' : D') → β x'))]
      = 𝒟[$ᵗ ((x : D) → β (d x))] := by
  classical
  let : Fintype D := Fintype.ofFinite D
  let : Fintype D' := Fintype.ofFinite D'
  let : ∀ x', Fintype (β x') := fun x' => Fintype.ofFinite (β x')
  let P : D' → Prop := fun x' => x' ∈ Set.range d
  have : DecidablePred P := Classical.decPred P
  let Pi₁ : Type := (y : {x' // P x'}) → β y.1
  let Pi₂ : Type := (y : {x' // ¬ P x'}) → β y.1
  have : Nonempty Pi₁ := ⟨fun y => Classical.arbitrary _⟩
  have : Nonempty Pi₂ := ⟨fun y => Classical.arbitrary _⟩
  let : SampleableType Pi₁ := SampleableType.ofFintype _
  let : SampleableType Pi₂ := SampleableType.ofFintype _
  let ε : ((x' : D') → β x') ≃ Pi₁ × Pi₂ := Equiv.piEquivPiSubtypeProd P β
  let eRange : D ≃ {x' // P x'} := Equiv.ofInjective d hd
  let τ : ((x : D) → β (d x)) ≃ Pi₁ :=
    Equiv.piCongrLeft (fun y : {x' // P x'} => β y.1) eRange
  -- Pointwise: restriction along `d` = reindexed first block of the `ε`-split.
  have hfun : ∀ g : (x' : D') → β x', (fun x : D => g (d x)) = τ.symm (ε g).1 := fun _ => rfl
  refine (evalDistEq_iff_forall_prEvent_eq_output.mpr fun f => ?_).evalDist_eq
  rw [prEvent_map]
  calc Pr{let g ← $ᵗ ((x' : D') → β x')}[(fun x : D => g (d x)) = f]
      = Pr{let g ← $ᵗ ((x' : D') → β x')}[τ.symm (ε g).1 = f] :=
        prEvent_congr _ _ _ fun g => by rw [hfun g]
    _ = Pr{let q ← $ᵗ (Pi₁ × Pi₂)}[τ.symm q.1 = f] :=
        prEvent_uniformSample_equiv ε (fun q => τ.symm q.1 = f)
    _ = Pr{let a ← $ᵗ Pi₁}[τ.symm a = f] :=
        prEvent_uniformSample_fst (fun a => τ.symm a = f)
    _ = Pr{let h ← $ᵗ ((x : D) → β (d x))}[h = f] :=
        prEvent_uniformSample_equiv τ.symm (fun h => h = f)

/-- Independent uniform draws remain uniform when stored in reverse execution order. -/
lemma evalDist_replicateRevM_uniform {U : Type} [SampleableType U] (m : ℕ) :
    (letI : MeasurableSpace (Vector U m) := ⊤;
      𝒟[Vector.replicateRevM ($ᵗ U : ProbComp U) m] = 𝒟[($ᵗ (Vector U m) : ProbComp _)]) := by
  induction m with
  | zero =>
    let : MeasurableSpace (Vector U 0) := ⊤
    refine (evalDistEq_iff_forall_prEvent_eq_output.mpr fun v => ?_).evalDist_eq
    have hv : v = #v[] := Vector.ext fun i hi => (by omega)
    subst v
    simp [Vector.replicateRevM]
  | succ m ih =>
    let : MeasurableSpace (Vector U m × U) := ⊤
    let _ : MeasurableSpace (Vector U (m + 1)) := ⊤
    have hpush : Function.Bijective (fun p : Vector U m × U => p.1.push p.2) := by
      constructor
      · intro p q h
        exact Prod.ext (Vector.pop_eq_of_push_eq h) (Vector.back_eq_of_push_eq h)
      · intro v
        exact ⟨(v.pop, v.back), Vector.push_pop_back v⟩
    have h : 𝒟[(do let v ← ($ᵗ (Vector U m) : ProbComp _)
                   let u ← ($ᵗ U : ProbComp U)
                   pure (v.push u))] = 𝒟[($ᵗ (Vector U (m + 1)) : ProbComp _)] := by
      have hpair := evalDist_uniformSample_prod_bind (α := Vector U m) (β := U)
      have hmap := (SampleableType.map_uniformSample_evalDistEq_of_bijective hpush).evalDist_eq
      rw [evalDist_map_of_discrete, ← hpair, ← evalDist_map_of_discrete] at hmap
      simpa only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def] using hmap
    change 𝒟[_] = 𝒟[_]
    rw [Vector.replicateRevM, OracleComp.evalDist_bind_bind_swap]
    exact (((evalDistEq_iff_evalDist_eq.mpr ih).bind_left _).evalDist_eq).trans h

end OracleComp
