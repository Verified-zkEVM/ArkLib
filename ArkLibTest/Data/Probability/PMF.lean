import ArkLib.Data.Probability.PMF
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

open scoped ENNReal ProbabilityTheory

example (mx : ProbComp Bool) (p : Bool → Prop) :
    Pr{let b ← mx}[p b] = 𝒟[p <$> mx] {True} :=
  prEvent_eq_evalDist_map mx p

example : Pr{let n ← $ᵗ (Fin 2)}[n = 0] = (1 / 2 : ENNReal) := by
  rw [SampleableType.prEvent_uniformSample]
  have hcard : (Finset.univ.filter (fun n : Fin 2 => n = 0)).card = 1 := by
    decide
  rw [hcard]
  norm_num

example :
    Pr{let n ← $ᵗ (Fin 2)}[Equiv.swap (0 : Fin 2) 1 n = 0] =
      Pr{let n ← $ᵗ (Fin 2)}[n = 0] := by
  exact SampleableType.prEvent_uniformSample_equiv
    (Equiv.swap 0 1) (fun n : Fin 2 => n = 0)
