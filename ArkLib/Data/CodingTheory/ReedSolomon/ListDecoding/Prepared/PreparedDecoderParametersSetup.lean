/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Prepared.PreparedDecoderParameters
public import ArkLib.Data.QuadraticAlgebra.SetupRefinement
/-!
# Actual quadratic setup and prepared decoding at the small-gap parameters

Search and setup return the actual interpolant, nonsquare, alphabet and sample prefix used by
the prepared run. The original block threshold and prime-field condition discharge all its
characteristic and residual-sampling premises. The oversized agreement threshold is a separate
outer branch. No combined driver or global cost bound is introduced here.

The reduced-separant larger-field condition does not itself provide `m*A` base-field samples.
A runtime proof for that improved regime remains separate; this theorem uses quadratic setup.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.PreparedDecoderParameters

open Polynomial JetHornerMachine HiddenDerivative ReedSolomon PolynomialDifferential

/-- Actual prescribed search and setup supply every premise of exact prepared decoding.
Both child ledgers and the prepared trace are retained, without a combined runtime-cost claim. -/
theorem prescribed_setup_exact {q : ℕ} [Fact q.Prime] (delta : ℝ) (hdelta : 0 < delta)
    (hquarter : delta < (1 / 4 : ℝ)) (n k A : ℕ)
    (hblock : 8 * weightedSupportMultiplicity delta ≤ n) (hk : 0 < k) (hkn : k ≤ n)
    (hA : ReedSolomon.agreementThreshold delta n k ≤ A) (hAn : A ≤ n) (hnq : n ≤ q)
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q) :
    let d := capacityDerivativeOrder delta
    let m := weightedSupportMultiplicity delta
    let rows := List.ofFn (fun i ↦ (domain i, received i))
    ∃ (found : AmbientSearchMachine.Output (ZMod q)) (searchCost : ℕ)
      (a : ZMod q) (data : QuadraticAlgebra.SetupMachine.Prepared q a)
      (setupCost : QuadraticAlgebra.SetupMachine.Cost)
      (correct : QuadraticAlgebra.SetupMachine.Correct (m * A) a data)
      (steps cost : ℕ) (out : List (List (ZMod q))),
      AmbientSearchMachine.run k d m A rows = (some found, searchCost) ∧
      QuadraticAlgebra.SetupMachine.runFuel (m * A)
        (QuadraticAlgebra.SetupMachine.budget q (m * A)) (.base .start) =
          (.done (some ⟨a, data⟩), setupCost) ∧
      searchCost ≤ AmbientSearchMachine.budget k d m A n ∧
      setupCost.total ≤ QuadraticAlgebra.SetupMachine.budget q (m * A) ∧
      let input : PreparedDecoderMachine.Input (ZMod q) a :=
        ⟨data.alphabet, data.samples, rows, d, found.degree, m * A, k, A⟩
      PreparedDecoderMachine.Trace input correct.nonsquare steps
        (.start found.interpolant.terms) cost (.done (some out)) ∧
      PreparedDecoderMachine.runFuel input correct.nonsquare steps
        (.start found.interpolant.terms) = (.done (some out), cost) ∧
      (out.map coefficientPolynomial).Nodup ∧ out.Nodup ∧
      (∀ f : (ZMod q)[X], f ∈ out.map coefficientPolynomial ↔
        f.degree < k ∧ A ≤ Code.agree (evalOnPoints domain f) received) ∧
      (∀ cs : List (ZMod q), cs ∈ out ↔ cs.length = k ∧
        (coefficientPolynomial cs).degree < k ∧
        A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received) := by
  obtain ⟨found, searchCost, hsearch, _hc, _hl, _hu, hchar, hweight, hL, hodd, hsc⟩ :=
    prescribed_search delta hdelta hquarter n k A hblock hk hkn hA hAn hnq domain received
  obtain ⟨a, data, setupCost, hsetup, correct, hsetupCost⟩ :=
    QuadraticAlgebra.SetupMachine.setup_correct
      (weightedSupportMultiplicity delta * A) (Fact.out : q.Prime) hodd hL
  obtain ⟨points, hpoints⟩ := correct.samples_embedding
  obtain ⟨steps, cost, out, htrace, hrun, hnpoly, hnvec, hpoly, hvec⟩ :=
    PreparedDecoderProof.run_exact domain received found (congrArg Prod.fst hsearch)
      a correct.nonsquare data.alphabet data.samples points hpoints correct.extension_complete
      correct.extension_nodup hchar hweight
  exact ⟨found, searchCost, a, data, setupCost, correct, steps, cost, out,
    hsearch, hsetup, hsc, hsetupCost, htrace, hrun, hnpoly, hnvec, hpoly, hvec⟩

end ReedSolomon.ListDecoding.PreparedDecoderParameters
