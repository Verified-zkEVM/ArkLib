/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.Linear

/-! Executed degree-one resultant and perturbation checks. -/

open CompPoly CompPoly.CPolynomial ArkLib.Rojas
open ArkLib.Rojas.Producer.Linear

namespace RojasLinearProducerTests

example : perturbation (2 : ℚ) 3 5 = C 2 * X - C 15 := by
  norm_num [perturbation_eq]

example : perturbation (2 : ℚ) 0 5 = C 2 * X := by
  simpa using perturbation_eq (2 : ℚ) 0 5

#print axioms ArkLib.Rojas.Producer.Linear.characteristic_resultant
#print axioms ArkLib.Rojas.Producer.Linear.extract_of_leading_ne_zero
#print axioms ArkLib.Rojas.Producer.Linear.factor_of_root

/-- Vary the original equation and specialization, retaining a zero root and
checking the scanner against the computed characteristic, not just its formula. -/
def run : IO Unit := do
  let h := characteristic (2 : ℚ) 3 5
  unless h.coeff 0 == C 2 * X - C 15 do
    throw (IO.userError "Rojas linear: wrong system-dependent constant coefficient")
  unless h.coeff 1 == -(X + C 5) do
    throw (IO.userError "Rojas linear: perturbation direction was omitted")
  unless h.coeff 2 == 0 do
    throw (IO.userError "Rojas linear: spurious perturbation degree")
  unless toricPerturbationCoefficient? h == some (C 2 * X - C 15) do
    throw (IO.userError "Rojas linear: extraction disagrees with resultant")
  unless perturbation (7 : ℚ) (-4) 3 == C 7 * X + C 12 do
    throw (IO.userError "Rojas linear: changed input coefficients were ignored")
  let zeroRoot := characteristic (2 : ℚ) 0 5
  unless toricPerturbationCoefficient? zeroRoot == some (C 2 * X) do
    throw (IO.userError "Rojas linear: zero-coordinate root was lost")
  unless perturbation (2 : ℚ) 3 0 == C 2 * X do
    throw (IO.userError "Rojas linear: zero auxiliary coefficient mishandled")
  unless toricPerturbationCoefficient? (characteristic (0 : ℚ) 0 5) == some (-(X + C 5)) do
    throw (IO.userError "Rojas linear: scanner failed to skip vanishing constant coefficient")
  IO.println "Rojas degree-one producer: system/specialization checks passed"

end RojasLinearProducerTests
