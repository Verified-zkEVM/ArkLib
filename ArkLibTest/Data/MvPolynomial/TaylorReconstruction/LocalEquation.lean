/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.MvPolynomial.TaylorReconstruction.LocalEquation

/-! Exact shifted coefficients and fibers, including repeated roots and no free variables. -/

open CPoly CPoly.CMvPolynomial CPoly.TaylorReconstruction CompPoly

namespace LocalEquationTests

private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

/-- Inspect stored shifted coefficients, including a repeated-root constant fiber. -/
def run : IO Unit := do
  let p : CMvPolynomial 3 ℤ := X 2 ^ 2 - X 0 * X 2 - X 1
  let a : Fin 2 → ℤ := ![1, 2]
  let q := localEquation 3 a p
  check "leading coefficient survives local conversion" <| q.coeff 2 == 1
  check "linear coefficient is shifted in the first free variable" <|
    (q.coeff 1).val == -(X 0 + 1 : CMvPolynomial 2 ℤ)
  check "constant coefficient is shifted in the second free variable" <|
    (q.coeff 0).val == -(X 1 + 2 : CMvPolynomial 2 ℤ)
  let z : CPolynomial ℤ := CPolynomial.X
  check "constant fiber uses the supplied sample" <| constantFiber a p == z ^ 2 - z - 2
  check "computed equation specializes exactly" <|
    ArkLib.ConfluentAlgebra.mapCoefficients (BoxAlgebra.constantSpecialization (by decide)) q ==
      z ^ 2 - z - 2
  let repeated : CMvPolynomial 2 ℤ := X 1 ^ 2 - X 0
  let q₀ := localEquation 2 (fun _ => (0 : ℤ)) repeated
  check "repeated-root fiber retains parameter deformation" <|
    q₀.coeff 2 == 1 && (q₀.coeff 0).val == -(X 0 : CMvPolynomial 1 ℤ) &&
      constantFiber (fun _ => 0) repeated == z ^ 2
  let single : CMvPolynomial 1 ℤ := X 0 ^ 2 + 3
  check "no free variables preserves the univariate equation" <|
    constantFiber (Fin.elim0) single == z ^ 2 + 3

end LocalEquationTests
