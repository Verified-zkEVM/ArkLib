/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import CompPoly.Multivariate.CMvPolynomial
import CompPoly.Multivariate.Operations
import CompPoly.Multivariate.Rename
import CompPoly.Univariate.ToPoly.Impl
import ArkLib.OracleReduction.OracleInterface

/-!
# Shared CompPoly Wrappers and Oracle Interfaces

Shared degree-bounded computable polynomial types used across protocols, together
with reusable `OracleInterface` instances.
-/

open CompPoly CPoly Std

namespace CPoly.CMvPolynomial

variable {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]

/-- `p` has individual degree at most `deg` when every monomial exponent is
bounded by `deg` in every coordinate. -/
def IndividualDegreeLE (deg : ℕ) (p : CMvPolynomial n R) : Prop :=
  letI := Classical.decEq R
  ∀ i : Fin n, ∀ mono ∈ Lawful.monomials p, mono.degreeOf i ≤ deg

end CPoly.CMvPolynomial

/-- A computable univariate polynomial with `natDegree ≤ d`. -/
def CDegreeLE (R : Type) [BEq R] [Semiring R] [LawfulBEq R] (d : ℕ) :=
  { p : CPolynomial R // p.natDegree ≤ d }

/-- A computable multivariate polynomial with individual degree at most `d` in
every coordinate. -/
def CMvDegreeLE
    (R : Type) [BEq R] [CommSemiring R] [LawfulBEq R] (n d : ℕ) :=
  { p : CMvPolynomial n R // CMvPolynomial.IndividualDegreeLE (R := R) d p }

section OracleInterface

open OracleComp OracleSpec

variable {n : ℕ} {deg : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]

instance instOracleInterfaceCMvPolynomial :
    OracleInterface (CMvPolynomial n R) where
   Query := Fin n → R
   toOC := {
     spec := (Fin n → R) →ₒ R
     impl := fun points => do return CMvPolynomial.eval points (← read)
   }

instance instOracleInterfaceCPolynomial [Nontrivial R] :
    OracleInterface (CPolynomial R) where
   Query := R
   toOC := {
     spec := R →ₒ R
     impl := fun point => do return CPolynomial.eval point (← read)
   }

instance instOracleInterfaceCDegreeLE [Semiring R] :
    OracleInterface (CDegreeLE R deg) where
   Query := R
   toOC := {
     spec := R →ₒ R
     impl := fun point => do return CPolynomial.eval point (← read).1
   }

instance instOracleInterfaceCMvDegreeLE :
    OracleInterface (CMvDegreeLE R n deg) where
   Query := Fin n → R
   toOC := {
     spec := (Fin n → R) →ₒ R
     impl := fun points => do return CMvPolynomial.eval points (← read).1
   }

namespace Examples

/-- A verifier-side query against a multivariate polynomial oracle.

The verifier supplies only an evaluation point. The polynomial itself is supplied
later as the read-only oracle environment. -/
def verifierQueryCMvPolynomial (points : Fin n → R) :
    ReaderM (CMvPolynomial n R) R :=
  (instOracleInterfaceCMvPolynomial (n := n) (R := R)).toOC.impl points

set_option linter.unusedSectionVars false

/-- Running the verifier-side query against a concrete polynomial agrees with
ordinary polynomial evaluation. -/
theorem verifierQueryCMvPolynomial_run (poly : CMvPolynomial n R) (points : Fin n → R) :
    (verifierQueryCMvPolynomial (R := R) points).run poly =
      CMvPolynomial.eval points poly := by
  unfold verifierQueryCMvPolynomial
  rfl

end Examples

end OracleInterface
