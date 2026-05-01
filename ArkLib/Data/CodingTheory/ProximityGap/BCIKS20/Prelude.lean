/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.Basic
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic.ComputeDegree
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Preimage
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import ArkLib.Data.Probability.Instances
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import ArkLib.Data.CodingTheory.InterleavedCode
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Logic.Function.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import ArkLib.Data.CodingTheory.BerlekampWelch.BerlekampWelch
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Determinant.Misc
import Mathlib.Logic.Equiv.Fin.Basic
import ArkLib.Data.CodingTheory.PolishchukSpielman.Degrees
import ArkLib.Data.CodingTheory.PolishchukSpielman
import ArkLib.Data.Polynomial.Trivariate
