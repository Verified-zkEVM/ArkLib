/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Polynomial.HasseTaylor.FiniteJet
import ArkLib.ToMathlib.Polynomial.HasseTaylor.Forward
import ArkLib.ToMathlib.Polynomial.HasseTaylor.Shift
import ArkLib.ToMathlib.Polynomial.HasseTaylor.JetDivisibility

/-!
# Characteristic-safe Hasse--Taylor infrastructure

This module exports ArkLib's reusable univariate Hasse--Taylor API.  It builds on Mathlib's
`Polynomial.hasseDeriv` and `Polynomial.taylor` without introducing factorial denominators or
characteristic lower bounds.

The API has four layers, listed in dependency order where one layer builds on another:

* `HasseTaylor.FiniteJet` packages derivative orders `< m` as the linear map `hasseJet` and gives
  exact degree lowering and finite-coordinate equivalences;
* `HasseTaylor.Forward` gives explicit finite forward truncations with a canonical `X ^ m`
  remainder quotient;
* `HasseTaylor.Shift` gives scalar Hasse vanishing/divisibility bridges, the elementary shift
  quotient, and the moving-point backward identity;
* `HasseTaylor.JetDivisibility` packages the scalar divisibility bridges as zero- and equal-jet
  characterizations for downstream finite-coordinate consumers.

Concrete convention and small-characteristic tests live in the sibling `*Canary` modules so this
umbrella does not import test-only arithmetic dependencies.
-/
