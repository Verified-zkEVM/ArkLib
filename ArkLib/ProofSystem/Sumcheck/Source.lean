/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Message.Basic

/-!
# Semantic sources for Sumcheck rounds

A source describes compatible witnesses and their uniquely determined round polynomial.
It is a semantic parameter; it neither supplies executable operations nor defines relations.
-/

@[expose] public section

namespace Sumcheck

open Polynomial

/-- Compatible witnesses for a context determine the same degree-bounded polynomial. -/
structure Source (Context W R : Type) [CommRing R] (d : ℕ) where
  compatible : Context → W → Prop
  polynomial : Context → W → R⦃≤ d⦄[X]
  fixed : ∀ c w v, compatible c w → compatible c v → polynomial c w = polynomial c v

/-- A context with an explicit polynomial meaning needs no witness. -/
def oracleSource {R : Type} [CommRing R] {d : ℕ}
    (P : Type) (meaning : P → R⦃≤ d⦄[X]) : Source P Unit R d where
  compatible _ _ := True
  polynomial p _ := meaning p
  fixed _ _ _ _ _ := rfl

end Sumcheck
