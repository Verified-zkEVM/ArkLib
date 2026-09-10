/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ExactOutput

/-!
# Received words under a field embedding

Decoder arithmetic may take place in an auxiliary extension. Injectivity of the field embedding
preserves the evaluation domain and exactly the positions of agreement, so the decoding threshold
can be transported without changing which base-field messages qualify.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FieldTransport
open Polynomial
variable {F E : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E]

/-- Embed the received positions into the field used for interpolation and lifting. -/
def liftedDomain {n : ℕ} (base : F →+* E) (domain : Fin n ↪ F) : Fin n ↪ E :=
  ⟨fun i => base (domain i), base.injective.comp domain.injective⟩

/-- Field embeddings preserve exactly which received positions a mapped message agrees with. -/
theorem liftedAgreement {n : ℕ} (base : F →+* E) (domain : Fin n ↪ F)
    (received : Fin n → F) (P : Polynomial F) :
    Code.agree (evalOnPoints (liftedDomain base domain) (P.map base))
      (fun i => base (received i)) = Code.agree (evalOnPoints domain P) received := by
  unfold Code.agree
  congr 1
  apply Finset.filter_congr
  intro i _
  change (P.map base).eval (base (domain i)) = base (received i) ↔
    P.eval (domain i) = received i
  rw [Polynomial.eval_map_apply, base.injective.eq_iff]

end ReedSolomon.ListDecoding.FieldTransport
