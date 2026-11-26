/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Execution

/-!
# Functional commitments on the interaction layer

A functional commitment (FC) commits to data `d : Data` and later opens the commitment to the
answer `I.answer d q` of a query `q`, where `I : OracleInterface Data` fixes the queries and their
answers. The syntax follows Kate, Zaverucha and Goldberg [KZG10] for polynomial commitments and
Chiesa, Guan, Knabenhans and Yu [CGKY25] for general functional commitments.

## Syntax

A scheme `FC : FunctionalCommitment ambient Data I` has
* a setup algorithm returning public parameters `pp : FC.PP`;
* a non-interactive commit algorithm returning a commitment `cm : FC.Cm` and the committer's
  auxiliary state `aux : FC.Aux`;
* for each query `q`, an opening protocol `FC.openSpec q` on the interaction layer, with an
  honest prover `FC.prover q` and a verifier `FC.verifier q`. The verifier's statement is
  `(pp, cm, r)` for the claimed answer `r`.

Setup, commit and the honest prover run in `OracleComp (unifSpec + ambient)`: `unifSpec` gives
them private coins and `ambient` is an oracle shared by every party, such as a random oracle.
The verifier only queries `ambient`, so the opening is public-coin. Group models are not oracles
here. They restrict the adversary class of a security game.

`Verifier.liftAmbient` runs a verifier over `ambient` inside `unifSpec + ambient`.

The security games are in `ArkLib.Commitments.FunctionalCommitment.Security`, and the
one-message constructor is in `ArkLib.Commitments.FunctionalCommitment.OneMessage`.

## References

* [Kate, A., Zaverucha, G. M., and Goldberg, I.,
  *Constant-Size Commitments to Polynomials and Their Applications*][KZG10]
* [Chiesa, A., Guan, Z., Knabenhans, C., and Yu, Z.,
  *On the Fiat–Shamir Security of Succinct Arguments from Functional Commitments*][CGKY25]
-/

@[expose] public section

open OracleComp OracleSpec Interaction

/-- A functional commitment for data `Data` with query interface `I`, over the shared oracle
`ambient`.

* `setup` samples the public parameters.
* `commit pp d` returns a commitment and the committer's auxiliary state. Commit is a
  non-interactive algorithm.
* `openSpec q` is the shape of the opening protocol for the query `q`.
* `prover q pp cm r d aux` is the honest opening prover for the claim that `cm` opens to `r`
  at `q`. It has private coins.
* `verifier q` decides on the statement `(pp, cm, r)` and queries only `ambient`. -/
structure FunctionalCommitment {ι : Type} (ambient : OracleSpec.{0, 0} ι)
    (Data : Type) (I : OracleInterface Data) where
  /-- Public parameters. -/
  PP : Type
  /-- Commitments. -/
  Cm : Type
  /-- The committer's auxiliary state, kept for openings. -/
  Aux : Type
  /-- Setup samples the public parameters. -/
  setup : OracleComp (unifSpec + ambient) PP
  /-- Commit to data, returning the commitment and the auxiliary state. -/
  commit : PP → Data → OracleComp (unifSpec + ambient) (Cm × Aux)
  /-- The shape of the opening protocol for each query. -/
  openSpec : I.Query → Protocol
  /-- The honest opening prover for the claim `(pp, cm, r)` at `q`, given the data and the
  auxiliary state. -/
  prover : (q : I.Query) → PP → Cm → I.spec q → Data → Aux →
    Prover plainSig (unifSpec + ambient) (openSpec q) (fun _ => PUnit)
  /-- The opening verifier for the claim `(pp, cm, r)` at `q`. -/
  verifier : (q : I.Query) → Verifier ambient (openSpec q) (PP × Cm × I.spec q) (fun _ => PUnit)

namespace Interaction
open PFunctor FreeM

/-- Run a verifier over `ambient` inside `unifSpec + ambient`. The lifted verifier makes no
`unifSpec` query, so it stays public-coin. -/
def Verifier.liftAmbient {ι : Type} {ambient : OracleSpec.{0, 0} ι} {s : Protocol}
    {S : Type} {T : Path s → Type} (V : Verifier ambient s S T) :
    Verifier (unifSpec + ambient) s S T where
  decide stmt p v := OptionT.mk (liftComp (V.decide stmt p v).run (unifSpec + ambient))

/-- The lifted decision is the lifted computation of the original decision. -/
theorem Verifier.run_decide_liftAmbient {ι : Type} {ambient : OracleSpec.{0, 0} ι}
    {s : Protocol} {S : Type} {T : Path s → Type} (V : Verifier ambient s S T) (stmt : S)
    (p : Path s) (v : PlainView s p) :
    (V.liftAmbient.decide stmt p v).run = liftComp (V.decide stmt p v).run (unifSpec + ambient) :=
  rfl

end Interaction
