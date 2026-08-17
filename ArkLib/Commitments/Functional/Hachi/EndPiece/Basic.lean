/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann, Pablo Martin
-/
import ArkLib.Commitments.Functional.Hachi.EndPiece.Reduction

/-!
# Hachi End-Piece (the closing component of the evaluation)

Umbrella module for `Hachi/EndPiece/`: the terminal link of Hachi's [NOZ26, §4.3] opening. It ends
a (possible run of) `iteration`(s): the prover sends the reduced witness `w̃` itself, and the
verifier checks the evaluation claim `relWEvalClaim` against it directly — recompute the
commitment, evaluate the table's multilinear extension at the sumcheck point. Nothing is left to
reduce, so the output relation is the full relation on `Unit`.

The end-piece consumes exactly the seam `Sumcheck/FinalEval.lean` produces, and
`Composition.lean` concatenates the two as `evaluation = iteration ▷ endPiece`.

## Folder structure

* `EndPiece/Reduction.lean` — the subprotocol: the wire format `pSpecEndPiece`, the check
  `endPieceCheck`, the guarded verifier and its guardedness, the extraction algorithm
  (`endPieceWitness`/`endPieceExtractor`), the CWSS certificate
  `endPiece_coordinateWiseSpecialSoundWith`, and the exported `endPiece : GCWSSPackage`.

Unlike the other subprotocols the end-piece is **escape-free and sorry-free**: its check re-reads
data the prover just sent, so no cryptographic assumption is consulted, and its extraction is the
identity on the transcript message rather than an algebraic recovery argument.

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/
