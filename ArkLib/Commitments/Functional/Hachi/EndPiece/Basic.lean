/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann, Pablo Martin
-/
import ArkLib.Commitments.Functional.Hachi.EndPiece.Reduction

/-!
# Hachi End-Piece (the closing step of the evaluation)

Umbrella module for `Hachi/EndPiece/`, the last step of Hachi's [NOZ26, §4.3] opening protocol.

`Sumcheck/FinalEval.lean` leaves an evaluation claim `relWEvalClaim` — a table `w̃` opening the
commitment `t`, whose multilinear extension takes the claimed value at the sumcheck point. The
end-piece consumes that claim: the prover sends `w̃`, and the verifier checks the claim against it
directly, leaving nothing to reduce. `Composition.lean` joins the two as
`evaluation = iteration ▷ endPiece`.

Unlike the other subprotocols, this one involves no cryptographic hardness and no algebraic
recovery: the verifier only re-reads data the prover just sent, and extraction returns that same
message.

## Folder structure

* `EndPiece/Reduction.lean` — the subprotocol: the wire format `pSpecEndPiece`, the check
  `endPieceCheck`, the guarded verifier, the extraction algorithm
  (`endPieceWitness`/`endPieceExtractor`), the special-soundness certificate
  `endPiece_coordinateWiseSpecialSoundWith`, and the exported `endPiece : GCWSSPackage`.

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/
