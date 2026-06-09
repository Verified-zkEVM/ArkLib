/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.CommitmentScheme.Ajtai.Simple.Correctness

/-!
# Simple Ajtai Commitment

Re-exports the simple non-hiding Ajtai [Ajt96] commitment scheme and its correctness over the
computable cyclotomic ring `Rq Φ`. (Binding security lives in `Simple/Security.lean`.)

## References

* [Ajtai, M., *Generating Hard Instances of Lattice Problems*][Ajt96]
-/
