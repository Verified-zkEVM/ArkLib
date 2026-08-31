/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import VCVio.CryptoFoundations.CommitmentScheme

/-!
  # Ordinary (Non-Interactive) Commitment Schemes

  This file is the entry point for *ordinary* commitment schemes in ArkLib: non-interactive
  schemes with a public parameter space `PP`, message space `M`, commitment space `C`, and
  opening (decommitment) space `D`, together with their standard security properties
  (correctness, hiding, binding, and trapdoor extractability).

  The core definitions are **not** redefined here. They are provided by the
  [VCV-io](https://github.com/dtumad/VCV-io) library, in
  `VCVio.CryptoFoundations.CommitmentScheme`:

  - `CommitmentScheme PP M C D` — the scheme bundle (`setup`, `commit`, `verify`).
  - `CommitmentScheme.PerfectlyCorrect` / `PerfectlyHiding` — perfect security notions.
  - `CommitmentScheme.hidingExp` / `bindingExp` — game-based hiding and binding experiments.
  - `TrapdoorExtractor` / `CommitmentScheme.extractExp` — trapdoor-based extraction.

  Concrete ordinary schemes (e.g. the simple Ajtai commitment under `Ajtai/`) instantiate
  `CommitmentScheme` directly. Importing this module re-exports those definitions, so
  downstream files can depend on `ArkLib.Commitments.Ordinary.Basic` as the canonical handle.

  For commitment schemes with *oracle openings* (functional commitments such as KZG), see
  `ArkLib.Commitments.Functional.Basic` instead.
-/
