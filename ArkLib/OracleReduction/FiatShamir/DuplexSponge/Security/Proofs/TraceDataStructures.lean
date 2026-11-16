/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import
  ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.TraceDataStructures.Basic
public import
  ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.TraceDataStructures.ListBacked

/-!
# [CO25, Definition 5.2] — Trace data structures

Re-exports the trace-table interface, `tr_∇`, and the list-backed default instantiation:

- `TraceDataStructures.Basic` — `TraceTableOps`, `LawfulTraceTable`, `TraceNabla`,
  forward-first sub-index, and `TraceNabla.ofQueryLog`.
- `TraceDataStructures.ListBacked` — `ListBacked.ListTraceTable`, `DefaultTraceDelta`, and the
  `IsSubsetOfQueryLog` invariant lemmas.
-/
