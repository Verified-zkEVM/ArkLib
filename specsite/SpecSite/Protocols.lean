/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VersoManual
import SpecSite.Meta.Blocks
import SpecSite.Protocols.Sumcheck
import SpecSite.Protocols.Spartan
import SpecSite.Protocols.Fri
import SpecSite.Protocols.Branching

open Verso.Genre Manual

#doc (Manual) "Four protocols" =>
%%%
tag := "protocols"
%%%

This chapter walks through four specifications from `Specs/Examples`. Each page states what the
protocol does and its parameters, shows the pieces of the specification and then the whole of it,
draws its figure, reads moves from its transcript with accessors, lists what Lean proves about it,
and records the module's design choices.

* {ref "sumcheck"}[Sum-check] is the running example of the {ref "language"}[language chapter]. Its
  loop is reused by two of the other pages, and Lean proves that the specification agrees with
  ArkLib's sum-check.
* {ref "spartan"}[Spartan] runs that loop twice, inside two named stages whose claims connect the
  two sum-checks.
* {ref "fri"}[FRI] has three loops, one nested in another: the fold rounds, the query rounds and a
  consistency check per fold inside each query.
* {ref "branching"}[A prover-chosen size] lets a prover message select the number of variables of a
  sum-check. As a result, the rest of the protocol has a different shape in each case.

{include 0 SpecSite.Protocols.Sumcheck}

{include 0 SpecSite.Protocols.Spartan}

{include 0 SpecSite.Protocols.Fri}

{include 0 SpecSite.Protocols.Branching}
