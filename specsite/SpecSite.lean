/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VersoManual
import SpecSite.Overview
import SpecSite.Language
import SpecSite.Protocols
import SpecSite.Proofs
import SpecSite.BeforeAfter
import SpecSite.Design
import SpecSite.Cost
import SpecSite.Adopting

open Verso.Genre Manual

#doc (Manual) "ArkLib protocol specifications" =>
%%%
authors := ["ArkLib contributors"]
shortTitle := "Protocol specifications"
%%%

This site documents a prototype for writing ArkLib's protocols as specifications: one text per
protocol, in protocol order, from which Lean derives the interaction tree, the honest prover, the
verifier, the stage claims, a JSON skeleton and a figure. Every excerpt, figure, table and theorem
name on the site is computed or checked by Lean when the site builds.

{include 0 SpecSite.Overview}

{include 0 SpecSite.Language}

{include 0 SpecSite.Protocols}

{include 0 SpecSite.Proofs}

{include 0 SpecSite.BeforeAfter}

{include 0 SpecSite.Design}

{include 0 SpecSite.Cost}

{include 0 SpecSite.Adopting}
