/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import SpecSite.Meta.Blocks

/-!
# The site's size tables

Each table lists files by group. Because `{sizes}` counts their lines when the site builds, a table
cannot fall behind the code it describes.
-/

namespace SpecSite

/-- A prototype file, relative to the repository root. -/
def spec (f : String) : String := s!"{prototypeDir}/Specs/{f}.lean"

/-- A file of today's sum-check, relative to the repository root. -/
def today (f : String) : String := s!"ArkLib/ProofSystem/Sumcheck/{f}.lean"

/-- The prototype by part. -/
def prototypeSizes : SizeTable where
  groups := [
    { name := "Spec layer"
      note := "the language, its semantics, the exports and the security notions"
      files := ["Formula", "Core", "Run", "Export", "Security"].map spec },
    { name := "Proof kit", note := "the generic theorems over rounds"
      files := ["Kit/Block", "Kit/Iteration", "Kit/Verifier", "Kit/ClaimReduction"].map spec },
    { name := "Kit instances", note := "three protocols proved through the kit"
      files := ["Kit/Sumcheck", "Kit/Fri", "Kit/TwoMessage"].map spec },
    { name := "Bridge and claims", note := "from a specification to the kit, and its stage claims"
      files := ["Bridge", "Bridge/Rounds", "Bridge/Sumcheck", "Claims"].map spec },
    { name := "Examples", note := "the four specifications"
      files := ["Examples/Sumcheck", "Examples/Spartan", "Examples/Fri",
        "Examples/Branching"].map spec }]
  total := some ("All of Specs/", s!"{prototypeDir}/Specs")
  caption := "Counted when this site was built. The total includes the bench files and Main.lean."

/-- The files of today's sum-check that the before-and-after chapter quotes. -/
def todaySumcheckSizes : SizeTable where
  groups := [
    { name := "The tree", files := ["MessageTree"].map today },
    { name := "The honest message", files := ["IndexedDomain", "IntervalCompleteness"].map today },
    { name := "The claim and its check", files := ["Interval"].map today },
    { name := "The verifier's fold", files := ["Interpreted"].map today },
    { name := "Moves by position", files := ["SingleRound"].map today },
    { name := "The recursion that every proof repeats", files := ["Indexed"].map today }]
  total := some ("All of ArkLib/ProofSystem/Sumcheck/", "ArkLib/ProofSystem/Sumcheck")
  caption := "Counted when this site was built: the files that the excerpts come from, whole."

/-- One specification against the files it replaces. -/
def sumcheckSpecSizes : SizeTable where
  groups := [
    { name := "Specification", note := "the round, the specification, its tree and figure tests"
      files := ["Examples/Sumcheck"].map spec },
    { name := "Soundness through the kit", note := "the instance of the generic round theorem"
      files := ["Kit/Sumcheck"].map spec },
    { name := "Bridge", note := "the specification's verifier is the kit's verifier"
      files := ["Bridge/Sumcheck"].map spec },
    { name := "Claims", note := "the stage claims are the soundness statement's languages"
      files := ["Claims"].map spec }]
  caption := "Counted when this site was built: what sum-check needs on top of the shared layers."

end SpecSite
