# TASK: Chiesa-Yogev textbook coverage audit of ArkLib's proposed oracle-reduction design

You are auditing whether a proposed formalization design can state and prove ALL the results in Chiesa-Yogev "Building Cryptographic Proofs from Hash Functions", with special depth on their BCS transformation (Merkle trees only). The claim to test: "once we get down to the precise cryptographic properties and reductions, a LOT of complications will crop up." Your job is to find those complications CONCRETELY, from the textbook's actual definitions and proofs.

## Materials (all local, read them)

1. THE DESIGN DOC (read fully first): /Users/quangdao/Documents/Lean/ArkLib-Oracle-Reduction-Design.md
2. THE TEXTBOOK TeX source (single file, 27250 lines): /Users/quangdao/Downloads/Papers/hash-based-snargs-book/snargs-book.tex
   Chapter line map (grep '\chapter{' to confirm):
   - The random oracle model: 2396 / Basic cryptographic properties: 2778
   - Arguments in the ROM: 3651 / Additional security defs: 3943 / Basic observations: 4395
   - Arguments in general oracle settings: 5616
   - State restoration: 8892
   - Basic commitment scheme: 11738 / Merkle commitment scheme: 12395
   - PCPs: 14598 / succinct args from PCPs: 15168 / Micali: 15748 / Additional security defs: 16229
   - Interactive oracle proofs: 16625 / Warmup succinct args from IOPs: 16971
   - THE BCS TRANSFORMATION: 17609-18413 / Additional security defs (BCS): 18414
   - Setting parameters: 19414 / Merkle optimizations: 19923
   - Special soundness: 20536 / Round-by-round soundness: 23498
   - Preprocessing: 24401 / Witness indistinguishability: 26021 / Error bounds: 26751
3. The ArkLib rebuild code (for grounding): /Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/ (esp. Oracle/BCS.lean, Oracle/Program.lean, Oracle/Security/, FiatShamir/)

## What to produce

### Part 1: Result inventory and coverage matrix (the core)
Go through the security-relevant chapters (prioritize: ROM + basic crypto properties; state restoration; basic + Merkle commitment; IOPs; BCS transformation + its additional security defs; special soundness; RBR soundness; salting/ZK; preprocessing; error bounds). For each key definition/construction/theorem (cite textbook numbering where visible in the tex source, else section names + line numbers):
- What EXACTLY does CY define/prove (their precise game, adversary interface, error function, quantifier order)?
- Can the proposed design STATE it? Which design objects does it map to (SourceCtx/VirtualOracle/ClosedClaim/WorldSpec Γ/extractor taxonomy/compiler passes)?
- Can the proposed design PROVE it — i.e., does the design have the needed intermediate objects (e.g. query traces, RO reprogramming, salts, Merkle extractor-in-the-ROM, output-commitment binding across forks)?
- Verdict per item: OK / OK-with-work (name the work) / GAP (name the missing object or the mismatch).

Pay SPECIFIC attention to these known-hard spots and check what CY actually requires:
a. The Merkle commitment in the ROM: CY's extractability notion (they extract from the RO query trace — a GLOBAL online object). How does that interact with the design's WorldSpec Γ (RO as persistent world) vs SourceCtx Δ split? Is the design's "commitment backend capability records" taxonomy (§6.10.7) able to express CY's exact Merkle properties (their extractability game, multi-extraction, corner cases: duplicate leaves, tree padding, salted leaves)?
b. BCS soundness: CY prove it via STATE RESTORATION soundness of the IOP (not plain soundness). Trace the exact reduction: adversary against BCS argument -> state-restoration prover against IOP, using RO trace to reconstruct a "computation tree"/database. What does the design need to express this reduction? Does §6.6 have state-restoration as a first-class game with the required replay/resource-identity semantics? Is the "computation tree from RO trace" expressible?
c. BCS knowledge soundness: extractor gets the RO query-answer trace; runs Merkle extraction to get IOP transcripts; invokes the IOP's (state-restoration) knowledge extractor. Check against the design's extractor taxonomy (§6.6.4) — which named point in the taxonomy is this exactly, and is the required composition of extractors (Merkle extractor ∘ IOP extractor) supported by the stated bridge theorems?
d. Zero knowledge: CY's BCS ZK uses salted Merkle leaves + honest-verifier ZK of the IOP. The design deliberately defers ZK. What objects would salting force (per-leaf randomness, hiding capability records, simulator for RO)?
e. CY's exact error bounds (their "Error bounds" chapter + per-theorem epsilons): can the design's error accounting (ε_s, ε_adm, ε_fault, κ path accumulation, backend multi-instance errors) represent CY's bounds compositionally, or is there a mismatch (e.g. CY count RO queries globally across phases; the design's Γ is per-world)?
f. CY restricted vs unrestricted BCS (they have variants: nonadaptive queries, restricted completeness); their treatment of IOP verifier randomness; their notion of "oracle-derived" randomness. Map each variant.
g. Preprocessing/holography chapter: does ResourceMeta.origin + the design's setup story suffice for CY's preprocessing arguments?
h. The "arguments in general oracle settings" chapter (they generalize beyond one RO): does WorldSpec cover their generality?

### Part 2: Complication catalog
List, severity-ranked, every place where formalizing CY in this design would hit friction the design doc does not currently acknowledge. Be concrete: name the CY theorem, the design section, and the missing lemma/object. Include Lean-specific pain (e.g. probability bookkeeping over RO tables, adaptive query counting, forking across a shared world).

### Part 3: Missed insights / consolidation
Given the textbook's viewpoint, are there abstractions CY use that the design should adopt (e.g. their "oracle algorithms with query budgets", their transcript-tree machinery, their specific game-hopping style)? Any place where the design's factoring (RepresentOracles/LowerAccesses/TransportBoundary/FiatShamir) does or does not match CY's proof structure for BCS? Would CY's proofs factor through the design's pipeline or fight it?

Write the complete markdown report as your final answer. Cite textbook line numbers and design-doc section numbers throughout. Be adversarial; do not assume the design works.
