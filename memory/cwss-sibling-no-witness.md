---
name: cwss-sibling-no-witness
description: Why the CWSS⇒KS additive bound must be proven in langOut failure-form, not relOut
metadata:
  type: project
---

In the CWSS ⇒ knowledge-soundness work (`Security/Implications/CoordinateWiseSpecialSoundnessRewinding.lean` + `docs/cwss-seeded-replay-plan.md`), the KS `accept` event is `(stmtOut, witOut) ∈ relOut` and `ε := Pr[accept]` is fixed by `knowledgeSoundnessRewinding`. But `ProtocolSpec.SiblingRun` carries only `(transcript, stmtOut)` — **no output witness**. So the rewinding collector and the heavy-lines counting can only test `stmtOut ∈ relOut.language` (`Set.language = Prod.fst '' relOut`), never the full relation.

**Why:** the reverse-induction / heavy-lines apparatus is therefore necessarily langOut-based (`L := stmtOut ∈ langOut`); it cannot carry the relation event `A := accept`.

**How to apply:** prove the additive bound in **failure form** `Pr[L ∧ ¬succeed] ≤ κ` (base of the recursion is `Pr[L]`, not `ε`), then connect to the relation event ONCE at the top via the trivial inclusion `A ⟹ L`: `Pr[A∧¬succeed] ≤ Pr[L∧¬succeed] ≤ κ`, hence `Pr[A∧succeed] ≥ ε−κ`. Do NOT claim `extractable ⟹ accept` or `T_{μ+1}=ε`. Also: the extractor's definition needs `[DecidablePred (· ∈ relOut.language)]` (collector branches on `if stmtOut ∈ langOut`).
</content>
