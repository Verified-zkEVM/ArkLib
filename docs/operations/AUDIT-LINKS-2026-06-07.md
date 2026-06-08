# ArkLib audit — issues & pull requests (2026-06-07)

Open-source fork: **[awidearray/ArkLib](https://github.com/awidearray/ArkLib)** (public)

Upstream target: **[Verified-zkEVM/ArkLib](https://github.com/Verified-zkEVM/ArkLib)**

---

## Fork branches

| Branch | Link |
|--------|------|
| `fix/larp-audit-honesty-labeling` | https://github.com/awidearray/ArkLib/tree/fix/larp-audit-honesty-labeling |
| `refactor/issue-110-grand-challenges-lattice-split` | https://github.com/awidearray/ArkLib/tree/refactor/issue-110-grand-challenges-lattice-split |
| `chore/production-readiness-infrastructure` | https://github.com/awidearray/ArkLib/tree/chore/production-readiness-infrastructure |

---

## Audit findings (issues on upstream)

| # | Title | Link |
|---|--------|------|
| 550 | Infrastructure: `lake exe cache get` fails with HTTP 403 in restricted networks | https://github.com/Verified-zkEVM/ArkLib/issues/550 |
| 551 | Audit: Grand Challenge prize resolution formalizes collapsed predicates, not external conjectures | https://github.com/Verified-zkEVM/ArkLib/issues/551 |
| 552 | Audit: 10 allowlisted residual axioms remain paper imports in flagship paths | https://github.com/Verified-zkEVM/ArkLib/issues/552 |
| 553 | Audit: Proximity prize open issues #138–#141 blocked on research mathematics | https://github.com/Verified-zkEVM/ArkLib/issues/553 |

---

## Fix pull requests — upstream (`Verified-zkEVM/ArkLib`)

| PR | Title | Related issues | Link |
|----|--------|----------------|------|
| 554 | fix(audit): honest axiom naming and sorry-tracker fetch behavior | #551, #552 | https://github.com/Verified-zkEVM/ArkLib/pull/554 |
| 555 | refactor(#110): split GrandChallengesLattice into focused submodules | #110, #551 | https://github.com/Verified-zkEVM/ArkLib/pull/555 |
| 556 | chore: production-readiness infrastructure and security scanning | #550 (blocker for full validate) | https://github.com/Verified-zkEVM/ArkLib/pull/556 |

---

## Fix pull requests — your fork (`awidearray/ArkLib`)

| PR | Title | Upstream mirror | Link |
|----|--------|-----------------|------|
| 1 | fix(audit): honest axiom naming and sorry-tracker fetch behavior | #554 | https://github.com/awidearray/ArkLib/pull/1 |
| 2 | refactor(#110): split GrandChallengesLattice into focused submodules | #555 | https://github.com/awidearray/ArkLib/pull/2 |
| 3 | chore: production-readiness infrastructure and security scanning | #556 | https://github.com/awidearray/ArkLib/pull/3 |

---

## Issue ↔ PR map

| Issue | What it tracks | Addressed by |
|-------|----------------|--------------|
| [#550](https://github.com/Verified-zkEVM/ArkLib/issues/550) | Mathlib cache HTTP 403 — blocks full `validate.sh` | Open; noted on [#556](https://github.com/Verified-zkEVM/ArkLib/pull/556) |
| [#551](https://github.com/Verified-zkEVM/ArkLib/issues/551) | Prize “resolution” = collapsed predicates, not external conjectures | Partial: [#554](https://github.com/Verified-zkEVM/ArkLib/pull/554), [#555](https://github.com/Verified-zkEVM/ArkLib/pull/555) |
| [#552](https://github.com/Verified-zkEVM/ArkLib/issues/552) | 10 allowlisted residual paper axioms | Naming fix: [#554](https://github.com/Verified-zkEVM/ArkLib/pull/554); proofs still open |
| [#553](https://github.com/Verified-zkEVM/ArkLib/issues/553) | #138–#141 blocked on research math | Informational; no close PR |

---

## Supporting docs (in [#556](https://github.com/Verified-zkEVM/ArkLib/pull/556) / fork PR #3)

- [Production readiness checklist](PRODUCTION-READINESS.md)
- Branch: `chore/production-readiness-infrastructure`
