# Production readiness

Operational checklist for deploying ArkLib changes to `main`. Evidence for each
item is produced by `./scripts/production-readiness-check.sh` (static gates) and
`./scripts/validate.sh` (full Lean build gates).

## Checklist

| # | Gate | Evidence command | CI workflow |
|---|------|------------------|-------------|
| 1 | Real tests, no mocks | `./scripts/production-readiness-check.sh` + `./scripts/validate.sh` | `.github/workflows/ci.yml` |
| 2 | Fail-loud error handling | `production-readiness-check.sh` §2 | same |
| 3 | Externalized config / no secrets in repo | `production-readiness-check.sh` §3 | review workflows use `secrets.*` |
| 4 | Performance under load | CI `build_timing_report.sh` artifacts | `ci.yml`, `build-timing-report.yml` |
| 5 | Pinned deps + security scan | `bash scripts/security-scan.sh` | `security-scan.yml` |
| 6 | Rollback path | this document § Rollback | `release-tag.yml` |
| 7 | Monitoring / alerting | this document § Monitoring | `ci.yml`, `build-timing-report.yml` |

## Rollback

ArkLib is a library, not a long-running service. Rollback means reverting the
git commit on `main` and restoring a known-good Lean toolchain tag.

### Before merge

1. Confirm `./scripts/validate.sh` passes on the PR branch (CI green).
2. Note the merge-base SHA (`git merge-base origin/main HEAD`).

### After a bad merge to `main`

1. **Identify last good commit**
   ```bash
   git log --oneline -20 origin/main
   ```
2. **Revert the bad commit** (preferred — preserves history):
   ```bash
   git revert <bad-sha> -m 1
   git push origin main
   ```
   Or reset only if policy allows force-push to `main` (discouraged).
3. **Restore Lean toolchain alignment**: if `lean-toolchain` changed, the
   `release-tag.yml` workflow tags releases on toolchain bumps; check tags on
   GitHub and pin consumers to the previous tag.
4. **Verify rollback**
   ```bash
   lake exe cache get
   ./scripts/validate.sh
   ```

### Cache / build rollback

CI caches `.lake` keyed on `lake-manifest.json`
(`actions/cache` in `ci.yml`). After rollback, a manifest change invalidates
the cache automatically; no manual cache purge is required.

## Monitoring

| Signal | Mechanism | Alert surface |
|--------|-----------|---------------|
| Build / test failure | `CI` workflow on every PR and `main` push | GitHub required checks |
| Build time regression | `build-timing-report.yml` posts PR comment vs baseline | PR comment (`<!-- arklib-build-timing-report -->`) |
| New proof holes | `sorry_census.py --fail-on-holes` in CI | CI failure |
| Laundering tokens / rogue axioms | `forbidden_tokens.py` precheck | CI failure |
| Flagship axiom drift | `axiom_audit.py` post-build | CI failure |
| Proximity prize clean-room | `proximity_prize_cleanroom_audit.py` | CI failure (via `validate.sh`) |
| Python dependency CVEs | `security-scan.yml` / `security-scan.sh` | CI failure |
| New `sorry` on `main` push | `sorry-tracker.yml` opens labeled issues | GitHub Issues |

There is no external APM (Datadog/Sentry) — appropriate for a formal-methods
library whose runtime is batch CI.

## Secrets

| Secret | Used by | Never commit |
|--------|---------|--------------|
| `GITHUB_TOKEN` | CI, sorry-tracker, release-tag | — (injected by Actions) |
| `GEMINI_API_KEY` | `summary.yml`, `review.yml` optional AI | yes |

Local Gemini usage for `sorry-tracker.py --model ...` requires
`gcloud auth application-default login` or equivalent; not stored in repo.

## Local preflight

```bash
bash scripts/production-readiness-check.sh   # fast, no Lean
./scripts/validate.sh                        # full mirror of CI
```
