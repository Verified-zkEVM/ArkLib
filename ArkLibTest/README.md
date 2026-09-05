# ArkLib acceptance tests

Put compile-time examples and regression tests here, mirroring the production module path.
Import the smallest production modules needed. Production files under `ArkLib/` must not import
`ArkLibTest`; the source-policy gate checks this boundary.

Run `lake test` to build every Lean module under this directory. No test umbrella needs updating.
`lake build` builds the production library independently; `./scripts/validate.sh` runs both targets
and rejects all test warnings, including admissions. Stage new tests before running validation so
the source-policy and source-trust inventory tools include them.

These acceptance tests share the production lint plugin and source-style policy. Deliberately
invalid policy and axiom-sweep fixtures remain in their dedicated directories under `scripts/`.
The kernel axiom baseline covers the production library; the source-trust inventory includes both
production and acceptance-test sources.
