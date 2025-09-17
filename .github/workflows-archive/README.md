# Archived Workflows

This directory contains old GitHub Actions workflows that are no longer active but kept for reference.

## Files

- **`blueprint-old.yml`** - Original monolithic workflow that handled building, blueprint generation, API docs, and deployment all in one. Replaced by separate focused workflows:
  - `check-imports.yml` - Import validation
  - `ci.yml` - Basic build and test
  - `docs.yml` - Documentation and blueprint generation

## Why Archived

The old blueprint workflow had several issues:
- Duplicate builds with CI workflow
- Cache race conditions
- Overly complex single workflow doing multiple jobs
- Cache timing bugs (saved after build instead of before)

The new structure follows Lean community best practices with focused, composable workflows.
