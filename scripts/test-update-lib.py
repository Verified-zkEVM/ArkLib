#!/usr/bin/env python3
"""Check import wrapping and output preservation when tracked-file inputs are rejected."""

from pathlib import Path
import subprocess
import tempfile


GENERATOR = Path(__file__).resolve().with_name("update-lib.sh")


def run(repo: Path, *args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(args, cwd=repo, capture_output=True, text=True, check=False)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="arklib-import-fixtures-") as temp:
        repo = Path(temp)
        (repo / "ArkLib").mkdir()
        target = repo / "ArkLib.lean"
        target.write_text("original output\n")
        subprocess.run(["git", "init", "-q"], cwd=repo, check=True)

        cases = [
            (8, "public import {module}\n"),
            (86, "public import {module}\n"),
            (87, "public import\n  {module}\n"),
            (98, "public import\n  {module}\n"),
            (99, "public import\n{module}\n"),
            (100, "public import\n{module}\n"),
        ]
        modules = ["ArkLib." + "A" * (length - 7) for length, _ in cases]
        for module in modules:
            path = repo / (module.replace(".", "/") + ".lean")
            path.write_text("module\n")
        subprocess.run(["git", "add", "ArkLib"], cwd=repo, check=True)

        expected = "module\n\n" + "".join(
            template.format(module=module) for module, (_, template) in zip(modules, cases)
        )

        for _ in range(2):
            result = run(repo, "bash", str(GENERATOR))
            require(result.returncode == 0, result.stderr)
            require(target.read_text() == expected, "Generated imports differ from the fixtures")
            require(all(len(line) <= 100 for line in target.read_text().splitlines()),
                    "A generated line exceeds 100 characters")

        untracked = repo / "ArkLib/Untracked.lean"
        untracked.write_text("module\n")
        result = run(repo, "bash", str(GENERATOR))
        require(result.returncode != 0, "Untracked source was accepted")
        require("Untracked Lean files" in result.stderr, result.stderr)
        require(target.read_text() == expected, "Rejected input replaced the umbrella")
        untracked.unlink()

        oversized = "ArkLib." + "A" * (101 - 7)
        path = repo / (oversized.replace(".", "/") + ".lean")
        path.write_text("module\n")
        subprocess.run(["git", "add", str(path.relative_to(repo))], cwd=repo, check=True)
        result = run(repo, "bash", str(GENERATOR))
        require(result.returncode != 0, "An oversized module name was accepted")
        require("Module name exceeds 100 characters" in result.stderr, result.stderr)
        require(target.read_text() == expected, "Rejected input replaced the umbrella")

    print("Import generation fixtures passed.")


if __name__ == "__main__":
    main()
