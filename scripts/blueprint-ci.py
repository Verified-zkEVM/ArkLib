#!/usr/bin/env python3
"""Check renderer completion and stage outputs in a fresh directory outside the project."""

import argparse
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


def require_success(result):
    if result != "success":
        raise ValueError(f"Blueprint rendering did not succeed: {result or 'missing result'}")


def stage_artifact(project, output):
    if output.resolve().is_relative_to(project.resolve()):
        raise ValueError("The artifact output directory must be outside the project")
    for ancestor in (project / "blueprint", project / "home_page"):
        if ancestor.is_symlink():
            raise ValueError(f"Generated output parent is a symlink: {ancestor.name}")
    files = (Path("blueprint/lean_decls"), Path("home_page/blueprint.pdf"))
    web = Path("home_page/blueprint")
    for relative in (*files, web):
        source = project / relative
        if source.is_symlink():
            raise ValueError(f"Generated output is a symlink: {relative}")
        if not (source.is_dir() if relative == web else source.is_file()):
            raise ValueError(f"Missing generated output: {relative}")
    for source in (project / web).rglob("*"):
        if source.is_symlink() or {".git", ".lake"}.intersection(source.relative_to(project).parts):
            raise ValueError(f"Unexpected generated output: {source.relative_to(project)}")
    output.mkdir(parents=True, exist_ok=False)
    for relative in files:
        target = output / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(project / relative, target)
    shutil.copytree(project / web, output / web)


class BlueprintCITests(unittest.TestCase):
    def test_actual_result_command_rejects_all_non_success_outcomes(self):
        for result in ("success", "failure", "cancelled", "skipped", "", "unexpected"):
            with self.subTest(result=result):
                environment = os.environ.copy()
                environment.pop("BLUEPRINT_JOB_RESULT", None)
                if result:
                    environment["BLUEPRINT_JOB_RESULT"] = result
                completed = subprocess.run(
                    [sys.executable, str(Path(__file__).resolve()), "require-success"],
                    env=environment, capture_output=True, text=True, check=False,
                )
                self.assertEqual(completed.returncode, 0 if result == "success" else 1)
                if result != "success":
                    self.assertIn("Blueprint rendering did not succeed", completed.stderr)

    def fixture(self, directory):
        project = Path(directory) / "project"
        for name, data in (
            ("blueprint/lean_decls", "Nat.add"),
            ("home_page/blueprint.pdf", "%PDF"),
            ("home_page/blueprint/index.html", "<html></html>"),
            ("home_page/blueprint/assets/style.css", "body {}"),
            ("home_page/blueprint/.nojekyll", ""),
            ("home_page/blueprint/.assets/hidden.css", "body {}"),
            (".lake/build/private", "not an output"),
            (".git/config", "not an output"),
            ("env/credentials", "not an output"),
        ):
            path = project / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(data)
        return project, Path(directory) / "artifact"

    def test_staging_copies_only_generated_outputs(self):
        with tempfile.TemporaryDirectory(prefix="arklib-blueprint-ci-") as directory:
            project, output = self.fixture(directory)
            stage_artifact(project, output)
            self.assertEqual(
                {str(path.relative_to(output)) for path in output.rglob("*") if path.is_file()},
                {"blueprint/lean_decls", "home_page/blueprint.pdf",
                 "home_page/blueprint/index.html", "home_page/blueprint/assets/style.css",
                 "home_page/blueprint/.nojekyll", "home_page/blueprint/.assets/hidden.css"},
            )
            self.assertEqual((output / "blueprint/lean_decls").read_text(), "Nat.add")
            with self.assertRaises(FileExistsError):
                stage_artifact(project, output)

    def test_staging_rejects_output_inside_the_project(self):
        for relative in ("artifact", "home_page/blueprint/artifact"):
            with self.subTest(relative=relative):
                with tempfile.TemporaryDirectory(prefix="arklib-blueprint-ci-") as directory:
                    project, _ = self.fixture(directory)
                    output = project / relative
                    with self.assertRaisesRegex(ValueError, "outside the project"):
                        stage_artifact(project, output)
                    self.assertFalse(output.exists())

    def test_staging_rejects_missing_linked_and_cache_outputs(self):
        for malformed in (
            "missing", "linked_file", "linked_directory", "linked_blueprint", "linked_home_page",
            "cache",
        ):
            with self.subTest(malformed=malformed):
                with tempfile.TemporaryDirectory(prefix="arklib-blueprint-ci-") as directory:
                    project, output = self.fixture(directory)
                    if malformed == "missing":
                        (project / "blueprint/lean_decls").unlink()
                    elif malformed == "linked_file":
                        (project / "home_page/blueprint.pdf").unlink()
                        (project / "home_page/blueprint.pdf").symlink_to(project / ".git/config")
                    elif malformed == "linked_directory":
                        (project / "home_page/blueprint/leak").symlink_to(project / ".lake")
                    elif malformed in ("linked_blueprint", "linked_home_page"):
                        name = "blueprint" if malformed == "linked_blueprint" else "home_page"
                        destination = Path(directory) / "outside"
                        shutil.move(str(project / name), destination)
                        (project / name).symlink_to(destination, target_is_directory=True)
                    else:
                        (project / "home_page/blueprint/.lake").mkdir()
                    with self.assertRaises(ValueError):
                        stage_artifact(project, output)
                    self.assertFalse(output.exists())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("require-success", "stage-artifact", "self-test"))
    parser.add_argument("output", nargs="?", type=Path)
    arguments = parser.parse_args()
    if arguments.command == "self-test":
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(BlueprintCITests)
        return 0 if unittest.TextTestRunner(verbosity=2).run(suite).wasSuccessful() else 1
    try:
        if arguments.command == "require-success":
            require_success(os.environ.get("BLUEPRINT_JOB_RESULT"))
        else:
            if arguments.output is None:
                parser.error("stage-artifact requires an output directory")
            stage_artifact(Path.cwd(), arguments.output)
    except (OSError, ValueError) as error:
        print(error, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
