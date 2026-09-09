#!/usr/bin/env python3
"""Check the import boundary of the mathematical RS entry points.

Lean parses import headers; this script traverses local imports and classifies
modules by the repository's naming conventions. This is a dependency-regression
check, not a semantic purity or axiom check.
"""

from functools import cache
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parent.parent
LOCAL_LIBRARY = ROOT / ".lake/build/lib/lean"
PREFIX = "ArkLib.Data.CodingTheory.ReedSolomon."
ENTRY_POINTS = (
    "ListDecodability.Capacity",
    "HiddenDerivative.Interpolation.Symbolic.ReceivedLine",
    "HiddenDerivative.RootFinding.Counting.TaylorAllSolutions",
    "HiddenDerivative.RootFinding.Counting.TaylorCharZeroSolutions",
    "ListDecodability.Capacity.CodewordBound",
    "MutualCorrelatedAgreement.Capacity",
    "ListDecodability.FirstOrder.Bounds",
    "ListDecodability.FirstOrder.Uniform",
    "ListDecodability.FirstOrder.Profile",
    "MutualCorrelatedAgreement.FirstOrder.Bounds",
    "MutualCorrelatedAgreement.FirstOrder.RateBounds",
    "MutualCorrelatedAgreement.Johnson.Agreement",
)
GENERIC_ENTRY_POINTS = (
    "ArkLib.Data.Polynomial.Differential.Basic",
    "ArkLib.Data.Polynomial.Differential.DerivativeDescent",
    "ArkLib.ToMathlib.Combinatorics.DiscreteSimplex.Variance",
    "ArkLib.ToMathlib.LinearAlgebra.ShiftedDegreeKernel",
    "ArkLib.ToMathlib.Analysis.Simplex.Moments",
    "ArkLib.ToMathlib.AlgebraicGeometry.Incidence.ProductBounds",
)


@cache
def imports(module):
    source = ROOT / (module.replace(".", "/") + ".lean")
    result = subprocess.run(
        ["lean", "--deps", str(source)], cwd=ROOT,
        capture_output=True, text=True, check=True,
    )
    local = []
    for line in result.stdout.splitlines():
        try:
            dependency = Path(line).relative_to(LOCAL_LIBRARY)
        except ValueError:
            continue
        if dependency.suffix == ".olean" and dependency.parts[0] == "ArkLib":
            local.append(".".join(dependency.with_suffix("").parts))
    return tuple(local)


def execution_module(module):
    return (module.startswith("ArkLib.Data.Computation.") or
            module.startswith(PREFIX + "Computation.") or
            module in (PREFIX + "Decoding.CapacityDecoder",
                       PREFIX + "ListDecoding.CapacityDecoder")) or any(
        word in module.rsplit(".", 1)[-1]
        for word in ("Machine", "Execution", "Cost", "Semantics", "Refinement")
    )


def main():
    failed = False
    for root in tuple(PREFIX + entry for entry in ENTRY_POINTS) + GENERIC_ENTRY_POINTS:
        pending = [(root, [])]
        seen = set()
        while pending:
            module, ancestors = pending.pop()
            if module in seen:
                continue
            seen.add(module)
            path = ancestors + [module]
            if execution_module(module) or (
                root in GENERIC_ENTRY_POINTS and
                module.startswith("ArkLib.Data.CodingTheory.")
            ):
                print("Forbidden dependency: " + " -> ".join(path), file=sys.stderr)
                failed = True
            pending.extend((child, path) for child in imports(module))
        print(f"{root}: checked {len(seen)} local modules", flush=True)
    return int(failed)


if __name__ == "__main__":
    if sys.argv[1:] != ["--lake-env"]:
        # Establish the pinned Lean executable and package search paths once,
        # rather than launching Lake separately for every source module.
        sys.exit(subprocess.call(
            ["lake", "env", "python3", str(Path(__file__).resolve()), "--lake-env"],
            cwd=ROOT,
        ))
    sys.exit(main())
