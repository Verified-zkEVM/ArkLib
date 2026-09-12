# Worker E: independently review the foundation checkpoint

Read [shared instructions](README.md). Review only the supplied immutable checkpoint.
Do not write code or push a branch. You must not have authored the implementation.

Inspect the new tower, preprocessing, agreement-recovery, and hidden-derivative decoder
modules and their tests. Trace executable calls separately from semantic theorems.
Check the scope of exactness claims, extension-point coverage, finite-algebra assumptions,
dispatch priorities, characteristic guards, and support-construction hypotheses.

Look for proof statements that assume their intended conclusion, proof/runtime mismatches,
unused batching, hidden enumeration or oracle inputs, and untested failure branches.
The checkpoint openly leaves symbolic decoding unavailable, batching disconnected,
inversion/materialization missing, and partition accounting unfinished: assess whether
its claims accurately reflect those gaps rather than reporting them as surprises.

Return severity-ranked findings with commit-pinned paths and lines, concrete mathematical
or runtime consequences, and suggested fixes. Distinguish verified issues from questions.
List checks actually run and the limitations of read-only connector inspection.
Do not certify Milestone 1 or complete paper-decoder correctness from this checkpoint.
