# Bit-RAM backend for Reed–Solomon decoding

Historical decoder development record, preserved from commit `765ae773`. Checkpoint statements
and remaining-work lists below describe that development stage. Current mathematical owners are
`ListDecodability/Capacity.lean` and `MutualCorrelatedAgreement/Capacity.lean`; the executable endpoint
is `ListDecoding/CapacityDecoder.lean`. The September 6 no-band revision migrates that endpoint
without adding a whole-decoder bit/RAM complexity claim.


This note records the route from the proved primitive-work decoder to a bit-cost decoder.
The implementation includes **address-serial bit RAM** access, shared-memory list operations,
literal scalar arithmetic, and a physical quadratic-arithmetic dispatcher. It does not yet prove
the complete decoder's bit complexity, tape-machine complexity or native Lean running time.

## Current frontier, September 5 sprint

The actual coordinate decoder and both primitive-work regimes are assembled in
[`CoordinateCapacityExecution.lean`](../../ArkLib/Data/CodingTheory/ReedSolomon/ListDecoding/Coordinate/CoordinateCapacityExecution.lean)
and exposed by the public `Capacity.lean` theorem. This completes coordinate lowering, not its
binary compilation. The following lower-level components are proved and independently audited:

- Fixed-width addition, multiplication, negation, prime-field inverse search and equality retain
  their physical operand/modulus words. Register instructions handle source/destination aliasing.
- Shared-heap allocation and reads preserve the same memory and list representation. The closed
  shared-memory Horner loop physically initializes zero and executes its arithmetic children.
- Eight scalar registers and two flags are physically initialized; loads restore their sources;
  pair and Boolean emission produce actual output words.
- `QuadraticArithmeticBitProgram` executes the finite source instruction lists through those
  children on the same 28 tapes. Launches and returns preserve the physical bank; equality adopts
  the new flag. Its child traces and initialization are proved, but its generic whole-program
  refinement and total bound are still separate obligations.
- `FiniteHeadProgram` restricts dispatch to finite labels and current head bits. Word copying and
  zero/one construction have exact refinements into that model. Injective static placement proves
  those executions preserve all unowned tapes. This is not yet a compiler for every child or RAM
  instruction, and simultaneous tape actions are not silently identified with serial bit steps.
- `HeapAllocationBudget` derives one allocator call's no-overflow premise from a remaining budget.
  The decoder-wide lifetime allocation bound needed to initialize that budget remains unproved.

The next implementation steps are therefore composition and adequacy, not another arithmetic
specification: prove the scalar dispatcher's generic execution/cost theorem; lower the remaining
coordinate controller clauses and administrative arithmetic; establish input-based bounds for
every word, counter and lifetime allocation; then account for external input/output and prove
the final bit-cost bound for one closed program. A component `BankStep` theorem alone cannot
exclude branching on hidden tape tails and is not accepted as finite-control adequacy.

## Implemented boundary

[`AddressedBits.lean`](../../ArkLib/Data/Computation/AddressedBits.lean) defines finite trie memory
and a literal controller. Its fixed instructions are start, transfer, restore, access, reset, and
halt. Operation data are either read or write one Boolean. No instruction accepts an arbitrary
function or a source-decoder callback.

An `Address` is a binary path with an implicit leading one. Its canonical wire word is
`true :: address`. The empty path addresses the root (binary one); zero is reserved and has no
`Address` representation. Paths starting with false are valid: `[false]` has wire word `[true,
false]`, whereas an *unprefixed raw wire word* starting with false is rejected. Distinct paths
select distinct trie cells. The controller also rejects an empty raw wire word.

The input path is already materialized on a local tape. Start writes the leading one. Transfer
consumes one input bit and pushes it onto the bus per transition. Restore reverses those bits
one at a time. Access then reads or writes one addressed bit. Reset erases every bus bit before
returning the result. These local bit-stack transitions have a fixed finite instruction vocabulary;
they do not model arbitrary heap-list operations as free tape operations.

**Architectural assumption:** the terminal access transition performs a random read/write of one
bit at the fully transferred address. Its routing latency is stipulated as one RAM transition.
`Memory.lookup` and `Memory.write` provide executable finite-trie denotations for that operation.
Their recursive host evaluation is not asserted to take one step, and it is not a tape simulation.
No arbitrary `Nat → Bool` oracle is supplied by a client.

[`AddressedBitsSemantics.lean`](../../ArkLib/Data/Computation/AddressedBitsSemantics.lean) proves:

- The literal run takes exactly `3 * address.length + 8` bit-RAM transitions, including transfer,
  restoration, access, and full reset.
- `execution_runFuel` observes the same final state as `execution_trace`; the observer's host fuel
  recursion is outside the architectural transition semantics.
- `read_correct` preserves the entire memory and returns the addressed bit.
- `write_correct` returns the actual updated memory, changes the addressed bit, and preserves every
  other address in that same run.
- Empty and zero-prefixed raw wire words return failure after reset without touching memory.

Memory equality is observational: redundant all-zero trie nodes are allowed. `Memory.Equivalent`
and its write-congruence theorem preserve lookup observations without asserting equality of trie
shapes. The overwrite canary uses the actual controller for writes and reads at distinct addresses,
including the empty path, and checks early fuel and malformed wire inputs.

## Dependency map

The outline below separates the original work packages. The frontier above identifies their
proved components; none of the packages is considered globally complete merely from local traces.

1. **Binary arithmetic code.** Implement literal bit loops for copying, comparison, carry addition,
   saturating subtraction, multiplication, and division/remainder. Prove decoded results and actual
   transition bounds. `Nat` and `BitVec` arithmetic remain semantic specifications until lowered.
2. **Prime-field arithmetic.** Encode `ZMod q` by integers in `[0,q)`. Reduce addition, multiplication,
   negation, equality, casts, and constants to binary code. A first inverse may scan at most `q`
   possible inverses using modular multiplication, with zero handled separately. This adds an
   absolute polynomial factor in `q`; it does not prove the general root theorem's poly(log q)
   arithmetic factor. Then instantiate the existing quadratic coordinate programs.
3. **Shared heap representation.** Give tags, fields, binary pointers, and a structural
   `RepList heap pointer values` relation. A cons allocates its own fields and retains the tail
   pointer. Prove allocation freshness, frame/extension laws, and live DAG validity. Retaining
   garbage is sufficient if cumulative allocation is bounded. Copying a pointer costs its width.
4. **Actual source-clause refinement.** Compile the existing concrete successors and recursive
   functions into fixed literal code, including calls, return frames, failure, and state wrappers.
   Coordinate solver lowering is an independent prerequisite. Do not use a whole source function
   as an oracle instruction or select code based on its desired answer.
5. **Widths and administration.** Derive input-based bounds for every live integer, address,
   exponent, dimension, ledger, fuel counter, and frame. Catalogue executable budget/length/mass
   calculations separately from proof-only bounds. Either lower source fuel bookkeeping, or prove
   a literal fuel-free runner equivalent to the same terminal execution and charge its loop.
6. **Closed decoder and serialization.** Include input parsing/materialization and emission of each
   output bit. Returning a heap pointer is not the external output contract. For fixed real gap
   `delta`, the natural constants `d,m` can be fixed program constants; this does not require an
   executable operation on arbitrary real numbers.

The local adequacy obligation is noncircular: given an actual source successor and a structural
representation of its initial state, fixed authored clause code has an actual bit-RAM run to a
representation of that **same successor**, within an explicit bound. Code is independent of the
output witness; representation is independent of successful execution. The closed theorem must
discharge every scalar, width, and administration premise. An arbitrary weighted cost function or
assumed per-step polynomial bound cannot serve as the backend.

## Preserve the candidate exponent

Let `T` bound primitive work, `I` input work, `O` serialization, and `H` the separately derived
administration omitted by the source ledger. A suitable target is linear in `T + I + O + H + 1`,
times fixed polynomials in `q` and the numeric/address bit widths. Address width depends
logarithmically on cumulative allocation; its bound must include scratch space and be proved before
use. Reading a `w`-bit word through this interface costs conservatively `O(w * (a + 1))` for
`a`-bit addresses. No whole-memory scan is needed for an access.

If `T ≤ C_delta * q^(e*d + a)`, with `e = 2` or `1` and absolute `a`, logarithmic addressing and
fixed-degree arithmetic overhead can retain the candidate exponent with an additive absolute
power of `q`. A whole-memory scan per source primitive could instead produce `T²`, multiplying
the coefficient of `d`. Neither the width/administration bounds nor a numerical final exponent
are established by this first prerequisite.

The final public theorem should name a fixed **address-serial bit-RAM program**, its binary input
and exact serialized output, and its bit-RAM transition bound in both field regimes. It must remain
explicitly RAM-relative until another model-adequacy theorem is proved.

## Frozen audit evidence

The design audit used lane head `14661c868d7f6bad535428740160e6142780a185` and central snapshot
`178af4b255384427e698aa0f48411b0e35c7c7b6`. The manuscript source was
`9e4d6488ead94be47cca69e5be915b5667143b66`, read from the local
`all-rate-rs-list-decoding` repository. Section 07 specifies binary sparse exponents and bit
operations; section 08 gives the two candidate exponents, without specifying RAM versus tape.
The requested additive absolute overhead is stronger than its displayed `O_delta(1)` notation.

The environment was Lean `v4.33.1`, with these committed dependency revisions:

| Dependency | Revision |
|---|---|
| Mathlib | `0df444a360eaa60ab8c11dca51a86af692955474` |
| cslib | `98e395a701f2027a413ad24729e1a11a6c772eb4` |
| PolyFun | `c0c923693fc827a41d17116579a0c16ed4873b19` |
| VCVio | `f9dc47d9dacfc5cb51dae9f92f1e34cb5ce2cc24` |
| CompPoly | `a09455a22fea4623a2a1c5b363cf6efc61486a83` |

The full manifest had blob `ea80bd6c6541694266877ea8326ed5838dce8059`. No pins were updated.
These reusable facts exist at those pins:

| Source | Available evidence and limitation |
|---|---|
| Mathlib `Data/Nat/Bits`, `Data/Nat/Size` | `bits`, `size_le`, `size_eq_bits_len`: representation and width facts |
| Mathlib `Data/ZMod/Basic` | `val_natCast`, `val_injective`, `val_add`, `val_mul`: scalar representation laws |
| Lean `Init/Data/BitVec/Lemmas` | `toNat_add`, `toNat_mul`: word semantics, without time certificates |
| Mathlib `Computability/StateTransition` | `EvalsToInTime.trans`: additive transition-count composition |
| Mathlib `Computability/TuringMachine/Computable` | Finite machine and time predicates; `TM2ComputableInPolyTime.comp` is `proof_wanted` |
| cslib `Computability/Machines/Turing/MultiTape/Deterministic` | Tape transition/time/space framework, without the needed addressed-heap compiler |
| PolyFun `Realizability/Quantitative/WordClass` | Adapter explicitly leaves standard-model adequacy to the backend |
| VCVio `CryptoFoundations/Asymptotics/ComputationalComplexity` | Explicitly backend-relative resource framework |
| ArkLib `QuadraticAlgebra/ArithmeticMachine` | Literal coordinate programs awaiting base-field bit lowering |
| ArkLib `List/CartesianProductMachine` | Concrete suffix sharing and separately charged list allocations |

The inspected library paths supplied no ready same-program bit backend or sharp tape simulation
for the decoder. The `proof_wanted` declaration supplies no proved compiler closure. Source ledgers
such as `InterpolationSupportMachine`, `NonzeroInterpolationMachine`, and `SeparateSampleExecution`
explicitly leave the relevant bit and host-administration obligations outside their present bounds.
