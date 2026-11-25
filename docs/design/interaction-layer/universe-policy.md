# Universe policy: evidence and workarounds

Record [D2](../interaction-rebuild/D2-ownership-and-universes.md#universe-policy) states the
policy. This document records why: what the earlier universe ledger cost, the Lean experiments
behind each failure, the options compared, and the workaround for each thing the policy rules
out. Counts were taken on main `16c12705` (2026-11-25); the declaration scan ran on `98aaeee1`,
which has the same core. The Lean snippets are excerpts from
[`prototypes/UniversePolicy.lean`](prototypes/UniversePolicy.lean), which records each expected
error with `#guard_msgs` and checks with `lake env lean` from a built worktree.

## The policy in one table

| Object | Universe | Parameter |
|---|---|---|
| Data: moves, challenges, query and response types, oracle indices, statements, witnesses, transcripts, costs | `Type` | none |
| Descriptions of data: positions, protocols, oracle interfaces, families and bundles, problem bundles | `Type 1` | none |
| Adversaries and extractors | `Type w` | one, determined by the model argument |
| Effects: the result universe of a generic monad `m : Type → Type v` | `Type v` | one, determined by the monad argument; the input universe stays `Type` |
| Generic polynomial machinery | PolyFun's universes | determined by `P` |

**Rule.** Every universe parameter occurs in the type of some argument.

## Cost of the earlier ledger

### Annotation density

The table counts explicit universe annotations (`.{…}`) per thousand lines.

| Code | Lines | Annotations | Per thousand lines |
|---|---:|---:|---:|
| Mathlib `Probability` | 43k | 9 | 0.2 |
| Mathlib `MeasureTheory` | 124k | 23 | 0.1 |
| VCVio | 222k | 976 | 4.4 |
| Mathlib, all | 2,368k | 18,795 | 7.9 |
| Mathlib `CategoryTheory` | 278k | 7,504 | 26.9 |
| PolyFun | 146k | 7,397 | 50.8 |
| ArkLib core (`Interaction/`, `Relation/`) | 21k | 1,308 | 61.2 |

Mathlib's probability library is written with `Type*` and almost never pins a universe, so
polymorphism alone is free. About 1,700 of the core's 19,000 non-blank lines carry a universe
annotation. The cost also reaches:

- tests: 370 annotations, 24 `ULift`s, and the 601-line `UniverseCanary.lean`;
- clients: 135 annotations, for example `OracleInterface.simOracle2.{0, 0, 0, 0, 0}` and
  `emptySpec.{0, 0}`, and universe variables threaded through Sumcheck's composition API even
  though all its data is in `Type`;
- maintenance: #1492 added the independent universes (+1,958/−628), #1579 proposed lifting three
  further limits (+581/−263), and the position of one pin in the test `routed_suffix_budget`
  changed in #1575, #1576 and #1579.

Clients already put their carriers in `Type`: binders such as `{F : Type}` appear 266 times in
`ProofSystem/` and `Commitments/`, and `{F : Type*}` 26 times.

### Undetermined universes

A Lean scan lists each core declaration (outside `Legacy/`) and each universe parameter that
occurs in no argument's type. Of 1,247 declarations, 1,153 are universe-polymorphic and 56 have
such a parameter.

| Cause | Declarations |
|---|---|
| Constants without arguments | `Protocol`, `PlainPos`, `PlainPoly`, `OraclePos`, `OraclePoly`, `OracleProtocol` (in `q`), `plainSig`, `oracleSig`, `viewSig`, `eraseOracle` |
| Universe of a structure field | `OracleInterface`, `OracleFamily`, `OracleBundle`, `ClaimFamily`, `Problem`, `Relation`, `KnowledgeStateFunction` |
| Universe that only a `Prop` mentions | `rbrKnowledgeSoundness`, `rbrKnowledgeSoundnessOfNodes` and their plain, oracle, `_iff` and `_cast` forms (9, all in `uK`) |
| Adapters whose only job is to change a universe | `liftQueries` (2), `lowerQueries`, `liftResponse` (5), `liftInputs` (3), `liftOutputs` (2), `KnowledgeStateFunction.lift`, `rbrKnowledgeSoundness.lift` |
| The adversary universe | `AdversaryModel`, `ExtractionInterface` (kept by the policy) |

All 8 `ULift`s in the core are inside the adapters.

The scan is a short meta program: for each constant, open its type with
`forallTelescopeReducing`, collect the level parameters of every binder type with
`collectLevelParams`, and report the constant's level parameters that were not collected. The
CI linter of migration step 7 is this program with an allowlist.

## The three failures

Each example is checked in the prototype file against VCVio `f1a4a8ec`.

**A constant without arguments gets fresh universes at each use.**

```lean
def zeroComp := (pure 3 : OracleComp []ₒ Nat)
-- zeroComp.{u_1, u_2} : OracleComp.{u_1, u_2, 0} emptySpec.{u_1, u_2} ℕ

theorem zeroComp_eq : zeroComp = (pure 3 : OracleComp []ₒ Nat) := rfl
-- zeroComp_eq.{u_1, u_2} : zeroComp.{u_2, u_1} = pure 3
```

Every use needs a pin, and the lemma names the constant's universes in the other order, so
`zeroComp_eq.{0, 1}` is a statement about `zeroComp.{1, 0}`. Clients write `emptySpec.{0, 0}`
39 times and `OracleComp.{0, 0, 0} []ₒ` 18 times for this reason.

**A universe that only a `Prop` mentions elaborates separately at each occurrence.**

```lean
def HasWitness.{k} (S : Type) (R : S → Prop) : Prop :=
  ∃ (K : S → Type k) (_ : ∀ s, K s → R s), ∀ s, R s → Nonempty (K s)

theorem use (S : Type) (R : S → Prop) (h : HasWitness S R) : HasWitness S R := h
-- error: Type mismatch: h has type HasWitness.{u_1} S R
--        but is expected to have type HasWitness.{u_2} S R
```

`rbrKnowledgeSoundness` has this shape in `uK`. That is why `rbrKnowledgeSoundness.lift` exists
and why the code carries 83 `.{_, _, uK}` annotations.

**Independent universes meeting the runner either fail or drift.**

```lean
def Runner (m : Type u → Type u) : Type u := m PUnit.{u+1}

def r1 {ι : Type v} (spec : OracleSpec.{v, u} ι) := Runner (OracleComp spec)
-- r1.{u_1, u_2, u_3} : … → Type (max (max u_3 u_1) u_2)       (a universe Lean invented)

def r2 {ι : Type v} (spec : OracleSpec.{v, u} ι) := Runner.{u} (OracleComp spec)
-- error: failed to solve universe constraint u =?= max u v
```

Lean cannot express `v ≤ u`. This is why the ledger already tied a prover's ambient index to `u`.

**The independence does not survive composition.** `Verifier.append` takes the input statement
in `Type uS` but the middle statement in `Type u`, because the middle statement is a run output.
Only the first statement of a chain has its own universe.

## Options compared

| Option | Failures | Generality it adds | Verdict |
|---|---|---|---|
| Independent universes per component (the earlier ledger) | All three; 15 adapters | Independent input, index and query universes; no client uses them, and composition ties most of them | Rejected |
| One polymorphic data universe `u` | Removes the second and third; keeps pins on constants without arguments (240 `PUnit.{u + 1}` in the core) and `Type u` throughout | Data in `Type u` for `u > 0`; no client needs it, and it does not serve quantum provers (below) | Not now; reachable later by a mechanical edit |
| Data in `Type`, one adversary universe, PolyFun universes for generic code | None; the linter prevents new ones | Everything a named client uses | **Adopted** |
| Everything in `Type`, including adversaries and generic code | None | Less | Rejected: blocks record D9 and PolyFun upstreaming |

**Quantum provers need a separate universe, not a larger data universe.** A quantum register
carries its carrier type, so `QReg : Type 1` and a quantum prover lives in `Type 1`, while its
messages are ordinary field elements (record D9). With one data universe, hosting the prover
means instantiating the whole protocol at `u = 1` and lifting every message:

```lean
def liftedExample : Proto.{1} :=
  .msg (ULift (ZMod 7)) fun _ => .chal (ULift (ZMod 7)) fun _ => .done
```

Under the policy the adversary has its own universe, which the model argument fixes:

```lean
structure AdversaryModel (S Obs : Type) where
  Adv : S → Type w
  outcome : (s : S) → Adv s → Obs   -- a measure in the real definition

def secure (M : AdversaryModel.{w} S Obs) (good : Obs → Prop) : Prop :=
  ∀ s (a : M.Adv s), good (M.outcome s a)

example : Prop := secure (quantum S Obs) good   -- quantum : AdversaryModel.{1} S Obs; no pin
```

## What the policy rules out, and the workarounds

The examples use a small model of the protocol tree:

```lean
inductive Proto : Type 1 where
  | done
  | msg  (X : Type) (next : X → Proto)   -- the prover sends x : X, and x selects the rest
  | chal (C : Type) (next : C → Proto)   -- the verifier samples c : C
```

### A move that is itself a type

```lean
def sendsAType : Proto := .msg Type fun α => .msg α fun _ => .done
-- error: argument Type has type Type 1 but is expected to have type Type
```

A message on a wire is never a type; a protocol sends a name for one. **Workaround:** send a code
and decode it. The type of the next move depends on the code.

```lean
inductive GroupCode | small | large

def GroupCode.El : GroupCode → Type
  | .small => ZMod 7
  | .large => ZMod 101

def sendsACode : Proto := .msg GroupCode fun g => .msg g.El fun _ => .done
def sendsASize : Proto := .msg ℕ fun n => .msg (Fin n → ZMod 7) fun _ => .done
```

The protocol fixes the set of codes in advance, as a finite list or a size. Choosing the next
sub-protocol at run time is not affected, because a move already selects the subtree:

```lean
def choosesSubprotocol (p q : Proto) : Proto := .msg Bool fun b => if b then p else q
```

No option makes a protocol a value of a run: at every universe, positions lie one universe above
values.

### A statement that bundles types

```lean
structure Rel : Type 1 where
  Stmt : Type
  Wit : Type
  holds : Stmt → Wit → Prop

abbrev UniversalStmt := (R : Rel) × R.Stmt

example (lang : Set UniversalStmt) : Prop := SoundFor UniversalStmt lang
-- error: UniversalStmt has type Type 1 but is expected to have type Type
```

**Workaround 1:** make the bundle a parameter, one protocol for each relation. Plonk already
treats its constraint system this way.

```lean
example (R : Rel) (lang : Set R.Stmt) : Prop := SoundFor R.Stmt lang
```

**Workaround 2:** when the verifier receives the relation at run time, send it as data. A
universal proof system receives a circuit, which is matrices over a field.

```lean
structure R1CS (F : Type) where
  rows : ℕ
  cols : ℕ
  A : Fin rows → Fin cols → F
  B : Fin rows → Fin cols → F
  C : Fin rows → Fin cols → F

abbrev UniversalR1CSStmt (F : Type) := (r : R1CS F) × (Fin r.cols → F)
```

### A carrier in a higher universe

```lean
def protocolOver (F : Type) [Field F] : Proto := .msg F fun _ => .done

example (F : Type 1) [Field F] : Proto := protocolOver F
-- error: F has type Type 1 but is expected to have type Type
```

**Workaround:** a finite field in any universe has an isomorphic copy in `Type`, and Mathlib
transfers the structure along the equivalence. No ArkLib field needs this: `ZMod`, Galois fields
and the binary towers are in `Type`.

```lean
noncomputable def smallCopy (F : Type u) [Field F] [Fintype F] :
    (K : Type) × Field K × (F ≃ K) :=
  let e := Fintype.equivFin F
  ⟨Fin (Fintype.card F), e.symm.field, e⟩
```

### Summary

| Ruled out | Workaround | Client today |
|---|---|---|
| A move that is a type | Send a code or a size and decode it | none |
| A statement that bundles types | Make the bundle a parameter, or send it as data | none; Plonk uses a parameter |
| A carrier in `Type 1` | An isomorphic copy in `Type` | none |
| A large adversary | Not ruled out: `AdversaryModel.{w}` | record D9 |
