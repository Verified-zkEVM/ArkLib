# Type-tree and oracle-interaction naming contract

PolyFun's generic `Interaction.TypeTree` rename and its cursor/append substrate have landed. This
document records the current generic vocabulary and the names implemented by ArkLib's structural
oracle refinement. It is not a plan for another PolyFun rename; later oracle access and execution
layers build on this contract.

## 1. Generic carrier

The generic sequential carrier is a well-founded dependent type tree:

```lean
Interaction.TypeTree :=
  PFunctor.FreeM TypeTree.basePFunctor PUnit

TypeTree.basePFunctor.A := Type u
TypeTree.basePFunctor.B := id

TypeTree.Path tree := PFunctor.FreeM.Path tree
```

Each internal node chooses a move type `X`; a value `x : X` selects the continuation. `Protocol`
does not name this bare carrier. Roles, participants, local syntax, execution, and security meaning
belong in decorations and later bundles.

The generic cutover landed in
[PolyFun #64](https://github.com/Verified-zkEVM/PolyFun/pull/64) at `45e4f2c`. Dependent
`TypeTree.Chain` concatenation and reassociation landed in
[PolyFun #66](https://github.com/Verified-zkEVM/PolyFun/pull/66) at `ff457e0`.

The supported vocabulary includes:

| Concept | Current API |
|---|---|
| sequential carrier | `Interaction.TypeTree` |
| complete branch | `TypeTree.Path` |
| node-local data | `TypeTree.Node.Context`, `TypeTree.Node.Schema` |
| finite dependent presentation | `TypeTree.Chain`, `TypeTree.StateChain` |
| chain concatenation | `TypeTree.Chain.then` |
| chain/path boundary | `thenPathEquiv`, `splitThenPath`, `appendThenPath` |
| three-stage reassociation | `TypeTree.Chain.reassoc`, `toTypeTree_then_assoc` |

Historical `Interaction.Spec`, `Spec.Transcript`, and `Chain.toSpec` names are not compatibility
APIs. Do not reintroduce them when porting the archived ArkLib prototype.

## 2. Oracle type tree

ArkLib's oracle refinement uses a polynomial that distinguishes public moves from opaque prover
oracle messages:

```lean
Interaction.Oracle.TypeTree :=
  PFunctor.FreeM Oracle.TypeTree.basePFunctor PUnit

Oracle.Position.Branch (.public X) := X
Oracle.Position.Branch (.oracle X) := PUnit
```

At an oracle node, the prover still sends a concrete value `x : X`. Only the structural branch
index is `PUnit`: every oracle payload selects the same continuation. The runtime lens exposes the
difference:

```lean
Oracle.TypeTree.runtimeLens :
  Oracle.TypeTree.basePFunctor ⟶ TypeTree.basePFunctor

public x ↦ x
oracle x ↦ PUnit.unit
```

This creates two canonical path types:

- `Oracle.TypeTree.BranchPath tree` records the values that choose structural continuations;
- `Oracle.TypeTree.ExecutionPath tree` records every concrete runtime message, including prover
  oracle payloads.

`BranchPath` does not mean one party controls every branch. It is the structural control-flow path.
`ExecutionPath` is the global message record, not the verifier's local observation. The canonical
projection is identity at public nodes and maps each oracle payload to `PUnit.unit`.

## 3. Higher-level vocabulary

Use the following terms consistently:

| Term | Meaning |
|---|---|
| `TypeTree` | bare generic or oracle-refined sequential shape |
| `BranchPath` | complete structural choices through an oracle type tree |
| `ExecutionPath` | complete concrete messages through an oracle type tree |
| verifier local view | public information and queries visible to the verifier; derived from an execution |
| world trace | ordered VCVio query/answer events from the external oracle runtime |
| state-restoration move trace | the protocol-specific move/response log used by the SR game |
| `Protocol` | decorated bundle containing at least a tree, roles, and oracle-interface data |
| `Reduction` | executable statement/witness transformation over protocol data |
| `OracleSpec` | VCVio's dependent query-response signature; unrelated to the old PolyFun `Spec` name |

Do not use “full transcript” in new APIs. Legacy code uses that phrase for several different
objects. Choose `ExecutionPath`, verifier local view, world trace, or state-restoration move trace.

## 4. Archived prototype migration map

The broad prototype predates the generic rename. Ported ArkLib declarations use the names below:

| Prototype name | Normative ArkLib name |
|---|---|
| `Interaction.Oracle.Spec` | `Interaction.Oracle.TypeTree` |
| `Oracle/Spec.lean` | `Oracle/TypeTree.lean` |
| `Oracle.Spec.basePFunctor` | `Oracle.TypeTree.basePFunctor` |
| `Oracle.Spec.executionLens` | `Oracle.TypeTree.runtimeLens` |
| `Oracle.Spec.toInteractionSpec` | `Oracle.TypeTree.toTypeTree` |
| `Oracle.Spec.PublicTranscript` | `Oracle.TypeTree.BranchPath` |
| `Oracle.Spec.FullTranscript` | `Oracle.TypeTree.ExecutionPath` |
| `Oracle.Spec.RoleDeco` | `Oracle.TypeTree.RoleDecoration` |
| `Oracle.Spec.OracleDeco` | `Oracle.TypeTree.OracleDecoration` |
| `Oracle.Spec.toSpecRoles` | `Oracle.TypeTree.RoleDecoration.toTypeTreeRoles` |
| `Oracle.Spec.toRuntimeRoles` | `Oracle.TypeTree.RoleDecoration.toRuntimeRoles` |
| `FullTranscript.toInteractionTranscript` | `ExecutionPath.toTypeTreePath` |
| `projectPublicFull` | `ExecutionPath.toBranchPath` |
| `PublicTranscript.*` | `BranchPath.*` |
| `transcriptAppend` | `ExecutionPath.append` |
| `Spec.OracleMessagesAt` | `Oracle.TypeTree.OracleMessagesAt` |
| `Oracle.Spec.Protocol` and projection `.spec` | `Oracle.Protocol` and projection `.tree` |

This table is a source-porting aid, not a compatibility layer. New modules contain no aliases for
the prototype names.

## 5. Acceptance gate for the ArkLib naming slice

AR-2A and AR-2B establish this contract when:

1. `Oracle.Position`, `Oracle.TypeTree`, `BranchPath`, and `ExecutionPath` elaborate at independent
   relevant universes;
2. public values select continuations while oracle payloads remain visible only in
   `ExecutionPath`;
3. execution-to-branch projection has stable constructor equations;
4. role and oracle decorations restrict along a real `FreeM.Cursor`;
5. a mixed dependent example distinguishes two public branches and two oracle payloads;
6. negative searches find no reintroduced `Interaction.Spec`, `Spec.Transcript`, or prototype
   oracle aliases;
7. imports and maintained documentation use `OracleSpec` only for VCVio query signatures.

The purpose of this naming is not cosmetic consistency. It keeps structural choices, exchanged
messages, local observations, and external-world queries separate before security theorems make
those distinctions load-bearing.
