## Critical

1. **`GuaranteeTransport` is not representable from the current oracle types.**  
   References: README D1; `02` §3.1, §3.3; `04` §2.

   `OracleFamily` records only `Obj` and `OracleInterface`; an arbitrary refined Lean type does not expose the predicate, raw carrier, or backend obligation that compilation must discover. Consequently `BackendAssignment` cannot surface `G_s`, and the promised compilation error is not implementable.

   Add an explicit, reified guarantee:

   ```lean
   structure OracleGuarantee where
     Raw  : Type
     good : Raw → Prop
     desc : GuaranteeDesc
     oracle : OracleInterface Raw

   abbrev OracleGuarantee.IdealObj (G) := {x : G.Raw // G.good x}

   structure GuaranteeTransport
       (G : OracleGuarantee) (A : CommitBackend G.Raw) where
     enforce :
       AcceptedOpenings A →
       Comp (Σ x : G.Raw, G.good x ∧ OpeningsRealize A x)
     error : ErrorFunctional
     enforce_bound : ...
   ```

   `OracleFamily` or `ResourceMeta` must carry this descriptor explicitly; subtype inspection cannot be the API.

   The example “codeword slots → proximity tests” is also false for an exact `Codeword` payload: proximity establishes closeness, not consistency with an exact codeword behavior. Replace it with:

   > Proximity testing does not discharge an exact-codeword guarantee. It requires an explicit guarantee-restoring reduction whose relation records proximity, followed by a decoding/query-agreement bridge; alternatively the backend must extract an exact codeword consistent with every accepted opening.

2. **`ExecutionArtifact` remains under-indexed and does not make “same run” structural.**  
   References: `02` §2, §3.5; `03` §2.

   The `pt`-first field ordering removes the earlier circular transcript index, but the remaining fields are independently constructible. Nothing ties `msgs`, `outcome`, `γState`, and `γTrace` to one execution. Moreover, `VerifierLocalView` cannot generally be projected from `pt + msgs + WorldTrace Γ`: Δ-query positions and answers are not recorded by `WorldTrace Γ`, and replay requires an explicit determinism/replay theorem. Finally, an uninterpreted `OracleComp` cannot itself return the final state and trace of the world that has not yet interpreted it.

   Make the artifact the dependent output of the world runner, with a Δ-query log:

   ```lean
   structure RunCore (pt : Spec.PublicTranscript (Context shared)) where
     msgs       : Spec.OracleMessagesAt (Context shared) pt
     inputEnv   : InputImpl shared
     deltaTrace : QueryTrace (srcSpecAt shared pt)
     outcome    :
       Terminal (OracleClaim (srcSpecAt shared pt) (Stmt pt) (Out pt)) Fault
     proverOut  : ProverPayload pt

   def execute : OracleComp Γ.spec ((pt : _) × RunCore pt) := ...

   def World.run (Γ : World) :
       OracleComp Γ.spec α →
       SPMF (α × Γ.State × WorldTrace Γ) := ...
   ```

   Either keep `ExecutionArtifact`’s constructor private and expose only `World.run execute`, or add a `Reachable` proof connecting all components. Define `VerifierLocalView` from `deltaTrace`, not by assertion.

## High

3. **The normative security layer still lacks the exact game and composition contracts.**  
   References: README ground rules 4–5; `02` §6; `03` §4; `05` Phase 4.

   `03` provides prose bullets, not the promised game records. It never fixes the complete false-input event, reachable-prefix quantification, fault contribution, or the conditional suffix theorem needed by Phase 4. The exact ordinary-soundness contract present in the archive was dropped.

   Restore at least:

   ```text
   Sound(r₁, R₀ → R₁, ε₁)
   ∧ OutputAdmissible(r₁, R₁, εadm)
   ∧ (∀ reachable mid history,
        Sound(r₂[mid, history], R₁ → R₂, ε₂(mid, history)))
   ∧ SequentialDecomposition(r₁, r₂)
   ⇒ Sound(r₁ ; r₂, R₀ → R₂,
            ε₁ + εadm + sup ε₂ + εfault).
   ```

   The adaptive and static constructors should explicitly quantify the input claim, setup/world sample, adversary, and acceptance event in their differing orders.

4. **Setup resources disappear from the Δ-side source construction.**  
   References: README “design in one paragraph”; `00` §“layer cake” and §“assumption families”; `02` §3.2; `03` §1; `04` §3, §7.

   README promises input, setup, and prover-message backing resources, but `02` §3.2 defines only input and transcript halves. This leaves preprocessing/index oracles, CRS handles, and correlated public parameters without a canonical location; `04` later assumes setup and origin metadata.

   Add a setup half:

   ```lean
   def sourcesAt (shared) (pt) :=
     setupSources shared
       |>.tensor (inputSources shared)
       |>.tensor (messageSources shared pt)
   ```

   State whether each setup source is public data, read-only Δ behavior, or a persistent Γ world, and require stable identity/origin metadata for setup/index resources.

5. **The foundation acceptance gate does not test the declared foundation.**  
   References: `01` §1.2, §2.2–2.3; `05` T-F and Phases 4–6.

   All four acceptance tests exercise V-items; none tests P1–P3. They also omit V1 correlated worlds and lazy/full equivalence, V6 replay/reprogramming, V8 conditioning, and V9’s failure conversion. Therefore “foundation adequate” can be declared while Phase 5 and CY proofs remain unstateable.

   Add acceptance tests for:

   - P1 cursor extension/restriction and P3 decoration transport, without casts.
   - A joint heterogeneous world plus lazy-table/full-function equivalence.
   - Fork/reprogram preservation with query-before-program events.
   - A conditioned ROM bad-event proof using V8.
   - A V9 theorem converting or excluding missing mass.
   - P2 reassociation only when P2 is promoted from reserve to an actual dependency.

6. **The roadmap understates foundation dependencies.**  
   References: `02` §5; `03` §§5–8; `05` Phases 3–6 and risk 2.

   Specific missing edges:

   - Phase 3 promises `≈op`, cost preservation, and order-preserving execution decomposition, but risk 2 says Phases 1–3 do not depend on T-F. Those results require at least V2/V4 or must be deferred.
   - Phase 4 adopts V4/V7 functionals but lists only V1/V2/V5/V9.
   - Phase 5 needs V1, V4, V6, V7, V8, and completed P1—not merely V2/V3/V5—to implement rewinding, special-soundness bridges, conditioned bounds, and constrained trees.
   - Phase 6 depends on V4/V6/V7/V8/V9 and the concrete capability interfaces, not only Phases 3+5.

   Correct the phase dependency annotations or split semantic skeletons from quantitative/security proofs.

7. **Phase 6’s gates refer to a matrix that is absent, and its implementation order is inverted.**  
   References: `04` §7; `05` Phase 6.

   `04` §7 says the round-3 matrix “stands” but does not reproduce it; `05` gates every stage on rows of that nonexistent v2 matrix. The archive therefore remains a hidden normative dependency. Also, `RepresentOracles` and `LowerAccesses` precede implementation of backend capability records, although their security contracts and `GuaranteeTransport` require those interfaces.

   Copy the full pass × property matrix into `04`, with named hypotheses and outputs. Reorder Phase 6 to:

   ```text
   capability/game interfaces
   → GuaranteeDesc + BackendAssignment
   → ResourceMeta/TypedPlan
   → passes against abstract capabilities
   → Merkle/Pedersen concrete instances
   → iBCS/FS transfer theorems.
   ```

8. **The end-state has no computational-assumption or reduction calculus.**  
   References: `00` §“assumption families”; `01` V1–V9; `03` §1, §8; `05` Phase 7+.

   “Hardness predicates on games” is insufficient for KZG, Pedersen/IPA, or Ajtai commitments. No layer provides security-parameter-indexed game ensembles, admissible/PPT adversary classes, reduction composition, advantage/negligibility, setup/key-generation distributions, or reduction runtime loss. `AdvCharacteristics` alone does not supply this.

   Add an L2 requirement before curve/lattice backends:

   ```lean
   structure GameFamily where
     Params : ℕ → Type
     experiment : ∀ λ, Params λ → Adversary λ → SPMF Bool

   structure SecurityReduction (G H : GameFamily) where
     mapAdversary : ∀ λ, Adversary G λ → Adversary H λ
     advantage_bound : ...
     time_bound : ...
     budget_bound : ...
   ```

   Assign ownership explicitly and add a Phase-7 gate demonstrating one DLOG/AGM or SIS-based backend theorem.

9. **`ClaimSchema`/`Problem` can host committed claims, but `Com_A[R]` remains undefined.**  
   References: `02` §6; `04` §3.

   The arbitrary dependent `Claim` and claim-dependent `Witness` repair C4 correctly. However, the suite never defines the committed-schema transformer or the deterministic handle-realization relation, so it does not prevent randomized commitment execution from being hidden inside `Prop`.

   Add:

   ```lean
   def ComProblem (A : BackendAssignment) (P : Problem S) :
       Problem (ComSchema A S) where
     Witness ctx cc :=
       Σ decoded : S.Claim ctx,
       P.Witness ctx decoded × A.OpeningWitness cc decoded
     admissible ctx cc := ...
     rel ctx cc w :=
       P.rel ctx w.1 w.2.1 ∧ A.RealizesHandles cc w.1 w.2.2
   ```

   State that commitment randomness and openings live in the witness and that `RealizesHandles` is deterministic or is the accepted result of a separately modeled protocol.

10. **The roadmap does not explicitly deliver all CY bridge obligations it claims closed.**  
    References: `03` §§5–7; `05` Phase 5.

    Phase 5 gates only `RBR → SR`, while `03` promises bridges from special soundness to ordinary KS and SRKS, CY/Ark RBR implications, and their named losses. These were explicit CY gaps.

    Extend the gate to require:

    > `ArkRBRK → CYRBRK`, `CYRBRK → ordinary KS`, `CYRBRK → SRKS`, and single-/multi-round special soundness → ordinary KS/SRKS, each under explicit replay, entropy, budget, and error hypotheses.

## Medium

11. **Protocol-specific budget dimensions are assigned inconsistently.**  
    References: `01` §0 and V4; `03` §8.

    The boundary rule assigns protocol/commitment concepts to ArkLib, yet the displayed “V4-based” budget contains `srMoves`, `commitments`, `configurations`, and `openings`. VCVio should own an extensible generic ledger and query accounting; ArkLib should define these labels and feasibility refinements.

    Suggested split:

    ```lean
    -- VCVio
    structure Ledger (K : Type) where amount : K → ℕ

    -- ArkLib
    inductive ProtocolResource
      | oracleQuery (id : OracleId) | srMove | commitment
      | configuration | opening
    ```

12. **The interface-freeze rule precedes completion of the interfaces being frozen.**  
    References: `01` §1.2, §4; `05` T-F.

    P1–P3 are to be built “before/during Phase 3–4,” but all P/V signature changes after Phase 2 require a decision-log entry. Freezing unimplemented signatures encourages debt stubs to become accidental API.

    Change the rule to:

    > Each V/P item freezes only after its acceptance test passes; changes to already accepted items require a decision-log entry.

13. **Several normative cross-references and names have drifted.**  
    References: README D1; `00` §“stable interfaces”; `04` §§5,7.

    - README D1 points to `02` §3.4; D1 is §3.3.
    - `TranscriptTransform`, `FiniteConsumer`, `TypedPlan`, `ResourceMeta`, and `CompilePolicy` are used as interfaces without even skeletal definitions.
    - `00` calls `TypedPlan` a stable load-bearing interface, while `05` postpones its first design to Phase 6.

    Fix the section reference and either provide minimal signatures in `04` or mark these names as provisional rather than stable.