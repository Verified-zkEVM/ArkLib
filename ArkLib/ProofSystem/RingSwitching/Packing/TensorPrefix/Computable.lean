/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.TensorPrefix
public import ArkLib.ProofSystem.RingSwitching.Packing.ProductSumcheck.Computable

/-!
# Executable tensor-prefix ring switching

The source and packed witness are Boolean evaluation tables. The prover transmits the column
coordinates of the tensor carrier, rather than constructing a tensor product. The runtime basis
is supplied as basis vectors and a coordinate map. The agreement lemmas compare this
implementation with `TensorPrefix`, the packing layout with the same opening and challenge
algebra. Other packing layouts do not use this backend.
-/

@[expose] public section

namespace RingSwitching.Packing.TensorPrefix.Computable

open MvPolynomial Module OracleSpec OracleComp ProtocolSpec CoordinateWise.ScalarRound
open Sumcheck.Structured (MultilinearPoly)

/-- Boolean index tuples in low-coordinate-first order. -/
abbrev Cube (n : ℕ) := Fin n → Fin 2

variable {K L : Type} [CommRing K] [CommRing L] [Algebra K L] {κ ℓ m : ℕ}

/-- One equality-kernel weight, evaluated without constructing a polynomial. -/
def eqWeight {n : ℕ} (y : Cube n) (r : Fin n → L) : L :=
  ∏ i, if y i = 0 then 1 - r i else r i

theorem eqWeight_eq {n : ℕ} (y : Cube n) (r : Fin n → L) :
    eqWeight y r = eqTilde (y : Fin n → L) r := by
  rw [eqWeight, eqTilde_eq_prod]
  apply Finset.prod_congr rfl
  intro i _
  generalize y i = b
  fin_cases b <;> simp

/-- Read the vector by its Boolean index rather than its numeric array position. -/
def vectorTable {R : Type} (state : Vector R (2 ^ κ)) : Cube κ → R :=
  fun u => state.get (finFunctionFinEquiv u)

/-- The result of tabulation, kept separate from an individual table lookup. -/
structure MaterializedTable (R : Type) (n : ℕ) where
  /-- Read one entry of the materialized table. -/
  read : Cube n → R

/-- Allocate the vector before returning its lookup closure. The structure result keeps Lean's
compiler from adding the lookup point to this function's arguments. -/
@[noinline]
def materializeTable {R : Type} (table : Cube κ → R) : MaterializedTable R κ :=
  ⟨vectorTable (Vector.ofFn fun j => table (finFunctionFinEquiv.symm j))⟩

/-- Materialize a table once so that subsequent reads do not recompute entries. -/
@[macro_inline]
def materialize {R : Type} (table : Cube κ → R) : Cube κ → R :=
  (materializeTable table).read

theorem vectorTable_ofFn {R : Type} (table : Cube κ → R) :
    vectorTable (Vector.ofFn fun j => table (finFunctionFinEquiv.symm j)) = table := by
  funext u
  simp [vectorTable]

@[simp] theorem materializeTable_read {R : Type} (table : Cube κ → R) :
    (materializeTable table).read = table :=
  vectorTable_ofFn table

@[simp] theorem materialize_eq {R : Type} (table : Cube κ → R) : materialize table = table :=
  materializeTable_read table

/-- View an abstract multilinear as its Boolean evaluation table. -/
noncomputable def toTable {R : Type} [CommRing R] {n : ℕ} (p : MultilinearPoly R n) :
    Cube n → R := fun y => p.val.eval (y : Fin n → R)

/-- The polynomial interpretation of a Boolean table. -/
noncomputable def toMultilinear {R : Type} [CommRing R] {n : ℕ} (table : Cube n → R) :
    MultilinearPoly R n := ⟨MLE table, MLE_mem_restrictDegree table⟩

@[simp] theorem toTable_toMultilinear {R : Type} [CommRing R] {n : ℕ}
    (table : Cube n → R) : toTable (toMultilinear table) = table := by
  funext y
  exact MLE_eval_zeroOne y table

theorem toMultilinear_toTable {R : Type} [CommRing R] {n : ℕ} (p : MultilinearPoly R n) :
    toMultilinear (toTable p) = p := by
  apply Subtype.ext
  exact (eq_MLE_of_degreeOf_le_one_of_eval_zeroOne_eq _ _
    ((mem_restrictDegree_iff_degreeOf_le _ _).mp p.property) (fun _ => rfl)).symm

/-- The first positions of the source query, in packed-prefix order. -/
def queryPrefix (h : ℓ = m + κ) (r : Fin ℓ → L) : Fin κ → L :=
  fun i => r ⟨i.val, by omega⟩

/-- The retained suffix of the source query. -/
def querySuffix (h : ℓ = m + κ) (r : Fin ℓ → L) : Fin m → L :=
  fun i => r ⟨i.val + κ, by omega⟩

/-- Plug a packed-prefix index and a retained Boolean point into the source table. -/
def sourceIndex (h : ℓ = m + κ) (v : Cube κ) (y : Cube m) : Cube ℓ :=
  fun i => if hi : i.val < κ then v ⟨i.val, hi⟩ else y ⟨i.val - κ, by omega⟩

/-- The packed witness table, using one basis expansion per retained Boolean point. -/
@[macro_inline]
def pack (basis : Cube κ → L) (h : ℓ = m + κ) (source : Cube ℓ → K) : Cube m → L :=
  materialize fun y => ∑ v, source (sourceIndex h v y) • basis v

/-- Form the carrier's column table using the already allocated suffix weights. -/
@[noinline]
def honestMessageTable (h : ℓ = m + κ) (source : Cube ℓ → K)
    (weight : MaterializedTable L m) : MaterializedTable L κ :=
  materializeTable fun v => ∑ y, weight.read y * algebraMap K L (source (sourceIndex h v y))

/-- The honest carrier message in column coordinates. Compute the suffix weights before
entering the column loop so every column can reuse them. -/
@[macro_inline]
def honestMessage (h : ℓ = m + κ) (r : Fin ℓ → L)
    (source : Cube ℓ → K) : Cube κ → L :=
  (honestMessageTable h source
    (materializeTable fun y => eqWeight y (querySuffix h r))).read

/-- The scalar claim reconstructed from the received columns. -/
def reconstruct (h : ℓ = m + κ) (r : Fin ℓ → L) (α : Cube κ → L) : L :=
  ∑ v, eqWeight v (queryPrefix h r) * α v

/-- Transpose the received columns, pack the resulting rows, and batch them. -/
def batch (basis : Cube κ → L) (coordinates : L → Cube κ → K)
    (α : Cube κ → L) (c : Fin κ → L) : L :=
  ∑ u, eqWeight u c * ∑ v, coordinates (α v) u • basis v

/-- The initial product-sumcheck statement after a successful head check. -/
abbrev HeadOutput (L : Type) (ℓ κ m : ℕ) :=
  ProductSumcheck.Statement ((Fin ℓ → L) × (Fin κ → L)) L (0 : Fin (m + 1))

/-- The batching head transition, conditional on a separate reconstruction check. -/
def headNext (basis : Cube κ → L) (coordinates : L → Cube κ → K)
    (r : Fin ℓ → L) (α : Cube κ → L) (c : Fin κ → L) : HeadOutput L ℓ κ m :=
  ⟨(r, c), Fin.elim0, batch basis coordinates α c⟩

/-- Verify the head on explicit column and challenge messages, or reject. -/
def headVerify [DecidableEq L] (basis : Cube κ → L) (coordinates : L → Cube κ → K)
    (h : ℓ = m + κ) (stmt : (Fin ℓ → L) × L) (α : Cube κ → L) (c : Fin κ → L) :
    Option (HeadOutput L ℓ κ m) :=
  if stmt.2 = reconstruct h stmt.1 α then some (headNext basis coordinates stmt.1 α c) else none

/-- The column message followed by the original batching challenge. -/
abbrev headPSpec (L : Type) (κ : ℕ) : ProtocolSpec 2 :=
  pSpecScalar (Cube κ → L) (Fin κ → L)

instance : ∀ j, OracleInterface ((headPSpec L κ).Message j) :=
  letI : OracleInterface (Cube κ → L) := OracleInterface.instDefault
  inferInstance

instance [SampleableType L] : ∀ j, SampleableType ((headPSpec L κ).Challenge j)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => inferInstanceAs (SampleableType (Fin κ → L))

/-- The runtime head state caches the column message until the batching challenge arrives. -/
def HeadState {ι : Type} (OStmt : ι → Type) (K L : Type) (ℓ κ : ℕ) : Fin 3 → Type
  | ⟨0, _⟩ => (((Fin ℓ → L) × L) × (∀ j, OStmt j)) × (Cube ℓ → K)
  | ⟨1, _⟩ =>
    ((((Fin ℓ → L) × L) × (∀ j, OStmt j)) × (Cube ℓ → K)) × (Cube κ → L)
  | ⟨2, _⟩ =>
    (((((Fin ℓ → L) × L) × (∀ j, OStmt j)) × (Cube ℓ → K)) × (Cube κ → L)) × (Fin κ → L)

/-- The honest head prover sends columns and forwards the packed table and unchanged oracles. -/
def headProver {ι : Type} (OStmt : ι → Type) (basis : Cube κ → L)
    (coordinates : L → Cube κ → K) (h : ℓ = m + κ) :
    OracleProver []ₒ ((Fin ℓ → L) × L) OStmt (Cube ℓ → K)
      (HeadOutput L ℓ κ m) OStmt (Cube m → L) (headPSpec L κ) where
  PrvState := HeadState OStmt K L ℓ κ
  input := id
  sendMessage
    | ⟨0, _⟩ => fun st =>
      let α := honestMessage h st.1.1.1 st.2
      pure (α, (st, α))
    | ⟨1, h⟩ => fun _ => nomatch h
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
    | ⟨1, _⟩ => fun st => pure fun c => (st, c)
  output := fun ((((stmt, ost), source), α), c) =>
    pure ((headNext basis coordinates stmt.1 α c, ost), pack basis h source)

instance {ι : Type} (OStmt : ι → Type) (basis : Cube κ → L)
    (coordinates : L → Cube κ → K) (h : ℓ = m + κ) :
    (headProver OStmt basis coordinates h).OutputIsPure where
  output_is_pure := ⟨fun ((((stmt, ost), source), α), c) =>
    ((headNext basis coordinates stmt.1 α c, ost), pack basis h source), fun _ => rfl⟩

/-- The runtime head verifier reads the column message before accepting or aborting. -/
def headVerifier [DecidableEq L] {ι : Type} (OStmt : ι → Type)
    [∀ j, OracleInterface (OStmt j)] (basis : Cube κ → L)
    (coordinates : L → Cube κ → K) (h : ℓ = m + κ) :
    OracleVerifier []ₒ ((Fin ℓ → L) × L) OStmt (HeadOutput L ℓ κ m) OStmt
      (headPSpec L κ) :=
  scalarRoundOracleVerifier (fun stmt α => stmt.2 = reconstruct h stmt.1 α)
    (fun stmt α c => headNext basis coordinates stmt.1 α c)

/-- The tensor batching reduction with coordinate messages and Boolean-table witnesses.
Agreement with the tensor specification assumes that `coordinates` gives the coefficients
in the supplied basis. -/
def headReduction [DecidableEq L] {ι : Type} (OStmt : ι → Type)
    [∀ j, OracleInterface (OStmt j)] (basis : Cube κ → L)
    (coordinates : L → Cube κ → K) (h : ℓ = m + κ) :
    OracleReduction []ₒ ((Fin ℓ → L) × L) OStmt (Cube ℓ → K)
      (HeadOutput L ℓ κ m) OStmt (Cube m → L) (headPSpec L κ) :=
  ⟨headProver OStmt basis coordinates h, headVerifier OStmt basis coordinates h⟩

instance [DecidableEq L] {ι : Type} (OStmt : ι → Type) [∀ j, OracleInterface (OStmt j)]
    (basis : Cube κ → L) (coordinates : L → Cube κ → K) (h : ℓ = m + κ) :
    (headReduction OStmt basis coordinates h).prover.OutputIsPure :=
  inferInstanceAs (headProver OStmt basis coordinates h).OutputIsPure

/-- The head never changes the commitment oracle. -/
theorem headReduction_materializeOutput [DecidableEq L] {ι : Type} (OStmt : ι → Type)
    [∀ j, OracleInterface (OStmt j)] (basis : Cube κ → L) (coordinates : L → Cube κ → K)
    (h : ℓ = m + κ) (c : (headPSpec L κ).Challenges) (ost : ∀ j, OStmt j)
    (msg : (headPSpec L κ).Messages) :
    (headReduction OStmt basis coordinates h).verifier.materializeOutput c ost msg = ost := rfl

/-- Verifying an explicit transcript applies exactly the executable head check and update. -/
theorem headVerifier_verify [DecidableEq L] {ι : Type} (OStmt : ι → Type)
    [∀ j, OracleInterface (OStmt j)]
    (basis : Cube κ → L) (coordinates : L → Cube κ → K) (h : ℓ = m + κ)
    (stmt : (Fin ℓ → L) × L) (ost : ∀ j, OStmt j) (α : Cube κ → L) (c : Fin κ → L) :
    (headVerifier OStmt basis coordinates h).toVerifier.verify (stmt, ost)
        (FullTranscript.mk2 α c) =
      match headVerify basis coordinates h stmt α c with
      | some out => pure (out, ost)
      | none => failure := by
  have hverify := (scalarRoundOracleVerifierGuardedForm (oSpec := []ₒ) (OStmt := OStmt)
    (fun (s : (Fin ℓ → L) × L) a => s.2 = reconstruct h s.1 a)
    (fun s a challenge => headNext (m := m) basis coordinates s.1 a challenge)).verify_eq
      (stmt, ost) (FullTranscript.mk2 α c)
  rw [scalarRoundOracleVerifierGuardedForm_check,
    scalarRoundOracleVerifierGuardedForm_out] at hverify
  rw [headVerifier]
  convert hverify using 1
  by_cases hc : stmt.2 = reconstruct h stmt.1 α <;> simp [headVerify, hc]

/-- The honest head samples exactly the displayed batching challenge and preserves the oracles. -/
theorem headProver_run {ι : Type} (OStmt : ι → Type)
    (basis : Cube κ → L) (coordinates : L → Cube κ → K) (h : ℓ = m + κ)
    (stmt : (Fin ℓ → L) × L) (ost : ∀ j, OStmt j) (source : Cube ℓ → K) :
    letI : ∀ j, OracleInterface ((headPSpec L κ).Challenge j) := challengeOracleInterface
    (headProver OStmt basis coordinates h).run (stmt, ost) source = (do
      let c ← (liftM (query (spec := [(headPSpec L κ).Challenge]ₒ) ⟨⟨1, rfl⟩, ()⟩ :
        OracleComp [(headPSpec L κ).Challenge]ₒ (Fin κ → L)) :
        OracleComp ([]ₒ + [(headPSpec L κ).Challenge]ₒ) (Fin κ → L))
      let α := honestMessage h stmt.1 source
      pure (FullTranscript.mk2 (pSpec := headPSpec L κ) α c,
        ((headNext basis coordinates stmt.1 α c, ost), pack basis h source))) := by
  have h0 : (headPSpec L κ).dir 0 = .P_to_V := rfl
  have h1 : (headPSpec L κ).dir 1 = .V_to_P := rfl
  simp only [Prover.run, Prover.runToRound, Fin.induction_two,
    Prover.processRound_of_dir_eq_P_to_V 0 h0, Prover.processRound_of_dir_eq_V_to_P 1 h1]
  simp only [headProver, id_eq, pure_bind, liftM_pure, bind_pure_comp,
    LawfulApplicative.map_pure, getChallenge]
  simp only [liftM, map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr
  intro c
  let _ : ∀ j, OracleInterface ((headPSpec L κ).Challenge j) := challengeOracleInterface
  let α := honestMessage h stmt.1 source
  let out := ((headNext (m := m) basis coordinates stmt.1 α c, ost), pack basis h source)
  change (pure (((default : (headPSpec L κ).Transcript 0).concat (m := 0) α).concat
      (m := 1) c, out) : OracleComp ([]ₒ + [(headPSpec L κ).Challenge]ₒ) _) =
    pure (FullTranscript.mk2 α c, out)
  congr 1
  exact congrArg (fun tr => (tr, out))
    (FullTranscript.mk2_eq_snoc_snoc (pSpec := headPSpec L κ) α c).symm

/-- The public product-sumcheck multiplier on Boolean input. -/
def multiplierTable (coordinates : L → Cube κ → K) (r : Fin m → L) (c : Fin κ → L)
    (y : Cube m) : L :=
  let openingWeight := eqWeight y r
  ∑ u, coordinates openingWeight u • eqWeight u c

/-- Apply each layer to a materialized coordinate vector. Materializing each intermediate
vector reuses its entries in the next multiplication. -/
def runLayers : {n : ℕ} → (Fin n → Matrix (Cube κ) (Cube κ) L) →
    Vector L (2 ^ κ) → Vector L (2 ^ κ)
  | 0, _, state => state
  | _ + 1, layers, state =>
    runLayers (fun i => layers i.succ)
      (Vector.ofFn fun j => (layers 0).mulVec (vectorTable state) (finFunctionFinEquiv.symm j))

theorem runLayers_eq {n : ℕ} (layers : Fin n → Matrix (Cube κ) (Cube κ) L)
    (state : Vector L (2 ^ κ)) :
    vectorTable (runLayers layers state) = Matrix.ReadOnce.run layers (vectorTable state) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
    rw [runLayers, ih, Matrix.ReadOnce.run_succ]
    rw [vectorTable_ofFn ((layers 0).mulVec (vectorTable state))]

/-- The multiplication matrix of a public value in the supplied basis. -/
def multiplicationMatrix (basis : Cube κ → L) (coordinates : L → Cube κ → K) (a : L) :
    Matrix (Cube κ) (Cube κ) L :=
  fun u v => algebraMap K L (coordinates (a * basis v) u)

/-- Evaluate the public multiplier by the read-once matrix algorithm used at the terminal check.
This does not enumerate the Boolean cube in the number of retained variables. -/
def evaluateMultiplier (basis : Cube κ → L) (coordinates : L → Cube κ → K)
    (r : Fin m → L) (c : Fin κ → L) (z : Fin m → L) : L :=
  let initial := Vector.ofFn fun j =>
    algebraMap K L (coordinates 1 (finFunctionFinEquiv.symm j))
  let layers i := Matrix.ReadOnce.interpolate (fun b =>
    multiplicationMatrix basis coordinates (if b = 0 then 1 - r i else r i)) (z i)
  let final := vectorTable (runLayers layers initial)
  ∑ u, eqWeight u c * final u

section Agreement

variable (P : RingSwitchingProfile K L κ) (h : ℓ = m + κ)

theorem pack_eq (t : MultilinearPoly K ℓ) :
    pack P.basis h (toTable t) = toTable (packMLE κ L K ℓ m h P.basis t) := by
  funext y
  simp only [pack, materialize_eq, toTable, packMLE, MLE_eval_zeroOne, Basis.equivFun_symm_apply]
  rfl

/-- The runtime packed table represents the packed witness of every source table. -/
theorem toMultilinear_pack (source : Cube ℓ → K) :
    toMultilinear (pack P.basis h source) =
      packMLE κ L K ℓ m h P.basis (toMultilinear source) := by
  rw [← toMultilinear_toTable (packMLE ..), ← pack_eq, toTable_toMultilinear]

theorem honestMessage_eq (r : Fin ℓ → L) (t : MultilinearPoly K ℓ) :
    honestMessage h r (toTable t) =
      Head.partials (PackingData.ofBasis P.basis) m (TensorPrefix.layout P h) r t := by
  have hdim := h.trans (Nat.add_comm m κ)
  cases hdim
  simp only [honestMessage, honestMessageTable, materializeTable_read]
  funext v
  change (∑ y, eqWeight y (querySuffix h r) * algebraMap K L ((toTable t) (sourceIndex h v y))) =
    aeval (querySuffix h r)
      (splitFirst κ m (sourceDimensionEquiv h t) v).val
  rw [aeval_multilinear_eq_sum_eqTilde (splitFirst κ m (sourceDimensionEquiv h t) v).property]
  simp only [eqWeight_eq, splitFirst_eval,
    sourceDimensionEquiv, Equiv.cast_refl, Equiv.refl_apply, toTable]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [show sourceIndex h v y = Fin.append v y from concat_eq_append (ℓ := κ + m) v y]
  rw [show (Fin.append (v : Fin κ → K) (y : Fin m → K)) =
    (fun i => ((Fin.append v y i : Fin 2) : K)) from
      Fin.append_comp (a := v) (b := y) (fun b : Fin 2 => (b : K))]

theorem reconstruct_eq (r : Fin ℓ → L) (s : L) (α : Cube κ → L) :
    (s = reconstruct h r α) ↔
      Head.check (PackingData.ofBasis P.basis) m (TensorPrefix.layout P h) (r, s) α := by
  simp only [reconstruct, eqWeight_eq, Head.check]
  rfl

theorem batch_eq [SampleableType L] (α : Cube κ → L) (c : Fin κ → L) :
    batch P.basis (fun x u => P.basis.repr x u) α c =
      (PackingData.ofBasis P.basis).derivedTarget α ((BatchingRule.eqFold L κ).weight c) := by
  simp only [batch, eqWeight_eq, PackingData.derivedTarget, BatchingRule.eqFold]
  change (∑ u : Cube κ, eqTilde (u : Fin κ → L) c *
      ∑ v, P.basis.repr (α v) u • P.basis v) =
    ∑ u : Cube κ, eqTilde (u : Fin κ → L) c * (PackingData.ofBasis P.basis).transpose α u
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [(PackingData.ofBasis P.basis).transpose_apply α u]

theorem headNext_eq [SampleableType L] (stmt : (Fin ℓ → L) × L) (α : Cube κ → L)
    (c : Fin κ → L) :
    headNext (m := m) P.basis (fun x u => P.basis.repr x u) stmt.1 α c =
      Head.nextStatement (PackingData.ofBasis P.basis) m (TensorPrefix.layout P h)
        (BatchingRule.eqFold L κ) stmt α c := by
  unfold headNext Head.nextStatement
  rw [batch_eq]
  rfl

/-- The head's actual send action agrees after decoding its carrier and interpreting the
runtime source table as the legacy packed state. -/
theorem headProver_sendMessage_eq [SampleableType L] (a : AbstractOStmtIn L m)
    (basis : Cube κ → L) (coordinates : L → Cube κ → K) (hBasis : basis = ⇑P.basis)
    (stmt : (Fin ℓ → L) × L) (ost : ∀ j, (TensorPrefix.commitment a).OStmt j)
    (source : Cube ℓ → K) :
    ((fun (α, ((s, t), cached)) =>
      ((TensorPrefix.messageEquiv P).symm α, ((s, toMultilinear (pack basis h t)), cached))) <$>
      (headProver (TensorPrefix.commitment a).OStmt basis coordinates h).sendMessage
        ⟨0, rfl⟩ ((stmt, ost), source)) =
      (TensorPrefix.headReduction P h a).prover.sendMessage
        ⟨0, rfl⟩ ((stmt, ost), toMultilinear source) := by
  subst basis
  simp only [headProver, TensorPrefix.headReduction, Head.reduction, Head.prover,
    Head.proverForOracles, LawfulApplicative.map_pure]
  rw [toMultilinear_pack P h, ← TensorPrefix.packedMLE_components_eq_packMLE]
  have hα : honestMessage h stmt.1 source =
      Head.partials (PackingData.ofBasis P.basis) m (TensorPrefix.layout P h)
        stmt.1 (toMultilinear source) := by
    simpa only [toTable_toMultilinear] using honestMessage_eq P h stmt.1 (toMultilinear source)
  rw [hα]
  rfl

/-- From corresponding cached states, the actual output actions return the same batched claim
and oracles, with the packed table interpreted as the legacy polynomial. -/
theorem headProver_output_eq [SampleableType L] (a : AbstractOStmtIn L m)
    (basis : Cube κ → L) (coordinates : L → Cube κ → K)
    (hBasis : basis = ⇑P.basis) (hCoordinates : coordinates = fun x u => P.basis.repr x u)
    (stmt : (Fin ℓ → L) × L) (ost : ∀ j, (TensorPrefix.commitment a).OStmt j)
    (source : Cube ℓ → K) (α : Cube κ → L) (c : Fin κ → L) :
    ((fun (s, packed) => (s, toMultilinear packed)) <$>
      (headProver (TensorPrefix.commitment a).OStmt basis coordinates h).output
        ((((stmt, ost), source), α), c)) =
      (TensorPrefix.headReduction P h a).prover.output
        ((((stmt, ost), (PackingData.ofBasis P.basis).packedMLE
          ((TensorPrefix.layout P h).components (toMultilinear source))), α), c) := by
  subst basis coordinates
  simp only [headProver, TensorPrefix.headReduction, Head.reduction, Head.prover,
    Head.proverForOracles, LawfulApplicative.map_pure]
  rw [headNext_eq P h, toMultilinear_pack P h, ← TensorPrefix.packedMLE_components_eq_packMLE]
  rfl

/-- The executable honest head accepts the original source claim and produces the
same-commitment product claim for the packed table. -/
theorem head_preservesRelation [DecidableEq L] [SampleableType L] (a : AbstractOStmtIn L m)
    (stmt : (Fin ℓ → L) × L) (ost : ∀ j, (TensorPrefix.commitment a).OStmt j)
    (source : Cube ℓ → K) (c : Fin κ → L)
    (hs : ((stmt, ost), toMultilinear source) ∈ TensorPrefix.relIn P h a) :
    let coordinates : L → Cube κ → K := fun x u => P.basis.repr x u
    let α := honestMessage h stmt.1 source
    let out := headNext (m := m) P.basis coordinates stmt.1 α c
    headVerify P.basis coordinates h stmt α c = some out ∧
      ((out, ost), toMultilinear (pack P.basis h source)) ∈ TensorPrefix.headRelOut P h a := by
  dsimp only
  have hα : honestMessage h stmt.1 source =
      Head.partials (PackingData.ofBasis P.basis) m (TensorPrefix.layout P h)
        stmt.1 (toMultilinear source) := by
    simpa only [toTable_toMultilinear] using honestMessage_eq P h stmt.1 (toMultilinear source)
  constructor
  · have hc := Head.check_partials_of_mem_relIn _ _ _ _ hs
    rw [headVerify, ite_eq_left]
    rwa [hα, reconstruct_eq P h]
  · rw [headNext_eq P h, hα, toMultilinear_pack P h,
      ← TensorPrefix.packedMLE_components_eq_packMLE]
    exact Head.nextStatement_mem_relOut _ _ _ (BatchingRule.eqFold L κ) _ hs c

/-- With the original basis operations, the runtime and abstract head verifiers agree
on every transcript after identifying the tensor carrier with its column coordinates. -/
theorem headVerifier_verify_eq [DecidableEq L] [SampleableType L]
    (a : AbstractOStmtIn L m) (stmt : (Fin ℓ → L) × L)
    (ost : ∀ j, (TensorPrefix.commitment a).OStmt j) (α : Cube κ → L) (c : Fin κ → L) :
    (headVerifier (TensorPrefix.commitment a).OStmt P.basis (fun x u => P.basis.repr x u)
      h).toVerifier.verify (stmt, ost) (FullTranscript.mk2 α c) =
      (TensorPrefix.headVerifier P h a).toVerifier.verify (stmt, ost)
        (FullTranscript.mk2 ((TensorPrefix.messageEquiv P).symm α) c) := by
  classical
  rw [headVerifier_verify]
  have hlegacy := (TensorPrefix.headGuardedForm P h a).verify_eq (stmt, ost)
    (FullTranscript.mk2 (pSpec := TensorPrefix.headPSpec P)
      ((TensorPrefix.messageEquiv P).symm α) c)
  change _ = (if (Head.guardedForm (PackingData.ofBasis P.basis) m
      (TensorPrefix.layout P h) (TensorPrefix.messageEquiv P) (BatchingRule.eqFold L κ)
      (TensorPrefix.commitment a)).check (stmt, ost) _ then _ else _) at hlegacy
  rw [Head.guardedForm_check] at hlegacy
  have hout := Head.guardedForm_out (PackingData.ofBasis P.basis) m
    (TensorPrefix.layout P h) (TensorPrefix.messageEquiv P) (BatchingRule.eqFold L κ)
    (TensorPrefix.commitment a) (stmt, ost)
    (FullTranscript.mk2 ((TensorPrefix.messageEquiv P).symm α) c)
  change (TensorPrefix.headGuardedForm P h a).out (stmt, ost) _ = _ at hout
  rw [hout] at hlegacy
  change _ = (if decide (Head.check (PackingData.ofBasis P.basis) m (TensorPrefix.layout P h)
      stmt ((TensorPrefix.messageEquiv P) ((TensorPrefix.messageEquiv P).symm α))) then
    pure (Head.nextStatement (PackingData.ofBasis P.basis) m (TensorPrefix.layout P h)
      (BatchingRule.eqFold L κ) stmt
      ((TensorPrefix.messageEquiv P) ((TensorPrefix.messageEquiv P).symm α)) c, ost)
    else failure) at hlegacy
  rw [hlegacy, Equiv.apply_symm_apply]
  by_cases hc : stmt.2 = reconstruct h stmt.1 α
  · have hcheck : Head.check (PackingData.ofBasis P.basis) m (TensorPrefix.layout P h) stmt α :=
      (reconstruct_eq P h stmt.1 stmt.2 α).mp hc
    rw [headVerify, ite_eq_left hc, ite_eq_left (decide_eq_true hcheck), headNext_eq P h stmt α c]
    rfl
  · have hcheck :
        ¬ Head.check (PackingData.ofBasis P.basis) m (TensorPrefix.layout P h) stmt α :=
      fun hp => hc ((reconstruct_eq P h stmt.1 stmt.2 α).mpr hp)
    rw [headVerify, ite_eq_right hc, ite_eq_right (fun hp => hcheck (of_decide_eq_true hp))]
    rfl

/-- Interpret the column message as the abstract carrier, keeping its batching challenge. -/
noncomputable def decodeHeadTranscript [SampleableType L]
    (tr : (headPSpec L κ).FullTranscript) : (TensorPrefix.headPSpec P).FullTranscript :=
  FullTranscript.mk2 ((TensorPrefix.messageEquiv P).symm (tr 0)) (tr 1)

theorem decodeHeadTranscript_challenge [SampleableType L]
    (tr : (headPSpec L κ).FullTranscript) : decodeHeadTranscript P tr 1 = tr 1 := rfl

/-- Arbitrary runtime head transcripts verify identically after carrier decoding. -/
theorem headVerifier_verify_decodeHeadTranscript [DecidableEq L] [SampleableType L]
    (a : AbstractOStmtIn L m) (stmt : (Fin ℓ → L) × L)
    (ost : ∀ j, (TensorPrefix.commitment a).OStmt j) (tr : (headPSpec L κ).FullTranscript) :
    (headVerifier (TensorPrefix.commitment a).OStmt P.basis (fun x u => P.basis.repr x u)
      h).toVerifier.verify (stmt, ost) tr =
      (TensorPrefix.headVerifier P h a).toVerifier.verify (stmt, ost)
        (decodeHeadTranscript P tr) := by
  have htr : FullTranscript.mk2 (pSpec := headPSpec L κ) (tr 0) (tr 1) = tr := by
    funext i
    fin_cases i <;> rfl
  have hagree := headVerifier_verify_eq P h a stmt ost (tr 0) (tr 1)
  rw [htr] at hagree
  exact hagree

theorem multiplierTable_eq [SampleableType L] (r : Fin ℓ → L) (c : Fin κ → L) (y : Cube m) :
    multiplierTable (fun x u => P.basis.repr x u) (querySuffix h r) c y =
      ((TensorPrefix.multiplier P h).polynomial (r, c)).val.eval (y : Fin m → L) := by
  rw [show ((TensorPrefix.multiplier P h).polynomial (r, c)).val.eval (y : Fin m → L) =
      ∑ u, (PackingData.ofBasis P.basis).eqCoord (querySuffix h r) y u •
          (BatchingRule.eqFold L κ).weight c u from
    (PackingData.ofBasis P.basis).multiplier_eval_zeroOne _ _ _]
  simp only [multiplierTable, eqWeight_eq, PackingData.eqCoord, BatchingRule.eqFold]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [show eqTilde (querySuffix h r) (y : Fin m → L) =
    eqTilde (y : Fin m → L) (querySuffix h r) by
      simp only [eqTilde, eqPolynomial_symm]]

theorem multiplicationMatrix_eq (a : L) :
    multiplicationMatrix P.basis (fun x u => P.basis.repr x u) a =
      (PackingData.ofBasis P.basis).challengeMulMatrix (C := L) a := by
  ext u v
  change algebraMap K L (P.basis.repr (a * P.basis v) u) =
    algebraMap K L (Algebra.leftMulMatrix P.basis a u v)
  rw [Algebra.leftMulMatrix_eq_repr_mul]

open scoped Classical in
theorem evaluateMultiplier_eq [SampleableType L] (r : Fin ℓ → L) (c : Fin κ → L)
    (z : Fin m → L) :
    evaluateMultiplier P.basis (fun x u => P.basis.repr x u) (querySuffix h r) c z =
      (TensorPrefix.multiplier P h).evaluate (r, c) z := by
  refine Eq.trans ?_ ((TensorPrefix.multiplier P h).evaluate_eq (r, c) z).symm
  refine Eq.trans ?_ ((PackingData.ofBasis P.basis).evaluateMultiplier_eq
    (querySuffix h r) ((BatchingRule.eqFold L κ).weight c) z)
  simp only [evaluateMultiplier, runLayers_eq, multiplicationMatrix_eq, eqWeight_eq,
    PackingData.evaluateMultiplier, BatchingRule.eqFold]
  rw [vectorTable_ofFn (fun u => algebraMap K L (P.basis.repr 1 u))]
  rfl

end Agreement

/-! ## The standalone executable prefix -/

/-- The source query and batching challenge retained through the relocation sumcheck. -/
abbrev Context (L : Type) (ℓ κ : ℕ) := (Fin ℓ → L) × (Fin κ → L)

/-- The product-sumcheck multiplier at Boolean points for a retained pair of public challenges.
Consumers tabulate the faces they need, so each lookup computes only its requested value. -/
def prefixMultiplierTable (coordinates : L → Cube κ → K) (h : ℓ = m + κ)
    (ctx : Context L ℓ κ) : Cube m → L :=
  multiplierTable coordinates (querySuffix h ctx.1) ctx.2

/-- The matrix evaluator used by the terminal verifier. -/
def prefixEvaluateMultiplier (basis : Cube κ → L) (coordinates : L → Cube κ → K)
    (h : ℓ = m + κ) (ctx : Context L ℓ κ) : (Fin m → L) → L :=
  evaluateMultiplier basis coordinates (querySuffix h ctx.1) ctx.2

theorem prefixMultiplierTable_eq [SampleableType L] (P : RingSwitchingProfile K L κ)
    (h : ℓ = m + κ) (ctx : Context L ℓ κ) (y : Cube m) :
    prefixMultiplierTable (fun x u => P.basis.repr x u) h ctx y =
      ((TensorPrefix.multiplier P h).polynomial ctx).val.eval (y : Fin m → L) :=
  multiplierTable_eq P h ctx.1 ctx.2 y

theorem prefixEvaluateMultiplier_eq [SampleableType L] (P : RingSwitchingProfile K L κ)
    (h : ℓ = m + κ) (ctx : Context L ℓ κ) :
    prefixEvaluateMultiplier P.basis (fun x u => P.basis.repr x u) h ctx =
      (TensorPrefix.multiplier P h).evaluate ctx :=
  funext (evaluateMultiplier_eq P h ctx.1 ctx.2)

/-- The coordinate head, scalar product-sumcheck rounds, and terminal evaluation message. -/
abbrev ringSwitchPSpec (L : Type) [CommRing L] (κ m : ℕ) :=
  headPSpec L κ ++ₚ ProductSumcheck.Computable.tailPSpec L m

instance : ∀ j, OracleInterface ((ringSwitchPSpec L κ m).Message j) :=
  ProtocolSpec.instOracleInterfaceMessageAppend
    (pSpec₁ := headPSpec L κ) (pSpec₂ := ProductSumcheck.Computable.tailPSpec L m)

instance [SampleableType L] : ∀ j, SampleableType ((ringSwitchPSpec L κ m).Challenge j) :=
  ProtocolSpec.instSampleableTypeChallengeAppend
    (pSpec₁ := headPSpec L κ) (pSpec₂ := ProductSumcheck.Computable.tailPSpec L m)

/-- Reduce a source claim to a packed opening claim using tensor ring switching.
This low-level constructor does not require a proof that the coordinate map agrees with the
basis. `ringSwitchReduction_verify_eq` states the agreement needed to recover the tensor
prefix specification. -/
def ringSwitchReduction [DecidableEq L] [BEq L] [LawfulBEq L] {ι : Type}
    (OStmt : ι → Type) [∀ j, OracleInterface (OStmt j)]
    (basis : Cube κ → L) (coordinates : L → Cube κ → K) (h : ℓ = m + κ) :
    OracleReduction []ₒ ((Fin ℓ → L) × L) OStmt (Cube ℓ → K)
      (Context L ℓ κ × ((Fin m → L) × L)) OStmt (Cube m → L) (ringSwitchPSpec L κ m) :=
  (headReduction OStmt basis coordinates h).append
    (ProductSumcheck.Computable.tailReduction OStmt (prefixMultiplierTable coordinates h)
      (prefixEvaluateMultiplier basis coordinates h))

instance [DecidableEq L] [BEq L] [LawfulBEq L] {ι : Type} (OStmt : ι → Type)
    [∀ j, OracleInterface (OStmt j)] (basis : Cube κ → L)
    (coordinates : L → Cube κ → K) (h : ℓ = m + κ) :
    (ringSwitchReduction OStmt basis coordinates h).prover.OutputIsPure :=
  Prover.OutputIsPure.append _ _
    (show (headReduction OStmt basis coordinates h).prover.OutputIsPure from inferInstance)
    (show (ProductSumcheck.Computable.tailReduction OStmt
      (prefixMultiplierTable coordinates h)
      (prefixEvaluateMultiplier basis coordinates h)).prover.OutputIsPure from inferInstance)

/-- The head and every tail round preserve the original commitment oracle. -/
theorem ringSwitchReduction_materializeOutput [DecidableEq L] [BEq L] [LawfulBEq L]
    {ι : Type} (OStmt : ι → Type) [∀ j, OracleInterface (OStmt j)]
    (basis : Cube κ → L) (coordinates : L → Cube κ → K) (h : ℓ = m + κ)
    (c : (ringSwitchPSpec L κ m).Challenges) (ost : ∀ j, OStmt j)
    (msg : (ringSwitchPSpec L κ m).Messages) :
    (ringSwitchReduction OStmt basis coordinates h).verifier.materializeOutput c ost msg = ost := by
  change ((headReduction OStmt basis coordinates h).verifier.append
      (ProductSumcheck.Computable.tailReduction OStmt (prefixMultiplierTable coordinates h)
        (prefixEvaluateMultiplier basis coordinates h)).verifier).materializeOutput c ost msg = ost
  rw [OracleVerifier.append_materializeOutput, headReduction_materializeOutput,
    ProductSumcheck.Computable.tailReduction_materializeOutput]

section VerifyAgreement

variable [DecidableEq L] [BEq L] [LawfulBEq L] [SampleableType L]
  (P : RingSwitchingProfile K L κ) (h : ℓ = m + κ) (a : AbstractOStmtIn L m)

/-- The full verifier comparison follows by checking the head and tail at their respective
transcript projections. Failure from either phase is preserved by sequential composition. -/
theorem ringSwitchReduction_verify_eq_of_tail
    (decodeTail : (ProductSumcheck.Computable.tailPSpec L m).FullTranscript →
      (ProductSumcheck.pSpec L m).FullTranscript)
    (hTail : ∀ (stmt : HeadOutput L ℓ κ m) (ost : ∀ j, (TensorPrefix.commitment a).OStmt j)
        (tr : (ProductSumcheck.Computable.tailPSpec L m).FullTranscript),
      (ProductSumcheck.Computable.tailReduction (TensorPrefix.commitment a).OStmt
        (prefixMultiplierTable (fun x u => P.basis.repr x u) h)
        (prefixEvaluateMultiplier P.basis (fun x u => P.basis.repr x u)
          h)).verifier.toVerifier.verify (stmt, ost) tr =
      (ProductSumcheck.verifier (TensorPrefix.multiplier P h)
        (TensorPrefix.commitment a)).toVerifier.verify (stmt, ost) (decodeTail tr))
    (stmt : (Fin ℓ → L) × L) (ost : ∀ j, (TensorPrefix.commitment a).OStmt j)
    (tr : (ringSwitchPSpec L κ m).FullTranscript) :
    (ringSwitchReduction (TensorPrefix.commitment a).OStmt P.basis (fun x u => P.basis.repr x u)
      h).verifier.toVerifier.verify (stmt, ost) tr =
      (TensorPrefix.verifier P h a).toVerifier.verify (stmt, ost)
        (decodeHeadTranscript P tr.fst ++ₜ decodeTail tr.snd) := by
  rw [ringSwitchReduction, OracleReduction.append, TensorPrefix.verifier,
    RingSwitch.verifier_toVerifier, OracleVerifier.append_toVerifier]
  simp only [Verifier.append, FullTranscript.append_fst,
    FullTranscript.append_snd]
  rw [show (headReduction (TensorPrefix.commitment a).OStmt P.basis (fun x u => P.basis.repr x u)
      h).verifier.toVerifier.verify (stmt, ost) tr.fst =
      (TensorPrefix.headVerifier P h a).toVerifier.verify (stmt, ost)
        (decodeHeadTranscript P tr.fst) from
    headVerifier_verify_decodeHeadTranscript P h a stmt ost tr.fst]
  simp only [hTail]
  rfl

/-- Interpret the executable prefix transcript on the original tensor and polynomial wire.
The carrier is reconstructed from columns and the scalar messages are decoded in order. -/
noncomputable def decodeRingSwitchTranscript
    (tr : (ringSwitchPSpec L κ m).FullTranscript) :
    (TensorPrefix.pSpec P (ℓ' := m)).FullTranscript :=
  decodeHeadTranscript P tr.fst ++ₜ ProductSumcheck.Computable.decodeTailTranscript tr.snd

/-- The executable prefix verifier agrees with the original verifier at every decoded transcript.
Acceptance, rejection, evaluation claims, and the output commitment oracles all agree.
The supplied runtime basis values and coordinates must represent the original basis. -/
theorem ringSwitchReduction_verify_eq
    (basis : Cube κ → L) (coordinates : L → Cube κ → K)
    (hBasis : basis = ⇑P.basis) (hCoordinates : coordinates = fun x u => P.basis.repr x u)
    (stmt : (Fin ℓ → L) × L) (ost : ∀ j, (TensorPrefix.commitment a).OStmt j)
    (tr : (ringSwitchPSpec L κ m).FullTranscript) :
    (ringSwitchReduction (TensorPrefix.commitment a).OStmt basis coordinates
      h).verifier.toVerifier.verify (stmt, ost) tr =
      (TensorPrefix.verifier P h a).toVerifier.verify (stmt, ost)
        (decodeRingSwitchTranscript P tr) := by
  subst basis coordinates
  refine ringSwitchReduction_verify_eq_of_tail P h a
    ProductSumcheck.Computable.decodeTailTranscript ?_ stmt ost tr
  intro s os tail
  exact ProductSumcheck.Computable.tailReduction_verify_eq (TensorPrefix.commitment a)
    (prefixMultiplierTable (fun x u => P.basis.repr x u) h)
    (prefixEvaluateMultiplier P.basis (fun x u => P.basis.repr x u) h)
    (TensorPrefix.multiplier P h)
    (fun ctx r => congrFun (prefixEvaluateMultiplier_eq P h ctx) r) s os tail

end VerifyAgreement

end RingSwitching.Packing.TensorPrefix.Computable
