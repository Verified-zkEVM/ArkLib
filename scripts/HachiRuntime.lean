/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
import ArkLib.Commitments.Functional.Hachi.Params

/-!
# Compiled nonrecursive-Hachi runtime checks

**What this certifies.** That the nonrecursive Hachi opening chain — `commit`, the
computable honest lifted witness, the concrete Ajtai lift commitment, the terminal
reveal-and-check, and the whole composed reduction `hachiNonrecursiveOpening` — is *executable*,
by running it at toy parameters against a deterministic oracle and checking that the honest run
is accepted. No theorem is proved here; the point is precisely the thing a theorem cannot say,
namely that every definition on the honest path compiles to code and produces an answer.

It is the executability half of the Aeneas extraction target: `hachiNonrecursiveConcrete`
(`Commitments/Functional/Hachi/Concrete.lean`) is what the Rust implementation is meant to agree
with, and an equivalence proof against something that cannot be run would be worth little.

**Why a compiled executable rather than `#eval`.** Files under `ArkLib/` are collected into the
generated library root, so a `#eval` there is paid on every build, and the interpreter is
far slower than compiled code on everything here. This mirrors `scripts/ToyProblemRuntime.lean`,
the repo's existing convention for compiled execution checks, and the default checks are wired
into `./scripts/validate.sh` the same way.

**Two entry points, and why.** With no argument the executable runs the checks that finish in
milliseconds — that is what `validate.sh` gates on. `--full` adds the composed run (**it passes**:
the verifier accepts, in about six minutes on one core), and `--timing` reports per-check timings.

The split is not cosmetic, and the asymmetry behind it is worth recording. The honest **sumcheck
prover** costs, by a very wide margin, more than everything else on the path put together: the
committer, the computable lift witness, the batching, the nested zero-check and the terminal
check together finish in milliseconds, while the composed run — the same chain plus the
sumcheck — takes minutes. The reason is the shape of the summand: `sumcheckPolyZero` is a
product of `bZero` copies of an `m₀`-variate multilinear extension, so it carries up to
`(bZero + 1)^m₀` monomials, and `computableRoundPoly` evaluates all of them at `2^(m₀ - i)`
points in round `i`. Here `m₀ = 4`, the digit-committed table being `(μ₀ + n₀·δ)·d = 16` rows
once the quotient block is committed as digits (`cubeCoversTable` certifies `16 ≤ 16` at compile
time), and `bZero = 3` — and the run still takes minutes, so this is the first thing to profile if
the honest prover is ever wanted at a realistic size. Every extra cube coordinate multiplies the
cost several-fold: raising `α` from `0` to `1` doubles `d` and so pushes `m₀` to `5`, and the
`τ = δ` table would have done the same.

**The parameters.** `q = 7`, `α = 0` (so `Rq = Z₇[X]/(X+1) ≅ Z₇`, ring dimension `d = 1`),
digit base `b = 3` (hence `δ = ⌈log₃ 7⌉ = 2`, for the message digits and — since `bZero = b` —
also for the quotient digits), one inner/outer/`D` row, `m = r = 0`, `μ₀ = 6`, `n₀ = 5`. The
range parameters sit at the healthy point the gadget decomposition buys — `bZero = b = 3` and
`γ = bZero − 1 = 2 < ⌊q/2⌋ = 3`, so Eq. (20)'s ball check is a real constraint (see `P` below) —
and the committed table is `μ₀ + n₀·δ = 16` rows wide, so `M + 1 = 4` already satisfies
`(μ₀ + n₀·δ)·deg φ ≤ 2^(M+1)` (`16 ≤ 16`, `cubeCoversTable`) — the `τ = δ` table's `18` rows
would have forced `M + 1 = 5`. Not `q = 5`, the
smallest prime admitting honest range parameters at all: the toy data below (keys, witnesses, the
separating pair of `liftComDistinguishes`) is built over `Z₇`. Deliberately tiny beyond that:
this is a code-generation check, and the security theorems are parametric, so nothing is learned
by running it larger.

**`τ` is explicit, and strictly below `δ`.** The folded-witness digit count is the parameter
`Tau = 1`, *not* `δ = 2` (`tauLtDigits`), so the composed run genuinely exercises the **bounded**
`z` decomposition (`boundedBalancedZmodDigitDecomposition`) rather than a full-width one; `ω` is
`1` so that the honest bound `2ʳ·ω·⌊b/2⌋ = 1` fits the balanced capacity of one base-`3` digit,
which is also `1` (`hcapToy` / `hzbToy`). Beyond the composed run, the bounded digit function is
checked directly at the **production** digit parameters `q = 4294967197`, `b = 16` and
`τ = 5` (`Params.lean`; [NOZ26] Figure 9's table says `τ = 4`, but §4.4's own rule gives `5`)
(`boundedDigitsReconstructProd`, `boundedDigitsInBoxProd`) — cheap, and the arithmetic an
extraction target has to reproduce. The full `ℓ = 30` prover is *not* run here.
-/

-- v4.33 respects transparency when synthesizing instances: `DecidableEq K.TCom` / `BEq K.TCom`
-- no longer resolve, because the concrete `K.TCom` projection only reduces past
-- `nonrecursiveLiftCom` at default transparency. File-scoped, as in
-- `Data/CodingTheory/ProximityGap/Errors.lean`.
set_option backward.isDefEq.respectTransparency false

namespace HachiRuntime

open OracleSpec ProtocolSpec OracleComp CompPoly ArkLib.Lattices
open ArkLib.Lattices.Ajtai ArkLib.Lattices.Ajtai.InnerOuter
open ArkLib.Lattices.CyclotomicModulus

/-! ## Toy parameters -/

/-- The toy modulus `q = 7`: not the smallest prime for which the honest range parameters are
satisfiable (they need `1 < b ≤ ⌊q/2⌋`, so `q = 5` is), but the smallest admitting `b = 3`,
which keeps the digit count at `δ = 2` and the committed table well inside the sumcheck
cube — see the parameter note in the module docstring. -/
abbrev Q : ℕ := 7
instance : Fact (Nat.Prime Q) := ⟨by decide⟩
/-- `α = 0`, so the ring is `Z₇[X]/(X + 1) ≅ Z₇` and the ring dimension is `d = 1`. -/
abbrev A : ℕ := 0
/-- The toy cyclotomic ring. -/
abbrev Rng := Rq 𝓜(Q, A)
/-- The extension field of the ring switch, taken to be the base field itself. Legitimate for
correctness (which has error `0`, so no property of any challenge is used); a soundness run would
need a genuine extension so that `2d` distinct challenges exist. -/
abbrev Fld := ZMod Q

abbrev B : ℕ := 3   -- digit base
abbrev Dg : ℕ := Nat.clog B Q   -- δ = 2
abbrev IR : ℕ := 1  -- innerRows
abbrev OR : ℕ := 1  -- outerRows
abbrev DR : ℕ := 1  -- dRows
abbrev Mm : ℕ := 0  -- m
abbrev Rr : ℕ := 0  -- r
abbrev MM : ℕ := 3  -- sumcheck width is M + 1 = 4; pinned by `cubeCoversTable` below
abbrev M1 : ℕ := 1  -- the nested zero-check's second block
abbrev W : ℕ := 1   -- ℓ₁ bound on short challenges (`ω`)

/-- **`τ = 1`, the folded-witness digit count — deliberately *below* `δ = 2`.** This is what makes
the composed run exercise the bounded `z` decomposition: a full `DigitDecomposition` of `ZMod 7`
into one base-`3` digit does not exist (`3 < 7`), and the honest `z` is short instead. -/
abbrev Tau : ℕ := 1
/-- The honest `ℓ∞` bound on `z` the `τ = 1` decomposition is sized for: `2ʳ·ω·⌊b/2⌋ = 1`. -/
abbrev ZB : ℕ := 1

/-- `τ < δ`: the toy profile really separates the two digit counts. -/
theorem tauLtDigits : Tau < Dg := by
  have hb : (1 : ℕ) < 3 := by norm_num
  have hδ : Nat.clog 3 7 = 2 := by
    have h1 : Nat.clog 3 7 ≤ 2 := (Nat.clog_le_iff_le_pow hb).mpr (by norm_num)
    have h2 : ¬ Nat.clog 3 7 ≤ 1 := fun h =>
      absurd ((Nat.clog_le_iff_le_pow hb).mp h) (by norm_num)
    omega
  simp [Dg, Tau, B, Q, hδ]

/-- `μ₀ = 6`: the `R^lin` column count at these parameters, **at `τ = 1`** (it would be `8` at the
full width `τ = δ = 2`). -/
abbrev Mu : ℕ := rlinCols IR Dg Dg Tau Mm Rr
/-- `n₀ = 5`: the `R^lin` row count at these parameters. -/
abbrev Nn : ℕ := rlinRows IR OR DR

/-- The pinned honest range parameters, at the **healthy** point the gadget decomposition buys:
`bZero = b = 3` and `γ = bZero − 1 = 2`, so `γ < ⌊q/2⌋ = 3` and Eq. (20)'s ball check is a real
constraint. Before the refactor the quotient's raw `q/2` bound forced `bZero = ⌊q/2⌋ + 1 = 4` and
`γ = 3 = ⌊q/2⌋`, at which that check was vacuous. -/
def P : HonestRangeParams Q where
  b := B; γ := 2; bZero := 3
  hb := by decide
  hbq := by decide
  hbγ := by decide
  hγZero := by decide
  hbZero := by decide
  hbZeroq := by decide
  hbZeroγ := by decide

/-- `hcap` at the toy profile: the honest bound `ZB = 1` fits the balanced capacity of one
base-`3` digit, `(3 − 1 − 1)·1 = 1`. -/
theorem hcapToy : ZB ≤ balancedDigitCapacity P.b Tau := by
  norm_num [ZB, balancedDigitCapacity, digitOnesValue, P, B, Tau]

/-- `hzb` at the toy profile: `2ʳ·ω·⌊b/2⌋ = 1 ≤ ZB`. -/
theorem hzbToy : 2 ^ Rr * W * (P.b / 2) ≤ ZB := by
  norm_num [ZB, Rr, W, P, B]

/-- `hτ`: `0 < τ`. -/
theorem hTauToy : 0 < Tau := by norm_num [Tau]

/-- A ring element from two coefficients. -/
def rr (a b : ℕ) : Rng := Rq.mk _ (CPolynomial.ofArray #[(a : ZMod Q), (b : ZMod Q)])

/-- Fixed Ajtai keys, standing in for `keygen`'s sampling (which is not what is being checked
here — `keygen` draws them uniformly, and correctness holds for every draw). -/
def pp : Hachi.PublicParamsD 𝓜(Q, A) IR (2 ^ Mm) Dg OR (2 ^ Rr) Dg DR where
  innerMatrix := fun _ j => rr (j.val + 1) (j.val + 2)
  outerMatrix := fun _ j => rr (j.val + 2) 1
  dMatrix := fun _ j => rr 1 (j.val + 1)

/-- The lift commitment's own key: `dRows × (μ₀ + n₀·δ)`, the width a whole lifted witness needs
once the quotient block is committed as its base-`bZero` digits (see the note above
`hachiLiftCom`). `δ = clog_{bZero} Q`. -/
def dMat : Ajtai.Simple.PublicParams 𝓜(Q, A) DR (Mu + Nn * rhoDigitCount Q P.bZero) :=
  fun _ j => rr (j.val + 1) (j.val * 2 + 1)

/-- **The sumcheck cube covers the committed table** — the coverage hypothesis (`hμn`/`hcov`) of
the chain's theorems, certified at the toy parameters so that this executable stays a model of
them. At `τ = 1` the digit-committed table is `μ₀ + n₀·δ = 6 + 5·2 = 16` rows, so the cube needs
`16·d ≤ 2^(M+1)`, and `MM = 3` meets it exactly (`16 ≤ 16`) — one coordinate fewer than the
`τ = δ` table's `18` rows needed, which is the sumcheck cost the `τ` separation saves here.
Without this hypothesis the checks can silently run on a truncated table: `wTable`
returns `0` off-cube, so every off-cube row would escape the range check and the `M̃_α`
contraction. -/
theorem cubeCoversTable :
    (Mu + Nn * rhoDigitCount Q P.bZero) * 𝓜(Q, A).φ.natDegree ≤ 2 ^ (MM + 1) := by
  have hb : (1 : ℕ) < 3 := by norm_num
  have hδ : Nat.clog 3 7 = 2 := by
    have h1 : Nat.clog 3 7 ≤ 2 := (Nat.clog_le_iff_le_pow hb).mpr (by norm_num)
    have h2 : ¬ Nat.clog 3 7 ≤ 1 := fun h =>
      absurd ((Nat.clog_le_iff_le_pow hb).mp h) (by norm_num)
    omega
  have hd : 𝓜(Q, A).φ.natDegree = 1 := by simp
  simp [Mu, Nn, rlinCols, rlinRows, rhoDigitCount, Dg, P, IR, OR, DR, hδ, hd, MM]

/-- The committed multilinear polynomial. -/
def toyPoly : CMlPolynomial Rng (Rr + Mm) :=
  CMlPolynomial.mk _ (Vector.ofFn (fun i : Fin (2 ^ (Rr + Mm)) => rr (i.val + 1) 1))

/-- The honest balanced commitment and its decommitment. -/
def cd := commit (α := A) B (by decide) pp toyPoly

/-- The concrete lift commitment of the chain. -/
abbrev K : LiftCom (LiftedWitness 𝓜(Q, A) Mu Nn) (liftShort 𝓜(Q, A) P.γ P.bZero) :=
  nonrecursiveLiftCom (α := A) (innerRows := IR) (outerRows := OR) (dRows := DR)
    (m := Mm) (r := Rr) P dMat

theorem hdToy : 0 < 𝓜(Q, A).φ.natDegree := by simp

/-! ## Deterministic challenges -/

theorem l1Norm_zero_toy : Rq.l1Norm 𝓜(Q, A) 0 = 0 := by
  simp only [Rq.l1Norm, Rq.zero_val]
  refine Finset.sum_eq_zero (fun x _ => ?_)
  rw [CPolynomial.coeff_zero]
  simp

instance : Inhabited (ShortChallenge 𝓜(Q, A) W) := ⟨⟨0, by rw [l1Norm_zero_toy]; omega⟩⟩

instance instInhSingleRound {CarrierCom C : Type} {r : ℕ} [Inhabited C] :
    ∀ i, Inhabited ((CoordinateWise.SingleRound.pSpec CarrierCom C r).Challenge i)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => (inferInstance : Inhabited (Fin (2 ^ r) → C))

instance instInhScalar {Msg C : Type} [Inhabited C] :
    ∀ i, Inhabited ((CoordinateWise.ScalarRound.pSpecScalar Msg C).Challenge i)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => (inferInstance : Inhabited C)

instance instInhNestedZC {F : Type} [Inhabited F] {m₀ m₁ : ℕ} :
    ∀ i, Inhabited ((pSpecNestedZeroCheck F m₀ m₁).Challenge i) := by
  intro i; change Inhabited F; infer_instance

instance instInhRounds {F : Type} [Field F] [Inhabited F] {b : ℕ} :
    ∀ (count : ℕ) (i : (roundsSpec F b count).ChallengeIdx),
      Inhabited ((roundsSpec F b count).Challenge i)
  | 0, i => Fin.elim0 i.1
  | count + 1, i =>
    letI := instInhRounds (F := F) (b := b) count
    ProtocolSpec.instInhabitedChallengeAppend
      (pSpec₁ := roundsSpec F b count)
      (pSpec₂ := CoordinateWise.ScalarRound.pSpecScalar (RoundMsg F b) F) i

instance instInhSumcheck {F : Type} [Field F] [Inhabited F] {b m₀ : ℕ} :
    ∀ i, Inhabited ((sumcheckSpec F b m₀).Challenge i) :=
  ProtocolSpec.instInhabitedChallengeAppend
    (h₁ := fun i => isEmptyElim i)
    (h₂ := ProtocolSpec.instInhabitedChallengeAppend
      (h₁ := instInhRounds (F := F) (b := b) m₀)
      (h₂ := fun i => isEmptyElim i))


/-! ### Assembling `Inhabited` through the composed spec

Mirrors `completePrefixSpecSampleable` / `throughSumcheckSpecSampleable` /
`nonrecursiveOpeningSpecSampleable` in the chain files: the generic append instance does not
fire reliably through a `ProtocolSpec` this deeply nested, so each layer is applied by name. -/

@[reducible] instance instInhPrefix :
    ∀ i, Inhabited
      (((!p[] : ProtocolSpec 0) ++ₚ
        (CoordinateWise.SingleRound.pSpec
            (CarrierCom 𝓜(Q, A) DR) (ShortChallenge 𝓜(Q, A) W) Rr ++ₚ
          ((!p[] : ProtocolSpec 0) ++ₚ
            (CoordinateWise.ScalarRound.pSpecScalar K.TCom Fld ++ₚ
              ((!p[] : ProtocolSpec 0) ++ₚ
                pSpecNestedZeroCheck Fld (MM + 1) M1))))).Challenge i) :=
  ProtocolSpec.instInhabitedChallengeAppend
    (h₁ := fun i => isEmptyElim i)
    (h₂ := ProtocolSpec.instInhabitedChallengeAppend
      (h₁ := by infer_instance)
      (h₂ := ProtocolSpec.instInhabitedChallengeAppend
        (h₁ := fun i => isEmptyElim i)
        (h₂ := ProtocolSpec.instInhabitedChallengeAppend
          (h₁ := by infer_instance)
          (h₂ := ProtocolSpec.instInhabitedChallengeAppend
            (h₁ := fun i => isEmptyElim i)
            (h₂ := by infer_instance)))))

@[reducible] instance instInhThroughSumcheck :
    ∀ i, Inhabited
      ((throughSumcheckSpec (F := Fld) (dRows := DR) (M := MM) (m₁ := M1) (ω := W) (r := Rr)
        𝓜(Q, A) K.TCom P.bZero).Challenge i) :=
  ProtocolSpec.instInhabitedChallengeAppend (h₁ := instInhPrefix)
    (h₂ := instInhSumcheck (F := Fld) (b := P.bZero) (m₀ := MM + 1))

@[reducible] instance instInhOpeningSpec :
    ∀ i, Inhabited
      ((nonrecursiveOpeningSpec (F := Fld) (innerRows := IR) (messageDigits := Dg)
        (outerRows := OR) (innerDigits := Dg) (dRows := DR) (zDigits := Tau)
        (m := Mm) (r := Rr) (M := MM) (m₁ := M1) (ω := W)
        𝓜(Q, A) K.TCom P.bZero).Challenge i) :=
  ProtocolSpec.instInhabitedChallengeAppend
    (h₁ := instInhThroughSumcheck) (h₂ := fun i => isEmptyElim i)

@[reducible] instance instInhSchemeSpec :
    ∀ i, Inhabited
      (((!p[] : ProtocolSpec 0) ++ₚ
        nonrecursiveOpeningSpec (F := Fld) (innerRows := IR) (messageDigits := Dg)
          (outerRows := OR) (innerDigits := Dg) (dRows := DR) (zDigits := Tau)
          (m := Mm) (r := Rr) (M := MM) (m₁ := M1) (ω := W)
          𝓜(Q, A) K.TCom P.bZero).Challenge i) :=
  ProtocolSpec.instInhabitedChallengeAppend
    (h₁ := fun i => isEmptyElim i) (h₂ := instInhOpeningSpec)

/-! ## The honest input, and the run -/

def query : Vector Rng (Rr + Mm) := #v[]

/-- The commitment API's honest input statement: the balanced commitment, the evaluation query,
and the polynomial's actual value there. -/
def stmtIn : CommitInputStatement Q A OR Mm Rr :=
  (cd.1, ⟨query, CMlPolynomial.eval toyPoly query⟩)

/-- The honest input witness: the data and its decommitment. Together with `stmtIn` this is a
member of `relCommitInput`, the relation `hachiNonrecursiveOpening_perfectCompleteness` is
stated at. -/
def witIn : CommitInputWitness B Q A IR Mm Rr := (toyPoly, cd.2)

/-- The composed nonrecursive opening at the concrete commitment. -/
def opening :=
  hachiNonrecursiveOpening (F := Fld) (ω := W) (M := MM) (m₁ := M1)
    (α := A) (innerRows := IR) (outerRows := OR) (dRows := DR) (m := Mm) (r := Rr)
    (τ := Tau) (zBound := ZB)
    P pp hcapToy K hdToy (by decide) (RingHom.id (ZMod Q))

/-- Answer every uniform query with the largest index — a fixed, total oracle standing in for
the sampling one. -/
def unifIdImpl : QueryImpl unifSpec Id := fun n => Fin.last n

/-- The deterministic challenge oracle: every challenge is the `default` of its type. The
`Id`-valued counterpart of `challengeQueryImpl`, and the reason the run is reproducible.
Legitimate because completeness here has error `0` — the honest prover is accepted at *every*
challenge, so a fixed one is as good as a sampled one. -/
def defaultChallengeImpl {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, Inhabited (pSpec.Challenge i)] :
    QueryImpl ([pSpec.Challenge]ₒ'challengeOracleInterface) Id :=
  fun q => (default : pSpec.Challenge q.1)

/-- **The honest run**: the verifier's verdict on the honest prover's transcript. `none` would
mean the computation failed; `some false` would mean the verifier rejected. -/
def honestVerdict : Unit → Option Bool := fun _ =>
  evalWithAnswerFn
    (QueryImpl.addLift (r := Id) unifIdImpl (@defaultChallengeImpl _ _ instInhSchemeSpec))
    (Reduction.verdict stmtIn witIn opening).run

/-! ## The checks -/

/-- The balanced committer runs and its two halves are consistent: recommitting the returned
decommitment reproduces the returned commitment. -/
def commitRuns : Unit → Bool := fun _ =>
  (commitWithDecomps 𝓜(Q, A) pp.toPublicParams cd.2) == cd.1

/-- A toy `R^lin` instance for the lift's honest witness, at the chain's own parameters. -/
def sToy : RlinStatement 𝓜(Q, A) Nn Mu where
  M := fun _ j => if j.val = 0 then rr 0 1 else 0
  yvec := fun i => rr i.val 2
  bound := P.γ

def zToy : PolyVec Rng Mu := fun j => rr (j.val + 1) (j.val + 2)

/-- The computable honest lifted witness at that instance. -/
def wToy : LiftedWitness 𝓜(Q, A) Mu Nn := honestLiftWitnessC 𝓜(Q, A) hdToy sToy zToy

/-! ### The computable quotient, checked where it is not forced to vanish

At the chain's own ring dimension `d = 1` the honest quotient is *identically* zero for
structural reasons: a row defect has degree `≤ 2d − 2 = 0`, below the modulus's degree, so the
division is trivial and a check there would be vacuous. So the division is also exercised on a
standalone instance at `d = 2` (`𝓜(Q, 1)`, one row and one column), where the row defect has
degree `2` and the quotient is a nonzero constant. `cQuotient` is generic in the modulus and the
dimensions, so this is the same code the chain runs. -/

/-- The `d = 2` modulus used for the quotient checks only. -/
abbrev A2 : ℕ := 1

theorem hd2 : 0 < 𝓜(Q, A2).φ.natDegree := by simp

def rr2 (a b : ℕ) : Rq 𝓜(Q, A2) :=
  Rq.mk _ (CPolynomial.ofArray #[(a : ZMod Q), (b : ZMod Q)])

/-- One row, one column: `M = X`, `z = 1 + 2X`, `y = 3`. The row defect is
`X·(1 + 2X) − 3 = 2X² + X − 3`, so dividing by `X² + 1` leaves the nonzero quotient `2`. -/
def s2 : RlinStatement 𝓜(Q, A2) 1 1 where
  M := fun _ _ => rr2 0 1
  yvec := fun _ => rr2 3 0
  bound := P.γ

def z2 : PolyVec (Rq 𝓜(Q, A2)) 1 := fun _ => rr2 1 2

/-- **The computable quotient is a genuine quotient.** The synthetic division `cQuotient`
performed by `honestLiftWitnessC` satisfies the defining identity
`∑ⱼ Mᵢⱼ·zⱼ − yᵢ = φ·ρᵢ + (remainder)` on the nose, on the computable representation. This is the
executable counterpart of `cQuotient_toPoly`: the lemma says the quotient is Mathlib's, this says
the code computes it. Checked at the chain's parameters and at the `d = 2` instance. -/
def quotientIdentityHolds : Unit → Bool := fun _ =>
  (List.all (List.finRange Nn) fun i =>
    (cRowSum 𝓜(Q, A) sToy zToy i - (sToy.yvec i).1)
      == 𝓜(Q, A).φ * cQuotient 𝓜(Q, A) sToy zToy i
        + (cRowSum 𝓜(Q, A) sToy zToy i - (sToy.yvec i).1).modByMonic 𝓜(Q, A).φ)
  && (List.all (List.finRange 1) fun i =>
    (cRowSum 𝓜(Q, A2) s2 z2 i - (s2.yvec i).1)
      == 𝓜(Q, A2).φ * cQuotient 𝓜(Q, A2) s2 z2 i
        + (cRowSum 𝓜(Q, A2) s2 z2 i - (s2.yvec i).1).modByMonic 𝓜(Q, A2).φ)

/-- The `d = 2` quotient is nonzero, so the identity above is not checked only at `0 = 0`. -/
def quotientNonzero : Unit → Bool := fun _ =>
  List.any (List.finRange 1) fun i => !(cQuotient 𝓜(Q, A2) s2 z2 i == 0)

/-- A second `R^lin` opening, differing from `zToy` in exactly coordinate `1`, giving a second
honest lifted witness for the commitment checks below. The differing coordinate is chosen with
some care: the commitments differ exactly when the key hits the witness difference, and at these
parameters `dMat`'s column `0` is `rr 1 1 = 0`, while a *constant* difference across the `z`
block is also annihilated (those key entries are `−j mod 7` for `j < 8`, summing to `−28 ≡ 0`).
Column `1`'s key entry is nonzero, so this pair genuinely separates. -/
def zToy' : PolyVec Rng Mu := fun j =>
  if j.val = 1 then rr (j.val + 2) (j.val + 2) else rr (j.val + 1) (j.val + 2)

def wToy' : LiftedWitness 𝓜(Q, A) Mu Nn := honestLiftWitnessC 𝓜(Q, A) hdToy sToy zToy'

/-- **The concrete lift commitment distinguishes witnesses.** `K.com` maps the two honest
witnesses to different commitments. Strictly stronger than merely running `K.com`: a `com` that
crashed, diverged, or collapsed to a constant all fail here. (Not implied by any theorem — Ajtai
commitments do have collisions, this check just certifies the code doesn't produce one at this
particular pair.) -/
def liftComDistinguishes : Unit → Bool := fun _ => K.com wToy != K.com wToy'

/-- **The terminal check decides.** It accepts the honest `(statement, witness)` pair it is
handed — the commitment matches, both halves of `liftShort` hold, and the claimed evaluation is
the one `wTableMleEval` computes — and rejects when the claimed value or the commitment is
perturbed. Both directions are checked, so an unconditionally-`true` check would fail here. -/
def terminalHonest : WEvalStatement K.TCom Fld (MM + 1) :=
  { t := K.com wToy
    point := fun _ => 0
    value := wTableMleEval 𝓜(Q, A) (MM + 1) (RingHom.id (ZMod Q)) P.bZero wToy (fun _ => 0) }

def terminalAcceptsHonest : Unit → Bool := fun _ =>
  endPieceCheck 𝓜(Q, A) (MM + 1) P.γ P.bZero P.bZero K (RingHom.id (ZMod Q)) terminalHonest wToy

def terminalRejectsPerturbed : Unit → Bool := fun _ =>
  !endPieceCheck 𝓜(Q, A) (MM + 1) P.γ P.bZero P.bZero K (RingHom.id (ZMod Q))
    { terminalHonest with value := terminalHonest.value + 1 } wToy

/-- The terminal check also rejects when the statement's commitment is not the witness's own —
the reject direction of `endPieceCheck`'s commitment clause. `terminalAcceptsHonest` cannot
exercise it, because `terminalHonest.t` is *defined as* `K.com wToy`, so its commitment
comparison holds by construction. The wrong commitment is the other witness's, which
`liftComDistinguishes` has certified is genuinely different. -/
def terminalRejectsWrongCommitment : Unit → Bool := fun _ =>
  !endPieceCheck 𝓜(Q, A) (MM + 1) P.γ P.bZero P.bZero K (RingHom.id (ZMod Q))
    { terminalHonest with t := K.com wToy' } wToy

/-- **The composed honest run is accepted.** -/
def openingAccepts : Unit → Bool := fun _ => honestVerdict () == some true

/-! ### The bounded (short-input) `z` decomposition, run directly

The composed run above already goes through `boundedBalancedZmodDigitDecomposition` at `τ = 1`.
These checks exercise the same digit function *at the production digit parameters*
(`q = 4294967197`, `b = 16`, `τ = 5` — `HachiParams`, the `ℓ = 30` parameters at the digit count
[NOZ26] §4.4's rule yields, not Figure 9's tabulated `4`), where the interesting arithmetic lives
and where a full-width `5`-digit decomposition is impossible (`16⁵ < q`,
`HachiParams.sixteen_pow_tau_lt_q`). Cheap: a handful of `ZMod q` sums. -/

open ArkLib.Lattices.Ajtai.InnerOuter.HachiParams in
/-- Centered representatives to test the bounded decomposition on: `0`, `±1`, the honest bound
`±131072`, and the extreme representable `±489335`. Encoded as canonical residues. -/
def prodTestResidues : List ℕ :=
  [0, 1, hachiQ - 1, 131072, hachiQ - 131072, 489335, hachiQ - 489335]

open ArkLib.Lattices.Ajtai.InnerOuter.HachiParams in
/-- **The `τ = 5` bounded balanced decomposition reconstructs every short value.** For each test
residue `x`, `∑_{e<5} 16ᵉ · digit x e = x` — the executable counterpart of
`boundedBalancedZmodDigit_reconstruct`, at the production parameters. -/
def boundedDigitsReconstructProd : Unit → Bool := fun _ =>
  prodTestResidues.all fun v =>
    let x : ZMod hachiQ := (v : ℕ)
    (∑ e : Fin hachiTau, (hachiB : ZMod hachiQ) ^ (e : ℕ)
        * boundedBalancedZmodDigit hachiB hachiTau x e) == x

open ArkLib.Lattices.Ajtai.InnerOuter.HachiParams in
/-- **Its digits lie in the paper's balanced box `S_b = [-8, 7]`** (`b = 16`), so the Eq. (20)
range check accepts them — the executable counterpart of
`boundedBalancedZmodDigit_valMinAbs_mem`. -/
def boundedDigitsInBoxProd : Unit → Bool := fun _ =>
  prodTestResidues.all fun v =>
    let x : ZMod hachiQ := (v : ℕ)
    (List.finRange hachiTau).all fun e =>
      let d := ZMod.valMinAbs (boundedBalancedZmodDigit hachiB hachiTau x e)
      decide (-8 ≤ d) && decide (d ≤ 7)

/-- **Non-vacuity**: at least one test residue has a nonzero digit, so the checks above are not
all reading zeros. -/
def boundedDigitsNonzeroProd : Unit → Bool := fun _ =>
  prodTestResidues.any fun v =>
    let x : ZMod HachiParams.hachiQ := (v : ℕ)
    (List.finRange HachiParams.hachiTau).any fun e =>
      !(boundedBalancedZmodDigit HachiParams.hachiB HachiParams.hachiTau x e == 0)

/-- The same reconstruction check at the **toy** parameters `q = 7`, `b = 3`, `τ = 1` — the very
instance the composed run uses, on all three residues that are short there (`0`, `±1`). -/
def boundedDigitsReconstructToy : Unit → Bool := fun _ =>
  ([0, 1, Q - 1] : List ℕ).all fun v =>
    let x : ZMod Q := (v : ℕ)
    (∑ e : Fin Tau, (B : ZMod Q) ^ (e : ℕ) * boundedBalancedZmodDigit B Tau x e) == x

def check (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw <| IO.userError s!"Hachi runtime check failed: {name}"

/-- Run a check and report how long producing its answer took. The call must go through
`IO.lazyPure` to stay inside the clocked window: with a plain `let ok := f ()`, the compiler is
free to sink the pure application to its first use — the result interpolation *after* the second
`IO.monoMsNow` — and the six-minute composed run then reports `0 ms`. (It did.) -/
def timedCheck (name : String) (f : Unit → Bool) : IO Unit := do
  IO.print s!"  {name} ... "
  (← IO.getStdout).flush
  let t0 ← IO.monoMsNow
  let ok ← IO.lazyPure f
  let t1 ← IO.monoMsNow
  IO.println s!"{ok} ({t1 - t0} ms)"
  (← IO.getStdout).flush
  check name ok

/-- The fast checks: every honest-path definition except the composed run. -/
def runFast : IO Unit := do
  check "balanced committer runs and reconstructs" (commitRuns ())
  check "computable honest quotient satisfies the row identity" (quotientIdentityHolds ())
  check "computable honest quotient is nonzero (non-vacuity)" (quotientNonzero ())
  check "concrete lift commitment distinguishes witnesses" (liftComDistinguishes ())
  check "terminal check accepts the honest claim" (terminalAcceptsHonest ())
  check "terminal check rejects a perturbed claim" (terminalRejectsPerturbed ())
  check "terminal check rejects a wrong commitment" (terminalRejectsWrongCommitment ())
  check "bounded z-digits reconstruct (toy q=7, b=3, tau=1)" (boundedDigitsReconstructToy ())
  check "bounded z-digits reconstruct (q=4294967197, b=16, tau=5)"
    (boundedDigitsReconstructProd ())
  check "bounded z-digits lie in the balanced box S_16 = [-8,7]" (boundedDigitsInBoxProd ())
  check "bounded z-digits are not all zero (non-vacuity)" (boundedDigitsNonzeroProd ())
  IO.println "Hachi nonrecursive runtime checks passed"

/-- The composed run, behind `--full`. Separated from `runFast` because the sumcheck's honest
prover dominates the cost by orders of magnitude: see the module docstring. -/
def runFull : IO Unit := do
  check "composed nonrecursive opening accepts the honest run" (openingAccepts ())
  IO.println "Hachi composed honest run accepted"

/-- Same checks, with per-check timings, for locating the cost. -/
def runTiming : IO Unit := do
  timedCheck "commit" commitRuns
  timedCheck "computable quotient identity" quotientIdentityHolds
  timedCheck "computable quotient non-vacuity" quotientNonzero
  timedCheck "concrete lift commitment (distinguishes)" liftComDistinguishes
  timedCheck "terminal check (accept)" terminalAcceptsHonest
  timedCheck "terminal check (reject value)" terminalRejectsPerturbed
  timedCheck "terminal check (reject commitment)" terminalRejectsWrongCommitment
  timedCheck "bounded z-digits reconstruct (toy)" boundedDigitsReconstructToy
  timedCheck "bounded z-digits reconstruct (tau=5)" boundedDigitsReconstructProd
  timedCheck "bounded z-digits in box S_16" boundedDigitsInBoxProd
  timedCheck "bounded z-digits non-vacuity" boundedDigitsNonzeroProd
  timedCheck "composed opening (prefix + sumcheck + terminal)" openingAccepts

end HachiRuntime

def main (args : List String) : IO Unit :=
  if args.contains "--timing" then HachiRuntime.runTiming
  else if args.contains "--full" then do HachiRuntime.runFast; HachiRuntime.runFull
  else HachiRuntime.runFast
