/-
Copyright (c) 2020 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Mathlib.Tactic.ReduceModChar
import Mathlib.NumberTheory.LucasPrimality

/-!
# The Lucas test for primes.

This file implements the Lucas test for primes (not to be confused with the Lucas-Lehmer test for
Mersenne primes). A number `a` witnesses that `n` is prime if `a` has order `n-1` in the
multiplicative group of integers mod `n`. This is checked by verifying that `a^(n-1) = 1 (mod n)`
and `a^d ≠ 1 (mod n)` for any divisor `d | n - 1`. This test is the basis of the Pratt primality
certificate.

## TODO

- Bonus: Show the reverse implication i.e. if a number is prime then it has a Lucas witness.
  Use `Units.IsCyclic` from `RingTheory/IntegralDomain` to show the group is cyclic.
- Write a tactic that uses this theorem to generate Pratt primality certificates
- Integrate Pratt primality certificates into the norm_num primality verifier

## Implementation notes

Note that the proof for `lucas_primality` relies on analyzing the multiplicative group
modulo `p`. Despite this, the theorem still holds vacuously for `p = 0` and `p = 1`: In these
cases, we can take `q` to be any prime and see that `hd` does not hold, since `a^((p-1)/q)` reduces
to `1`.
-/

section New

-- TODO: port to `Mathlib`?
lemma Nat.Prime.dvd_mul_list {p : ℕ} {l : List ℕ} (h : p.Prime) :
    p ∣ l.prod ↔ ∃ r ∈ l, p ∣ r := by
  constructor
  · intro hdiv
    induction l with
    | nil =>
      simp at *
      rw [hdiv] at h
      aesop
    | cons hd tl ih =>
      rw [List.prod_cons] at hdiv
      rcases h.dvd_mul.mp hdiv with (hdiv|hdiv)
      · use hd
        simp
        exact hdiv
      · rcases ih hdiv with ⟨r, hr, hdiv⟩
        use r
        simp at *
        exact ⟨Or.inr hr, hdiv⟩
  · intro h
    rcases h with ⟨r, hr, hdiv⟩
    rw [←List.prod_erase hr]
    exact h.dvd_mul.mpr (Or.inl hdiv)

/-- Recursive form of a Pratt certificate for `p`, which may take in Pratt certificates
  for a list of prime powers `r` less than `p` whose product is equal to `p - 1`. -/
inductive PrattPartList : (p : ℕ) → (a : ZMod p) → ℕ → Prop
  | prime : {p : ℕ} → {a : ZMod p} → (n k nk : ℕ) → n.Prime →
      a ^ ((p - 1) / n) ≠ 1 → n ^ k = nk → PrattPartList p a nk
  | split : {p : ℕ} → {a : ZMod p} → {n : ℕ} → (list : List ℕ) →
      (∀ r ∈ list, PrattPartList p a r) → list.prod = n → PrattPartList p a n

/-- Alternative form of a Pratt certificate for `p`, which may take in Pratt certificates
  for a list of prime powers `r` less than `p` whose product is equal to `p - 1`. -/
structure PrattCertificate' (p : ℕ) : Type where
  a : ZMod p
  pow_eq_one : a ^ (p - 1) = 1
  part : PrattPartList p a (p - 1)

theorem PrattPartList.out {p : ℕ} {a : ZMod p} {n : ℕ} (h : PrattPartList p a n) :
    ∀ q : ℕ, q.Prime → q ∣ n → a ^ ((p - 1) / q) ≠ 1 := by
  induction h with
  | prime n' k nk hprime hpow hnk =>
      subst hnk
      intro q hq hdiv
      cases (Nat.prime_dvd_prime_iff_eq hq hprime).mp (hq.dvd_of_dvd_pow hdiv)
      exact hpow
  | split list hprev hprod ih =>
    rw [←hprod]
    intro q hq hdiv
    rcases hq.dvd_mul_list.mp hdiv with ⟨r, hr, hdiv⟩
    · exact ih r hr q hq hdiv

theorem PrattCertificate'.out {p : ℕ} (c : PrattCertificate' p) : p.Prime :=
  lucas_primality p c.a c.pow_eq_one c.part.out

end New

/-- The binary version of `PrattPartList`. This is the one in the original file. -/
inductive PrattPart : (p : ℕ) → (a : ZMod p) → ℕ → Prop
  | prime : {p : ℕ} → {a : ZMod p} → (n k nk : ℕ) → n.Prime →
      a ^ ((p - 1) / n) ≠ 1 → n ^ k = nk → PrattPart p a nk
  | split : {p : ℕ} → {a : ZMod p} → {n : ℕ} → (l r : ℕ) →
      PrattPart p a l → PrattPart p a r → l * r = n → PrattPart p a n

structure PrattCertificate (p : ℕ) : Type where
  a : ZMod p
  pow_eq_one : a ^ (p - 1) = 1
  part : PrattPart p a (p - 1)

theorem PrattPart.out {p : ℕ} {a : ZMod p} {n : ℕ} (h : PrattPart p a n) :
    ∀ q : ℕ, q.Prime → q ∣ n → a ^ ((p - 1) / q) ≠ 1 := by
  induction h with
  | prime n k nk hprime hpow hnk =>
    subst hnk
    intro q hq hdiv
    cases (Nat.prime_dvd_prime_iff_eq hq hprime).mp (hq.dvd_of_dvd_pow hdiv)
    exact hpow
  | split n l r _ hlr ih₁ ih₂ =>
    subst hlr
    intro q hq hdiv
    rcases hq.dvd_mul.mp hdiv with (hdiv|hdiv)
    · exact ih₁ _ hq hdiv
    · exact ih₂ _ hq hdiv

theorem PrattCertificate.out {p : ℕ} (c : PrattCertificate p) : p.Prime :=
  lucas_primality p c.a c.pow_eq_one c.part.out

-- cannot do ^1 correctly it seems?

theorem prime_2 : Nat.Prime 2 := Nat.prime_two
theorem prime_3 : Nat.Prime 3 := Nat.prime_three
theorem prime_5 : Nat.Prime 5 := by
  refine PrattCertificate.out ⟨2, by reduce_mod_char, ?_⟩
  exact .prime 2 2 _ prime_2 (by reduce_mod_char; decide) (by norm_num)
theorem prime_7 : Nat.Prime 7 := by
  refine PrattCertificate.out ⟨3, by reduce_mod_char, ?_⟩
  refine .split 2 3 ?_ ?_ (by norm_num)
  · exact .prime 2 1 _ prime_2 (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 1 _ prime_3 (by reduce_mod_char; decide) (by norm_num)
theorem prime_11 : Nat.Prime 11 := by
  refine PrattCertificate.out ⟨2, by reduce_mod_char, ?_⟩
  refine .split 2 5 ?_ ?_ (by norm_num)
  · exact .prime 2 1 _ prime_2 (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 5 1 _ prime_5 (by reduce_mod_char; decide) (by norm_num)
theorem prime_13 : Nat.Prime 13 := by
  refine PrattCertificate.out ⟨2, by reduce_mod_char, ?_⟩
  refine .split 4 3 ?_ ?_ (by norm_num)
  · exact .prime 2 2 _ prime_2 (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 1 _ prime_3 (by reduce_mod_char; decide) (by norm_num)
theorem prime_17 : Nat.Prime 17 := by
  refine PrattCertificate.out ⟨3, by reduce_mod_char, ?_⟩
  exact .prime 2 4 _ prime_2 (by reduce_mod_char; decide) (by norm_num)
theorem prime_19 : Nat.Prime 19 := by
  refine PrattCertificate.out ⟨2, by reduce_mod_char, ?_⟩
  refine .split 2 9 ?_ ?_ (by norm_num)
  · exact .prime 2 1 _ prime_2 (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 2 _ prime_3 (by reduce_mod_char; decide) (by norm_num)
theorem prime_23 : Nat.Prime 23 := by
  refine PrattCertificate.out ⟨5, by reduce_mod_char, ?_⟩
  refine .split 2 11 ?_ ?_ (by norm_num)
  · exact .prime 2 1 _ prime_2 (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 11 1 _ prime_11 (by reduce_mod_char; decide) (by norm_num)
theorem prime_29 : Nat.Prime 29 := by
  refine PrattCertificate.out ⟨2, by reduce_mod_char, ?_⟩
  refine .split 4 7 ?_ ?_ (by norm_num)
  · exact .prime 2 2 _ prime_2 (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 7 1 _ prime_7 (by reduce_mod_char; decide) (by norm_num)
theorem prime_31 : Nat.Prime 31 := by
  refine PrattCertificate.out ⟨3, by reduce_mod_char, ?_⟩
  refine .split 3 10 ?_ ?_ (by norm_num)
  · exact .prime 3 1 _ prime_3 (by reduce_mod_char; decide) (by norm_num)
  · refine .split 2 5 ?_ ?_ (by norm_num)
    · exact .prime 2 1 _ prime_2 (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 5 1 _ prime_5 (by reduce_mod_char; decide) (by norm_num)
theorem prime_37 : Nat.Prime 37 := by
  refine PrattCertificate.out ⟨2, by reduce_mod_char, ?_⟩
  refine .split 4 9 ?_ ?_ (by norm_num)
  · exact .prime 2 2 _ prime_2 (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 2 _ prime_3 (by reduce_mod_char; decide) (by norm_num)
theorem prime_41 : Nat.Prime 41 := by
  refine PrattCertificate.out ⟨6, by reduce_mod_char, ?_⟩
  refine .split 5 8 ?_ ?_ (by norm_num)
  · exact .prime 5 1 _ prime_5 (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 2 3 _ prime_2 (by reduce_mod_char; decide) (by norm_num)
theorem prime_43 : Nat.Prime 43 := by
  refine PrattCertificate.out ⟨3, by reduce_mod_char, ?_⟩
  refine .split 6 7 ?_ ?_ (by norm_num)
  · refine .split 2 3 ?_ ?_ (by norm_num)
    · exact .prime 2 1 _ prime_2 (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 3 1 _ prime_3 (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 7 1 _ prime_7 (by reduce_mod_char; decide) (by norm_num)
theorem prime_47 : Nat.Prime 47 := by
  refine PrattCertificate.out ⟨5, by reduce_mod_char, ?_⟩
  refine .split 2 23 ?_ ?_ (by norm_num)
  · exact .prime 2 1 _ prime_2 (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 23 1 _ prime_23 (by reduce_mod_char; decide) (by norm_num)

theorem prime_101 : Nat.Prime 101 := by
  refine PrattCertificate.out ⟨2, by reduce_mod_char, ?_⟩
  refine .split 4 25 ?_ ?_ (by norm_num)
  · refine .prime 2 2 _ ?_ (by reduce_mod_char; decide) (by norm_num)
    exact Nat.prime_two
  · refine .prime 5 2 _ ?_ (by reduce_mod_char; decide) (by norm_num)
    refine PrattCertificate.out ⟨2, by reduce_mod_char, ?_⟩
    refine .prime 2 2 _ ?_ (by reduce_mod_char; decide) (by norm_num)
    exact Nat.prime_two

-- theorem prime_987654319 : Nat.Prime 987654319 := sorry

def powMod (a b m : ℕ) : ℕ := Id.run do
  let mut x := a
  let mut n := b
  let mut res := 1

  while n > 0 do
    if n % 2 == 1 then
      res := (x * res) % m
    x := (x * x) % m
    n := n / 2

  return res

structure PowTwoRepr where
  two_exp : ℕ
  odd_part : ℕ

def factorOutTwos (n : ℕ) : PowTwoRepr := Id.run do
  let mut two_exp := 0
  let mut odd_part := n

  while odd_part % 2 = 0 do
    two_exp := two_exp + 1
    odd_part := odd_part / 2

  return ⟨two_exp, odd_part⟩

def millerRabinBases : List ℕ :=
  [2, 325, 9375, 28178, 450775, 9780504, 1795265022]

def deterministicMillerRabin (n : ℕ) : Bool := Id.run do
  if n ≤ 2 ∨ n % 2 = 0 then
    return n = 2

  let ⟨s, d⟩ := factorOutTwos (n - 1)
  for a in millerRabinBases do
    if a % n == 0 then
      continue

    let mut x := powMod a d n
    if x = 1 ∨ x = n - 1 then
      continue

    for _ in [0:s] do
      x := (x * x) % n
      if x == n - 1 ∨ x ≤ 1 then
        break
    if x ≠ n - 1 then
      return false

  return true

def g (n : ℕ) (c : ℕ) (x : ℕ) := (x * x + c) % n

/-- Auxiliary function for `rho` that tries to find a factor of `n` -/
def rho' (n : ℕ) (start : ℕ) (c : ℕ) : Option ℕ := Id.run do
  if n % 2 = 0 then
    return some 2

  let mut x := start
  let mut y := x
  let mut d := 1

  while d = 1 do
    x := g n c x
    y := g n c (g n c y)
    d := Nat.gcd (Int.natAbs (x - y)) n

  if d = n then
    return none
  else
    return some d

def rho (n : ℕ) : Option ℕ := Id.run do
  for st in [2:n] do
    for c in [1:n] do
      if let some d := rho' n st c then
        return some d

  return none

partial def factor (n : ℕ) : Option (List ℕ) :=
  if deterministicMillerRabin n then
    [n]
  else do
    let f ← rho n
    let lhs ← factor f
    let rhs ← factor (n / f)
    return (lhs ++ rhs)

structure PrimeWithMultiplicity : Type where
  prime : ℕ
  multiplicity : ℕ
deriving Repr

/-- Factor `n` into a list of prime numbers with their multiplicities -/
def factor' (n : ℕ) : Option (List PrimeWithMultiplicity) := do
  let facts := List.mergeSort (← factor n)
  let groups := List.splitBy (· = ·) facts
  return groups.map (fun g => ⟨g[0]!, g.length⟩)

mutual

  inductive UnverifiedPrattPart : Type
    | prime : (p : ℕ) → (k : ℕ) → (hp : UnverifiedPrattCertificate p) → UnverifiedPrattPart
    | split : UnverifiedPrattPart → UnverifiedPrattPart → UnverifiedPrattPart
  deriving Repr

  inductive UnverifiedPrattCertificate : ℕ → Type
    | knownPrime : (n : ℕ) → UnverifiedPrattCertificate n
    | of : (n : ℕ) → (a : ℕ) → (part : UnverifiedPrattPart) → UnverifiedPrattCertificate n
  deriving Repr

end

instance {n : ℕ} : ToString (UnverifiedPrattCertificate n) where
  toString := fun c => s!"{repr c}"


mutual

  partial def computePrattPart (l : List PrimeWithMultiplicity) : Option UnverifiedPrattPart := do
    if let [⟨p, k⟩] := l then
      let cert ← computePrattCertificate p
      return .prime p k cert

    let ⟨left, right⟩ := l.splitAt (l.length / 2)
    let lhs ← computePrattPart left
    let rhs ← computePrattPart right
    return .split lhs rhs

  partial def computePrattCertificate (n : ℕ) : Option (UnverifiedPrattCertificate n) :=
    -- TODO does this shortcut?
    if n ≤ 50 ∧ deterministicMillerRabin n then
      some (.knownPrime n)
    else do
      let fs ← factor' (n - 1)
      let a ← findWitness n fs
      let part ← computePrattPart fs
      return .of n a part
  where
    findWitness (n : ℕ) (fs : List PrimeWithMultiplicity) : Option ℕ := do
      for a in [2:n] do
        let mut ok := true
        for ⟨p, _⟩ in fs do
          if powMod a ((n - 1) / p) n = 1 then
            ok := false
            break

        if ok then
          return a

      none

end

namespace Tactic

open Lean Meta Simp
open Lean.Elab
open Tactic
open Qq
open Mathlib.Meta.NormNum

def verifySmallPrime (n' : Q(ℕ)) : MetaM Q(Nat.Prime $n') :=
  match n'.natLit! with
    | 2 => do haveI : $n' =Q 2 := ⟨⟩; return q(prime_2)
    | 3 => do haveI : $n' =Q 3 := ⟨⟩; return q(prime_3)
    | 5 => do haveI : $n' =Q 5 := ⟨⟩; return q(prime_5)
    | 7 => do haveI : $n' =Q 7 := ⟨⟩; return q(prime_7)
    | 11 => do haveI : $n' =Q 11 := ⟨⟩; return q(prime_11)
    | 13 => do haveI : $n' =Q 13 := ⟨⟩; return q(prime_13)
    | 17 => do haveI : $n' =Q 17 := ⟨⟩; return q(prime_17)
    | 19 => do haveI : $n' =Q 19 := ⟨⟩; return q(prime_19)
    | 23 => do haveI : $n' =Q 23 := ⟨⟩; return q(prime_23)
    | 29 => do haveI : $n' =Q 29 := ⟨⟩; return q(prime_29)
    | 31 => do haveI : $n' =Q 31 := ⟨⟩; return q(prime_31)
    | 37 => do haveI : $n' =Q 37 := ⟨⟩; return q(prime_37)
    | 41 => do haveI : $n' =Q 41 := ⟨⟩; return q(prime_41)
    | 43 => do haveI : $n' =Q 43 := ⟨⟩; return q(prime_43)
    | 47 => do haveI : $n' =Q 47 := ⟨⟩; return q(prime_47)
    | _ => failure

theorem ZMod.powEqOfPowMod :
   ∀ {n a' c : ℕ} (a : ZMod n), (a' : ZMod n) = a →
      Nat.mod (Nat.pow a' (n - 1)) n = c → c = 1 → a ^ (n - 1) = 1
  | n, a, _,  _, rfl, h, rfl => by
    change a ^ (n - 1) % n = 1 at h
    rw [← Nat.cast_pow, CharP.natCast_eq_natCast_mod (ZMod n) n, h, Nat.cast_one]

theorem ZMod.bla : ∀ {n c : ℕ} (a : ZMod n), c = 1 → IsNat (a ^ (n - 1)) c → a ^ (n - 1) = 1
  | n, _, a, rfl, h => by
    conv_rhs => rw [← Nat.cast_one]
    exact h.out

def verifyEqOne (n a' : Q(ℕ)) (a : Q(ZMod $n)) (_ : Q(($a' : ZMod $n) = $a)) :
    MetaM Q($a ^ ($n - 1) = 1) := do
  let p : Q(ZMod $n) := q($a ^ ($n - 1))
  let .isNat _ c hc ← Tactic.ReduceModChar.normIntNumeral n p
    q(CommRing.toRing) q(ZMod.charP $n) | failure
  assumeInstancesCommute
  haveI : $p =Q $a ^ ($n - 1) := ⟨⟩
  haveI : $c =Q 1 := ⟨⟩
  return q(ZMod.bla $a (.refl _) $hc)

  -- return q(sorry)
  -- have npred : Q(ℕ) := mkRawNatLit (n.natLit! - 1)
  -- haveI : $n =Q Nat.succ $npred := ⟨⟩
  -- -- haveI : $npred =Q $n - 1 := ⟨⟩
  -- let ⟨c, pc⟩ := evalNatPowMod a' npred n
  -- let pc' : Q(Nat.mod (Nat.pow «$a'» «$npred») «$n» = «$c») := q(sorry)
  -- -- have hc : Q(decide ($c = 1) = true) := (q(Eq.refl true) : Expr)
  -- haveI : $c =Q 1 := ⟨⟩
  -- -- return q(sorry)
  -- return q(ZMod.powEqOfPowMod $a $ha $pc' (.refl _))

theorem ZMod.powNeOfPowMod :
    ∀ {n a' q c : ℕ} (a : ZMod n), (a' : ZMod n) = a → decide (n ≥ 2) = true →
      Nat.mod (Nat.pow a' ((n - 1) / q)) n = c → decide (c ≠ 1) = true → a ^ ((n - 1) / q) ≠ 1
  | n, a, q, _, _, rfl, hn, rfl, h => by
    rw [← Nat.cast_pow]
    conv_rhs => rw [← Nat.cast_one]
    intro h'
    rw [CharP.natCast_eq_natCast (ZMod n) n] at h'
    replace h := of_decide_eq_true h
    apply h
    change a ^ ((n - 1) / q) % n = 1 % n at h'
    convert h'
    replace hn := of_decide_eq_true hn
    exact (Nat.mod_eq_of_lt hn).symm

theorem ZMod.blub :
    ∀ {n q c : ℕ} (a : ZMod n), (decide (n ≥ 2) = true) → (decide (c < n) = true) →
      (decide (c ≠ 1) = true) → IsNat (a ^ ((n - 1) / q)) c → a ^ ((n - 1) / q) ≠ 1
  | n, q, c, a, hn, hc₁, hc₂, ⟨h⟩ => by
    rw [h]
    intro h'
    apply of_decide_eq_true hc₂
    rw [← Nat.cast_one, CharP.natCast_eq_natCast (ZMod n) n] at h'
    rw [← Nat.mod_eq_of_lt (of_decide_eq_true hc₁),
      ← Nat.mod_eq_of_lt (show 1 < n from of_decide_eq_true hn)]
    exact h'

def verifyNeOne (n a' q : Q(ℕ)) (a : Q(ZMod $n)) (_ : Q(($a' : ZMod $n) = $a)) :
    MetaM Q($a ^ (($n - 1) / $q) ≠ 1) := do
  -- return q(sorry)
  let p : Q(ZMod $n) := q($a ^ (($n - 1) / $q))
  let .isNat _ c hc ← Tactic.ReduceModChar.normIntNumeral n p
    q(CommRing.toRing) q(ZMod.charP $n) | failure
  -- have npd : Q(ℕ) := mkRawNatLit ((n.natLit! - 1) / q.natLit!)
  -- haveI : $npd =Q ($n - 1) / $q := ⟨⟩
  -- let ⟨c, pc⟩ := evalNatPowMod a' npd n
  assumeInstancesCommute
  have hn : Q(decide ($n ≥ 2) = true) := (q(Eq.refl true) : Expr)
  have hc₁ : Q(decide ($c < $n) = true) := (q(Eq.refl true) : Expr)
  have hc₂ : Q(decide ($c ≠ 1) = true) := (q(Eq.refl true) : Expr)
  return q(ZMod.blub $a $hn $hc₁ $hc₂ $hc)
  -- return q(ZMod.powNeOfPowMod $a $ha $hn $pc $hc)

-- Invariant: n'.natLit! = n
partial def verifyCertificate (n' : Q(ℕ)) (n : ℕ) :
    UnverifiedPrattCertificate n → MetaM Q(Nat.Prime $n')
  | .knownPrime n => verifySmallPrime n'
  | .of n a part => do
      let cert ← generateCertificate n' n a part
      return q(PrattCertificate.out $cert)
  where
  generateCertificate (n' : Q(ℕ)) (_ : ℕ) (a : ℕ) (part : UnverifiedPrattPart) :
      MetaM Q(PrattCertificate $n') := do
    have alit : Q(ℕ) := mkRawNatLit a
    let ⟨a', pa'⟩ ← mkOfNat q(ZMod $n') q(instAddMonoidWithOne) alit
    let hpow : Q($a' ^ ($n' - 1) = 1) ← verifyEqOne n' alit a' pa'
    let result ← generatePart n' a' alit pa' part
    haveI : $(result.1) =Q $n' - 1 := ⟨⟩
    return q(PrattCertificate.mk $a' $hpow $(result.2))
  generatePart (n' : Q(ℕ)) (a : Q(ZMod $n')) (a' : Q(ℕ)) (pa' : Q(($a' : ZMod $n') = $a)) :
      UnverifiedPrattPart → MetaM ((nn : Q(ℕ)) × Q(PrattPart $n' $a $nn))
    | .prime p k hp => do
      -- dbg_trace "prime {p} {k}"
      have plit : Q(ℕ) := mkRawNatLit p
      let inner ← verifyCertificate plit p hp
      have pklit : Q(ℕ) := mkRawNatLit (p ^ k)
      have klit : Q(ℕ) := mkRawNatLit k
      let hpow ← verifyNeOne n' a' plit a pa'
      haveI : $pklit =Q $plit ^ $klit := ⟨⟩
      return ⟨pklit, q(PrattPart.prime $plit $klit _ $inner $hpow (.refl _))⟩
    | .split left right => do
      let ⟨nleft, pleft⟩ ← generatePart n' a a' pa' left
      let ⟨nright, pright⟩ ← generatePart n' a a' pa' right
      -- dbg_trace "split {nleft.natLit!} {nright.natLit!}"
      have nn : Q(ℕ) := mkRawNatLit (nleft.natLit! * nright.natLit!)
      haveI : $nn =Q $nleft * $nright := ⟨⟩
      return ⟨nn, q(PrattPart.split $nleft $nright $pleft $pright (.refl _))⟩

theorem Nat.Prime_of_isNat : ∀ {n n' : ℕ}, IsNat n n' → n'.Prime → n.Prime
  | _, _, ⟨rfl⟩, hp => hp

elab "pratt" : tactic => do
  -- TODO: use closeMainGoalUsing
  let g ← getMainGoal
  let .app (f : Q(ℕ → Prop)) (n : Q(ℕ)) ← whnf (← g.getType) | failure
  guard <|← withDefault <| withNewMCtxDepth <| isDefEq f q(Nat.Prime)
  let ⟨n', pn⟩ ← deriveNat n q(instAddMonoidWithOneNat)
  let some unverifiedCert := computePrattCertificate n'.natLit! | failure
  let cert ← verifyCertificate n' n'.natLit! unverifiedCert
  let u := q(Nat.Prime_of_isNat $pn $cert)
  closeMainGoal (Name.mkSimple "pratt") u

-- set_option linter.style.setOption false
-- set_option trace.profiler true
-- set_option profiler true

-- example : Nat.Prime 5915587277 := by pratt
-- example : Nat.Prime 1500450271 := by pratt
-- example : Nat.Prime 3267000013 := by pratt
-- example : Nat.Prime 5754853343 := by pratt
-- example : Nat.Prime 4093082899 := by pratt
-- example : Nat.Prime 9576890767 := by pratt
-- example : Nat.Prime 3628273133 := by pratt
-- example : Nat.Prime 2860486313 := by pratt
-- example : Nat.Prime 5463458053 := by pratt
-- example : Nat.Prime 3367900313 := by pratt

end Tactic
