/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.NumberTheory.PrattCertificate

/-!
  # The Secp256k1 base and scalar prime fields

  We define the two primes underlying the Secp256k1 elliptic curve.

  The base prime is the prime on which the elliptic curve is defined.

  The scalar prime is the prime that divides the order of the curve.

  ## References

  `p` is the base prime, and `n` is the scalar prime in [Section 2.4.1](http://www.secg.org/sec2-v2.pdf).

-/

namespace Secp256k1

-- Base field

@[reducible]
def BASE_FIELD_CARD : Nat := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f

/- Alternative representation -/
example : BASE_FIELD_CARD = 2 ^ 256 - 2 ^ 32 - 2 ^ 9 - 2 ^ 8 - 2 ^ 7 - 2 ^ 6 - 2 ^ 4 - 1
  := by unfold BASE_FIELD_CARD; norm_num

abbrev BaseField := ZMod BASE_FIELD_CARD


/- Pratt certificate for BASE_FIELD_CARD

(3 (2 3 7 13441 205115282021455665897114700593932402728804164701536103180137503955397371)
     (1 1 1 1 1)
     (() () () ()
      (10 (2 3 5 29 31 7723 132896956044521568488119 255515944373312847190720520512484175977)
          (1 1 1 2 1 1 1 1)
          (() () () () () ()
           (6 (2 3 22149492674086928081353)
              (1 1 1)
              (() ()
               (5 (2 3 5323 173378833005251801)
                  (3 1 1 1)
                  (() () ()
                   (6 (2 5 2621 24809 13331831)
                      (3 2 1 1 1)
                      (() () () ()
                       (13 (2 5 971 1373)
                           (1 1 1 1)
                           (() () () ()))
                       ))
                   ))
               ))
           (3 (2 7 11 1627 2657 4423 41201 96557 7240687 107590001)
              (3 2 1 1 1 1 1 1 1 1)
              (() () () () () () () () ()
               (3 (2 5 7 29 53)
                  (4 4 1 1 1)
                  (() () () () ()))
               ))
           ))
      )))

-/

theorem BaseField_is_prime : Nat.Prime BASE_FIELD_CARD := by
  unfold BASE_FIELD_CARD
  refine PrattCertificate'.out (p := BASE_FIELD_CARD) ⟨3, (by reduce_mod_char), ?_⟩
  refine .split [2, 3, 7, 13441,
    205115282021455665897114700593932402728804164701536103180137503955397371]
    (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr | hr | hr
  all_goals rw [hr]
  · exact .prime 2 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 7 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 13441 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · refine .prime 205115282021455665897114700593932402728804164701536103180137503955397371 1 _ ?_
      (by reduce_mod_char; decide) (by norm_num)
    · refine PrattCertificate'.out ⟨10, (by reduce_mod_char), ?_⟩
      refine .split [2, 3, 5, 29 ^ 2, 31, 7723, 132896956044521568488119,
        255515944373312847190720520512484175977] (fun r hr => ?_) (by norm_num)
      simp at hr
      rcases hr with hr | hr | hr | hr | hr | hr | hr | hr
      all_goals rw [hr]
      · exact .prime 2 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 3 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 5 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 29 2 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 31 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 7723 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 132896956044521568488119 1 _ (by pratt)
          (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 255515944373312847190720520512484175977 1 _ (by pratt)
          (by reduce_mod_char; decide) (by norm_num)

instance : Fact (Nat.Prime BASE_FIELD_CARD) := ⟨BaseField_is_prime⟩

instance : Field BaseField := ZMod.instField BASE_FIELD_CARD



-- Scalar field

@[reducible]
def SCALAR_FIELD_CARD : Nat := 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141

abbrev ScalarField := ZMod SCALAR_FIELD_CARD

theorem ScalarField_is_prime : Nat.Prime SCALAR_FIELD_CARD := by
  unfold SCALAR_FIELD_CARD
  refine PrattCertificate'.out (p := SCALAR_FIELD_CARD) ⟨7, (by reduce_mod_char), ?_⟩
  refine .split [2 ^ 6, 3, 149, 631, 107361793816595537, 174723607534414371449,
    341948486974166000522343609283189] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr
  all_goals rw [hr]
  · exact .prime 2 6 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 149 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 631 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 107361793816595537 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 174723607534414371449 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · refine .prime 341948486974166000522343609283189 1 _ ?_ (by reduce_mod_char; decide)
      (by norm_num)
    · refine PrattCertificate'.out ⟨2, (by reduce_mod_char), ?_⟩
      refine .split [2 ^ 2, 3 ^ 3, 109, 29047611873442575647497758179] (fun r hr => ?_)
        (by norm_num)
      simp at hr
      rcases hr with hr | hr | hr | hr
      all_goals rw [hr]
      · exact .prime 2 2 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 3 3 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 109 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 29047611873442575647497758179 1 _ (by pratt) (by reduce_mod_char; decide)
          (by norm_num)

instance : Fact (Nat.Prime SCALAR_FIELD_CARD) := ⟨ScalarField_is_prime⟩

instance : Field ScalarField := ZMod.instField SCALAR_FIELD_CARD

end Secp256k1
