/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.FieldTheory.NonBinaryField.KoalaBear
import ArkLib.Data.Vector.Basic

/-!
  # Poseidon2 Reference Implementation

  This is the Lean translation of the reference Python implementation of Poseidon2 in
  `leanEthereum/leanSpec`, with KoalaBear as the base field.

  The translation is done on Sep 12, 2025.

  ## References

  - Poseidon2: [Poseidon2: A Faster Version of the Poseidon Hash
    Function](https://eprint.iacr.org/2023/323)

  - Lean Ethereum spec:
    https://github.com/leanEthereum/leanSpec/blob/main/src/lean_spec/subspecs/poseidon2
-/

set_option linter.style.nativeDecide false
-- set_option maxRecDepth 300

open Vector

namespace Poseidon2

/-! First, we give the round constants -/

/-- The constants for Poseidon2 with 16 rounds
(total of 8 * 16 + 20 = 148 constants) -/
def rawConstants16 : Vector KoalaBear.Field 148 := #v[
    2128964168,
    288780357,
    316938561,
    2126233899,
    426817493,
    1714118888,
    1045008582,
    1738510837,
    889721787,
    8866516,
    681576474,
    419059826,
    1596305521,
    1583176088,
    1584387047,
    1529751136,
    1863858111,
    1072044075,
    517831365,
    1464274176,
    1138001621,
    428001039,
    245709561,
    1641420379,
    1365482496,
    770454828,
    693167409,
    757905735,
    136670447,
    436275702,
    525466355,
    1559174242,
    1030087950,
    869864998,
    322787870,
    267688717,
    948964561,
    740478015,
    679816114,
    113662466,
    2066544572,
    1744924186,
    367094720,
    1380455578,
    1842483872,
    416711434,
    1342291586,
    1692058446,
    1493348999,
    1113949088,
    210900530,
    1071655077,
    610242121,
    1136339326,
    2020858841,
    1019840479,
    678147278,
    1678413261,
    1361743414,
    61132629,
    1209546658,
    64412292,
    1936878279,
    1980661727,
    1423960925,
    2101391318,
    1915532054,
    275400051,
    1168624859,
    1141248885,
    356546469,
    1165250474,
    1320543726,
    932505663,
    1204226364,
    1452576828,
    1774936729,
    926808140,
    1184948056,
    1186493834,
    843181003,
    185193011,
    452207447,
    510054082,
    1139268644,
    630873441,
    669538875,
    462500858,
    876500520,
    1214043330,
    383937013,
    375087302,
    636912601,
    307200505,
    390279673,
    1999916485,
    1518476730,
    1606686591,
    1410677749,
    1581191572,
    1004269969,
    143426723,
    1747283099,
    1016118214,
    1749423722,
    66331533,
    1177761275,
    1581069649,
    1851371119,
    852520128,
    1499632627,
    1820847538,
    150757557,
    884787840,
    619710451,
    1651711087,
    505263814,
    212076987,
    1482432120,
    1458130652,
    382871348,
    417404007,
    2066495280,
    1996518884,
    902934924,
    582892981,
    1337064375,
    1199354861,
    2102596038,
    1533193853,
    1436311464,
    2012303432,
    839997195,
    1225781098,
    2011967775,
    575084315,
    1309329169,
    786393545,
    995788880,
    1702925345,
    1444525226,
    908073383,
    1811535085,
    1531002367,
    1635653662,
    1585100155,
    867006515,
    879151050,
]

/-- The constants for Poseidon2 with width 24
(total of 8 * 24 + 23 = 215 constants) -/
def RAW_CONSTANTS_24 : Vector KoalaBear.Field 215 := #v[
    487143900,
    1829048205,
    1652578477,
    646002781,
    1044144830,
    53279448,
    1519499836,
    22697702,
    1768655004,
    230479744,
    1484895689,
    705130286,
    1429811285,
    1695785093,
    1417332623,
    1115801016,
    1048199020,
    878062617,
    738518649,
    249004596,
    1601837737,
    24601614,
    245692625,
    364803730,
    1857019234,
    1906668230,
    1916890890,
    835590867,
    557228239,
    352829675,
    515301498,
    973918075,
    954515249,
    1142063750,
    1795549558,
    608869266,
    1850421928,
    2028872854,
    1197543771,
    1027240055,
    1976813168,
    963257461,
    652017844,
    2113212249,
    213459679,
    90747280,
    1540619478,
    324138382,
    1377377119,
    294744504,
    512472871,
    668081958,
    907306515,
    518526882,
    1907091534,
    1152942192,
    1572881424,
    720020214,
    729527057,
    1762035789,
    86171731,
    205890068,
    453077400,
    1201344594,
    986483134,
    125174298,
    2050269685,
    1895332113,
    749706654,
    40566555,
    742540942,
    1735551813,
    162985276,
    1943496073,
    1469312688,
    703013107,
    1979485151,
    1278193166,
    548674995,
    2118718736,
    749596440,
    1476142294,
    1293606474,
    918523452,
    890353212,
    1691895663,
    1932240646,
    1180911992,
    86098300,
    1592168978,
    895077289,
    724819849,
    1697986774,
    1608418116,
    1083269213,
    691256798,
    328586442,
    1572520009,
    1375479591,
    322991001,
    967600467,
    1172861548,
    1973891356,
    1503625929,
    1881993531,
    40601941,
    1155570620,
    571547775,
    1361622243,
    1495024047,
    1733254248,
    964808915,
    763558040,
    1887228519,
    994888261,
    718330940,
    213359415,
    603124968,
    1038411577,
    2099454809,
    949846777,
    630926956,
    1168723439,
    222917504,
    1527025973,
    1009157017,
    2029957881,
    805977836,
    1347511739,
    540019059,
    589807745,
    440771316,
    1530063406,
    761076336,
    87974206,
    1412686751,
    1230318064,
    514464425,
    1469011754,
    1770970737,
    1510972858,
    965357206,
    209398053,
    778802532,
    40567006,
    1984217577,
    1545851069,
    879801839,
    1611910970,
    1215591048,
    330802499,
    1051639108,
    321036,
    511927202,
    591603098,
    1775897642,
    115598532,
    278200718,
    233743176,
    525096211,
    1335507608,
    830017835,
    1380629279,
    560028578,
    598425701,
    302162385,
    567434115,
    1859222575,
    958294793,
    1582225556,
    1781487858,
    1570246000,
    1067748446,
    526608119,
    1666453343,
    1786918381,
    348203640,
    1860035017,
    1489902626,
    1904576699,
    860033965,
    1954077639,
    1685771567,
    971513929,
    1877873770,
    137113380,
    520695829,
    806829080,
    1408699405,
    1613277964,
    793223662,
    648443918,
    893435011,
    403879071,
    1363789863,
    1662900517,
    2043370,
    2109755796,
    931751726,
    2091644718,
    606977583,
    185050397,
    946157136,
    1350065230,
    1625860064,
    122045240,
    880989921,
    145137438,
    1059782436,
    1477755661,
    335465138,
    1640704282,
    1757946479,
    1551204074,
    681266718,
]

/-- The degree of the S-Box for Poseidon2 over the KoalaBear field -/
def sBoxDegree : Nat := 3

/-- The parameters determining a Poseidon2 permutation (over the KoalaBear field) -/
structure Params where
  -- First, the parameters
  width : Nat
  numFullRounds : Nat
  numPartialRounds : Nat
  internalDiagVectors : Vector KoalaBear.Field width
  roundConstants : Vector KoalaBear.Field (numFullRounds * width + numPartialRounds)

  -- Conditions on the parameters

  /-- The width must be non-zero (i.e. positive) -/
  [width_ne_zero : NeZero width]

  /-- The number of full rounds must be non-zero (i.e. positive) -/
  [numFullRounds_ne_zero : NeZero numFullRounds]

  /-- The number of partial rounds must be non-zero (i.e. positive) -/
  [numPartialRounds_ne_zero : NeZero numPartialRounds]

  /-- The width must be a multiple of 4 -/
  width_dvd_by_4 : 4 ∣ width
  /-- The number of full rounds must be even -/
  numFullRounds_even : Even numFullRounds

namespace Params

variable (params : Params)

@[simp]
lemma width_pos : 0 < params.width := Nat.zero_lt_of_ne_zero params.width_ne_zero.out

@[simp]
lemma numFullRounds_pos : 0 < params.numFullRounds :=
  Nat.zero_lt_of_ne_zero params.numFullRounds_ne_zero.out

@[simp]
lemma numPartialRounds_pos : 0 < params.numPartialRounds :=
  Nat.zero_lt_of_ne_zero params.numPartialRounds_ne_zero.out

def widthDiv4 : Nat := params.width / 4

@[simp]
lemma widthDiv4_mul_4_eq_width : params.widthDiv4 * 4 = params.width :=
  Nat.div_mul_cancel params.width_dvd_by_4

def halfNumFullRounds : Nat := params.numFullRounds / 2

@[simp]
lemma numFullRounds_dvd_by_2 : 2 ∣ params.numFullRounds :=
  even_iff_two_dvd.mp params.numFullRounds_even

@[simp]
lemma halfNumFullRounds_mul_2_eq_numFullRounds :
    params.halfNumFullRounds * 2 = params.numFullRounds :=
  Nat.div_mul_cancel params.numFullRounds_dvd_by_2

end Params

def params16 : Params where
  width := 16
  numFullRounds := 8
  numPartialRounds := 20
  internalDiagVectors := #v[
       -2,
        1,
        2,
        1 / 2,
        3,
        4,
        -1 / 2,
        -3,
        -4,
        1 / (2 ^ 8),
        1 / 8,
        1 / (2 ^ 24),
        -1 / (2 ^ 8),
        -1 / 8,
        -1 / 16,
        -1 / (2 ^ 24),
    ]
  roundConstants := rawConstants16
  width_dvd_by_4 := by decide
  numFullRounds_even := by decide

/-! ## Parameter set for width 24 -/

/-- Parameters for width = 24, following the Python spec. -/
def params24 : Params where
  width := 24
  numFullRounds := 8
  numPartialRounds := 23
  internalDiagVectors := #v[
        -2,
        1,
        2,
        1 / 2,
        3,
        4,
        -1 / 2,
        -3,
        -4,
        1 / (2 ^ 8),
        1 / 4,
        1 / 8,
        1 / 16,
        1 / 32,
        1 / 64,
        1 / (2 ^ 24),
        -1 / (2 ^ 8),
        -1 / 8,
        -1 / 16,
        -1 / 32,
        -1 / 64,
        -1 / (2 ^ 7),
        -1 / (2 ^ 9),
        -1 / (2 ^ 24)
    ]
  roundConstants := RAW_CONSTANTS_24
  width_dvd_by_4 := by decide
  numFullRounds_even := by decide

/-! ## M4 matrix and linear layers -/

/-- The M4 matrix -/
def m4Matrix : Vector (Vector KoalaBear.Field 4) 4 :=
  #v[
    #v[2, 3, 1, 1],
    #v[1, 2, 3, 1],
    #v[1, 1, 2, 3],
    #v[3, 1, 1, 2]
  ]

/-- Multiply the m4 block with an input vector of length 4
TODO: define matrix-vector multiplication with `Vector` representation generally -/
def applyM4 (chunk : Vector KoalaBear.Field 4) : Vector KoalaBear.Field 4 :=
  Vector.Matrix.mulVec m4Matrix chunk

variable (params : Params)

/--
Applies the external linear layer (M_E), which is structured for efficiency.

The matrix `M_E` is applied in two steps:
1.  **Block-Diagonal Matrix Multiplication**: The `width`-element state vector is treated as a
    `width/4 × 4` matrix. Each 4-element row is multiplied by the `m4Matrix`.
    This is equivalent to multiplying the state vector by a block-diagonal matrix where each
    block is `m4Matrix`.

2.  **Diffusion Layer**: A diffusion effect is achieved by adding the sum of all elements in each
    column to every element in that same column. This mixes the state across the 4-element chunks.
    If `s'` is the state after the M4 multiplication, the output is `s''` where
    `s''_{i,j} = s'_{i,j} + ∑_k s'_{k,j}`.
-/
def externalLinearLayer (state : Vector KoalaBear.Field params.width) :
    Vector KoalaBear.Field params.width :=
  -- First step: convert `state` into chunks of length 4, then apply M4 to each chunk
  let chunks := Vector.Matrix.ofFlatten (state.cast (params.widthDiv4_mul_4_eq_width).symm)
  let chunksAfterM4 := chunks.map (fun chunk => applyM4 chunk)

  -- Diffusion step: add column sums to each row
  -- This is equivalent to multiplication by circ(2*I, I, ..., I)

  -- Transpose the matrix
  let transposedMatrix := Vector.Matrix.transpose chunksAfterM4

  -- Compute the sum of each column
  let columnSums := transposedMatrix.map (fun col => col.foldl (· + ·) 0)

  -- Add the column sums to each row
  let chunksAfterDiffusion := chunksAfterM4.map (fun row => row.zipWith (· + ·) columnSums)

  -- Convert back to flat vector
  (Vector.flatten chunksAfterDiffusion).cast (params.widthDiv4_mul_4_eq_width)

/--
Applies the internal linear layer (M_I), optimized for partial rounds.

This layer's matrix is `M_I = J + D`, where `J` is the all-ones matrix and `D` is a
diagonal matrix defined by `internalDiagVectors`. This structure allows the matrix-vector
product `M_I * s` to be computed in `O(width)` time instead of `O(width^2)`.

The computation is performed as `M_I * s = J*s + D*s`:
- `J*s` is a vector where each element is the sum of all elements in `s`.
- `D*s` is the element-wise product of the state `s` and the diagonal vector `d`.
-/
def internalLinearLayer (state : Vector KoalaBear.Field params.width) :
    Vector KoalaBear.Field params.width :=
  -- 1. Calculate the sum of all elements in the state vector.
  -- This single sum will be used for every element of the `J*s` product.
  let sumAll := state.foldl (fun acc x => acc + x) 0

  -- 2. Compute `(J*s)_i + (D*s)_i` for each element `i`.
  -- This is `sumAll + d_i * s_i`.
  state.zipWith (fun s d => sumAll + d * s) params.internalDiagVectors

/-- A single full round of the Poseidon2 permutation. -/
def fullRound (params : Params) (state : Vector KoalaBear.Field params.width)
    (roundConstants : Vector KoalaBear.Field params.width) : Vector KoalaBear.Field params.width :=
  -- 1. Add round constants
  let stateWithConstants := state.zipWith (·+·) roundConstants
  -- 2. Apply S-box to full state
  let stateAfterSbox := stateWithConstants.map (fun x => x ^ sBoxDegree)
  -- 3. Apply external linear layer
  externalLinearLayer params stateAfterSbox

/-- A single partial round of the Poseidon2 permutation. -/
def partialRound (state : Vector KoalaBear.Field params.width) (roundConstant : KoalaBear.Field) :
    Vector KoalaBear.Field params.width :=
  -- 1. Add round constant to the first element
  let stateWithConstant := state.set 0 (state[0] + roundConstant)
  -- 2. Apply S-box to the first element
  let stateAfterSbox := stateWithConstant.set 0 (stateWithConstant[0] ^ sBoxDegree)
  -- 3. Apply internal linear layer
  internalLinearLayer params stateAfterSbox

/-- Full Poseidon2 permutation on a state vector. -/
@[inline]
def permute (params : Params) (state : Vector KoalaBear.Field params.width) :
    Vector KoalaBear.Field params.width :=
  letI rcs := params.roundConstants

  -- Initial external linear layer
  let st0 := externalLinearLayer params state

  -- First half of full rounds
  let st1 : Vector KoalaBear.Field params.width :=
    Fin.foldl params.halfNumFullRounds (fun st_acc rc_idx =>
      let rc_chunk := (rcs.extract rc_idx (rc_idx + params.width)).cast (by sorry)
      let st_new := fullRound params st_acc rc_chunk
      st_new) st0

  -- Drop the round constants used in the first half of full rounds
  let rcs := rcs.drop (params.halfNumFullRounds * params.width)

  -- Partial rounds
  let st2 := Fin.foldl params.numPartialRounds (fun st_acc rc_idx =>
    let rc_val := rcs[rc_idx]'(sorry)
    let st_new := partialRound params st_acc rc_val
    st_new) st1

  -- Drop the round constants used in the partial rounds
  let rcs := rcs.drop params.numPartialRounds

  -- Second half of full rounds
  let st3 := Fin.foldl params.halfNumFullRounds (fun st_acc rc_idx =>
    let rc_chunk := (rcs.extract rc_idx (rc_idx + params.width)).cast (by sorry)
    let st_new := fullRound params st_acc rc_chunk
    st_new) st2

  st3

end Poseidon2
