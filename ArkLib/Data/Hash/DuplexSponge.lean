/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Classes.HasSize
import ArkLib.Data.Classes.Initialize
import ArkLib.Data.Classes.Serde
import ArkLib.Data.Classes.Zeroize

/-!
  # Duplex Sponge API

  This file contains the API for the duplex sponge, which is a sponge that can be used to hash
  data.

  The API is based on the [spongefish](https://github.com/arkworks-rs/spongefish) Rust library.

  The API is designed to be as close as possible to the Rust implementation (as of June 22, 2025).

  The API is subject to change as spongefish changes.
-/

/-- Type class for types that can be used as units in a cryptographic sponge.

Following the [spongefish](https://github.com/arkworks-rs/spongefish) Rust library, we require the
following:

- The type has zero (i.e. `zeroize` in Rust)
- The type can be serialized and deserialized to/from `ByteArray`
- The type has a fixed size in bytes
- The type implements `write` and `read` methods, which are used to write and read the unit to/from
  an IO stream. They are implemented by default using the `serialize` and `deserialize` methods, and
  the `IO.FS.Stream.{read/write}` functions.
-/
class SpongeUnit (α : Type) extends Zeroize α, Serde α ByteArray, HasSize α UInt8 where
  /--
  Rust interface:
  ```rust
    /// Write a bunch of units in the wire.
    fn write(bunch: &[Self], w: &mut impl std::io::Write) -> Result<(), std::io::Error>;
  ```
  Default implementation: serialize each unit of `α`, then write to stream
  -/
  write (stream : IO.FS.Stream) : Array α → IO Unit :=
    Array.foldlM (fun _ a => IO.FS.Stream.write stream (serialize a)) ()
  /--
  Rust interface:
  ```rust
    /// Read a bunch of units from the wire
    fn read(r: &mut impl std::io::Read, bunch: &mut [Self]) -> Result<(), std::io::Error>;
  ```
  Default implementation: read `byteSize * array.length` bytes from stream, deserialize each
  unit of `α`, then return the array if there is no error, otherwise throw an error
  -/
  read (stream : IO.FS.Stream) : Array α → IO (Array α) :=
    fun arr => do
      let bytes ← Array.mapM (fun _ => IO.FS.Stream.read stream (USize.ofNat (HasSize.size α UInt8))) arr
      let units := Array.mapM deserialize bytes
      if h : units.isSome
        then return units.get h
        else IO.throwServerError "Failed to read units"

/-- Type class for types that can be used as a duplex sponge, with respect to the sponge unit type
  `U`.

Following the [spongefish](https://github.com/arkworks-rs/spongefish) Rust library, we require the
following:

- The type is inhabited (`Default` in Rust), and can be zeroized (i.e. `Zeroize` in Rust)
- The type can be initialized from a 32-byte vector (seed)
- There are 3 methods:
  - `absorbUnchecked` to absorb an array of units in the sponge
  - `squeezeUnchecked` to squeeze out an array of units, changing the state of the sponge
  - `ratchetUnchecked` to ratchet the state of the sponge
-/
class DuplexSpongeInterface (U : Type) [SpongeUnit U] (α : Type*)
    extends Inhabited α, Zeroize α, Initialize α (Vector UInt8 32) where
  /-- Absorb new elements in the sponge.
  ```rust
    fn absorb_unchecked(&mut self, input: &[U]) -> &mut Self;
  ```
  -/
  absorbUnchecked : α × Array U → α

  /-- Squeeze out new elements, changing the state of the sponge.
  ```rust
    fn squeeze_unchecked(&mut self, output: &mut [U]) -> &mut Self;
  ```
  -/
  squeezeUnchecked : α × Array U → α × Array U

  /-- Ratcheting.
  ```rust
    fn ratchet_unchecked(&mut self) -> &mut Self;
  ```

  More notes from the Rust implementation:
  ```rust
    /// This operations makes sure that different elements are processed in different blocks.
    /// Right now, this is done by:
    /// - permuting the state.
    /// - zero rate elements.
    /// This has the effect that state holds no information about the elements absorbed so far.
    /// The resulting state is compressed.
  ```
  -/
  ratchetUnchecked : α → α


/-- Type class for storing the length & rate of a sponge permutation. -/
class SpongePermutationSize where
  /-- The width of the sponge, equal to rate R plus capacity. -/
  N : Nat
  /-- The rate of the sponge. -/
  R : Nat
  /-- The rate is less than the width. -/
  R_lt_N : R < N := by omega
  /-- The rate is non-zero (i.e. positive). -/
  [neZero_R : NeZero R]

attribute [instance] SpongePermutationSize.neZero_R

namespace SpongePermutationSize

variable [sz : SpongePermutationSize]

/-- The capacity of the sponge, defined as `N - R`, the width minus the rate. -/
def C : Nat := sz.N - sz.R

instance [sz : SpongePermutationSize] : NeZero sz.C where
  out := by
    have := sz.R_lt_N
    simp [C]; omega

end SpongePermutationSize

/-- Type class for cryptographic permutations used in sponge constructions.

Rust interface:
```rust
pub trait Permutation: Zeroize + Default + Clone + AsRef<[Self::U]> + AsMut<[Self::U]> {
    type U: Unit;
    const N: usize;  // The width of the sponge
    const R: usize;  // The rate of the sponge
    fn new(iv: [u8; 32]) -> Self;
    fn permute(&mut self);
}
```
Note that we do not quite know how to handle `AsRef` and `AsMut`. My interpretation is that they
basically provide a way to get to the underlying state of the sponge, which is `Vector U N`.
Because of this, I give a tentative API for `AsRef` and `AsMut` basically as a lens between `α` and
`Vector U N` (i.e. `view` and `update`).

TODO: figure out the needed properties here
-/
class SpongePermutation (U : Type) [SpongeUnit U] (α : Type*) extends
    Inhabited α,
    Zeroize α,
    SpongePermutationSize,
    Initialize α (Vector UInt8 32) where
  -- TENTATIVE: a lens between `α` and `Vector U N`
  view : α → Vector U N
  update : α → Vector U N → α

  /-- Permute the **state** of the sponge. Note that this does _not_ imply a permutation (i.e.
    bijection) for the entire type.

    TODO: figure out the needed properties here (that it is a permutation on the state?) -/
  permute : α → α


-- need to "descend" from `permute : α → α` to `permuteState : Vector U N → Vector U N`, and then
-- for the reverse direction

class LawfulSpongePermutation (U : Type) [SpongeUnit U] (α : Type*) [SpongePermutation U α] where
  /- TODO: the permutation is a bijection on the state. -/

/-- A cryptographic duplex sponge.

Rust interface:
```rust
#[derive(Clone, PartialEq, Eq, Default, Zeroize, ZeroizeOnDrop)]
pub struct DuplexSponge<C: Permutation> {
    permutation: C,
    absorb_pos: usize,
    squeeze_pos: usize,
}
```
-/
structure DuplexSponge (U : Type) [SpongeUnit U] (C : Type*) [SpongePermutation U C] where
  permutation : C
  /-- Current position in the rate portion for absorbing data (0 ≤ absorbPos < R) -/
  absorbPos : Fin (SpongePermutationSize.R)
  /-- Current position in the rate portion for squeezing data (0 ≤ squeezePos ≤ R) -/
  squeezePos : Fin (SpongePermutationSize.R)
deriving Inhabited

namespace DuplexSponge

variable {U : Type} {C : Type*} [SpongeUnit U] [SpongePermutation U C]

-- Make DuplexSponge zeroizable
instance : Zeroize (DuplexSponge U C) where
  zeroize sponge := {
    permutation := Zeroize.zeroize sponge.permutation,
    absorbPos := 0,
    squeezePos := 0
  }

-- Make DuplexSponge initializable from 32-byte vector
instance : Initialize (DuplexSponge U C) (Vector UInt8 32) where
  new iv := {
    permutation := Initialize.new iv,
    absorbPos := 0,
    squeezePos := 0
  }

/--
## Algorithm Documentation for DuplexSponge Implementation

(Generated by Claude 4 Sonnet based on the Rust implementation)

### absorbUnchecked: Absorb an array of units into the sponge
Algorithm (from Rust implementation):
1. Process input array in chunks that fit within the remaining rate space
2. While there's still input data:
   - If absorb_pos == R (rate is full): permute the state, reset absorb_pos to 0
   - Otherwise:
     * Calculate chunk_size = min(remaining_input.length, R - absorb_pos)
     * Copy chunk into state[absorb_pos..absorb_pos + chunk_size]
     * Update absorb_pos += chunk_size
     * Continue with remaining input
3. After processing all input, set squeeze_pos = R (force permutation on next squeeze)

Key insight: The sponge state (Vector U N) has the first R elements as the "rate" portion
where data is absorbed/squeezed, and the last (N-R) elements as the "capacity" portion
that provides security but is never directly touched.

### squeezeUnchecked: Squeeze out an array of units from the sponge
Algorithm (from Rust implementation):
1. If output array is empty, return immediately
2. Process output in chunks:
   - If squeeze_pos == R:
     * Permute the state first
     * Reset squeeze_pos = 0, absorb_pos = 0
   - Calculate chunk_size = min(remaining_output.length, R - squeeze_pos)
   - Copy state[squeeze_pos..squeeze_pos + chunk_size] into output
   - Update squeeze_pos += chunk_size
   - Recursively handle remaining output
3. Return updated sponge and filled output array

Note: Unlike absorb which processes input sequentially, squeeze may need to permute
multiple times if the requested output is larger than what's available in the rate.

### ratchetUnchecked: Ratchet the sponge state for domain separation
Algorithm (from Rust implementation):
1. Permute the state (ensures domain separation from previous operations)
2. Zero out the rate portion: state[0..R] = all zeros
   (This erases any information about previously absorbed elements)
3. Set squeeze_pos = R (forces permutation on next squeeze operation)

Purpose: This operation ensures that different elements are processed in different
blocks, providing domain separation. After ratcheting, the state holds no information
about elements absorbed so far - the state is "compressed" and secure.
-/

-- Implement DuplexSpongeInterface for DuplexSponge. TODO: port from the Rust implementation
instance : DuplexSpongeInterface U (DuplexSponge U C) where
  absorbUnchecked := sorry
  squeezeUnchecked := sorry
  ratchetUnchecked := sorry

end DuplexSponge

namespace UInt8

-- Implement SpongeUnit for UInt8

instance : Zeroize UInt8 where
  zeroize _ := 0

instance : Serialize UInt8 ByteArray where
  serialize byte := ByteArray.mk #[byte]

/-- Deserialize a single byte from a byte array. Gives `none` if the array is not of size 1. -/
instance : DeserializeOption UInt8 ByteArray where
  deserialize bytes :=
    if h : bytes.size = 1 then
      some bytes[0]
    else
      none

instance : Serde UInt8 ByteArray where

instance : HasSize UInt8 UInt8 where
  size := 1
  toFun := ⟨fun byte => #v[byte], by intro x y; simp⟩

instance : SpongeUnit UInt8 where

end UInt8
