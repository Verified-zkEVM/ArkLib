# Permission and Provenance Record for `kz99/rs-ld-mca`

Status: project-owner attestation recorded; direct grant evidence and license terms not yet archived

Record created: 2026-09-04

Last updated: 2026-09-05

## Purpose

This record documents the permission and provenance presently relied upon when adapting material
from Kai Zhe Zheng's [`kz99/rs-ld-mca`](https://github.com/kz99/rs-ld-mca) formalization into
Quang Dao's ArkLib fork. It is deliberately narrower than a software license. It records what the
project owner has attested, the source versions used, the material adapted so far, and the facts
that still require direct evidence.

## Project-owner attestation

On 2026-09-04, Quang Dao stated in the Codex project thread for this formalization:

> they have given us approval to use those materials as we do our formalization. we should ofc
> credit them.

The antecedent of "they" was "one of the authors" of the partial formalization at
`kz99/rs-ld-mca`. This committed record is Quang Dao's durable attestation that such permission was
received. The underlying message or other direct evidence from the grantor has not yet been
archived in this repository.

On 2026-09-05, Quang Dao further identified the grantor as his coauthor Kai Zhe Zheng
(`kz99`) and confirmed that he had given full approval for seamless integration into ArkLib.
Quang specifically authorized replacing provenance-based names such as `Donor` with intrinsic
mathematical names while retaining authorship credit. This is an additional project-owner
attestation; it does not replace the original grant message, which is not archived here.

The attestation is currently understood to authorize adapting the source formalization for this
Reed-Solomon list-decoding formalization, subject to explicit credit. It does **not**, by itself,
establish any of the following:

- the date, medium, or exact wording of the original grant;
- a blanket public software license for the source repository;
- permission to relicense the donor source under Apache-2.0;
- license compatibility for verbatim redistribution; or
- permission for uses outside this formalization project.

These limitations are factual provenance boundaries, not a conclusion that any particular use is
forbidden. This record is not legal advice and does not replace a license or direct permission
grant.

## Source identity and audited revisions

| Item | Durable identifier | Role in this project |
|---|---|---|
| Source repository | [`kz99/rs-ld-mca`](https://github.com/kz99/rs-ld-mca) | Donor Lean formalization |
| Initially audited snapshot | [`82c1d5c00820f74a7ec18be716c033430bef5ae8`](https://github.com/kz99/rs-ld-mca/commit/82c1d5c00820f74a7ec18be716c033430bef5ae8) | First version reviewed for possible reuse |
| Substantive original formalization | [`be57cd2`](https://github.com/kz99/rs-ld-mca/commit/be57cd2) | Kai Zhe Zheng's original development |
| Adaptation source snapshot | [`9699ee7a6143f6efe1d8cfed84998a4f8c79c40f`](https://github.com/kz99/rs-ld-mca/commit/9699ee7a6143f6efe1d8cfed84998a4f8c79c40f) | Exact donor head used by the first ArkLib port |
| Free-order contribution | [`b1e346fc39780adb442ed2504a316b32702b97af`](https://github.com/kz99/rs-ld-mca/commit/b1e346fc39780adb442ed2504a316b32702b97af) | Commit metadata names Codex as author and Pratyush Mishra as committer; merged by Kai Zhe Zheng through [PR 1](https://github.com/kz99/rs-ld-mca/pull/1) |

No `LICENSE`, `COPYING`, or `NOTICE` file was visible in the donor repository at the audited
`82c1d5c...` or adaptation-source `9699ee7...` revisions. Consequently, this project relies on the
permission attested above and does not infer a license from the repository's public availability.

## Material adapted into ArkLib

The first port was authored in ArkLib commits
[`a0508a30`](https://github.com/quangvdao/ArkLib/commit/a0508a3062840796fd1d406d2d354eadbd06b4bc)
and
[`ec88ca64`](https://github.com/quangvdao/ArkLib/commit/ec88ca64b1a0ccb701c91524c06500d069743280),
then integrated on the all-rate formalization branch by merge commit
[`52903c27`](https://github.com/quangvdao/ArkLib/commit/52903c27). The following table records
the adapted surface at that integration point.

| Donor material at `9699ee7...` | ArkLib adaptation | Credited contributors |
|---|---|---|
| `RSListDecoding/Defs/InterpolationSpace.lean` | [`InterpolationSpace.lean`](../../../../ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Space.lean) | Kai Zhe Zheng |
| `RSListDecoding/Lemmas/GlobalDimension.lean` | [`GlobalDimension.lean`](../../../../ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Global/Dimension.lean) | Kai Zhe Zheng |
| `RSListDecoding/Defs/Parameters.lean` and the free-order parameter layer | [`Parameters/Basic.lean`](../../../../ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/Basic.lean) | Kai Zhe Zheng and Pratyush Mishra |
| `RSListDecoding/Lemmas/FreeParameters.lean`, `FreeRankThreshold.lean`, and related free-order estimates | [`Parameters/FreeOrder.lean`](../../../../ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/FreeOrder.lean) | Kai Zhe Zheng and Pratyush Mishra |
| `RSListDecoding/Lemmas/ScopedGlobalDimension.lean` and its free-order analogue | [`ScopedGlobalDimension.lean` in the full development](https://github.com/quangvdao/ArkLib/blob/765ae773/ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/ScopedGlobalDimension.lean) | Kai Zhe Zheng and Pratyush Mishra |

The original port also included `FreeOrderDimensionCanary.lean`, an ArkLib-specific validation
client rather than adapted material. The reconciled development retains this client at
`HiddenDerivative/Interpolation/FreeOrderDimensionCanary.lean`.

Each adapted file names its contributors, source repository, and pinned source commit in its
header or module documentation. Future adaptations must preserve the same file-level attribution
and add their exact donor and integration commits to this record.

Subsequent adaptations, from the same pinned donor revision `9699ee7...`, are recorded below.

| Donor material | ArkLib adaptation | Integration commit | Credited contributors |
|---|---|---|---|
| `RSListDecoding/Lemmas/GlobalBudgets.lean` | [`RootFinding/SpecializationDegree.lean`](../../../../ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/DegreeBounds/SpecializationDegree.lean) | `14568bfd` | Kai Zhe Zheng and Quang Dao; specialization bounds generalized to commutative semirings |
| `RSListDecoding/Lemmas/Contact.lean` | [`LocalContact.lean`](../../../../ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Local/Contact.lean) | `c88abc18` | Kai Zhe Zheng and Quang Dao; monomial divisibility adapted and composed with ArkLib's canonical specialization |
| Translation-support argument in `RSListDecoding/Lemmas/ConstraintFactorization.lean` | [`LocalIntermediateSpace.lean`](../../../../ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Local/IntermediateSpace.lean) | `0004a411`, lint repair `30ce14a6` | Kai Zhe Zheng, Quang Dao, and Justin Thaler; exact finite coordinate and kernel interfaces are new |
| Signed support-weight helpers, via the preceding `LocalIntermediateSpace.lean` adaptation | [`Local/Coordinates.lean`](../../../../ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Local/Coordinates.lean) (formerly the asymmetric-band local-rank route) | `73b968e4` (source `3ce3fcf2`) | Kai Zhe Zheng credited for the inherited support argument; asymmetric-band inequalities and coordinate rank bound are new |
| `RSListDecoding/Defs/ScaledLattice.lean` and `RSListDecoding/Lemmas/ScaledLattice.lean` | [`Parameters/ScaledLattice.lean`](../../../../ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/Lattice/ScaledLattice.lean) | `2da2d754`, documentation `c59c3bc8` | Kai Zhe Zheng, Pratyush Mishra, and Quang Dao |
| `RSListDecoding/Lemmas/ScaledShellDiscrete.lean` | [`Parameters/ScaledShellDiscrete.lean`](../../../../ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/Lattice/ScaledShellDiscrete.lean) | `c59c3bc8` | Kai Zhe Zheng, Pratyush Mishra, and Quang Dao |
| `RSListDecoding/Lemmas/ScaledShell.lean` | [`Parameters/RoundedScaledShell.lean`](../../../../ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/Lattice/RoundedScaledShell.lean) | `c59c3bc8`, comment `ad5ca87b` | Kai Zhe Zheng, Pratyush Mishra, and Quang Dao |
| Scalar comparison in `RSListDecoding/Lemmas/RankArithmetic.lean` and cancellation in `RSListDecoding/Lemmas/DimensionComparison.lean` | [`Interpolation/FreeOrderDimension.lean`](../../../../ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/FreeOrderDimension.lean) | `301597fb` | Kai Zhe Zheng, Pratyush Mishra, and Quang Dao; the certified-kernel residual arithmetic is ArkLib-specific |

[`RateBinDimensionBound.lean`](../../../../ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity/RatePartition/DimensionBound.lean)
at `dab8a72c` is ArkLib-specific uniform finite-bin assembly consuming these estimates, not a
further donor port. These adaptations do not import the donor's root-counting or runtime axioms.

## Evidence needed to upgrade this record

Before this project claims a public license grant or compatibility with ArkLib's Apache-2.0
license, archive or link a direct confirmation from an authorized grantor that records:

1. the grantor's identity and authority over the relevant material;
2. the date and medium of the grant;
3. whether the grant covers adaptation, publication, and redistribution of source code;
4. the covered repository revisions or files; and
5. the license or other terms under which the adapted material may be distributed.

The direct message need not be made public if it contains private information. In that case, this
record should identify its custodian, preservation location, date, and a cryptographic digest or
other stable reference sufficient for the project maintainers to retrieve and verify it.
