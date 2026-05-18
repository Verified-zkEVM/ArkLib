import Mathlib.Algebra.Polynomial.BigOperators

namespace Polynomial

theorem natDegree_sum_lt_of_forall_lt.{u_1, w}
  {ι : Type w} (s : Finset ι) {S : Type u_1} [Semiring S]
  {n : ℕ} [inst : NeZero n] (f : ι → Polynomial S) (h : ∀ i ∈ s, (f i).natDegree < n) :
  (∑ i ∈ s, f i).natDegree < n := by
  rw [←Nat.le_pred_iff_lt (by aesop (add safe forward [inst.out]) (add safe (by omega)))]
  exact natDegree_sum_le_of_forall_le _ _ <| fun i hi ↦ 
    Nat.le_pred_of_lt (h _ hi)

end Polynomial
