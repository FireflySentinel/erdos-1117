import Mathlib

open Set Polynomial

namespace Erdos1117

/-- A nonzero power has at most its degree many roots. -/
theorem power_fiber_bound (k : ℕ) (hk : 0 < k) (a : ℂ) :
    {z : ℂ | z ^ k = a}.Finite ∧ {z : ℂ | z ^ k = a}.ncard ≤ k := by
  classical
  rw [← Polynomial.nthRootsFinset_toSet hk a]
  refine ⟨Finset.finite_toSet _, ?_⟩
  simp only [Set.ncard_coe_finset, Polynomial.nthRootsFinset_def]
  exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots k a)

/-- Away from zero all complex roots of a power equation are simple. -/
theorem power_fiber_card (k : ℕ) (hk : 0 < k) (a : ℂ) (ha : a ≠ 0) :
    {z : ℂ | z ^ k = a}.ncard = k := by
  classical
  rw [← Polynomial.nthRootsFinset_toSet hk a, Set.ncard_coe_finset,
    Polynomial.nthRootsFinset_def]
  have hn : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [Polynomial.nthRoots,
    Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots
      (Polynomial.separable_X_pow_sub_C a hn ha)),
    IsAlgClosed.card_roots_eq_natDegree, Polynomial.natDegree_X_pow_sub_C]

/-- The local coordinate `A - m = χ^k` supplies the required root count. -/
theorem coordinate_fiber_bound {A χ : ℂ → ℂ} {U : Set ℂ} {m : ℂ}
    {k : ℕ} (hk : 0 < k) (hinj : InjOn χ U)
    (hcoord : ∀ z ∈ U, A z - m = χ z ^ k) (a : ℂ) :
    {z ∈ U | A z = a}.Finite ∧ {z ∈ U | A z = a}.ncard ≤ k := by
  have hsub : χ '' {z ∈ U | A z = a} ⊆ {q : ℂ | q ^ k = a - m} := by
    rintro _ ⟨z, ⟨hz, heq⟩, rfl⟩
    simpa [heq] using (hcoord z hz).symm
  have hi : InjOn χ {z ∈ U | A z = a} := hinj.mono (fun _ h => h.1)
  have hb := power_fiber_bound k hk (a - m)
  refine ⟨(hb.1.subset hsub).of_finite_image hi, ?_⟩
  rw [← hi.ncard_image]
  exact (Set.ncard_le_ncard hsub hb.1).trans hb.2

end Erdos1117
