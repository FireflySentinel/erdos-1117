import Erdos1117.FactoredFunction
import Erdos1117.SmallFiber
import Erdos1117.Exceptions

open Set Complex

namespace Erdos1117

noncomputable def reflected (A : ℂ → ℂ) (w : ℂ) : ℂ := starRingEnd ℂ (A (starRingEnd ℂ w))

/-- Distinct maximum points give distinct points in one product fibre. -/
theorem maximum_points_bound_of_fiber {f : ℂ → ℂ} {r lam : ℝ} {K : ℕ}
    (hcommon : ∀ z ∈ maximumPoints f r, logarithmicDerivative f z = (lam : ℂ))
    (hcard : (productFiber (logarithmicDerivative f) (reflected (logarithmicDerivative f))
      ((r ^ 2 : ℝ) : ℂ) lam).encard ≤ K) :
    (maximumPoints f r).encard ≤ K := by
  let j := fun z : ℂ => (z, starRingEnd ℂ z)
  have hj : InjOn j (maximumPoints f r) := by
    intro z hz w hw heq
    exact congrArg Prod.fst heq
  have hmap : MapsTo j (maximumPoints f r)
      (productFiber (logarithmicDerivative f) (reflected (logarithmicDerivative f))
        ((r ^ 2 : ℝ) : ℂ) lam) := by
    intro z hz
    refine ⟨?_, hcommon z hz, ?_⟩
    · change z * starRingEnd ℂ z = ((r ^ 2 : ℝ) : ℂ)
      rw [Complex.mul_conj', hz.1, Complex.ofReal_pow]
    · change reflected (logarithmicDerivative f) (starRingEnd ℂ z) = (lam : ℂ)
      simp [reflected, hcommon z hz]
  exact (Set.encard_le_encard_of_injOn hmap hj).trans hcard

/-- The global fibre estimate needed on physical radii. -/
def GlobalFibreBound (m k : ℕ) (h : ℂ → ℂ) : Prop :=
  ∃ S : Set ℝ, S.Countable ∧ S ⊆ Ioi 0 ∧
    ∀ r : ℝ, 0 < r → r ∉ S → ∀ a : ℝ, (m : ℝ) < a →
      (productFiber (logarithmicDerivative (factoredFunction m h))
        (reflected (logarithmicDerivative (factoredFunction m h)))
        ((r ^ 2 : ℝ) : ℂ) a).encard ≤ 2 * k

/-- The maximum-point bound, conditional on the global fibre estimate. -/
theorem maximum_bound_off_countable_of_global_fiber_bound (m k : ℕ) {h : ℂ → ℂ}
    (hh : Differentiable ℂ h) (h0 : h 0 ≠ 0) (hnc : ¬ ∃ c : ℂ, ∀ z, h z = c)
    (hg : GlobalFibreBound m k h) :
    ∃ E : Set ℝ, E.Countable ∧ E ⊆ Ioi 0 ∧ ∀ r : ℝ, 0 < r → r ∉ E →
      (maximumPoints (factoredFunction m h) r).encard ≤ 2 * k := by
  obtain ⟨S, hS, _, hglobal⟩ := hg
  obtain ⟨N, hN, hcommon⟩ := maximum_points_common_value_off_countable m hh h0 hnc
  refine ⟨(S ∪ N) ∩ Ioi 0, (hS.union hN).mono inter_subset_left, inter_subset_right, ?_⟩
  intro r hr hnot
  have hS' : r ∉ S := fun hs => hnot ⟨Or.inl hs, hr⟩
  have hN' : r ∉ N := fun hn => hnot ⟨Or.inr hn, hr⟩
  obtain ⟨lam, hlt, hc⟩ := hcommon r hr hN'
  exact maximum_points_bound_of_fiber hc (hglobal r hr hS' lam hlt)

end Erdos1117
