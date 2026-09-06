import Erdos1117.FactoredFunction
import Erdos1117.SmallFiber
import Erdos1117.Exceptions

open Set Complex

namespace Erdos1117

noncomputable def reflected (A : ℂ → ℂ) (w : ℂ) : ℂ := starRingEnd ℂ (A (starRingEnd ℂ w))

/-- Distinct maximum points give distinct points in one product fibre. -/
theorem maximum_points_bound_of_fiber {f : ℂ → ℂ} {r lam : ℝ} {K : ℕ}
    (hcommon : ∀ z ∈ maximumPoints f r, logarithmicDerivative f z = (lam : ℂ))
    (hfinite : (productFiber (logarithmicDerivative f) (reflected (logarithmicDerivative f))
      ((r ^ 2 : ℝ) : ℂ) lam).Finite)
    (hcard : (productFiber (logarithmicDerivative f) (reflected (logarithmicDerivative f))
      ((r ^ 2 : ℝ) : ℂ) lam).ncard ≤ K) :
    (maximumPoints f r).Finite ∧ (maximumPoints f r).ncard ≤ K := by
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
  refine ⟨(hfinite.subset (Set.image_subset_iff.mpr hmap)).of_finite_image hj, ?_⟩
  exact (Set.ncard_le_ncard_of_injOn j hmap hj hfinite).trans hcard

/-- Positive common values exclude zeros of the original function in both coordinates. -/
theorem productFiber_regular_of_pos {f : ℂ → ℂ} {s : ℂ} {a : ℝ} (ha : 0 < a)
    {p : ℂ × ℂ} (hp : p ∈ productFiber (logarithmicDerivative f)
      (reflected (logarithmicDerivative f)) s a) :
    f p.1 ≠ 0 ∧ f (starRingEnd ℂ p.2) ≠ 0 := by
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  constructor
  · intro hzero
    have := hp.2.1
    simp [logarithmicDerivative, hzero] at this
    exact ha0 this.symm
  · intro hzero
    have := hp.2.2
    simp [reflected, logarithmicDerivative, hzero] at this
    exact ha0 this.symm

/-- The final application, conditional on the total fibre bound of Proposition 4.2. -/
theorem maximum_bound_off_countable_of_global_fiber_bound (m k : ℕ) {h : ℂ → ℂ}
    (hh : Differentiable ℂ h) (h0 : h 0 ≠ 0) (hnc : ¬ ∃ c : ℂ, ∀ z, h z = c)
    {T : Set (ℂ × ℂ)} (hT : T.Countable)
    (hglobal : ∀ (s : ℂ) (a : ℝ), s ≠ 0 → (m : ℝ) < a → (s, (a : ℂ)) ∉ T →
      (productFiber (logarithmicDerivative (factoredFunction m h))
        (reflected (logarithmicDerivative (factoredFunction m h))) s a).Finite ∧
      (productFiber (logarithmicDerivative (factoredFunction m h))
        (reflected (logarithmicDerivative (factoredFunction m h))) s a).ncard ≤ 2 * k) :
    ∃ E : Set ℝ, E.Countable ∧ ∀ r : ℝ, 0 < r → r ∉ E →
      (maximumPoints (factoredFunction m h) r).Finite ∧
      (maximumPoints (factoredFunction m h) r).ncard ≤ 2 * k := by
  let v := factoredLogMaximum m h
  refine ⟨exceptionalRadii v T, exceptionalRadii_countable (factoredLogMaximum_convex m hh h0) hT, ?_⟩
  intro r hr hnot
  have hd := differentiable_off_exceptionalRadii hr hnot
  obtain ⟨hlt, hcommon⟩ := factored_maximum_common_value m hh h0 hnc hd.hasDerivAt
  rw [Real.exp_log hr] at hcommon
  have hs : (((r ^ 2 : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast pow_ne_zero 2 hr.ne'
  have hbound := hglobal _ _ hs hlt (fibre_value_off_exceptionalRadii hr.le hnot _)
  exact maximum_points_bound_of_fiber hcommon hbound.1 hbound.2

end Erdos1117
