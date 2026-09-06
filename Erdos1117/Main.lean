import Erdos1117.FiberApplication
import Erdos1117.EntireFactor

open Set Filter Topology

namespace Erdos1117

/-- Theorem 1.1 for `f = z^m h`, conditional on `GlobalFibreBound`. -/
theorem theorem_1_1_of_global (m k : ℕ) {h : ℂ → ℂ}
    (hh : Differentiable ℂ h) (h0 : h 0 ≠ 0) (hnc : ¬ ∃ c : ℂ, ∀ z, h z = c)
    (hg : GlobalFibreBound m k h) :
    (∃ E : Set ℝ, E.Countable ∧ E ⊆ Ioi 0 ∧ ∀ r : ℝ, 0 < r → r ∉ E →
      (maximumPoints (factoredFunction m h) r).encard ≤ 2 * k) ∧
    ∃ᶠ r in atTop, (maximumPoints (factoredFunction m h) r).encard ≤ 2 * k := by
  have hb := maximum_bound_off_countable_of_global_fiber_bound m k hh h0 hnc hg
  refine ⟨hb, ?_⟩
  obtain ⟨E, hE, _, hbound⟩ := hb
  exact frequently_bounded_of_countable_exceptions hE hbound

/-- The original entire-function formulation, with the zero order and Taylor gap
extracted from `f`; the global fibre estimate is the remaining hypothesis. -/
theorem theorem_1_1_of_entire (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hne : f ≠ 0)
    (hnm : ¬ ∃ (c : ℂ) (m : ℕ), ∀ z, f z = c * z ^ m)
    (hg : GlobalFibreBound (analyticOrderNatAt f 0) (firstGap f hf hne)
      (entireFactor f hf hne)) :
    0 < firstGap f hf hne ∧
    (∃ E : Set ℝ, E.Countable ∧ E ⊆ Ioi 0 ∧ ∀ r : ℝ, 0 < r → r ∉ E →
      (maximumPoints f r).encard ≤ 2 * firstGap f hf hne) ∧
    ∃ᶠ r in atTop, (maximumPoints f r).encard ≤ 2 * firstGap f hf hne := by
  obtain ⟨hh, h0, heq⟩ := entireFactor_spec hf hne
  have hb := theorem_1_1_of_global (analyticOrderNatAt f 0) (firstGap f hf hne)
    hh h0 (entireFactor_nonconstant hf hne hnm) hg
  rw [← heq] at hb
  exact ⟨firstGap_pos hf hne hnm, hb⟩

end Erdos1117
