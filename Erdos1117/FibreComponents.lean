import Erdos1117.FactoredCoordinates
import Erdos1117.Main

/-! Propagation of the total fibre bound along connected components.
The two hypotheses below are consequences required from the manuscript's global
analytic argument. They are not statements of Remmert's or Gross's theorem. -/

open Set Complex Filter Topology

namespace Erdos1117

/-- Nonempty fibres with nonzero product and common value different from `0` and `m`.
Excluding zero also excludes values introduced by totalized division at poles. -/
def fibreImage (A B : ℂ → ℂ) (m : ℂ) : Set (ℂ × ℂ) :=
  {y | y.1 ≠ 0 ∧ y.2 ≠ m ∧ y.2 ≠ 0 ∧ (productFiber A B y.1 y.2).Nonempty}

/-- Constancy concerns the whole fibre, including all source components. -/
def FibreDegreeConstancy (A B : ℂ → ℂ) (m : ℂ) (T : Set (ℂ × ℂ)) : Prop :=
  IsLocallyConstant (fun y : ↥(fibreImage A B m \ T) => (productFiber A B y.1.1 y.1.2).encard)

/-- Every regular image component reaches arbitrarily small nonzero products.
This is the remaining small-product/normalization conclusion, not a cited theorem. -/
def SmallProductsOnComponents (A B : ℂ → ℂ) (m : ℂ) (T : Set (ℂ × ℂ)) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ x : ↥(fibreImage A B m \ T),
    ∃ y ∈ connectedComponent x, ‖y.1.1‖ < η ^ 2

/-- The local bound controls total fibres throughout the regular image. -/
theorem fibre_bound_of_component_data {A B : ℂ → ℂ} {m : ℂ} {T : Set (ℂ × ℂ)}
    {η : ℝ} {k : ℕ} (hη : 0 < η)
    (hlocal : ∀ s a : ℂ, s ≠ 0 → ‖s‖ < η ^ 2 → (productFiber A B s a).encard ≤ 2 * k)
    (hdegree : FibreDegreeConstancy A B m T)
    (hsmall : SmallProductsOnComponents A B m T)
    (x : ↥(fibreImage A B m \ T)) : (productFiber A B x.1.1 x.1.2).encard ≤ 2 * k := by
  obtain ⟨y, hy, hys⟩ := hsmall η hη x
  have he := hdegree.apply_eq_of_isPreconnected
    isConnected_connectedComponent.isPreconnected mem_connectedComponent hy
  exact he ▸ hlocal y.1.1 y.1.2 y.2.1.1 hys

/-- Projecting the exceptional values yields a countable set of positive radii. -/
theorem globalFibreBound_of_component_data (m k : ℕ) {h : ℂ → ℂ}
    (hh : Differentiable ℂ h) (h0 : h 0 ≠ 0) (hk : 0 < k)
    (horder : analyticOrderAt (fun z => h z - h 0) 0 = k)
    (T : Set (ℂ × ℂ)) (hT : T.Countable)
    (hdegree : FibreDegreeConstancy (logarithmicDerivative (factoredFunction m h))
      (reflected (logarithmicDerivative (factoredFunction m h))) m T)
    (hsmall : SmallProductsOnComponents (logarithmicDerivative (factoredFunction m h))
      (reflected (logarithmicDerivative (factoredFunction m h))) m T) :
    GlobalFibreBound m k h := by
  obtain ⟨η, hη, hlocal⟩ := small_product_fiber_bound_of_order m k hh h0 hk horder
  let S := (fun y : ℂ × ℂ => Real.sqrt ‖y.1‖) '' T
  refine ⟨S ∩ Ioi 0, (hT.image _).mono inter_subset_left, inter_subset_right, ?_⟩
  intro r hr hnot a ha
  have hr2 : ((r ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_ne_zero 2 hr.ne')
  have ham : (a : ℂ) ≠ m := by exact_mod_cast (ne_of_gt ha)
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_le_of_lt (Nat.cast_nonneg m) ha))
  have hnT : (((r ^ 2 : ℝ) : ℂ), (a : ℂ)) ∉ T := by
    intro ht
    apply hnot
    refine ⟨?_, hr⟩
    refine ⟨(((r ^ 2 : ℝ) : ℂ), (a : ℂ)), ht, ?_⟩
    simp [Complex.norm_real, abs_of_pos hr, Real.sqrt_sq_eq_abs]
  by_cases hne : (productFiber (logarithmicDerivative (factoredFunction m h))
      (reflected (logarithmicDerivative (factoredFunction m h))) ((r ^ 2 : ℝ) : ℂ) a).Nonempty
  · exact fibre_bound_of_component_data hη hlocal hdegree hsmall
      ⟨(((r ^ 2 : ℝ) : ℂ), (a : ℂ)), ⟨⟨hr2, ham, ha0, hne⟩, hnT⟩⟩
  · rw [not_nonempty_iff_eq_empty.mp hne]
    simp

/-- Theorem 1.1 with the two remaining analytic conclusions separated. -/
theorem theorem_1_1_of_component_data (m k : ℕ) {h : ℂ → ℂ}
    (hh : Differentiable ℂ h) (h0 : h 0 ≠ 0) (hnc : ¬ ∃ c : ℂ, ∀ z, h z = c)
    (hk : 0 < k) (horder : analyticOrderAt (fun z => h z - h 0) 0 = k)
    (T : Set (ℂ × ℂ)) (hT : T.Countable)
    (hdegree : FibreDegreeConstancy (logarithmicDerivative (factoredFunction m h))
      (reflected (logarithmicDerivative (factoredFunction m h))) m T)
    (hsmall : SmallProductsOnComponents (logarithmicDerivative (factoredFunction m h))
      (reflected (logarithmicDerivative (factoredFunction m h))) m T) :
    (∃ E : Set ℝ, E.Countable ∧ E ⊆ Ioi 0 ∧ ∀ r : ℝ, 0 < r → r ∉ E →
      (maximumPoints (factoredFunction m h) r).encard ≤ 2 * k) ∧
    ∃ᶠ r in atTop, (maximumPoints (factoredFunction m h) r).encard ≤ 2 * k :=
  theorem_1_1_of_global m k hh h0 hnc
    (globalFibreBound_of_component_data m k hh h0 hk horder T hT hdegree hsmall)

/-- The entire-function entry point with the two component hypotheses. -/
theorem theorem_1_1_of_entire_component_data (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hne : f ≠ 0)
    (hnm : ¬ ∃ (c : ℂ) (m : ℕ), ∀ z, f z = c * z ^ m)
    (T : Set (ℂ × ℂ)) (hT : T.Countable)
    (hdegree : FibreDegreeConstancy (logarithmicDerivative f)
      (reflected (logarithmicDerivative f)) (analyticOrderNatAt f 0) T)
    (hsmall : SmallProductsOnComponents (logarithmicDerivative f)
      (reflected (logarithmicDerivative f)) (analyticOrderNatAt f 0) T) :
    0 < firstGap f hf hne ∧
    (∃ E : Set ℝ, E.Countable ∧ E ⊆ Ioi 0 ∧ ∀ r : ℝ, 0 < r → r ∉ E →
      (maximumPoints f r).encard ≤ 2 * firstGap f hf hne) ∧
    ∃ᶠ r in atTop, (maximumPoints f r).encard ≤ 2 * firstGap f hf hne := by
  obtain ⟨hh, h0, heq⟩ := entireFactor_spec hf hne
  have hk := firstGap_pos hf hne hnm
  have hb := theorem_1_1_of_component_data (analyticOrderNatAt f 0) (firstGap f hf hne)
    hh h0 (entireFactor_nonconstant hf hne hnm) hk (firstGap_order hf hne hnm) T hT
    (by simpa only [← heq] using hdegree) (by simpa only [← heq] using hsmall)
  rw [← heq] at hb
  exact ⟨hk, hb⟩

end Erdos1117
