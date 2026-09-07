import Erdos1117

/-! Conditional bridge to the Formal Conjectures statement of Problem 1117.
The two analytic claims are parameters, and refer to the same exceptional set. -/

open Set Complex Filter Topology

namespace Erdos1117

/-- A function which is not a constant multiple of a nonnegative integer power. -/
def IsNonMonomial (f : ℂ → ℂ) : Prop :=
  ¬ ∃ (c : ℂ) (m : ℕ), ∀ z, f z = c * z ^ m

/-- The number of maximum modulus points on the circle of radius `r`. -/
noncomputable def maximumCount (f : ℂ → ℂ) (r : ℝ) : ℕ∞ :=
  {z : ℂ | ‖z‖ = r ∧ ∀ w : ℂ, ‖w‖ = r → ‖f w‖ ≤ ‖f z‖}.encard

/-- The product/common-value fibre for the actual logarithmic derivative. -/
def commonValueFibre (f : ℂ → ℂ) (s a : ℂ) : Set (ℂ × ℂ) :=
  {p | p.1 * p.2 = s ∧ p.1 * deriv f p.1 / f p.1 = a ∧
    starRingEnd ℂ ((starRingEnd ℂ p.2) * deriv f (starRingEnd ℂ p.2) /
      f (starRingEnd ℂ p.2)) = a}

/-- Image values relevant to the maximum modulus argument. -/
def commonValueImage (f : ℂ → ℂ) : Set (ℂ × ℂ) :=
  {y | y.1 ≠ 0 ∧ y.2 ≠ (analyticOrderNatAt f 0 : ℂ) ∧ y.2 ≠ 0 ∧
    (commonValueFibre f y.1 y.2).Nonempty}

/-- Local finiteness relative to the image, rather than at the excluded base values. -/
def LocallyFiniteExceptions (f : ℂ → ℂ) (T : Set (ℂ × ℂ)) : Prop :=
  ∀ y ∈ commonValueImage f, ∃ U ∈ 𝓝 y, (T ∩ U).Finite

theorem erdos_1117.variants.countable_exceptions
    (hdegree : ∀ f : ℂ → ℂ, Differentiable ℂ f → IsNonMonomial f →
      ∃ T : Set (ℂ × ℂ), T.Countable ∧ LocallyFiniteExceptions f T ∧
        IsLocallyConstant (fun y : ↥(commonValueImage f \ T) =>
          (commonValueFibre f y.1.1 y.1.2).encard))
    (hsmall : ∀ f : ℂ → ℂ, Differentiable ℂ f → IsNonMonomial f →
      ∀ T : Set (ℂ × ℂ), T.Countable → LocallyFiniteExceptions f T →
        IsLocallyConstant (fun y : ↥(commonValueImage f \ T) =>
          (commonValueFibre f y.1.1 y.1.2).encard) →
        ∀ η : ℝ, 0 < η → ∀ x : ↥(commonValueImage f \ T),
          ∃ y ∈ connectedComponent x, ‖y.1.1‖ < η ^ 2) :
    ∀ f : ℂ → ℂ, Differentiable ℂ f → IsNonMonomial f →
      ∃ k : ℕ, 0 < k ∧ ∃ E : Set ℝ, E.Countable ∧ E ⊆ Ioi 0 ∧
        ∀ r : ℝ, 0 < r → r ∉ E → maximumCount f r ≤ 2 * k := by
  intro f hf hnm
  have hne : f ≠ 0 := by
    rintro rfl
    exact hnm ⟨0, 0, by simp⟩
  obtain ⟨T, hT, hloc, hd⟩ := hdegree f hf hnm
  have hs := hsmall f hf hnm T hT hloc hd
  obtain ⟨hk, hb, _⟩ := theorem_1_1_of_entire_component_data f hf hne hnm T hT hd hs
  exact ⟨firstGap f hf hne, hk, hb⟩

/-- The two named analytic claims imply the negative answer to the second question. -/
theorem erdos_1117.parts.ii
    (hdegree : ∀ f : ℂ → ℂ, Differentiable ℂ f → IsNonMonomial f →
      ∃ T : Set (ℂ × ℂ), T.Countable ∧ LocallyFiniteExceptions f T ∧
        IsLocallyConstant (fun y : ↥(commonValueImage f \ T) =>
          (commonValueFibre f y.1.1 y.1.2).encard))
    (hsmall : ∀ f : ℂ → ℂ, Differentiable ℂ f → IsNonMonomial f →
      ∀ T : Set (ℂ × ℂ), T.Countable → LocallyFiniteExceptions f T →
        IsLocallyConstant (fun y : ↥(commonValueImage f \ T) =>
          (commonValueFibre f y.1.1 y.1.2).encard) →
        ∀ η : ℝ, 0 < η → ∀ x : ↥(commonValueImage f \ T),
          ∃ y ∈ connectedComponent x, ‖y.1.1‖ < η ^ 2) :
    False ↔ ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ IsNonMonomial f ∧
      ∀ N : ℕ, ∀ᶠ r : ℝ in atTop, (N : ℕ∞) ≤ maximumCount f r := by
  refine ⟨False.elim, ?_⟩
  rintro ⟨f, hf, hnm, hdiv⟩
  obtain ⟨k, _, E, hE, _, hbound⟩ := erdos_1117.variants.countable_exceptions hdegree hsmall f hf hnm
  have hfreq := frequently_bounded_of_countable_exceptions hE hbound
  obtain ⟨r, hr, hlarge⟩ := (hfreq.and_eventually (hdiv (2 * k + 1))).exists
  have h := hlarge.trans hr
  norm_cast at h
  omega

/-- info: 'Erdos1117.erdos_1117.parts.ii' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Erdos1117.erdos_1117.parts.ii

/-- info: 'Erdos1117.erdos_1117.variants.countable_exceptions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Erdos1117.erdos_1117.variants.countable_exceptions

end Erdos1117
