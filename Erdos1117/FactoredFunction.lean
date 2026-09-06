import Erdos1117.MaximumModulus
import Erdos1117.Convexity

open Set Complex Filter Topology

namespace Erdos1117

noncomputable def factoredFunction (m : ℕ) (h : ℂ → ℂ) (z : ℂ) : ℂ := z ^ m * h z

noncomputable def factoredLogMaximum (m : ℕ) (h : ℂ → ℂ) (x : ℝ) : ℝ :=
  m * x + logMaximum h x

theorem factored_entire (m : ℕ) {h : ℂ → ℂ} (hh : Differentiable ℂ h) :
    Differentiable ℂ (factoredFunction m h) := by
  unfold factoredFunction
  fun_prop

theorem factored_profile (m : ℕ) {h : ℂ → ℂ} (hh : Differentiable ℂ h) (h0 : h 0 ≠ 0) :
    LogMaximumProfile (factoredFunction m h) (factoredLogMaximum m h) := by
  intro x
  have hv := logMaximum_profile hh h0
  have he : Real.exp (factoredLogMaximum m h x) = (Real.exp x) ^ m * Real.exp (logMaximum h x) := by
    simp [factoredLogMaximum, Real.exp_add, Real.exp_nat_mul]
  constructor
  · intro z hz
    rw [factoredFunction, norm_mul, norm_pow, hz, he]
    exact mul_le_mul_of_nonneg_left ((hv x).1 z hz) (pow_nonneg (Real.exp_pos x).le m)
  · obtain ⟨z, hz, hval⟩ := (hv x).2
    refine ⟨z, hz, ?_⟩
    rw [factoredFunction, norm_mul, norm_pow, hz, hval, he]

theorem factoredLogMaximum_convex (m : ℕ) {h : ℂ → ℂ}
    (hh : Differentiable ℂ h) (h0 : h 0 ≠ 0) :
    ConvexOn ℝ univ (factoredLogMaximum m h) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hc := (logMaximum_convex hh h0).2 hx hy ha hb hab
  simp only [smul_eq_mul] at hc ⊢
  dsimp [factoredLogMaximum]
  calc
    _ ≤ (m : ℝ) * (a * x + b * y) + (a * logMaximum h x + b * logMaximum h y) :=
      add_le_add le_rfl hc
    _ = _ := by ring

/-- All maximum points share a real logarithmic derivative strictly greater than the zero order. -/
theorem factored_maximum_common_value (m : ℕ) {h : ℂ → ℂ}
    (hh : Differentiable ℂ h) (h0 : h 0 ≠ 0) (hnc : ¬ ∃ c : ℂ, ∀ z, h z = c)
    {x lam : ℝ} (hd : HasDerivAt (factoredLogMaximum m h) lam x) :
    (m : ℝ) < lam ∧ ∀ z ∈ maximumPoints (factoredFunction m h) (Real.exp x),
      logarithmicDerivative (factoredFunction m h) z = (lam : ℂ) := by
  have hb : HasDerivAt (logMaximum h) (lam - m) x := by
    convert! hd.sub ((hasDerivAt_id x).const_mul (m : ℝ)) using 1
    · ext t; simp [factoredLogMaximum]
    · simp
  have hp := logMaximum_derivative_pos hh h0 hnc hb
  refine ⟨by linarith, fun z hz => ?_⟩
  exact maximum_point_common_value (factored_profile m hh h0) hd (factored_entire m hh z) hz

/-- The local conclusion of §5, for the actual entire function `z^m h(z)`. -/
theorem maximum_points_common_value_off_countable (m : ℕ) {h : ℂ → ℂ}
    (hh : Differentiable ℂ h) (h0 : h 0 ≠ 0) (hnc : ¬ ∃ c : ℂ, ∀ z, h z = c) :
    ∃ E : Set ℝ, E.Countable ∧ ∀ r : ℝ, 0 < r → r ∉ E →
      ∃ lam : ℝ, (m : ℝ) < lam ∧
        ∀ z ∈ maximumPoints (factoredFunction m h) r,
          logarithmicDerivative (factoredFunction m h) z = (lam : ℂ) := by
  let v := factoredLogMaximum m h
  let E := Real.exp '' {x | ¬ DifferentiableAt ℝ v x}
  refine ⟨E, (convex_countable_nondifferentiable (factoredLogMaximum_convex m hh h0)).image _, ?_⟩
  intro r hr hnot
  have hd : DifferentiableAt ℝ v (Real.log r) := by
    by_contra he
    exact hnot ⟨Real.log r, he, Real.exp_log hr⟩
  have hc := factored_maximum_common_value m hh h0 hnc hd.hasDerivAt
  rw [Real.exp_log hr] at hc
  exact ⟨deriv v (Real.log r), hc⟩

end Erdos1117
