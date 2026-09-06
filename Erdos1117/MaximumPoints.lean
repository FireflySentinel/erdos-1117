import Erdos1117.Derivatives
import Erdos1117.Convexity

open Set Complex Filter Topology

namespace Erdos1117

/-- Maximum points on the circle of radius `r`. -/
def maximumPoints (f : ℂ → ℂ) (r : ℝ) : Set ℂ :=
  {z | ‖z‖ = r ∧ ∀ w : ℂ, ‖w‖ = r → ‖f w‖ ≤ ‖f z‖}

/-- `v(t)` is the logarithm of the actual maximum modulus on radius `exp t`. -/
def LogMaximumProfile (f : ℂ → ℂ) (v : ℝ → ℝ) : Prop :=
  ∀ t, (∀ z : ℂ, ‖z‖ = Real.exp t → ‖f z‖ ≤ Real.exp (v t)) ∧
    ∃ z : ℂ, ‖z‖ = Real.exp t ∧ ‖f z‖ = Real.exp (v t)

theorem maximum_point_value {f : ℂ → ℂ} {v : ℝ → ℝ} {x : ℝ} {z : ℂ}
    (hv : LogMaximumProfile f v) (hz : z ∈ maximumPoints f (Real.exp x)) :
    ‖f z‖ = Real.exp (v x) := by
  obtain ⟨w, hw, heq⟩ := (hv x).2
  exact le_antisymm ((hv x).1 z hz.1) (heq ▸ hz.2 w hw)

/-- At every maximum point the angular derivative vanishes. -/
theorem maximum_point_im_zero {f : ℂ → ℂ} {r : ℝ} {z : ℂ}
    (hz : z ∈ maximumPoints f r) (hf : DifferentiableAt ℂ f z) (hne : f z ≠ 0) :
    (logarithmicDerivative f z).im = 0 := by
  have hd := angular_derivative hf hne
  have hc : ContinuousAt (fun t : ℝ => f (z * Complex.exp (t * I))) 0 := by
    exact (show ContinuousAt f _ from by simpa using hf.continuousAt).comp (by fun_prop)
  have hne' : f (z * Complex.exp ((0 : ℝ) * I)) ≠ 0 := by simpa using hne
  have hmax : IsLocalMax (fun t : ℝ => Real.log ‖f (z * Complex.exp (t * I))‖) 0 := by
    filter_upwards [hc.eventually_ne hne'] with t ht
    have hnorm : ‖z * Complex.exp (t * I)‖ = r := by simp [Complex.norm_exp, hz.1]
    have hb := hz.2 _ hnorm
    simpa using Real.log_le_log (norm_pos_iff.mpr ht) hb
  have h := hmax.hasDerivAt_eq_zero hd
  linarith

/-- Every maximum point on one differentiability circle has the same real value of `A`. -/
theorem maximum_point_common_value {f : ℂ → ℂ} {v : ℝ → ℝ} {x lam : ℝ} {z : ℂ}
    (hv : LogMaximumProfile f v) (hd : HasDerivAt v lam x)
    (hf : DifferentiableAt ℂ f z) (hz : z ∈ maximumPoints f (Real.exp x)) :
    logarithmicDerivative f z = (lam : ℂ) := by
  have hval := maximum_point_value hv hz
  have hne : f z ≠ 0 := by
    intro h
    exact (Real.exp_ne_zero (v x)) (by simpa [h] using hval.symm)
  have him := maximum_point_im_zero hz hf hne
  have hr := radial_derivative hf hne
  have hc : ContinuousAt (fun t : ℝ => f (Complex.exp t * z)) 0 := by
    exact (show ContinuousAt f _ from by simpa using hf.continuousAt).comp (by fun_prop)
  have hne' : f (Complex.exp (0 : ℝ) * z) ≠ 0 := by simpa using hne
  have hle : ∀ᶠ (t : ℝ) in 𝓝 (0 : ℝ), Real.log ‖f (Complex.exp t * z)‖ ≤ v (x + t) := by
    filter_upwards [hc.eventually_ne hne'] with t ht
    have hnorm : ‖Complex.exp t * z‖ = Real.exp (x + t) := by
      simp [Complex.norm_exp, hz.1, Real.exp_add, mul_comm]
    have hb := (hv (x + t)).1 _ hnorm
    simpa using Real.log_le_log (norm_pos_iff.mpr ht) hb
  have hv' : HasDerivAt (fun t => v (x + t)) lam 0 := by
    convert! (show HasDerivAt v lam _ from by simpa using hd).comp 0 ((hasDerivAt_id (0 : ℝ)).const_add x) using 1
    simp
  have heq : Real.log ‖f (Complex.exp (0 : ℝ) * z)‖ = v (x + 0) := by simp [hval]
  have hre := derivative_at_contact hr hv' hle heq
  exact Complex.ext (by simpa using hre) (by simpa using him)

end Erdos1117
