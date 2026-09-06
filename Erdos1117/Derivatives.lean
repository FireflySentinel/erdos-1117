import Mathlib

open Complex Filter Topology

namespace Erdos1117

/-- The quotient `zf'/f`, used at points where `f z ≠ 0`. -/
noncomputable def logarithmicDerivative (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * deriv f z / f z

/-- The real derivative of log modulus along a complex-valued path. -/
theorem hasDerivAt_log_norm {g : ℝ → ℂ} {g' : ℂ} {t : ℝ}
    (hg : HasDerivAt g g' t) (hne : g t ≠ 0) :
    HasDerivAt (fun s => Real.log ‖g s‖) (g' / g t).re t := by
  have h := (hg.norm_sq.log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))).div_const 2
  convert! h using 1
  · ext s
    simp [Real.log_pow]
  · rw [Complex.inner, Complex.div_re, Complex.normSq_eq_norm_sq]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring

/-- Rotation through a fixed point has logarithmic-modulus derivative `-Im A`. -/
theorem angular_derivative {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hne : f z ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log ‖f (z * Complex.exp (t * I))‖)
      (-(logarithmicDerivative f z).im) 0 := by
  have hp : HasDerivAt (fun t : ℝ => z * Complex.exp (t * I)) (z * I) 0 := by
    convert! (((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const I).cexp.const_mul z) using 1
    simp
  have h := hasDerivAt_log_norm ((show HasDerivAt f (deriv f z) _ from by simpa using hf.hasDerivAt).comp 0 hp) (by simpa using hne)
  convert! h using 1
  simp only [Function.comp_apply, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  change -(z * deriv f z / f z).im = (deriv f z * (z * I) / f z).re
  rw [show deriv f z * (z * I) / f z = (z * deriv f z / f z) * I by ring]
  simp

/-- Logarithmic radial displacement has logarithmic-modulus derivative `Re A`. -/
theorem radial_derivative {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hne : f z ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log ‖f (Complex.exp t * z)‖)
      (logarithmicDerivative f z).re 0 := by
  have hp : HasDerivAt (fun t : ℝ => Complex.exp t * z) z 0 := by
    simpa using (Complex.hasDerivAt_exp (0 : ℂ)).comp_ofReal.mul_const z
  have h := hasDerivAt_log_norm ((show HasDerivAt f (deriv f z) _ from by simpa using hf.hasDerivAt).comp 0 hp) (by simpa using hne)
  convert! h using 1
  simp only [Function.comp_apply, Complex.ofReal_zero, Complex.exp_zero, one_mul]
  congr 1
  dsimp [logarithmicDerivative]
  ring

/-- Two differentiable real functions that touch have the same derivative. -/
theorem derivative_at_contact {u v : ℝ → ℝ} {a b x : ℝ}
    (hu : HasDerivAt u a x) (hv : HasDerivAt v b x)
    (hle : ∀ᶠ t in 𝓝 x, u t ≤ v t) (heq : u x = v x) : a = b := by
  have hmin : IsLocalMin (fun t => v t - u t) x := by
    filter_upwards [hle] with t ht
    change v x - u x ≤ v t - u t
    rw [heq, sub_self]
    exact sub_nonneg.mpr ht
  have hz := hmin.hasDerivAt_eq_zero (hv.sub hu)
  linarith

end Erdos1117
