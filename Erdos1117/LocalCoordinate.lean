import Erdos1117.LocalRoots

open Set Complex Filter Topology

namespace Erdos1117

/-- A zero of finite positive order admits an injective power coordinate. -/
theorem exists_local_coordinate {F : ℂ → ℂ} {k : ℕ} (hF : AnalyticAt ℂ F 0)
    (hk : 0 < k) (horder : analyticOrderAt F 0 = k) :
    ∃ χ : ℂ → ℂ, AnalyticAt ℂ χ 0 ∧ χ 0 = 0 ∧ deriv χ 0 ≠ 0 ∧
      ∃ η : ℝ, 0 < η ∧ InjOn χ (Metric.ball 0 η) ∧
        ∀ z ∈ Metric.ball 0 η, F z = χ z ^ k := by
  obtain ⟨g, hg, hg0, heq⟩ := hF.analyticOrderAt_eq_natCast.mp horder
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  let b := Complex.exp (Complex.log (g 0) / k)
  let u := fun z => b * Complex.exp (Complex.log (g z / g 0) / k)
  let χ := fun z => z * u z
  have hu : AnalyticAt ℂ u 0 := by
    apply analyticAt_const.mul
    apply AnalyticAt.cexp
    apply AnalyticAt.div_const
    apply AnalyticAt.clog hg.div_const
    simp [hg0]
  have hχ : AnalyticAt ℂ χ 0 := analyticAt_id.mul hu
  have hu0 : u 0 = b := by simp [u, hg0]
  have hb0 : b ≠ 0 := Complex.exp_ne_zero _
  have hd : HasDerivAt χ b 0 := by
    convert! (hasDerivAt_id (0 : ℂ)).mul hu.differentiableAt.hasDerivAt using 1
    simp [hu0]
  have hroot : ∀ᶠ z in 𝓝 (0 : ℂ), F z = χ z ^ k := by
    filter_upwards [heq, hg.continuousAt.eventually_ne hg0] with z hz hgz
    have hb : b ^ k = g 0 := by
      change (Complex.exp (Complex.log (g 0) / k)) ^ k = g 0
      rw [← Complex.exp_nat_mul, mul_div_cancel₀ _ hk0, Complex.exp_log hg0]
    have hzroot : (Complex.exp (Complex.log (g z / g 0) / k)) ^ k = g z / g 0 := by
      rw [← Complex.exp_nat_mul, mul_div_cancel₀ _ hk0,
        Complex.exp_log (div_ne_zero hgz hg0)]
    simpa [χ, u, mul_pow, hb, hzroot, hg0, mul_div_cancel₀] using hz
  have hinv := (hd.deriv ▸ hχ.hasStrictDerivAt).eventually_left_inverse hb0
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp (hroot.and hinv)
  refine ⟨χ, hχ, by simp [χ], hd.deriv.symm ▸ hb0, η, hη, ?_, ?_⟩
  · intro z hz w hw he
    have hz' := (hball hz).2
    have hw' := (hball hw).2
    rw [he] at hz'
    exact hz'.symm.trans hw'
  · intro z hz
    exact (hball hz).1

end Erdos1117
