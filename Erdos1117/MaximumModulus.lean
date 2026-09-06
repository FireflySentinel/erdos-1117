import Erdos1117.MaximumPoints

open Set Complex Metric Filter Topology

namespace Erdos1117

noncomputable def circleSup (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z => ‖f z‖) '' sphere 0 r)

private theorem circle_compact {f : ℂ → ℂ} (hf : Continuous f) (r : ℝ) :
    IsCompact ((fun z => ‖f z‖) '' sphere 0 r) :=
  (isCompact_sphere 0 r).image hf.norm

private theorem circle_nonempty (r : ℝ) (hr : 0 ≤ r) : (sphere (0 : ℂ) r).Nonempty := by
  refine ⟨(r : ℂ), ?_⟩
  simp [abs_of_nonneg hr]

theorem norm_le_circleSup {f : ℂ → ℂ} (hf : Continuous f) {r : ℝ} {z : ℂ}
    (hz : ‖z‖ = r) : ‖f z‖ ≤ circleSup f r :=
  le_csSup (circle_compact hf r).bddAbove ⟨z, by simpa using hz, rfl⟩

theorem circleSup_attained {f : ℂ → ℂ} (hf : Continuous f) {r : ℝ} (hr : 0 ≤ r) :
    ∃ z : ℂ, ‖z‖ = r ∧ ‖f z‖ = circleSup f r := by
  obtain ⟨z, hz, heq⟩ := (circle_compact hf r).sSup_mem ((circle_nonempty r hr).image _)
  exact ⟨z, by simpa using hz, heq⟩

/-- The maximum principle extends the circle bound to its disc. -/
theorem norm_le_circleSup_of_le {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z‖ ≤ r) : ‖f z‖ ≤ circleSup f r := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball (x := (0 : ℂ)) (r := r)) hf.diffContOnCl
  · intro w hw
    rw [frontier_ball (0 : ℂ) (ne_of_gt hr)] at hw
    exact norm_le_circleSup hf.continuous (by simpa using hw)
  · rw [closure_ball (0 : ℂ) (ne_of_gt hr)]
    simpa using hz

theorem circleSup_pos {h : ℂ → ℂ} (hh : Differentiable ℂ h) (h0 : h 0 ≠ 0)
    {r : ℝ} (hr : 0 < r) : 0 < circleSup h r :=
  (norm_pos_iff.mpr h0).trans_le (norm_le_circleSup_of_le hh hr (by simpa using hr.le))

noncomputable def logMaximum (h : ℂ → ℂ) (x : ℝ) : ℝ :=
  Real.log (circleSup h (Real.exp x))

theorem logMaximum_profile {h : ℂ → ℂ} (hh : Differentiable ℂ h) (h0 : h 0 ≠ 0) :
    LogMaximumProfile h (logMaximum h) := by
  intro x
  have hp := circleSup_pos hh h0 (Real.exp_pos x)
  simp only [logMaximum, Real.exp_log hp]
  exact ⟨fun z hz => norm_le_circleSup hh.continuous hz,
    circleSup_attained hh.continuous (Real.exp_pos x).le⟩

/-- Nonconstant entire functions have strictly increasing maximum modulus. -/
theorem circleSup_strictMono {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (hnc : ¬ ∃ c : ℂ, ∀ z, h z = c) {r s : ℝ} (hr : 0 ≤ r) (hrs : r < s) :
    circleSup h r < circleSup h s := by
  by_contra hnot
  have hle := le_of_not_gt hnot
  obtain ⟨z, hz, hval⟩ := circleSup_attained hh.continuous hr
  have hzs : z ∈ ball (0 : ℂ) s := by simpa [hz] using hrs
  have hmax : IsMaxOn (norm ∘ h) (ball 0 s) z := by
    intro w hw
    have hwr : ‖w‖ < s := by simpa using hw
    exact (norm_le_circleSup_of_le hh (hr.trans_lt hrs) hwr.le).trans (by simpa only [Function.comp_apply, hval] using hle)
  have heq := Complex.eq_const_of_exists_max hh.differentiableOn hzs hmax
  have hevent : h =ᶠ[𝓝 z] (fun _ => h z) :=
    heq.eventuallyEq.filter_mono (le_principal_iff.mpr (isOpen_ball.mem_nhds hzs))
  have hall := (hh.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq analyticOnNhd_const hevent
  apply hnc
  exact ⟨h z, fun w => congrFun hall w⟩

theorem logMaximum_strictMono {h : ℂ → ℂ} (hh : Differentiable ℂ h) (h0 : h 0 ≠ 0)
    (hnc : ¬ ∃ c : ℂ, ∀ z, h z = c) : StrictMono (logMaximum h) := by
  intro x y hxy
  exact Real.log_lt_log (circleSup_pos hh h0 (Real.exp_pos x))
    (circleSup_strictMono hh hnc (Real.exp_pos x).le (Real.exp_lt_exp.mpr hxy))

private theorem profile_convex_inequality {h : ℂ → ℂ} {v : ℝ → ℝ}
    (hh : Differentiable ℂ h) (hv : LogMaximumProfile h v)
    {x y a b : ℝ} (hxy : x < y) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    v (a * x + b * y) ≤ a * v x + b * v y := by
  let t := a * x + b * y
  obtain ⟨z, hz, hval⟩ := (hv t).2
  have hz0 : z ≠ 0 := by
    intro heq
    have := Real.exp_pos t
    simp [heq] at hz
    linarith
  have hlog : (Complex.log z).re = t := by rw [Complex.log_re, hz, Real.log_exp]
  have htx : x ≤ t := by
    dsimp [t]
    rw [show a = 1 - b by linarith]
    nlinarith [mul_pos hb (sub_pos.mpr hxy)]
  have hty : t ≤ y := by
    dsimp [t]
    rw [show b = 1 - a by linarith]
    nlinarith [mul_pos ha (sub_pos.mpr hxy)]
  have hB : BddAbove ((norm ∘ fun w => h (Complex.exp w)) ''
      Complex.HadamardThreeLines.verticalClosedStrip x y) := by
    refine ⟨circleSup h (Real.exp y), ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    apply norm_le_circleSup_of_le hh (Real.exp_pos y)
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr hw.2
  have hleft : ∀ w ∈ Complex.re ⁻¹' {x}, ‖h (Complex.exp w)‖ ≤ Real.exp (v x) := by
    intro w hw
    exact (hv x).1 _ (by rw [Complex.norm_exp]; exact congrArg Real.exp hw)
  have hright : ∀ w ∈ Complex.re ⁻¹' {y}, ‖h (Complex.exp w)‖ ≤ Real.exp (v y) := by
    intro w hw
    exact (hv y).1 _ (by rw [Complex.norm_exp]; exact congrArg Real.exp hw)
  have hbound := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (f := fun w => h (Complex.exp w)) (z := Complex.log z) hxy
    (by change (Complex.log z).re ∈ Icc x y; simpa [hlog] using And.intro htx hty)
    (hh.comp Complex.differentiable_exp).diffContOnCl hB hleft hright
  have hratio : (t - x) / (y - x) = b := by
    apply (div_eq_iff (sub_ne_zero.mpr hxy.ne')).mpr
    dsimp [t]
    rw [show a = 1 - b by linarith]
    ring
  rw [Complex.exp_log hz0, hval, hlog, hratio,
    show 1 - b = a by linarith,
    Real.rpow_def_of_pos (Real.exp_pos _) _, Real.rpow_def_of_pos (Real.exp_pos _) _,
    Real.log_exp, Real.log_exp, ← Real.exp_add] at hbound
  have := Real.exp_le_exp.mp hbound
  simpa [t, mul_comm] using this

/-- Hadamard convexity, obtained from mathlib's three-lines theorem by composing with exp. -/
theorem logMaximum_convex {h : ℂ → ℂ} (hh : Differentiable ℂ h) (h0 : h 0 ≠ 0) :
    ConvexOn ℝ univ (logMaximum h) := by
  rw [convexOn_iff_pairwise_pos]
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy hne a b ha hb hab
  rcases lt_or_gt_of_ne hne with hxy | hyx
  · exact profile_convex_inequality hh (logMaximum_profile hh h0) hxy ha hb hab
  · simpa [add_comm] using profile_convex_inequality hh (logMaximum_profile hh h0)
      hyx hb ha (by linarith : b + a = 1)

/-- The logarithmic maximum slope is strictly positive for a nonconstant entire function. -/
theorem logMaximum_derivative_pos {h : ℂ → ℂ} (hh : Differentiable ℂ h) (h0 : h 0 ≠ 0)
    (hnc : ¬ ∃ c : ℂ, ∀ z, h z = c) {x d : ℝ} (hd : HasDerivAt (logMaximum h) d x) :
    0 < d := by
  have hlt := logMaximum_strictMono hh h0 hnc (show x - 1 < x by linarith)
  have hs := (logMaximum_convex hh h0).slope_le_of_hasDerivAt
    (mem_univ (x - 1)) (mem_univ x) (by linarith) hd
  rw [slope_def_field] at hs
  have hp : 0 < (logMaximum h x - logMaximum h (x - 1)) / (x - (x - 1)) :=
    div_pos (sub_pos.mpr hlt) (by linarith)
  exact hp.trans_le hs

end Erdos1117
