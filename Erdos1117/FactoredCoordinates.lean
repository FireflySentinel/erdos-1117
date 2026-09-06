import Erdos1117.LocalCoordinate
import Erdos1117.FiberApplication

open Set Complex Filter Topology

namespace Erdos1117

/-- The holomorphic value at the origin after removing the zero of order `m`. -/
noncomputable def regularLogarithmicDerivative (m : ℕ) (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  m + logarithmicDerivative h z

@[simp] theorem regularLogarithmicDerivative_zero (m : ℕ) (h : ℂ → ℂ) :
    regularLogarithmicDerivative m h 0 = m := by
  simp [regularLogarithmicDerivative, logarithmicDerivative]

theorem logarithmicDerivative_factored {h : ℂ → ℂ} {z : ℂ} (m : ℕ)
    (hh : DifferentiableAt ℂ h z) (hz : z ≠ 0) (hne : h z ≠ 0) :
    logarithmicDerivative (factoredFunction m h) z = regularLogarithmicDerivative m h z := by
  have hd : HasDerivAt (factoredFunction m h)
      ((m : ℂ) * z ^ (m - 1) * h z + z ^ m * deriv h z) z := by
    convert! ((hasDerivAt_id z).pow m).mul hh.hasDerivAt using 1
    simp
  simp only [logarithmicDerivative, regularLogarithmicDerivative, hd.deriv, factoredFunction]
  cases m with
  | zero => simp
  | succ n =>
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp

/-- The order of `A-m` equals the order of the first nonconstant term of `h`. -/
theorem logarithmicDerivative_order {h : ℂ → ℂ} (hh : AnalyticAt ℂ h 0)
    (h0 : h 0 ≠ 0) :
    analyticOrderAt (logarithmicDerivative h) 0 =
      analyticOrderAt (fun z => h z - h 0) 0 := by
  have hid : AnalyticAt ℂ (id : ℂ → ℂ) 0 := analyticAt_id
  have hi := hh.inv h0
  have he : logarithmicDerivative h = id * deriv h * h⁻¹ := by
    funext z
    simp [logarithmicDerivative, div_eq_mul_inv]
  rw [he, analyticOrderAt_mul (hid.mul hh.deriv) hi,
    analyticOrderAt_mul hid hh.deriv]
  have hu : analyticOrderAt h⁻¹ 0 = 0 :=
    hi.analyticOrderAt_eq_zero.mpr (inv_ne_zero h0)
  rw [hu, add_zero]
  simpa [add_comm] using hh.analyticOrderAt_deriv_add_one

/-- Local power coordinates give the small-fibre estimate for the actual quotient `zf'/f`. -/
theorem small_product_fiber_bound_of_order (m k : ℕ) {h : ℂ → ℂ}
    (hh : Differentiable ℂ h) (h0 : h 0 ≠ 0) (hk : 0 < k)
    (horder : analyticOrderAt (fun z => h z - h 0) 0 = k) :
    ∃ η : ℝ, 0 < η ∧ ∀ s a : ℂ, s ≠ 0 → ‖s‖ < η ^ 2 →
      (productFiber (logarithmicDerivative (factoredFunction m h))
        (reflected (logarithmicDerivative (factoredFunction m h))) s a).encard ≤ 2 * k := by
  have hA : AnalyticAt ℂ (logarithmicDerivative h) 0 :=
    (analyticAt_id.mul (hh.analyticAt 0).deriv).div (hh.analyticAt 0) h0
  obtain ⟨χ, _, _, _, ε, hε, hχ, hcoord⟩ := exists_local_coordinate hA hk
    ((logarithmicDerivative_order (hh.analyticAt 0) h0).trans horder)
  obtain ⟨δ, hδ, hnz⟩ := Metric.eventually_nhds_iff.mp ((hh 0).continuousAt.eventually_ne h0)
  let η := min ε δ
  have hη : 0 < η := lt_min hε hδ
  have heq (z : ℂ) (hz : 0 < ‖z‖ ∧ ‖z‖ < η) :
      logarithmicDerivative (factoredFunction m h) z - m = χ z ^ k := by
    have hzε : z ∈ Metric.ball 0 ε := by simpa using hz.2.trans_le (min_le_left ε δ)
    have hzδ : dist z 0 < δ := by simpa using hz.2.trans_le (min_le_right ε δ)
    rw [logarithmicDerivative_factored m (hh z) (norm_pos_iff.mp hz.1) (hnz hzδ)]
    simpa [regularLogarithmicDerivative] using hcoord z hzε
  have hinj : InjOn χ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < η} := by
    apply hχ.mono
    intro z hz
    simpa using hz.2.trans_le (min_le_left ε δ)
  refine ⟨η, hη, ?_⟩
  intro s a hs hsmall
  apply Set.encard_le_coe_iff_finite_ncard_le.mpr
  apply small_product_fiber_bound_of_coordinates (m := (m : ℂ)) hk hη hs hsmall
    hinj (χ := χ) (ψ := reflected χ)
  · intro z hz w hw he
    have hz' : 0 < ‖starRingEnd ℂ z‖ ∧ ‖starRingEnd ℂ z‖ < η := by simpa using hz
    have hw' : 0 < ‖starRingEnd ℂ w‖ ∧ ‖starRingEnd ℂ w‖ < η := by simpa using hw
    exact (starRingEnd ℂ).injective (hinj hz' hw' ((starRingEnd ℂ).injective he))
  · exact heq
  · intro z hz
    have hz' : 0 < ‖starRingEnd ℂ z‖ ∧ ‖starRingEnd ℂ z‖ < η := by simpa using hz
    simpa [reflected] using congrArg (starRingEnd ℂ) (heq _ hz')

end Erdos1117
