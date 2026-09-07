import Erdos1117.ProperCorrespondence
import Erdos1117.FactoredCoordinates

/-! Finite fibres for the actual logarithmic derivative, without choosing a
global coprime numerator-denominator representation. -/

open Set Complex

namespace Erdos1117

/-- Every relevant fibre of the actual product/common-value map is finite.
The equations with numerator `m h + z h'` contain this fibre even at common zeros
of numerator and denominator, so no global cancellation theorem is needed. -/
theorem factored_productFiber_finite (m : ℕ) {h : ℂ → ℂ}
    (hh : Differentiable ℂ h) (h0 : h 0 ≠ 0) {s a : ℂ}
    (hs : s ≠ 0) (ha : a ≠ m) (ha0 : a ≠ 0) :
    (productFiber (logarithmicDerivative (factoredFunction m h))
      (reflected (logarithmicDerivative (factoredFunction m h))) s a).Finite := by
  let p : ℂ → ℂ := fun z => m * h z + z * deriv h z
  let P : ℂ → ℂ := fun w => starRingEnd ℂ (p (starRingEnd ℂ w))
  let Q : ℂ → ℂ := fun w => starRingEnd ℂ (h (starRingEnd ℂ w))
  have hp : Differentiable ℂ p := (hh.const_mul _).add (differentiable_id.mul hh.deriv)
  have hP : Continuous P := continuous_star.comp (hp.continuous.comp continuous_star)
  have hQ : Continuous Q := continuous_star.comp (hh.continuous.comp continuous_star)
  have hQ0 : Q 0 ≠ 0 := by simpa [Q] using h0
  have hp0 : p 0 = (m : ℂ) * h 0 := by simp [p]
  have hP0 : P 0 = (m : ℂ) * Q 0 := by simp [P, Q, hp0]
  have hf := correspondence_fiber_finite hp hh hP hQ h0 hQ0 hp0 hP0 hs ha
  have heq (z b : ℂ) (hz : z ≠ 0) (hb : b ≠ 0)
      (hv : logarithmicDerivative (factoredFunction m h) z = b) : p z = b * h z := by
    have hn : h z ≠ 0 := by
      intro hn
      apply hb
      simpa [logarithmicDerivative, factoredFunction, hn] using hv.symm
    rw [logarithmicDerivative_factored m (hh z) hz hn] at hv
    dsimp [regularLogarithmicDerivative, logarithmicDerivative] at hv
    dsimp [p]
    calc
      (m : ℂ) * h z + z * deriv h z = ((m : ℂ) + z * deriv h z / h z) * h z := by
        field_simp
      _ = b * h z := by rw [hv]
  apply (hf.image (fun x : ℂ × ℂ × ℂ => (x.1, x.2.1))).subset
  intro x hx
  have hz : x.1 ≠ 0 := by intro h; apply hs; simpa [h] using hx.1.symm
  have hw : x.2 ≠ 0 := by intro h; apply hs; simpa [h] using hx.1.symm
  have hv : logarithmicDerivative (factoredFunction m h) (starRingEnd ℂ x.2) =
      starRingEnd ℂ a := by
    simpa [reflected] using congrArg (starRingEnd ℂ) hx.2.2
  have he := heq (starRingEnd ℂ x.2) (starRingEnd ℂ a)
    (by simpa using hw) (by simpa using ha0) hv
  refine ⟨(x.1, x.2, a), ⟨?_, heq x.1 a hz ha0 hx.2.1, ?_⟩, rfl⟩
  · simpa using hx.1
  · simpa [P, Q] using congrArg (starRingEnd ℂ) he

end Erdos1117
