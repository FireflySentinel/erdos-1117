import Erdos1117.LocalRoots

open Set

namespace Erdos1117

def productFiber (A B : ℂ → ℂ) (s a : ℂ) : Set (ℂ × ℂ) :=
  {p | p.1 * p.2 = s ∧ A p.1 = a ∧ B p.2 = a}

/-- In the small-product region one coordinate lies in the local disc. -/
theorem small_coordinate {z w : ℂ} {η : ℝ} (hη : 0 < η)
    (h : ‖z * w‖ < η ^ 2) : ‖z‖ < η ∨ ‖w‖ < η := by
  rw [norm_mul] at h
  by_contra hc
  push Not at hc
  have := mul_le_mul hc.1 hc.2 hη.le (norm_nonneg z)
  nlinarith

/-- The two endpoint counts bound the entire fibre, without a prior finiteness assumption. -/
theorem small_product_fiber_bound {A B : ℂ → ℂ} {s a : ℂ} {η : ℝ} {k : ℕ}
    (hη : 0 < η) (hs : s ≠ 0) (hsmall : ‖s‖ < η ^ 2)
    (hA : {z : ℂ | (0 < ‖z‖ ∧ ‖z‖ < η) ∧ A z = a}.Finite)
    (hB : {w : ℂ | (0 < ‖w‖ ∧ ‖w‖ < η) ∧ B w = a}.Finite)
    (hAc : {z : ℂ | (0 < ‖z‖ ∧ ‖z‖ < η) ∧ A z = a}.ncard ≤ k)
    (hBc : {w : ℂ | (0 < ‖w‖ ∧ ‖w‖ < η) ∧ B w = a}.ncard ≤ k) :
    (productFiber A B s a).Finite ∧ (productFiber A B s a).ncard ≤ 2 * k := by
  let L := (fun z : ℂ => (z, s / z)) '' {z : ℂ | (0 < ‖z‖ ∧ ‖z‖ < η) ∧ A z = a}
  let R := (fun w : ℂ => (s / w, w)) '' {w : ℂ | (0 < ‖w‖ ∧ ‖w‖ < η) ∧ B w = a}
  have hL : L.Finite := hA.image _
  have hR : R.Finite := hB.image _
  have hsub : productFiber A B s a ⊆ L ∪ R := by
    rintro ⟨z,w⟩ ⟨heq, hza, hwa⟩
    have hz : z ≠ 0 := by intro hz; simp [hz] at heq; exact hs heq.symm
    have hw : w ≠ 0 := by intro hw; simp [hw] at heq; exact hs heq.symm
    rcases small_coordinate hη (by rwa [heq]) with hlocal | hlocal
    · left
      refine ⟨z, ⟨⟨norm_pos_iff.mpr hz, hlocal⟩, hza⟩, ?_⟩
      simp only [Prod.mk.injEq, true_and]
      rw [← heq, mul_div_cancel_left₀ _ hz]
    · right
      refine ⟨w, ⟨⟨norm_pos_iff.mpr hw, hlocal⟩, hwa⟩, ?_⟩
      simp only [Prod.mk.injEq, and_true]
      rw [← heq, mul_div_cancel_right₀ _ hw]
  refine ⟨(hL.union hR).subset hsub, ?_⟩
  calc
    (productFiber A B s a).ncard ≤ (L ∪ R).ncard := Set.ncard_le_ncard hsub (hL.union hR)
    _ ≤ L.ncard + R.ncard := Set.ncard_union_le _ _
    _ ≤ k + k := add_le_add ((Set.ncard_image_le hA).trans hAc) ((Set.ncard_image_le hB).trans hBc)
    _ = 2 * k := by omega

/-- Applying the two local coordinates gives the manuscript's small-fibre estimate. -/
theorem small_product_fiber_bound_of_coordinates {A B χ ψ : ℂ → ℂ} {s a m : ℂ}
    {η : ℝ} {k : ℕ} (hk : 0 < k) (hη : 0 < η) (hs : s ≠ 0)
    (hsmall : ‖s‖ < η ^ 2)
    (hχ : InjOn χ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < η}) (hψ : InjOn ψ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < η})
    (hA : ∀ z : ℂ, (0 < ‖z‖ ∧ ‖z‖ < η) → A z - m = χ z ^ k)
    (hB : ∀ z : ℂ, (0 < ‖z‖ ∧ ‖z‖ < η) → B z - m = ψ z ^ k) :
    (productFiber A B s a).Finite ∧ (productFiber A B s a).ncard ≤ 2 * k := by
  have ha := coordinate_fiber_bound hk hχ hA a
  have hb := coordinate_fiber_bound hk hψ hB a
  exact small_product_fiber_bound hη hs hsmall ha.1 hb.1 ha.2 hb.2

end Erdos1117
