import Mathlib

open Set Filter Topology

namespace Erdos1117

/-- A convex real function is differentiable outside a countable set. -/
theorem convex_countable_nondifferentiable {v : ℝ → ℝ} (hc : ConvexOn ℝ univ v) :
    {x | ¬ DifferentiableAt ℝ v x}.Countable := by
  let l := fun x => derivWithin v (Iio x) x
  let r := fun x => derivWithin v (Ioi x) x
  have hl x : HasDerivWithinAt v (l x) (Iio x) x :=
    hc.hasDerivWithinAt_leftDeriv_of_mem_interior (by simp)
  have hr x : HasDerivWithinAt v (r x) (Ioi x) x :=
    hc.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp)
  have hlt x (hx : ¬ DifferentiableAt ℝ v x) : l x < r x := by
    apply lt_of_le_of_ne (hc.leftDeriv_le_rightDeriv_of_mem_interior (by simp))
    intro heq
    apply hx
    have hh := (((hl x).congr_deriv heq).Iic_of_Iio).union (hr x).Ici_of_Ioi
    rw [Iic_union_Ici] at hh
    exact hh.differentiableWithinAt.differentiableAt Filter.univ_mem
  have hsep {x y : ℝ} (hxy : x < y) : r x ≤ l y :=
    (hc.le_slope_of_hasDerivWithinAt_Ioi (mem_univ _) (mem_univ _) hxy (hr x)).trans
      (hc.slope_le_of_hasDerivWithinAt_Iio (mem_univ _) (mem_univ _) hxy (hl y))
  have hd : {x | ¬ DifferentiableAt ℝ v x}.PairwiseDisjoint (fun x => Ioo (l x) (r x)) := by
    intro x hx y hy hne
    rcases lt_or_gt_of_ne hne with hxy | hyx
    · exact Set.disjoint_left.mpr (fun t ht hu => (not_lt_of_ge (hsep hxy)) (hu.1.trans ht.2))
    · exact Set.disjoint_left.mpr (fun t ht hu => (not_lt_of_ge (hsep hyx)) (ht.1.trans hu.2))
  exact hd.countable_of_isOpen (fun _ _ => isOpen_Ioo) (fun x hx => nonempty_Ioo.mpr (hlt x hx))

end Erdos1117
