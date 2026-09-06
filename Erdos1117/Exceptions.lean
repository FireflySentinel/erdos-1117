import Erdos1117.Convexity

open Set Filter Topology

namespace Erdos1117

/-- Local finiteness of the exceptional image points implies countability. -/
theorem countable_of_locally_finite_points {T : Set (ℂ × ℂ)}
    (hT : LocallyFinite (fun p : T => ({p.val} : Set (ℂ × ℂ)))) : T.Countable := by
  have hu := hT.countable_univ (fun p => singleton_nonempty p.val)
  have : Countable T := Set.countable_univ_iff.mp hu
  exact Set.to_countable T

/-- Countably many exceptional radii cannot contain any tail interval. -/
theorem exists_large_nonexceptional {E : Set ℝ} (hE : E.Countable) (R : ℝ) :
    ∃ r : ℝ, R < r ∧ 0 < r ∧ r ∉ E := by
  obtain ⟨r, hr, hnot⟩ := (hE.dense_compl ℝ).inter_open_nonempty
    (Ioi (max R 0)) isOpen_Ioi nonempty_Ioi
  exact ⟨r, (le_max_left _ _).trans_lt hr, (le_max_right _ _).trans_lt hr, hnot⟩

theorem frequently_bounded_of_countable_exceptions {α : Type*} [Preorder α]
    {E : Set ℝ} {ν : ℝ → α} {K : α}
    (hE : E.Countable) (hν : ∀ r, 0 < r → r ∉ E → ν r ≤ K) :
    ∃ᶠ r in atTop, ν r ≤ K := by
  rw [Filter.frequently_atTop]
  intro R
  obtain ⟨r, hr, hpos, hnot⟩ := exists_large_nonexceptional hE R
  exact ⟨r, hr.le, hν r hpos hnot⟩

theorem not_tendsto_atTop_of_countable_exceptions {E : Set ℝ} {ν : ℝ → ℕ} {K : ℕ}
    (hE : E.Countable) (hν : ∀ r, 0 < r → r ∉ E → ν r ≤ K) :
    ¬ Tendsto ν atTop atTop := by
  intro h
  have he := h.eventually (eventually_gt_atTop K)
  obtain ⟨r, hr, hgt⟩ := ((frequently_bounded_of_countable_exceptions hE hν).and_eventually he).exists
  omega

end Erdos1117
