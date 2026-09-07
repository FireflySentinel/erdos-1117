import Erdos1117

/-! The current conditional theorem, with the remaining assumption and the
maximum-point set expanded. This check does not turn the assumption into a proof. -/

open Set Complex Filter Topology

example (m k : ℕ) (h : ℂ → ℂ) (hh : Differentiable ℂ h) (h0 : h 0 ≠ 0)
    (hnc : ¬ ∃ c : ℂ, ∀ z, h z = c)
    (hglobal : ∃ S : Set ℝ, S.Countable ∧ S ⊆ Ioi 0 ∧
      ∀ r : ℝ, 0 < r → r ∉ S → ∀ a : ℝ, (m : ℝ) < a →
        ({p : ℂ × ℂ | p.1 * p.2 = ((r ^ 2 : ℝ) : ℂ) ∧
          p.1 * deriv (fun z => z ^ m * h z) p.1 / (p.1 ^ m * h p.1) = (a : ℂ) ∧
          starRingEnd ℂ ((starRingEnd ℂ p.2) *
            deriv (fun z => z ^ m * h z) (starRingEnd ℂ p.2) /
            ((starRingEnd ℂ p.2) ^ m * h (starRingEnd ℂ p.2))) = (a : ℂ)}).encard ≤ 2 * k) :
    (∃ E : Set ℝ, E.Countable ∧ E ⊆ Ioi 0 ∧
      ∀ r : ℝ, 0 < r → r ∉ E →
        ({z : ℂ | ‖z‖ = r ∧ ∀ w : ℂ, ‖w‖ = r →
          ‖w ^ m * h w‖ ≤ ‖z ^ m * h z‖}).encard ≤ 2 * k) ∧
    ∃ᶠ r in atTop,
      ({z : ℂ | ‖z‖ = r ∧ ∀ w : ℂ, ‖w‖ = r →
        ‖w ^ m * h w‖ ≤ ‖z ^ m * h z‖}).encard ≤ 2 * k := by
  exact Erdos1117.theorem_1_1_of_global m k hh h0 hnc hglobal
