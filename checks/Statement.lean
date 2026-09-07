import Erdos1117

/-! The entire-function conclusion with both remaining component hypotheses
expanded into Mathlib definitions. -/

open Set Complex Filter Topology

example (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hne : f ≠ 0)
    (hnm : ¬ ∃ (c : ℂ) (m : ℕ), ∀ z, f z = c * z ^ m)
    (T : Set (ℂ × ℂ)) (hT : T.Countable) :
    let A := fun z : ℂ => z * deriv f z / f z
    let B := fun w : ℂ => starRingEnd ℂ (A (starRingEnd ℂ w))
    let F := fun s a : ℂ => {p : ℂ × ℂ | p.1 * p.2 = s ∧ A p.1 = a ∧ B p.2 = a}
    let G := {y : ℂ × ℂ | y.1 ≠ 0 ∧ y.2 ≠ (analyticOrderNatAt f 0 : ℂ) ∧
      y.2 ≠ 0 ∧ (F y.1 y.2).Nonempty} \ T
    IsLocallyConstant (fun y : G => (F y.1.1 y.1.2).encard) →
    (∀ η : ℝ, 0 < η → ∀ x : G,
      ∃ y ∈ connectedComponent x, ‖y.1.1‖ < η ^ 2) →
    ∃ k : ℕ, 0 < k ∧
      (∃ E : Set ℝ, E.Countable ∧ E ⊆ Ioi 0 ∧ ∀ r : ℝ, 0 < r → r ∉ E →
        ({z : ℂ | ‖z‖ = r ∧ ∀ w : ℂ, ‖w‖ = r → ‖f w‖ ≤ ‖f z‖}).encard ≤ 2 * k) ∧
      ∃ᶠ r in atTop,
        ({z : ℂ | ‖z‖ = r ∧ ∀ w : ℂ, ‖w‖ = r → ‖f w‖ ≤ ‖f z‖}).encard ≤ 2 * k := by
  dsimp only
  intro hdegree hsmall
  exact ⟨Erdos1117.firstGap f hf hne,
    Erdos1117.theorem_1_1_of_entire_component_data f hf hne hnm T hT hdegree hsmall⟩
