import Erdos1117.FactoredFunction

open Set Complex Filter Topology

namespace Erdos1117

/-- Extract the zero at the origin while keeping the remaining factor entire. -/
theorem exists_entire_factor {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hne : f ≠ 0) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ h 0 ≠ 0 ∧
      f = factoredFunction (analyticOrderNatAt f 0) h := by
  have htop : analyticOrderAt f 0 ≠ ⊤ := by
    intro ht
    exact hne ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero 0 hf.analyticAt).mp ht)
  obtain ⟨g, hg, hg0, heq⟩ := (hf.analyticAt 0).analyticOrderAt_eq_natCast.mp
    (Nat.cast_analyticOrderNatAt htop).symm
  let m := analyticOrderNatAt f 0
  let h := fun z : ℂ => if z = 0 then g 0 else f z / z ^ m
  have hlocal : h =ᶠ[𝓝 0] g := by
    filter_upwards [heq] with z hz
    dsimp [h]
    split_ifs with hz0
    · simp [hz0]
    · simpa [m, sub_zero, smul_eq_mul, pow_ne_zero _ hz0] using
        congrArg (fun w : ℂ => w / z ^ m) hz
  have hh : Differentiable ℂ h := by
    intro z
    by_cases hz : z = 0
    · subst z
      exact (hg.congr hlocal.symm).differentiableAt
    · have he : h =ᶠ[𝓝 z] (fun w => f w / w ^ m) := by
        filter_upwards [eventually_ne_nhds hz] with w hw
        simp [h, hw]
      exact ((hf z).div ((differentiableAt_id).pow m) (pow_ne_zero _ hz)).congr_of_eventuallyEq he
  refine ⟨h, hh, by simpa [h] using hg0, ?_⟩
  funext z
  by_cases hz : z = 0
  · subst z
    simpa [factoredFunction, h, m, sub_zero, smul_eq_mul] using heq.self_of_nhds
  · simp [factoredFunction, h, m, hz, pow_ne_zero _ hz, mul_div_cancel₀]

/-- The entire factor obtained by removing the zero at the origin. -/
noncomputable def entireFactor (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hne : f ≠ 0) : ℂ → ℂ :=
  (exists_entire_factor hf hne).choose

theorem entireFactor_spec {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hne : f ≠ 0) :
    Differentiable ℂ (entireFactor f hf hne) ∧ entireFactor f hf hne 0 ≠ 0 ∧
      f = factoredFunction (analyticOrderNatAt f 0) (entireFactor f hf hne) :=
  (exists_entire_factor hf hne).choose_spec

/-- The gap between the first two nonzero Taylor terms of `f`. -/
noncomputable def firstGap (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hne : f ≠ 0) : ℕ :=
  analyticOrderNatAt (fun z => entireFactor f hf hne z - entireFactor f hf hne 0) 0

theorem entireFactor_nonconstant {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hne : f ≠ 0)
    (hnm : ¬ ∃ (c : ℂ) (m : ℕ), ∀ z, f z = c * z ^ m) :
    ¬ ∃ c : ℂ, ∀ z, entireFactor f hf hne z = c := by
  rintro ⟨c, hc⟩
  apply hnm
  refine ⟨c, analyticOrderNatAt f 0, ?_⟩
  intro z
  conv_lhs => rw [(entireFactor_spec hf hne).2.2]
  simp [factoredFunction, hc, mul_comm]

theorem firstGap_pos {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hne : f ≠ 0)
    (hnm : ¬ ∃ (c : ℂ) (m : ℕ), ∀ z, f z = c * z ^ m) :
    0 < firstGap f hf hne := by
  let h := entireFactor f hf hne
  have hh := (entireFactor_spec hf hne).1
  have hnc := entireFactor_nonconstant hf hne hnm
  have htop : analyticOrderAt (fun z => h z - h 0) 0 ≠ ⊤ := by
    intro ht
    have he := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero
      (f := fun z => h z - h 0) 0 (fun z => (hh.analyticAt z).sub analyticAt_const)).mp ht
    exact hnc ⟨h 0, fun z => sub_eq_zero.mp (congrFun he z)⟩
  have hpos : analyticOrderAt (fun z => h z - h 0) 0 ≠ 0 := by
    exact analyticOrderAt_ne_zero.mpr ⟨(hh.analyticAt 0).sub analyticAt_const, sub_self _⟩
  have hc := Nat.cast_analyticOrderNatAt htop
  have hn : analyticOrderNatAt (fun z => h z - h 0) 0 ≠ 0 := by
    intro he
    exact hpos (by simpa [he] using hc.symm)
  exact Nat.pos_of_ne_zero hn

/-- The extracted Taylor gap is the analytic order of the nonconstant part. -/
theorem firstGap_order {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hne : f ≠ 0)
    (hnm : ¬ ∃ (c : ℂ) (m : ℕ), ∀ z, f z = c * z ^ m) :
    analyticOrderAt (fun z => entireFactor f hf hne z - entireFactor f hf hne 0) 0 =
      firstGap f hf hne := by
  have hh := (entireFactor_spec hf hne).1
  have htop : analyticOrderAt
      (fun z => entireFactor f hf hne z - entireFactor f hf hne 0) 0 ≠ ⊤ := by
    intro ht
    have he := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero 0
      (fun z => (hh.analyticAt z).sub analyticAt_const)).mp ht
    exact entireFactor_nonconstant hf hne hnm
      ⟨entireFactor f hf hne 0, fun z => sub_eq_zero.mp (congrFun he z)⟩
  exact (Nat.cast_analyticOrderNatAt htop).symm

end Erdos1117
