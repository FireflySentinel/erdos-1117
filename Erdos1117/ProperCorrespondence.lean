import Mathlib

/-! Properness and finite fibres for the correspondence, in graph coordinates.
The common value is retained as a third coordinate so that poles are handled by
holomorphic equations, rather than by Lean's totalized division. -/

open Set Filter Topology

namespace Erdos1117

/-- Points over a set of product/common-value pairs. -/
def correspondenceOver (p q P Q : ℂ → ℂ) (K : Set (ℂ × ℂ)) : Set (ℂ × ℂ × ℂ) :=
  {x | (x.1 * x.2.1, x.2.2) ∈ K ∧
    p x.1 = x.2.2 * q x.1 ∧ P x.2.1 = x.2.2 * Q x.2.1}

private lemma exclude_small_coordinate {p q : ℂ → ℂ} {m : ℂ} {L : Set ℂ}
    (hp : Continuous p) (hq : Continuous q) (hq0 : q 0 ≠ 0)
    (hzero : p 0 = m * q 0) (hL : IsClosed L) (hm : m ∉ L) :
    ∃ δ > (0 : ℝ), ∀ z a : ℂ, ‖z‖ < δ → a ∈ L → p z ≠ a * q z := by
  have hc : ContinuousAt (fun z => p z / q z) 0 := hp.continuousAt.div hq.continuousAt hq0
  have hv : p 0 / q 0 = m := by rw [hzero, mul_div_cancel_right₀ _ hq0]
  have he : ∀ᶠ z in 𝓝 (0 : ℂ), p z / q z ∉ L :=
    hc.eventually (hL.isOpen_compl.mem_nhds (by simpa [hv] using hm))
  obtain ⟨δ, hδ, hd⟩ := Metric.eventually_nhds_iff.mp (he.and (hq.continuousAt.eventually_ne hq0))
  refine ⟨δ, hδ, ?_⟩
  intro z a hz ha heq
  obtain ⟨hne, hqz⟩ := hd (by simpa using hz)
  apply hne
  simpa [heq, mul_div_cancel_right₀ _ hqz] using ha

/-- The compact-preimage assertion of Lemma 4.1, before invoking analyticity. -/
theorem correspondenceOver_isCompact {p q P Q : ℂ → ℂ} {m : ℂ} {K : Set (ℂ × ℂ)}
    (hp : Continuous p) (hq : Continuous q) (hP : Continuous P) (hQ : Continuous Q)
    (hq0 : q 0 ≠ 0) (hQ0 : Q 0 ≠ 0)
    (hp0 : p 0 = m * q 0) (hP0 : P 0 = m * Q 0)
    (hK : IsCompact K) (hbase : ∀ y ∈ K, y.2 ≠ m) :
    IsCompact (correspondenceOver p q P Q K) := by
  have hL := hK.image continuous_snd
  have hm : m ∉ Prod.snd '' K := by
    rintro ⟨y, hy, he⟩
    exact hbase y hy he
  obtain ⟨δ, hδ, hd⟩ := exclude_small_coordinate hp hq hq0 hp0 hL.isClosed hm
  obtain ⟨ε, hε, he⟩ := exclude_small_coordinate hP hQ hQ0 hP0 hL.isClosed hm
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  have hclosed : IsClosed (correspondenceOver p q P Q K) := by
    apply IsClosed.inter (hK.isClosed.preimage (by fun_prop))
    exact (isClosed_eq (hp.comp continuous_fst) (by fun_prop)).inter
      (isClosed_eq (hP.comp (continuous_fst.comp continuous_snd)) (by fun_prop))
  apply Metric.isCompact_of_isClosed_isBounded hclosed
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨max (R / ε) (max (R / δ) R), ?_⟩
  intro x hx
  have hlam : x.2.2 ∈ Prod.snd '' K := ⟨_, hx.1, rfl⟩
  have hz : δ ≤ ‖x.1‖ := le_of_not_gt (fun h => hd _ _ h hlam hx.2.1)
  have hw : ε ≤ ‖x.2.1‖ := le_of_not_gt (fun h => he _ _ h hlam hx.2.2)
  have hb : ‖x.1‖ * ‖x.2.1‖ ≤ R := by
    have hb' : ‖x.1 * x.2.1‖ ≤ R := (norm_fst_le (x.1 * x.2.1, x.2.2)).trans (hR _ hx.1)
    simpa [norm_mul] using hb'
  have hzR : ‖x.1‖ ≤ R / ε := (le_div_iff₀ hε).mpr (by nlinarith [norm_nonneg x.1])
  have hwR : ‖x.2.1‖ ≤ R / δ := (le_div_iff₀ hδ).mpr (by nlinarith [norm_nonneg x.2.1])
  have hlR : ‖x.2.2‖ ≤ R := (norm_snd_le (x.1 * x.2.1, x.2.2)).trans (hR _ hx.1)
  exact max_le (hzR.trans (le_max_left _ _))
    (max_le (hwR.trans ((le_max_left _ _).trans (le_max_right _ _)))
      (hlR.trans ((le_max_right _ _).trans (le_max_right _ _))))

/-- A compact subset of the zero set of a nonzero entire function is finite. -/
theorem finite_zeros_in_compact {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hg0 : g 0 ≠ 0) {K : Set ℂ} (hK : IsCompact K) :
    {z ∈ K | g z = 0}.Finite := by
  have hc := (show AnalyticOnNhd ℂ g Set.univ from fun z _ => hg.analyticAt z).preimage_zero_mem_codiscrete hg0
  have hf := hK.finite_sdiff_of_mem_codiscreteWithin
    (Filter.codiscreteWithin_mono (subset_univ K) hc)
  exact hf.subset (by intro z hz; simpa using hz)

/-- The finite-fibre assertion of Lemma 4.1. -/
theorem correspondence_fiber_finite {p q P Q : ℂ → ℂ} {m s a : ℂ}
    (hp : Differentiable ℂ p) (hq : Differentiable ℂ q)
    (hP : Continuous P) (hQ : Continuous Q)
    (hq0 : q 0 ≠ 0) (hQ0 : Q 0 ≠ 0)
    (hp0 : p 0 = m * q 0) (hP0 : P 0 = m * Q 0)
    (hs : s ≠ 0) (ha : a ≠ m) :
    (correspondenceOver p q P Q {(s, a)}).Finite := by
  have hcompact := correspondenceOver_isCompact hp.continuous hq.continuous hP hQ
    hq0 hQ0 hp0 hP0 (K := {(s, a)}) isCompact_singleton (by simpa using ha)
  let K := Prod.fst '' correspondenceOver p q P Q {(s, a)}
  have hK : IsCompact K := hcompact.image continuous_fst
  have hg : Differentiable ℂ (fun z => p z - a * q z) := hp.sub (hq.const_mul a)
  have hg0 : p 0 - a * q 0 ≠ 0 := by
    rw [hp0, ← sub_mul]
    exact mul_ne_zero (sub_ne_zero.mpr ha.symm) hq0
  have hfinite := finite_zeros_in_compact hg hg0 hK
  apply (hfinite.subset (show K ⊆ {z ∈ K | p z - a * q z = 0} from ?_)).of_finite_image
  · intro z hz w hw heq
    have hzv : z.1 * z.2.1 = s ∧ z.2.2 = a := Prod.mk.inj (mem_singleton_iff.mp hz.1)
    have hwv : w.1 * w.2.1 = s ∧ w.2.2 = a := Prod.mk.inj (mem_singleton_iff.mp hw.1)
    have hzne : z.1 ≠ 0 := by intro h; apply hs; simpa [h] using hzv.1.symm
    apply Prod.ext heq
    apply Prod.ext _ (hzv.2.trans hwv.2.symm)
    exact mul_left_cancel₀ hzne (hzv.1.trans (by simpa [heq] using hwv.1.symm))
  · rintro z ⟨x, hx, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    have hv : x.2.2 = a := congrArg Prod.snd (mem_singleton_iff.mp hx.1)
    simp [hx.2.1, hv]

/-- The target excludes zero products and the common value at the origin. -/
abbrev CorrespondenceBase (m : ℂ) := {y : ℂ × ℂ // y.1 ≠ 0 ∧ y.2 ≠ m}

/-- The correspondence with its common value recorded as a graph coordinate. -/
abbrev CorrespondenceDomain (p q P Q : ℂ → ℂ) (m : ℂ) :=
  {x : ℂ × ℂ × ℂ // x.1 * x.2.1 ≠ 0 ∧ x.2.2 ≠ m ∧
    p x.1 = x.2.2 * q x.1 ∧ P x.2.1 = x.2.2 * Q x.2.1}

def correspondenceMap (p q P Q : ℂ → ℂ) (m : ℂ) :
    CorrespondenceDomain p q P Q m → CorrespondenceBase m :=
  fun x => ⟨(x.1.1 * x.1.2.1, x.1.2.2), x.2.1, x.2.2.1⟩

/-- Lemma 4.1: properness in Mathlib's standard `IsProperMap` sense. -/
theorem correspondenceMap_isProper {p q P Q : ℂ → ℂ} {m : ℂ}
    (hp : Continuous p) (hq : Continuous q) (hP : Continuous P) (hQ : Continuous Q)
    (hq0 : q 0 ≠ 0) (hQ0 : Q 0 ≠ 0)
    (hp0 : p 0 = m * q 0) (hP0 : P 0 = m * Q 0) :
    IsProperMap (correspondenceMap p q P Q m) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨by unfold correspondenceMap; fun_prop, ?_⟩
  intro K hK
  rw [Subtype.isCompact_iff]
  have hc := correspondenceOver_isCompact hp hq hP hQ hq0 hQ0 hp0 hP0
    (hK.image continuous_subtype_val) (by rintro y ⟨z, hz, rfl⟩; exact z.2.2)
  convert hc using 1
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨correspondenceMap p q P Q m z, hz, rfl⟩, z.2.2.2⟩
  · intro hx
    obtain ⟨y, hy, heq⟩ := hx.1
    have hb : x.1 * x.2.1 ≠ 0 ∧ x.2.2 ≠ m := by simpa only [heq] using y.2
    obtain ⟨hs, ha⟩ := hb
    refine ⟨⟨x, hs, ha, hx.2⟩, ?_, rfl⟩
    change correspondenceMap p q P Q m ⟨x, hs, ha, hx.2⟩ ∈ K
    have he : correspondenceMap p q P Q m ⟨x, hs, ha, hx.2⟩ = y := Subtype.ext heq.symm
    rwa [he]

/-- The image is closed in the base, as a topological consequence of properness. -/
theorem correspondenceMap_range_isClosed {p q P Q : ℂ → ℂ} {m : ℂ}
    (hp : Continuous p) (hq : Continuous q) (hP : Continuous P) (hQ : Continuous Q)
    (hq0 : q 0 ≠ 0) (hQ0 : Q 0 ≠ 0)
    (hp0 : p 0 = m * q 0) (hP0 : P 0 = m * Q 0) :
    IsClosed (Set.range (correspondenceMap p q P Q m)) :=
  (correspondenceMap_isProper hp hq hP hQ hq0 hQ0 hp0 hP0).isClosed_range

/-- Lemma 4.1: every fibre of the proper map is finite. -/
theorem correspondenceMap_fiber_finite {p q P Q : ℂ → ℂ} {m : ℂ}
    (hp : Differentiable ℂ p) (hq : Differentiable ℂ q)
    (hP : Continuous P) (hQ : Continuous Q)
    (hq0 : q 0 ≠ 0) (hQ0 : Q 0 ≠ 0)
    (hp0 : p 0 = m * q 0) (hP0 : P 0 = m * Q 0)
    (y : CorrespondenceBase m) :
    ((correspondenceMap p q P Q m) ⁻¹' {y}).Finite := by
  have hf := correspondence_fiber_finite hp hq hP hQ hq0 hQ0 hp0 hP0 y.2.1 y.2.2
  apply (hf.preimage Subtype.val_injective.injOn).subset
  intro x hx
  have he := congrArg Subtype.val (mem_singleton_iff.mp hx)
  exact ⟨mem_singleton_iff.mpr he, x.2.2.2⟩

/-- Coprime numerator/denominator data identify the graph equations with the
ordinary quotient equation and exclude poles. -/
theorem quotient_equation_iff {p q : ℂ → ℂ} {z a : ℂ}
    (hcoprime : p z ≠ 0 ∨ q z ≠ 0) :
    p z = a * q z ↔ q z ≠ 0 ∧ p z / q z = a := by
  constructor
  · intro he
    have hq : q z ≠ 0 := by
      rcases hcoprime with hp | hq
      · intro hq
        exact hp (by simpa [hq] using he)
      · exact hq
    exact ⟨hq, (div_eq_iff hq).mpr he⟩
  · rintro ⟨hq, he⟩
    exact (div_eq_iff hq).mp he

end Erdos1117
