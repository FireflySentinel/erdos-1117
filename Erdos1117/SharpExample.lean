import Erdos1117.MaximumPoints
import Erdos1117.LocalRoots

open Set Complex

namespace Erdos1117

noncomputable def sharpFunction (k : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (2 * z ^ k - z ^ (2 * k))

theorem sharp_entire (k : ℕ) : Differentiable ℂ (sharpFunction k) := by
  unfold sharpFunction
  fun_prop

/-- The square identity in Remark 5.1, with `Re(z^k)` in place of `R cos φ`. -/
theorem sharp_log_norm (k : ℕ) (z : ℂ) :
    Real.log ‖sharpFunction k z‖ =
      ‖z‖ ^ (2 * k) + 1 / 2 - 2 * ((z ^ k).re - 1 / 2) ^ 2 := by
  rw [sharpFunction, Complex.norm_exp, Real.log_exp]
  have hn := Complex.sq_norm_sub_sq_re (z ^ k)
  rw [norm_pow] at hn
  rw [show z ^ (2 * k) = (z ^ k) ^ 2 by rw [← pow_mul]; congr 1; omega,
    show ‖z‖ ^ (2 * k) = (‖z‖ ^ k) ^ 2 by rw [← pow_mul]; congr 1; omega]
  norm_num [Complex.sub_re, Complex.mul_re, pow_two]
  nlinarith

/-- Each nonzero target has exactly `k` roots, and they lie on the required circle. -/
theorem power_fiber_on_circle {k : ℕ} (hk : 0 < k) {r : ℝ} (hr : 0 ≤ r)
    {a : ℂ} (ha : ‖a‖ = r ^ k) {z : ℂ} (hz : z ^ k = a) : ‖z‖ = r := by
  apply (pow_left_inj₀ (norm_nonneg z) hr hk.ne').mp
  rw [← norm_pow, hz, ha]

private theorem power_fiber_nonempty {k : ℕ} (hk : 0 < k) {a : ℂ} (ha : a ≠ 0) :
    ∃ z : ℂ, z ^ k = a := by
  have hc := power_fiber_card k hk a ha
  have hp : 0 < {z : ℂ | z ^ k = a}.ncard := by omega
  exact Set.nonempty_of_ncard_ne_zero (ne_of_gt hp)

noncomputable def upperTarget (R : ℝ) : ℂ := (1 / 2 : ℂ) + (Real.sqrt (R ^ 2 - 1 / 4) : ℂ) * I
noncomputable def lowerTarget (R : ℝ) : ℂ := (1 / 2 : ℂ) - (Real.sqrt (R ^ 2 - 1 / 4) : ℂ) * I

private theorem targets_norm {R : ℝ} (hR : 1 / 2 < R) :
    ‖upperTarget R‖ = R ∧ ‖lowerTarget R‖ = R := by
  have hs : 0 ≤ R ^ 2 - 1 / 4 := by nlinarith
  have hsq := Real.sq_sqrt hs
  constructor <;> apply (pow_left_inj₀ (norm_nonneg _) (by linarith : 0 ≤ R) (by decide : 2 ≠ 0)).mp <;>
    norm_num [Complex.sq_norm, Complex.normSq_apply, upperTarget, lowerTarget] <;> nlinarith

private theorem upperTarget_ne_zero (R : ℝ) : upperTarget R ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num [upperTarget] at this

private theorem lowerTarget_ne_zero (R : ℝ) : lowerTarget R ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num [lowerTarget] at this

private theorem targets_distinct {R : ℝ} (hR : 1 / 2 < R) : upperTarget R ≠ lowerTarget R := by
  have hs : 0 < Real.sqrt (R ^ 2 - 1 / 4) := Real.sqrt_pos.mpr (by nlinarith)
  intro h
  have := congrArg Complex.im h
  norm_num [upperTarget, lowerTarget] at this
  linarith

/-- On a large circle, the two target values are exactly the equality cases. -/
private theorem targets_iff {q : ℂ} {R : ℝ} (hq : ‖q‖ = R) :
    q.re = 1 / 2 ↔ q = upperTarget R ∨ q = lowerTarget R := by
  constructor
  · intro hre
    have hn := Complex.sq_norm_sub_sq_re q
    rw [hq, hre] at hn
    have hs := Real.sq_sqrt (show 0 ≤ R ^ 2 - 1 / 4 by nlinarith)
    have he : q.im = Real.sqrt (R ^ 2 - 1 / 4) ∨ q.im = -Real.sqrt (R ^ 2 - 1 / 4) := by
      apply (sq_eq_sq_iff_eq_or_eq_neg).mp
      nlinarith
    rcases he with hi | hi
    · left; apply Complex.ext <;> simp [upperTarget, hre, hi]
    · right; apply Complex.ext <;> simp [lowerTarget, hre, hi]
  · rintro (rfl | rfl) <;> norm_num [upperTarget, lowerTarget]

private theorem sharp_norm_pos (k : ℕ) (z : ℂ) : 0 < ‖sharpFunction k z‖ := by
  rw [sharpFunction, Complex.norm_exp]
  exact Real.exp_pos _

/-- The equality cases on a large circle, stated for the actual maximum set. -/
theorem sharp_maximum_iff_large {k : ℕ} (hk : 0 < k) {r : ℝ} (hr : 0 < r)
    (hR : 1 / 2 < r ^ k) (z : ℂ) :
    z ∈ maximumPoints (sharpFunction k) r ↔ ‖z‖ = r ∧ (z ^ k).re = 1 / 2 := by
  obtain ⟨y, hy⟩ := power_fiber_nonempty hk (upperTarget_ne_zero (r ^ k))
  have hyr : ‖y‖ = r := power_fiber_on_circle hk hr.le (targets_norm hR).1 hy
  have hyre : (y ^ k).re = 1 / 2 := by rw [hy]; norm_num [upperTarget]
  constructor
  · intro hz
    refine ⟨hz.1, ?_⟩
    have hb := Real.log_le_log (sharp_norm_pos k y) (hz.2 y hyr)
    rw [sharp_log_norm, sharp_log_norm, hyr, hz.1, hyre] at hb
    nlinarith [sq_nonneg ((z ^ k).re - 1 / 2)]
  · rintro ⟨hz, hre⟩
    refine ⟨hz, fun w hw => ?_⟩
    apply (Real.log_le_log_iff (sharp_norm_pos k w) (sharp_norm_pos k z)).mp
    rw [sharp_log_norm, sharp_log_norm, hz, hw, hre]
    nlinarith [sq_nonneg ((w ^ k).re - 1 / 2)]

/-- For `r^k > 1/2`, there are exactly `2k` distinct maximum modulus points. -/
theorem sharp_maximum_card_large {k : ℕ} (hk : 0 < k) {r : ℝ} (hr : 0 < r)
    (hR : 1 / 2 < r ^ k) :
    (maximumPoints (sharpFunction k) r).Finite ∧
      (maximumPoints (sharpFunction k) r).ncard = 2 * k := by
  have heq : maximumPoints (sharpFunction k) r =
      {z : ℂ | z ^ k = upperTarget (r ^ k)} ∪ {z : ℂ | z ^ k = lowerTarget (r ^ k)} := by
    ext z
    rw [sharp_maximum_iff_large hk hr hR]
    constructor
    · rintro ⟨hz, hre⟩
      exact (targets_iff (by rw [norm_pow, hz])).mp hre
    · rintro (hz | hz)
      · have hzr := power_fiber_on_circle hk hr.le (targets_norm hR).1 hz
        exact ⟨hzr, (targets_iff (by rw [norm_pow, hzr])).mpr (Or.inl hz)⟩
      · have hzr := power_fiber_on_circle hk hr.le (targets_norm hR).2 hz
        exact ⟨hzr, (targets_iff (by rw [norm_pow, hzr])).mpr (Or.inr hz)⟩
  rw [heq]
  have hA := (power_fiber_bound k hk (upperTarget (r ^ k))).1
  have hB := (power_fiber_bound k hk (lowerTarget (r ^ k))).1
  refine ⟨hA.union hB, ?_⟩
  rw [Set.ncard_union_eq (Set.disjoint_left.mpr (fun z hz hw => targets_distinct hR (hz.symm.trans hw))) hA hB,
    power_fiber_card k hk _ (upperTarget_ne_zero _), power_fiber_card k hk _ (lowerTarget_ne_zero _)]
  omega

/-- For `0 < r^k ≤ 1/2`, the maximum points are the roots of the positive target. -/
theorem sharp_maximum_iff_small {k : ℕ} (hk : 0 < k) {r : ℝ} (hr : 0 < r)
    (hR : r ^ k ≤ 1 / 2) (z : ℂ) :
    z ∈ maximumPoints (sharpFunction k) r ↔ z ^ k = (r ^ k : ℝ) := by
  have hpos : 0 < r ^ k := pow_pos hr k
  have hne : ((r ^ k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hnorm : ‖((r ^ k : ℝ) : ℂ)‖ = r ^ k := by simp [abs_of_pos hr]
  obtain ⟨y, hy⟩ := power_fiber_nonempty hk hne
  have hyr : ‖y‖ = r := power_fiber_on_circle hk hr.le hnorm hy
  have hyre : (y ^ k).re = r ^ k := by rw [hy]; rfl
  constructor
  · intro hz
    have hb := Real.log_le_log (sharp_norm_pos k y) (hz.2 y hyr)
    rw [sharp_log_norm, sharp_log_norm, hyr, hz.1, hyre] at hb
    have hzr : (z ^ k).re ≤ r ^ k := by simpa [norm_pow, hz.1] using Complex.re_le_norm (z ^ k)
    have hre : (z ^ k).re = r ^ k := by
      nlinarith [sq_nonneg ((z ^ k).re - r ^ k)]
    have hn := Complex.sq_norm_sub_sq_re (z ^ k)
    rw [norm_pow, hz.1, hre] at hn
    apply Complex.ext
    · exact hre
    · simp only [Complex.ofReal_im]
      nlinarith [sq_nonneg (z ^ k).im]
  · intro hz
    have hzr := power_fiber_on_circle hk hr.le hnorm hz
    refine ⟨hzr, fun w hw => ?_⟩
    apply (Real.log_le_log_iff (sharp_norm_pos k w) (sharp_norm_pos k z)).mp
    rw [sharp_log_norm, sharp_log_norm, hzr, hw, hz, Complex.ofReal_re]
    have hwr : (w ^ k).re ≤ r ^ k := by simpa [norm_pow, hw] using Complex.re_le_norm (w ^ k)
    nlinarith [mul_nonneg (sub_nonneg.mpr hwr) (show 0 ≤ 1 - r ^ k - (w ^ k).re by linarith)]

/-- The small-circle count includes the transition radius. -/
theorem sharp_maximum_card_small {k : ℕ} (hk : 0 < k) {r : ℝ} (hr : 0 < r)
    (hR : r ^ k ≤ 1 / 2) :
    (maximumPoints (sharpFunction k) r).Finite ∧
      (maximumPoints (sharpFunction k) r).ncard = k := by
  have heq : maximumPoints (sharpFunction k) r = {z : ℂ | z ^ k = ((r ^ k : ℝ) : ℂ)} := by
    ext z; exact sharp_maximum_iff_small hk hr hR z
  rw [heq]
  exact ⟨(power_fiber_bound k hk _).1,
    power_fiber_card k hk _ (by exact_mod_cast (pow_pos hr k).ne')⟩

/-- The logarithmic derivative has the factor `z^k` and a nonzero remaining factor at zero. -/
theorem sharp_logarithmicDerivative {k : ℕ} (hk : 0 < k) (z : ℂ) :
    logarithmicDerivative (sharpFunction k) z = (2 * k : ℂ) * z ^ k * (1 - z ^ k) := by
  have hpow : z * z ^ (k - 1) = z ^ k := by
    rw [← pow_succ']
    congr 1
    omega
  have hfun : sharpFunction k = fun w : ℂ => Complex.exp (2 * w ^ k - (w ^ k) ^ 2) := by
    funext w
    rw [sharpFunction, ← pow_mul]
    congr 3
    omega
  have hd := ((((hasDerivAt_id z).pow k).const_mul 2).sub (((hasDerivAt_id z).pow k).pow 2)).cexp
  simp only [Pi.sub_apply, Pi.pow_apply, id_eq] at hd
  rw [hfun, logarithmicDerivative, hd.deriv]
  simp only [mul_one, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  have hne := Complex.exp_ne_zero (2 * z ^ k - (z ^ k) ^ 2)
  calc
    _ = 2 * (k : ℂ) * (z * z ^ (k - 1)) * (1 - z ^ k) := by field_simp
    _ = _ := by rw [hpow]

theorem sharp_remaining_factor_nonzero {k : ℕ} (hk : 0 < k) :
    (2 * k : ℂ) * (1 - (0 : ℂ) ^ k) ≠ 0 := by
  simp [zero_pow hk.ne', hk.ne']

end Erdos1117
