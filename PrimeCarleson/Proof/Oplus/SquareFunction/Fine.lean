module

public import PrimeCarleson.Proof.Oplus.SquareFunction.Convolution

/-!
# Fine scales: `‖(A_k - I) D_j f‖₂ ≲ 2^{(k-j)/2} ‖D_j f‖₂` for `k < j`

The fine-scale decay in the proof of the square-function estimate of
Jones–Kaufman–Rosenblatt–Wierdl (proved here).

* `lintegral_sq_translate_sub_le`: for `g` constant on the dyadic intervals of length `2^n`,
  `‖g(· - t) - g‖₂² ≤ 4 (|t|/2^n) ‖g‖₂²`;
* `sqn_schwartzAvg_sub_le_fine`: since `∫ ψ = 1`, `A_k g - g = ∫ ψ_k(t) (g(· - t) - g) dt`, and
  Cauchy-Schwarz against the weight `|ψ_k(t)| dt` followed by the translation estimate gives
  `‖A_k g - g‖₂² ≤ 8 ‖ψ‖₁ (∫ |ψ(s)||s| ds) 2^{k-j} ‖g‖₂²` for `g` constant on the intervals of
  length `2^{j-1}`.  (One can also use the weight `|ψ_k(t)||t|^{1/2}` and obtain the same
  decay `2^{(k-j)/2}` for the norm.)
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal SchwartzMap

open PrimeCarleson.Proof.Lepingle

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- `‖a - b‖² ≤ 2‖a‖² + 2‖b‖²`. -/
theorem enorm_sub_sq_le (a b : ℂ) : ‖a - b‖ₑ ^ 2 ≤ 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
  have := enorm_add_sq_le a (-b)
  rwa [← sub_eq_add_neg, enorm_neg] at this

/-- The points `x` such that `x` and `x - t` lie in different dyadic intervals of length `2^n`. -/
def crossSet (n : ℤ) (t : ℝ) : Set ℝ := {x | dyadicIdx n (x - t) ≠ dyadicIdx n x}

/-- The set `crossSet n t` is measurable. -/
theorem measurableSet_crossSet (n : ℤ) (t : ℝ) : MeasurableSet (crossSet n t) := by
  have h : MeasurableSet {x : ℝ | dyadicIdx n (x - t) = dyadicIdx n x} :=
    measurableSet_eq_fun ((measurable_dyadicIdx n).comp (measurable_id.sub_const t))
      (measurable_dyadicIdx n)
  exact h.compl

/-- A dyadic interval meets `crossSet n t` in a set of measure `≤ |t|`. -/
theorem volume_dyadicIco_inter_crossSet_le (n m : ℤ) (t : ℝ) :
    volume (dyadicIco n m ∩ crossSet n t) ≤ ENNReal.ofReal |t| := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := zpow_pos (by norm_num) n
  rcases le_or_gt 0 t with ht | ht
  · have hsub : dyadicIco n m ∩ crossSet n t ⊆ Ico ((2 : ℝ) ^ n * m) ((2 : ℝ) ^ n * m + t) := by
      intro x ⟨hx, hc⟩
      obtain ⟨hx1, hx2⟩ := hx
      refine ⟨hx1, ?_⟩
      by_contra hcon
      apply hc
      have hxm : x - t ∈ dyadicIco n m := ⟨by linarith, by linarith⟩
      exact (mem_dyadicIco_iff.1 hxm).trans (mem_dyadicIco_iff.1 ⟨hx1, hx2⟩).symm
    refine (measure_mono hsub).trans ?_
    rw [Real.volume_Ico, abs_of_nonneg ht]
    exact le_of_eq (by congr 1; ring)
  · have hsub : dyadicIco n m ∩ crossSet n t ⊆
        Ico ((2 : ℝ) ^ n * (m + 1) + t) ((2 : ℝ) ^ n * (m + 1)) := by
      intro x ⟨hx, hc⟩
      obtain ⟨hx1, hx2⟩ := hx
      refine ⟨?_, hx2⟩
      by_contra hcon
      apply hc
      have hxm : x - t ∈ dyadicIco n m := ⟨by linarith, by linarith⟩
      exact (mem_dyadicIco_iff.1 hxm).trans (mem_dyadicIco_iff.1 ⟨hx1, hx2⟩).symm
    refine (measure_mono hsub).trans ?_
    rw [Real.volume_Ico, abs_of_neg ht]
    exact le_of_eq (by congr 1; ring)

/-- `∫_B |g|² ≤ (s / 2^n) ∫ |g|²` when `g` is constant on the dyadic intervals of length `2^n`
and every such interval meets `B` in a set of measure `≤ s`. -/
theorem setLIntegral_sq_le_of_inter {n : ℤ} {g : ℝ → ℂ} (hconst : ConstOnDyadic n g) {B : Set ℝ}
    (hBm : MeasurableSet B) {s : ℝ} (hs : 0 ≤ s)
    (hB : ∀ m, volume (dyadicIco n m ∩ B) ≤ ENNReal.ofReal s) :
    ∫⁻ x in B, ‖g x‖ₑ ^ 2 ≤ ENNReal.ofReal (s / (2 : ℝ) ^ n) * ∫⁻ x, ‖g x‖ₑ ^ 2 := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := zpow_pos (by norm_num) n
  rw [← lintegral_indicator hBm,
    lintegral_eq_tsum_dyadicIco n (fun x => B.indicator (fun x => ‖g x‖ₑ ^ 2) x),
    lintegral_eq_tsum_dyadicIco n (fun x => ‖g x‖ₑ ^ 2), ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun m => ?_
  rw [setLIntegral_indicator hBm]
  set x₀ : ℝ := (2 : ℝ) ^ n * m with hx₀
  have hx₀m : x₀ ∈ dyadicIco n m := ⟨le_rfl, by rw [hx₀]; nlinarith⟩
  have e1 : ∫⁻ x in B ∩ dyadicIco n m, ‖g x‖ₑ ^ 2 =
      ‖g x₀‖ₑ ^ 2 * volume (dyadicIco n m ∩ B) := by
    rw [setLIntegral_congr_fun (hBm.inter (measurableSet_dyadicIco n m))
      (fun x hx => by rw [hconst.eq_of_mem hx.2 hx₀m]), lintegral_const,
      Measure.restrict_apply_univ, Set.inter_comm]
  have e2 : ∫⁻ x in dyadicIco n m, ‖g x‖ₑ ^ 2 = ‖g x₀‖ₑ ^ 2 * ENNReal.ofReal ((2 : ℝ) ^ n) := by
    rw [setLIntegral_congr_fun (measurableSet_dyadicIco n m)
      (fun x hx => by rw [hconst.eq_of_mem hx hx₀m]), lintegral_const,
      Measure.restrict_apply_univ, volume_dyadicIco]
  rw [e1, e2]
  calc ‖g x₀‖ₑ ^ 2 * volume (dyadicIco n m ∩ B) ≤ ‖g x₀‖ₑ ^ 2 * ENNReal.ofReal s :=
        mul_le_mul_right (hB m) _
    _ = ENNReal.ofReal (s / (2 : ℝ) ^ n) * (‖g x₀‖ₑ ^ 2 * ENNReal.ofReal ((2 : ℝ) ^ n)) := by
        have : ENNReal.ofReal s =
            ENNReal.ofReal (s / (2 : ℝ) ^ n) * ENNReal.ofReal ((2 : ℝ) ^ n) := by
          rw [← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ h2.ne']
        rw [this]
        ring

/-- **Translation estimate**: for `g` constant on the dyadic intervals of length `2^n`,
`‖g(· - t) - g‖₂² ≤ 4 (|t| / 2^n) ‖g‖₂²`. -/
theorem lintegral_sq_translate_sub_le {n : ℤ} {g : ℝ → ℂ} (hg : Measurable g)
    (hconst : ConstOnDyadic n g) (t : ℝ) :
    ∫⁻ x, ‖g (x - t) - g x‖ₑ ^ 2 ≤
      ENNReal.ofReal (4 * (|t| / (2 : ℝ) ^ n)) * ∫⁻ x, ‖g x‖ₑ ^ 2 := by
  have hBm := measurableSet_crossSet n t
  set B := crossSet n t with hB
  have hpt : ∀ x, ‖g (x - t) - g x‖ₑ ^ 2 ≤
      B.indicator (fun x => 2 * ‖g (x - t)‖ₑ ^ 2 + 2 * ‖g x‖ₑ ^ 2) x := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
      exact enorm_sub_sq_le _ _
    · rw [Set.indicator_of_notMem hx]
      have : g (x - t) = g x := hconst _ _ (by simpa [hB, crossSet] using hx)
      rw [this]
      simp
  have hm1 : Measurable fun x => ‖g (x - t)‖ₑ ^ 2 :=
    (hg.comp (measurable_id.sub_const t)).enorm.pow_const 2
  have hm2 : Measurable fun x => ‖g x‖ₑ ^ 2 := hg.enorm.pow_const 2
  -- the two pieces
  have hB1 : ∫⁻ x in B, ‖g x‖ₑ ^ 2 ≤ ENNReal.ofReal (|t| / (2 : ℝ) ^ n) * ∫⁻ x, ‖g x‖ₑ ^ 2 :=
    setLIntegral_sq_le_of_inter hconst hBm (abs_nonneg t)
      (fun m => volume_dyadicIco_inter_crossSet_le n m t)
  have hB2 : ∫⁻ x in B, ‖g (x - t)‖ₑ ^ 2 ≤
      ENNReal.ofReal (|t| / (2 : ℝ) ^ n) * ∫⁻ x, ‖g x‖ₑ ^ 2 := by
    have h1 := setLIntegral_sq_le_of_inter hconst (measurableSet_crossSet n (-t))
      (abs_nonneg (-t)) (fun m => volume_dyadicIco_inter_crossSet_le n m (-t))
    rw [abs_neg] at h1
    refine le_trans (le_of_eq ?_) h1
    rw [← lintegral_indicator hBm, ← lintegral_indicator (measurableSet_crossSet n (-t))]
    rw [← lintegral_sub_right_eq_self
      ((crossSet n (-t)).indicator (fun x => ‖g x‖ₑ ^ 2)) t]
    refine lintegral_congr fun x => ?_
    have : x ∈ B ↔ x - t ∈ crossSet n (-t) := by
      simp only [hB, crossSet, Set.mem_ofPred_eq, sub_neg_eq_add, sub_add_cancel]
      exact ne_comm
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (this.1 hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (this.2 h))]
  calc ∫⁻ x, ‖g (x - t) - g x‖ₑ ^ 2
      ≤ ∫⁻ x, B.indicator (fun x => 2 * ‖g (x - t)‖ₑ ^ 2 + 2 * ‖g x‖ₑ ^ 2) x :=
        lintegral_mono hpt
    _ = ∫⁻ x in B, (2 * ‖g (x - t)‖ₑ ^ 2 + 2 * ‖g x‖ₑ ^ 2) := lintegral_indicator hBm _
    _ = 2 * (∫⁻ x in B, ‖g (x - t)‖ₑ ^ 2) + 2 * ∫⁻ x in B, ‖g x‖ₑ ^ 2 := by
        rw [lintegral_add_left (hm1.const_mul 2), lintegral_const_mul _ hm1,
          lintegral_const_mul _ hm2]
    _ ≤ 2 * (ENNReal.ofReal (|t| / (2 : ℝ) ^ n) * ∫⁻ x, ‖g x‖ₑ ^ 2) +
        2 * (ENNReal.ofReal (|t| / (2 : ℝ) ^ n) * ∫⁻ x, ‖g x‖ₑ ^ 2) :=
        add_le_add (mul_le_mul_right hB2 _) (mul_le_mul_right hB1 _)
    _ = ENNReal.ofReal (4 * (|t| / (2 : ℝ) ^ n)) * ∫⁻ x, ‖g x‖ₑ ^ 2 := by
        rw [ENNReal.ofReal_mul (by norm_num), show ENNReal.ofReal 4 = 4 by norm_num]
        ring

/-! ### The fine-scale estimate -/

/-- `∫ |ψ_k(t)| |t| dt = 2^k ∫ |ψ(s)| |s| ds`. -/
theorem lintegral_enorm_schwartzScale_mul_abs (ψ : 𝓢(ℝ, ℂ)) (k : ℤ) :
    ∫⁻ t, ‖schwartzScale ψ k t‖ₑ * ENNReal.ofReal |t| =
      ENNReal.ofReal ((2 : ℝ) ^ k) * ∫⁻ s, ‖ψ s‖ₑ * ENNReal.ofReal |s| := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (-k) := by positivity
  have hmeas : Measurable fun s : ℝ => ‖ψ s‖ₑ * ENNReal.ofReal |s| :=
    ψ.continuous.measurable.enorm.mul (ENNReal.measurable_ofReal.comp continuous_abs.measurable)
  have hpt : ∀ t : ℝ, ‖schwartzScale ψ k t‖ₑ * ENNReal.ofReal |t| =
      (fun s : ℝ => ‖ψ s‖ₑ * ENNReal.ofReal |s|) ((2 : ℝ) ^ (-k) * t) := by
    intro t
    simp only [enorm_schwartzScale, abs_mul, abs_of_pos h2]
    rw [ENNReal.ofReal_mul h2.le]
    ring
  simp_rw [hpt]
  rw [lintegral_comp_mul_left_of_pos h2 hmeas, zpow_neg, inv_inv]

/-- **Fine scales**: for `∫ ψ = 1` and `g ∈ L²` constant on the dyadic intervals of length
`2^{j-1}`, `‖A_k g - g‖₂² ≤ ‖ψ‖₁ · 8 · 2^{k-j} · (∫ |ψ(s)||s| ds) · ‖g‖₂²`. -/
theorem sqn_schwartzAvg_sub_le_fine (ψ : 𝓢(ℝ, ℂ)) (hψ : ∫ t, ψ t = 1) {j k : ℤ} {g : ℝ → ℂ}
    (hg : Measurable g) (hgL : MemLp g 2 volume) (hconst : ConstOnDyadic (j - 1) g) :
    ∫⁻ x, ‖schwartzAvg ψ k g x - g x‖ₑ ^ 2 ≤
      (∫⁻ t, ‖ψ t‖ₑ) * (ENNReal.ofReal (8 * (2 : ℝ) ^ (k - j)) *
        ∫⁻ s, ‖ψ s‖ₑ * ENNReal.ofReal |s|) * ∫⁻ y, ‖g y‖ₑ ^ 2 := by
  have hgsq := lintegral_sq_lt_top_of_memLp hgL
  set w : ℝ → ℝ≥0∞ := fun t => ‖schwartzScale ψ k t‖ₑ with hw
  have hwm : Measurable w := (measurable_schwartzScale ψ k).enorm
  have hwint : Integrable (schwartzScale ψ k) :=
    ⟨(continuous_schwartzScale ψ k).aestronglyMeasurable, lintegral_enorm_schwartzScale_lt_top ψ k⟩
  have hw1 : ∫⁻ t, w t = ∫⁻ t, ‖ψ t‖ₑ := lintegral_enorm_schwartzScale ψ k
  -- Step 1: the integral formula
  have hform : ∀ x, schwartzAvg ψ k g x - g x =
      ∫ t, schwartzScale ψ k t * (g (x - t) - g x) := by
    intro x
    have hFi := integrable_schwartzScale_mul ψ k hg hgsq x
    have hi1 : Integrable (fun t => schwartzScale ψ k t * g (x - t)) := by
      have := hFi.comp_sub_left x
      simpa only [sub_sub_cancel] using this
    have hi2 : Integrable (fun t => schwartzScale ψ k t * g x) := hwint.mul_const _
    have h1 : schwartzAvg ψ k g x = ∫ t, schwartzScale ψ k t * g (x - t) := by
      unfold schwartzAvg
      rw [← integral_sub_left_eq_self (fun t => schwartzScale ψ k t * g (x - t)) volume x]
      simp only [sub_sub_cancel]
    have h2 : g x = ∫ t, schwartzScale ψ k t * g x := by
      rw [integral_mul_const, integral_schwartzScale, hψ, one_mul]
    conv_lhs => rw [h1, h2]
    rw [← integral_sub hi1 hi2]
    simp only [mul_sub]
  -- Step 2 and 3: Cauchy-Schwarz in `t`
  have hpt : ∀ x, ‖schwartzAvg ψ k g x - g x‖ₑ ^ 2 ≤
      (∫⁻ t, ‖ψ t‖ₑ) * ∫⁻ t, w t * ‖g (x - t) - g x‖ₑ ^ 2 := by
    intro x
    have hHm : Measurable fun t => ‖g (x - t) - g x‖ₑ :=
      ((hg.comp (measurable_const.sub measurable_id)).sub measurable_const).enorm
    have h1 : ‖schwartzAvg ψ k g x - g x‖ₑ ≤ ∫⁻ t, w t * ‖g (x - t) - g x‖ₑ := by
      rw [hform x]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      simp only [enorm_mul, hw]
    calc ‖schwartzAvg ψ k g x - g x‖ₑ ^ 2 ≤ (∫⁻ t, w t * ‖g (x - t) - g x‖ₑ) ^ 2 :=
          pow_le_pow_left' h1 2
      _ ≤ (∫⁻ t, w t) * ∫⁻ t, w t * ‖g (x - t) - g x‖ₑ ^ 2 := lintegral_mul_sq_le hwm hHm
      _ = _ := by rw [hw1]
  -- Step 4: integrate in `x`, swap, translation estimate
  have hjm : Measurable (Function.uncurry fun (x t : ℝ) => w t * ‖g (x - t) - g x‖ₑ ^ 2) := by
    have h1 : Measurable fun p : ℝ × ℝ => w p.2 := hwm.comp measurable_snd
    have h2 : Measurable fun p : ℝ × ℝ => ‖g (p.1 - p.2) - g p.1‖ₑ ^ 2 :=
      (((hg.comp (measurable_fst.sub measurable_snd)).sub (hg.comp measurable_fst)).enorm).pow_const
        2
    exact h1.mul h2
  have hl : (8 : ℝ) * (2 : ℝ) ^ (k - j) = 4 * (2 : ℝ) ^ k / (2 : ℝ) ^ (j - 1) := by
    rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
    field_simp
    ring
  calc ∫⁻ x, ‖schwartzAvg ψ k g x - g x‖ₑ ^ 2
      ≤ ∫⁻ x, (∫⁻ t, ‖ψ t‖ₑ) * ∫⁻ t, w t * ‖g (x - t) - g x‖ₑ ^ 2 := lintegral_mono hpt
    _ = (∫⁻ t, ‖ψ t‖ₑ) * ∫⁻ x, ∫⁻ t, w t * ‖g (x - t) - g x‖ₑ ^ 2 :=
        lintegral_const_mul' _ _ (lintegral_enorm_schwartz_lt_top ψ).ne
    _ = (∫⁻ t, ‖ψ t‖ₑ) * ∫⁻ t, ∫⁻ x, w t * ‖g (x - t) - g x‖ₑ ^ 2 := by
        rw [lintegral_lintegral_swap hjm.aemeasurable]
    _ ≤ (∫⁻ t, ‖ψ t‖ₑ) * ∫⁻ t, w t * (ENNReal.ofReal (4 * (|t| / (2 : ℝ) ^ (j - 1))) *
          ∫⁻ y, ‖g y‖ₑ ^ 2) := by
        refine mul_le_mul_right (lintegral_mono fun t => ?_) _
        have hmt : Measurable fun x => ‖g (x - t) - g x‖ₑ ^ 2 :=
          (((hg.comp (measurable_id.sub_const t)).sub hg).enorm).pow_const 2
        rw [lintegral_const_mul _ hmt]
        exact mul_le_mul_right (lintegral_sq_translate_sub_le hg hconst t) _
    _ = (∫⁻ t, ‖ψ t‖ₑ) * (ENNReal.ofReal (8 * (2 : ℝ) ^ (k - j)) *
          ∫⁻ s, ‖ψ s‖ₑ * ENNReal.ofReal |s|) * ∫⁻ y, ‖g y‖ₑ ^ 2 := by
        have h4 : ∀ t : ℝ, w t * (ENNReal.ofReal (4 * (|t| / (2 : ℝ) ^ (j - 1))) *
            ∫⁻ y, ‖g y‖ₑ ^ 2) = (ENNReal.ofReal (4 / (2 : ℝ) ^ (j - 1)) *
              ∫⁻ y, ‖g y‖ₑ ^ 2) * (w t * ENNReal.ofReal |t|) := by
          intro t
          have : 4 * (|t| / (2 : ℝ) ^ (j - 1)) = 4 / (2 : ℝ) ^ (j - 1) * |t| := by ring
          rw [this, ENNReal.ofReal_mul (by positivity)]
          ring
        simp_rw [h4]
        have hK : ∫⁻ t, w t * ENNReal.ofReal |t| =
            ENNReal.ofReal ((2 : ℝ) ^ k) * ∫⁻ s, ‖ψ s‖ₑ * ENNReal.ofReal |s| :=
          lintegral_enorm_schwartzScale_mul_abs ψ k
        have hc : ENNReal.ofReal (8 * (2 : ℝ) ^ (k - j)) =
            ENNReal.ofReal (4 / (2 : ℝ) ^ (j - 1)) * ENNReal.ofReal ((2 : ℝ) ^ k) := by
          rw [hl, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
        have hmeas : Measurable fun t => w t * ENNReal.ofReal |t| :=
          hwm.mul (ENNReal.measurable_ofReal.comp continuous_abs.measurable)
        rw [lintegral_const_mul _ hmeas, hK, hc]
        ring

end PrimeCarleson.Proof.Oplus
