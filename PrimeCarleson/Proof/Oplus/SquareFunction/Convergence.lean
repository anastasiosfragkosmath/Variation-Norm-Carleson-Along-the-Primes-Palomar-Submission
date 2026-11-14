module

public import PrimeCarleson.Proof.Oplus.SquareFunction.Basic
public import PrimeCarleson.Proof.MswTransference.Schur
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# `L²` convergence of the dyadic averages

A preliminary of the proof of the square-function estimate of Jones–Kaufman–Rosenblatt–Wierdl
(proved here): for `f ∈ L²(ℝ)`,

* `tendsto_sqn_dyadicAvg_atTop`: `‖E_J f‖₂ → 0` as `J → +∞`;
* `tendsto_sqn_sub_dyadicAvg_atBot`: `‖f - E_{-J} f‖₂ → 0` as `J → +∞`.

Both are proved by approximation: `E_k` is a contraction (`sqn_dyadicAvg_le`), the first claim is
checked on functions supported in `[-R, R]` and the second on continuous functions of compact
support.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

open PrimeCarleson.Proof.Lepingle PrimeCarleson.Proof.MswTransference

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-! ### Elementary inequalities in `ℝ≥0∞` -/

/-- `‖a + b‖² ≤ 2‖a‖² + 2‖b‖²`. -/
theorem enorm_add_sq_le (a b : ℂ) : ‖a + b‖ₑ ^ 2 ≤ 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
  calc ‖a + b‖ₑ ^ 2 ≤ (‖a‖ₑ + ‖b‖ₑ) ^ 2 := pow_le_pow_left' (enorm_add_le a b) 2
    _ ≤ 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
      have := ENNReal.rpow_add_le_mul_rpow_add_rpow ‖a‖ₑ ‖b‖ₑ (p := 2) (by norm_num)
      simp only [ENNReal.rpow_two] at this
      norm_num at this
      rw [mul_add] at this
      exact this

/-- Cauchy-Schwarz in `ℝ≥0∞`: `(∫ k G)² ≤ (∫ k)(∫ k G²)`. -/
theorem lintegral_mul_sq_le {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} {k G : Y → ℝ≥0∞}
    (hk : Measurable k) (hG : Measurable G) :
    (∫⁻ y, k y * G y ∂ν) ^ 2 ≤ (∫⁻ y, k y ∂ν) * ∫⁻ y, k y * G y ^ 2 ∂ν := by
  have h := lintegral_mul_rpow_le_rpow_mul_lintegral (ν := ν) hk hG (p := 2) (by norm_num)
  have e : (2 : ℝ) - 1 = 1 := by norm_num
  rw [e, ENNReal.rpow_one] at h
  simpa [ENNReal.rpow_two] using h

/-- Approximation principle: a sequence that is, for every `ε > 0`, bounded by a null sequence
plus a constant `≤ ε` tends to `0`. -/
theorem tendsto_zero_of_forall_approx {S : ℕ → ℝ≥0∞}
    (h : ∀ ε : ℝ≥0∞, 0 < ε → ∃ (T : ℕ → ℝ≥0∞) (B : ℝ≥0∞),
      Tendsto T atTop (𝓝 0) ∧ B ≤ ε ∧ ∀ J, S J ≤ T J + B) :
    Tendsto S atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨T, B, hT, hB, hS⟩ := h (ε / 2) (ENNReal.half_pos hε.ne')
  have := (ENNReal.tendsto_nhds_zero.1 hT) (ε / 2) (ENNReal.half_pos hε.ne')
  filter_upwards [this] with J hJ
  calc S J ≤ T J + B := hS J
    _ ≤ ε / 2 + ε / 2 := add_le_add hJ hB
    _ = ε := ENNReal.add_halves ε

/-- `2^{-J} → 0` as `J → ∞`, in `ℝ≥0∞`. -/
theorem tendsto_ofReal_two_zpow_neg :
    Tendsto (fun J : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (-(J : ℤ)))) atTop (𝓝 0) := by
  have h : Tendsto (fun J : ℕ => ((1 : ℝ) / 2) ^ J) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h2 := ENNReal.tendsto_ofReal h
  simp only [ENNReal.ofReal_zero] at h2
  refine h2.congr fun J => ?_
  congr 1
  rw [zpow_neg, zpow_natCast, one_div, inv_pow]

/-! ### The part of `E_k f` coming from a bounded window -/

/-- The square norm of `E_k f` on one dyadic interval. -/
theorem setLIntegral_sq_dyadicAvg (f : ℝ → ℂ) (k m : ℤ) :
    ∫⁻ x in dyadicIco k m, ‖dyadicAvg f k x‖ₑ ^ 2 =
      ENNReal.ofReal ((2 : ℝ) ^ (-k)) * ‖∫ x in dyadicIco k m, f x‖ₑ ^ 2 := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  have hav : ∀ x ∈ dyadicIco k m, dyadicAvg f k x = ((2 : ℝ) ^ k)⁻¹ • ∫ y in dyadicIco k m, f y :=
    fun x hx => dyadicAvg_of_mem hx
  have hab : ENNReal.ofReal ((2 : ℝ) ^ (-k)) * ENNReal.ofReal ((2 : ℝ) ^ k) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), ← zpow_add₀ (by norm_num), neg_add_cancel,
      zpow_zero, ENNReal.ofReal_one]
  have hn : ‖((2 : ℝ) ^ k)⁻¹‖ₑ = ENNReal.ofReal ((2 : ℝ) ^ (-k)) := by
    rw [Real.enorm_eq_ofReal (inv_nonneg.2 h2.le), zpow_neg]
  rw [setLIntegral_congr_fun (measurableSet_dyadicIco k m)
    (fun x hx => by rw [hav x hx]), lintegral_const, Measure.restrict_apply_univ,
    volume_dyadicIco, enorm_smul, hn]
  calc (ENNReal.ofReal ((2 : ℝ) ^ (-k)) * ‖∫ y in dyadicIco k m, f y‖ₑ) ^ 2 *
        ENNReal.ofReal ((2 : ℝ) ^ k)
      = ENNReal.ofReal ((2 : ℝ) ^ (-k)) * (ENNReal.ofReal ((2 : ℝ) ^ (-k)) *
          ENNReal.ofReal ((2 : ℝ) ^ k)) * ‖∫ y in dyadicIco k m, f y‖ₑ ^ 2 := by ring
    _ = _ := by rw [hab, mul_one]

/-- Cauchy-Schwarz for the integral over `I` of a function supported in `S`. -/
theorem enorm_setIntegral_sq_le {f : ℝ → ℂ} (hf : Measurable f) {I S : Set ℝ}
    (hS : MeasurableSet S) (hsupp : ∀ x, x ∉ S → f x = 0) :
    ‖∫ x in I, f x‖ₑ ^ 2 ≤ volume (I ∩ S) * ∫⁻ x in I, ‖f x‖ₑ ^ 2 := by
  have h1 : ‖∫ x in I, f x‖ₑ ≤ ∫⁻ x in I, ‖f x‖ₑ := enorm_integral_le_lintegral_enorm f
  have h2 : ∫⁻ x in I, ‖f x‖ₑ = ∫⁻ x in I, S.indicator (1 : ℝ → ℝ≥0∞) x * ‖f x‖ₑ := by
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ S
    · simp [hx]
    · simp [hx, hsupp x hx]
  have h3 := lintegral_mul_sq_le (ν := volume.restrict I) (k := S.indicator (1 : ℝ → ℝ≥0∞))
    (G := fun x => ‖f x‖ₑ) (measurable_one.indicator hS) hf.enorm
  have h4 : ∫⁻ x in I, S.indicator (1 : ℝ → ℝ≥0∞) x = volume (I ∩ S) := by
    rw [lintegral_indicator_one hS, Measure.restrict_apply hS, Set.inter_comm]
  have h5 : ∫⁻ x in I, S.indicator (1 : ℝ → ℝ≥0∞) x * ‖f x‖ₑ ^ 2 = ∫⁻ x in I, ‖f x‖ₑ ^ 2 := by
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ S
    · simp [hx]
    · simp [hx, hsupp x hx]
  calc ‖∫ x in I, f x‖ₑ ^ 2 ≤ (∫⁻ x in I, ‖f x‖ₑ) ^ 2 := pow_le_pow_left' h1 2
    _ = (∫⁻ x in I, S.indicator (1 : ℝ → ℝ≥0∞) x * ‖f x‖ₑ) ^ 2 := by rw [h2]
    _ ≤ _ := h3
    _ = _ := by rw [h4, h5]

/-- If `f` vanishes outside `S` and `S` meets each interval of length `2^k` in a set of measure
`≤ M`, then `‖E_k f‖₂² ≤ 2^{-k} M ‖f‖₂²`. -/
theorem sqn_dyadicAvg_le_of_support {f : ℝ → ℂ} (hfm : Measurable f) {S : Set ℝ}
    (hS : MeasurableSet S) (hsupp : ∀ x, x ∉ S → f x = 0) (k : ℤ) {M : ℝ≥0∞}
    (hM : ∀ m, volume (dyadicIco k m ∩ S) ≤ M) :
    ∫⁻ x, ‖dyadicAvg f k x‖ₑ ^ 2 ≤ ENNReal.ofReal ((2 : ℝ) ^ (-k)) * M * ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  rw [lintegral_eq_tsum_dyadicIco k (fun x => ‖dyadicAvg f k x‖ₑ ^ 2),
    lintegral_eq_tsum_dyadicIco k (fun x => ‖f x‖ₑ ^ 2), ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun m => ?_
  rw [setLIntegral_sq_dyadicAvg, mul_assoc]
  refine mul_le_mul_right ?_ _
  exact (enorm_setIntegral_sq_le hfm hS hsupp).trans (mul_le_mul_left (hM m) _)

/-- The tails `∫_{|x|>R} |f|²` of an `L²` function tend to `0`. -/
theorem tendsto_tail_sq {f : ℝ → ℂ} (hfm : Measurable f) (hfin : ∫⁻ x, ‖f x‖ₑ ^ 2 < ∞) :
    Tendsto (fun R : ℕ => ∫⁻ x in (Icc (-(R : ℝ)) R)ᶜ, ‖f x‖ₑ ^ 2) atTop (𝓝 0) := by
  have hmeas : ∀ R : ℕ, MeasurableSet (Icc (-(R : ℝ)) R)ᶜ := fun R => measurableSet_Icc.compl
  have := tendsto_lintegral_of_dominated_convergence (μ := volume)
    (F := fun (R : ℕ) x => (Icc (-(R : ℝ)) R)ᶜ.indicator (fun x => ‖f x‖ₑ ^ 2) x)
    (f := fun _ => 0) (fun x => ‖f x‖ₑ ^ 2)
    (fun R => (hfm.enorm.pow_const 2).indicator (hmeas R))
    (fun R => Filter.Eventually.of_forall fun x => Set.indicator_le_self _ _ x)
    hfin.ne (Filter.Eventually.of_forall fun x => ?_)
  · simp only [lintegral_zero] at this
    refine this.congr fun R => ?_
    rw [lintegral_indicator (hmeas R)]
  · refine tendsto_atTop_of_eventually_const (i₀ := ⌈|x|⌉₊) fun R hR => ?_
    have hx : x ∈ Icc (-(R : ℝ)) R := by
      have h1 : |x| ≤ R := (Nat.le_ceil _).trans (by exact_mod_cast hR)
      exact ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
    simp [hx]

/-- **First half**: `‖E_J f‖₂ → 0` as `J → +∞`. -/
theorem tendsto_sqn_dyadicAvg_atTop {f : ℝ → ℂ} (hfm : Measurable f) (hf : MemLp f 2 volume) :
    Tendsto (fun J : ℕ => ∫⁻ x, ‖dyadicAvg f (J : ℤ) x‖ₑ ^ 2) atTop (𝓝 0) := by
  have hfin : ∫⁻ x, ‖f x‖ₑ ^ 2 < ∞ := lintegral_sq_lt_top_of_memLp hf
  have htail := tendsto_tail_sq hfm hfin
  refine tendsto_zero_of_forall_approx fun ε hε => ?_
  obtain ⟨R, hR⟩ := ((ENNReal.tendsto_nhds_zero.1 htail) (ε / 2)
    (ENNReal.half_pos hε.ne')).exists
  set s : Set ℝ := Icc (-(R : ℝ)) R with hs
  have hsm : MeasurableSet s := measurableSet_Icc
  set C : ℝ≥0∞ := ENNReal.ofReal (2 * R) * ∫⁻ x, ‖f x‖ₑ ^ 2 with hC
  have hCfin : C ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne
  refine ⟨fun J => 2 * (ENNReal.ofReal ((2 : ℝ) ^ (-(J : ℤ))) * C),
    2 * ∫⁻ x in sᶜ, ‖f x‖ₑ ^ 2, ?_, ?_, fun J => ?_⟩
  · have := (ENNReal.Tendsto.mul_const tendsto_ofReal_two_zpow_neg (Or.inr hCfin))
    have h2 := ENNReal.Tendsto.const_mul this (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ∞))
    simpa using h2
  · calc 2 * ∫⁻ x in sᶜ, ‖f x‖ₑ ^ 2 ≤ 2 * (ε / 2) := mul_le_mul_right hR _
      _ = ε := ENNReal.mul_div_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  · -- the splitting `f = f₁ + f₂`
    set f₁ : ℝ → ℂ := s.indicator f with hf₁
    set f₂ : ℝ → ℂ := sᶜ.indicator f with hf₂
    have hsplit : f₁ + f₂ = f := Set.indicator_self_add_compl s f
    have hf₁m : Measurable f₁ := hfm.indicator hsm
    have hf₂m : Measurable f₂ := hfm.indicator hsm.compl
    have hf₁L : MemLp f₁ 2 volume := hf.indicator hsm.nullMeasurableSet
    have hf₂L : MemLp f₂ 2 volume := hf.indicator hsm.compl.nullMeasurableSet
    have hpt : ∀ x, ‖dyadicAvg f (J : ℤ) x‖ₑ ^ 2 ≤
        2 * ‖dyadicAvg f₁ (J : ℤ) x‖ₑ ^ 2 + 2 * ‖dyadicAvg f₂ (J : ℤ) x‖ₑ ^ 2 := fun x => by
      have := dyadicAvg_add hf₁L hf₂L (J : ℤ) x
      rw [hsplit] at this
      rw [this]
      exact enorm_add_sq_le _ _
    have h1 : ∫⁻ x, ‖dyadicAvg f₁ (J : ℤ) x‖ₑ ^ 2 ≤
        ENNReal.ofReal ((2 : ℝ) ^ (-(J : ℤ))) * C := by
      have hM : ∀ m, volume (dyadicIco (J : ℤ) m ∩ s) ≤ ENNReal.ofReal (2 * R) := by
        intro m
        refine (measure_mono inter_subset_right).trans ?_
        rw [hs, Real.volume_Icc]
        refine le_of_eq (congrArg ENNReal.ofReal (by ring))
      have := sqn_dyadicAvg_le_of_support hf₁m hsm
        (fun x hx => by simp [hf₁, Set.indicator_of_notMem hx]) (J : ℤ) hM
      refine this.trans ?_
      rw [mul_assoc]
      refine mul_le_mul_right (mul_le_mul_right (lintegral_mono fun x => ?_) _) _
      refine pow_le_pow_left' ?_ 2
      by_cases hx : x ∈ s
      · simp [hf₁, hx]
      · simp [hf₁, hx]
    have h2 : ∫⁻ x, ‖dyadicAvg f₂ (J : ℤ) x‖ₑ ^ 2 ≤ ∫⁻ x in sᶜ, ‖f x‖ₑ ^ 2 := by
      refine (sqn_dyadicAvg_le hf₂L (J : ℤ)).trans (le_of_eq ?_)
      rw [← lintegral_indicator hsm.compl]
      refine lintegral_congr fun x => ?_
      by_cases hx : x ∈ sᶜ
      · simp [hf₂, hx]
      · simp [hf₂, hx]
    calc ∫⁻ x, ‖dyadicAvg f (J : ℤ) x‖ₑ ^ 2
        ≤ ∫⁻ x, (2 * ‖dyadicAvg f₁ (J : ℤ) x‖ₑ ^ 2 + 2 * ‖dyadicAvg f₂ (J : ℤ) x‖ₑ ^ 2) :=
          lintegral_mono hpt
      _ = 2 * (∫⁻ x, ‖dyadicAvg f₁ (J : ℤ) x‖ₑ ^ 2) +
            2 * ∫⁻ x, ‖dyadicAvg f₂ (J : ℤ) x‖ₑ ^ 2 := by
          rw [lintegral_add_left (((measurable_dyadicAvg f₁ _).enorm.pow_const 2).const_mul 2),
            lintegral_const_mul _ ((measurable_dyadicAvg f₁ _).enorm.pow_const 2),
            lintegral_const_mul _ ((measurable_dyadicAvg f₂ _).enorm.pow_const 2)]
      _ ≤ 2 * (ENNReal.ofReal ((2 : ℝ) ^ (-(J : ℤ))) * C) + 2 * ∫⁻ x in sᶜ, ‖f x‖ₑ ^ 2 :=
          add_le_add (mul_le_mul_right h1 _) (mul_le_mul_right h2 _)

/-! ### `E_{-J} f → f` -/

/-- Small positive `δ` with `δ² c ≤ ε`. -/
theorem exists_pos_ofReal_mul_sq_le {ε : ℝ≥0∞} (hε : 0 < ε) (c : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal (δ ^ 2 * c) ≤ ε := by
  have h1 : Tendsto (fun δ : ℝ => δ ^ 2 * c) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun δ : ℝ => δ ^ 2 * c) := by fun_prop
    simpa using hcont.tendsto 0
  have h2 : Tendsto (fun δ : ℝ => ENNReal.ofReal (δ ^ 2 * c)) (𝓝[>] 0) (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (h1.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ))))
    simpa using this
  obtain ⟨δ, hδ1, hδ2⟩ := ((h2.eventually (gt_mem_nhds hε)).and self_mem_nhdsWithin).exists
  exact ⟨δ, hδ2, hδ1.le⟩

/-- If `g` varies by at most `δ` on scale `2^k`, then `E_k g` is `δ`-close to `g` pointwise. -/
theorem norm_sub_dyadicAvg_le {g : ℝ → ℂ} (hg : MemLp g 2 volume) {k : ℤ} {δ : ℝ}
    (h : ∀ y z : ℝ, |y - z| < (2 : ℝ) ^ k → ‖g y - g z‖ ≤ δ) (x : ℝ) :
    ‖g x - dyadicAvg g k x‖ ≤ δ := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  set m := dyadicIdx k x with hm
  have hint := integrableOn_dyadicIco_of_memLp_two hg k m
  have hvolfin : volume (dyadicIco k m) ≠ ∞ := by
    rw [volume_dyadicIco]; exact ENNReal.ofReal_ne_top
  have hvol : (volume (dyadicIco k m)).toReal = (2 : ℝ) ^ k := by
    rw [volume_dyadicIco, ENNReal.toReal_ofReal h2.le]
  have key : g x - dyadicAvg g k x =
      ((2 : ℝ) ^ k)⁻¹ • ∫ y in dyadicIco k m, (g x - g y) := by
    rw [integral_sub (integrableOn_const hvolfin) hint, setIntegral_const, measureReal_def, hvol,
      smul_sub, smul_smul, inv_mul_cancel₀ h2.ne', one_smul]
    rfl
  have hI : ∀ y ∈ dyadicIco k m, ‖g x - g y‖ ≤ δ := by
    intro y hy
    have hx : x ∈ dyadicIco k m := mem_dyadicIco_dyadicIdx k x
    refine h x y ?_
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    rw [abs_sub_lt_iff]
    constructor <;> nlinarith
  have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := dyadicIco k m)
    (f := fun y => g x - g y) hvolfin.lt_top hI
  rw [key, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 h2.le)]
  rw [measureReal_def, hvol] at hb
  calc ((2 : ℝ) ^ k)⁻¹ * ‖∫ y in dyadicIco k m, (g x - g y)‖
      ≤ ((2 : ℝ) ^ k)⁻¹ * (δ * (2 : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.2 h2.le)
    _ = δ := by field_simp

/-- For continuous `g` of compact support, `‖g - E_{-J} g‖₂ → 0`. -/
theorem tendsto_sqn_sub_dyadicAvg_of_continuous {g : ℝ → ℂ} (hg : Continuous g)
    (hc : HasCompactSupport g) (hL : MemLp g 2 volume) :
    Tendsto (fun J : ℕ => ∫⁻ x, ‖g x - dyadicAvg g (-(J : ℤ)) x‖ₑ ^ 2) atTop (𝓝 0) := by
  have hUC := hc.uniformContinuous_of_continuous hg
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hc.isCompact.isBounded
  have hR0 : ∀ y, R < |y| → g y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun hmem => by
      have := hR hmem
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
      linarith
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := exists_pos_ofReal_mul_sq_le hε (2 * R + 2)
  obtain ⟨η, hη, hηδ⟩ := Metric.uniformContinuous_iff.1 hUC δ hδ
  have hev : ∀ᶠ J : ℕ in atTop, (2 : ℝ) ^ (-(J : ℤ)) < min η 1 := by
    have h : Tendsto (fun J : ℕ => ((1 : ℝ) / 2) ^ J) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    filter_upwards [h.eventually (gt_mem_nhds (lt_min hη one_pos))] with J hJ
    have e : (2 : ℝ) ^ (-(J : ℤ)) = ((1 : ℝ) / 2) ^ J := by
      rw [zpow_neg, zpow_natCast, one_div, inv_pow]
    rwa [e]
  filter_upwards [hev] with J hJ
  set k : ℤ := -(J : ℤ) with hk
  have hk1 : (2 : ℝ) ^ k < 1 := hJ.trans_le (min_le_right _ _)
  have hkη : (2 : ℝ) ^ k < η := hJ.trans_le (min_le_left _ _)
  have hclose : ∀ x, ‖g x - dyadicAvg g k x‖ ≤ δ := fun x =>
    norm_sub_dyadicAvg_le hL (fun y z hyz => by
      have := hηδ (a := y) (b := z) (by rw [Real.dist_eq]; exact hyz.trans hkη)
      rw [dist_eq_norm] at this
      exact this.le) x
  have hfar : ∀ x, R + 1 < |x| → g x - dyadicAvg g k x = 0 := by
    intro x hx
    have hgx : g x = 0 := hR0 x (by linarith)
    have hI : ∀ y ∈ dyadicIco k (dyadicIdx k x), g y = 0 := by
      intro y hy
      have hx' := mem_dyadicIco_dyadicIdx k x
      have hdist : |x - y| < (2 : ℝ) ^ k := by
        obtain ⟨hx1, hx2⟩ := hx'
        obtain ⟨hy1, hy2⟩ := hy
        rw [abs_sub_lt_iff]
        constructor <;> nlinarith
      refine hR0 y ?_
      have := abs_sub_abs_le_abs_sub x y
      linarith
    have : dyadicAvg g k x = 0 := by
      simp only [dyadicAvg]
      rw [setIntegral_eq_zero_of_forall_eq_zero hI, smul_zero]
    rw [hgx, this, sub_zero]
  have hpt : ∀ x, ‖g x - dyadicAvg g k x‖ₑ ^ 2 ≤
      (Icc (-(R + 1)) (R + 1)).indicator (fun _ => ENNReal.ofReal δ ^ 2) x := by
    intro x
    by_cases hx : x ∈ Icc (-(R + 1)) (R + 1)
    · rw [Set.indicator_of_mem hx]
      refine pow_le_pow_left' ?_ 2
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hclose x)
    · rw [Set.indicator_of_notMem hx]
      have : R + 1 < |x| := by
        by_contra hcon
        exact hx (abs_le.1 (not_lt.1 hcon))
      rw [hfar x this]
      simp
  calc ∫⁻ x, ‖g x - dyadicAvg g k x‖ₑ ^ 2
      ≤ ∫⁻ x, (Icc (-(R + 1)) (R + 1)).indicator (fun _ => ENNReal.ofReal δ ^ 2) x :=
        lintegral_mono hpt
    _ = ENNReal.ofReal δ ^ 2 * ENNReal.ofReal (2 * R + 2) := by
        rw [lintegral_indicator measurableSet_Icc, lintegral_const, Measure.restrict_apply_univ,
          Real.volume_Icc]
        congr 2
        ring
    _ = ENNReal.ofReal (δ ^ 2 * (2 * R + 2)) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hδ.le]
    _ ≤ ε := hδε

/-- **Second half**: `‖f - E_{-J} f‖₂ → 0` as `J → +∞`. -/
theorem tendsto_sqn_sub_dyadicAvg_atBot {f : ℝ → ℂ} (hfm : Measurable f) (hf : MemLp f 2 volume) :
    Tendsto (fun J : ℕ => ∫⁻ x, ‖f x - dyadicAvg f (-(J : ℤ)) x‖ₑ ^ 2) atTop (𝓝 0) := by
  refine tendsto_zero_of_forall_approx fun ε hε => ?_
  obtain ⟨δ, hδ, hδε⟩ := exists_pos_ofReal_mul_sq_le hε 6
  obtain ⟨g, hgc, hgf, hgcont, hgL⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le
    (p := 2) ENNReal.ofNat_ne_top (ε := ENNReal.ofReal δ) (by simpa using hδ)
  have hgm : Measurable g := hgcont.measurable
  set A : ℝ≥0∞ := ∫⁻ x, ‖f x - g x‖ₑ ^ 2 with hA
  have hAle : A ≤ ENNReal.ofReal δ ^ 2 := by
    have h1 : A = eLpNorm (f - g) 2 volume ^ 2 :=
      lintegral_sq_eq_eLpNorm_sq (g := f - g) ((hf.sub hgL).aestronglyMeasurable)
    rw [h1]
    exact pow_le_pow_left' hgf 2
  refine ⟨fun J => 4 * ∫⁻ x, ‖g x - dyadicAvg g (-(J : ℤ)) x‖ₑ ^ 2, 6 * A, ?_, ?_, fun J => ?_⟩
  · have := ENNReal.Tendsto.const_mul (a := 4)
      (tendsto_sqn_sub_dyadicAvg_of_continuous hgcont hgc hgL) (Or.inr (by norm_num))
    simpa using this
  · calc 6 * A ≤ 6 * ENNReal.ofReal δ ^ 2 := mul_le_mul_right hAle _
      _ = ENNReal.ofReal (δ ^ 2 * 6) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hδ.le]
          simp [mul_comm]
      _ ≤ ε := hδε
  · set k : ℤ := -(J : ℤ) with hk
    have hpt : ∀ x, ‖f x - dyadicAvg f k x‖ₑ ^ 2 ≤
        4 * ‖f x - g x‖ₑ ^ 2 + 4 * ‖g x - dyadicAvg g k x‖ₑ ^ 2 +
          2 * ‖dyadicAvg (g - f) k x‖ₑ ^ 2 := by
      intro x
      have hE := dyadicAvg_sub hgL hf k x
      have e : f x - dyadicAvg f k x = ((f x - g x) + (g x - dyadicAvg g k x)) +
          dyadicAvg (g - f) k x := by rw [hE]; ring
      rw [e]
      calc ‖((f x - g x) + (g x - dyadicAvg g k x)) + dyadicAvg (g - f) k x‖ₑ ^ 2
          ≤ 2 * ‖(f x - g x) + (g x - dyadicAvg g k x)‖ₑ ^ 2 +
              2 * ‖dyadicAvg (g - f) k x‖ₑ ^ 2 := enorm_add_sq_le _ _
        _ ≤ 2 * (2 * ‖f x - g x‖ₑ ^ 2 + 2 * ‖g x - dyadicAvg g k x‖ₑ ^ 2) +
              2 * ‖dyadicAvg (g - f) k x‖ₑ ^ 2 :=
            add_le_add (mul_le_mul_right (enorm_add_sq_le _ _) _) le_rfl
        _ = 4 * ‖f x - g x‖ₑ ^ 2 + 4 * ‖g x - dyadicAvg g k x‖ₑ ^ 2 +
              2 * ‖dyadicAvg (g - f) k x‖ₑ ^ 2 := by ring
    have hm1 : Measurable fun x => ‖f x - g x‖ₑ ^ 2 := (hfm.sub hgm).enorm.pow_const 2
    have hm2 : Measurable fun x => ‖g x - dyadicAvg g k x‖ₑ ^ 2 :=
      (hgm.sub (measurable_dyadicAvg g k)).enorm.pow_const 2
    have hm3 : Measurable fun x => ‖dyadicAvg (g - f) k x‖ₑ ^ 2 :=
      (measurable_dyadicAvg (g - f) k).enorm.pow_const 2
    have hcontr : ∫⁻ x, ‖dyadicAvg (g - f) k x‖ₑ ^ 2 ≤ A := by
      refine (sqn_dyadicAvg_le (hgL.sub hf) k).trans (le_of_eq ?_)
      refine lintegral_congr fun x => ?_
      simp only [Pi.sub_apply]
      rw [enorm_sub_rev]
    calc ∫⁻ x, ‖f x - dyadicAvg f k x‖ₑ ^ 2
        ≤ ∫⁻ x, (4 * ‖f x - g x‖ₑ ^ 2 + 4 * ‖g x - dyadicAvg g k x‖ₑ ^ 2 +
            2 * ‖dyadicAvg (g - f) k x‖ₑ ^ 2) := lintegral_mono hpt
      _ = (4 * A + 4 * (∫⁻ x, ‖g x - dyadicAvg g k x‖ₑ ^ 2)) +
            2 * ∫⁻ x, ‖dyadicAvg (g - f) k x‖ₑ ^ 2 := by
          have hm12 : Measurable fun x => 4 * ‖f x - g x‖ₑ ^ 2 +
              4 * ‖g x - dyadicAvg g k x‖ₑ ^ 2 := (hm1.const_mul 4).add (hm2.const_mul 4)
          rw [lintegral_add_left hm12,
            lintegral_add_left (hm1.const_mul 4), lintegral_const_mul _ hm1,
            lintegral_const_mul _ hm2, lintegral_const_mul _ hm3]
      _ ≤ (4 * A + 4 * (∫⁻ x, ‖g x - dyadicAvg g k x‖ₑ ^ 2)) + 2 * A :=
          add_le_add le_rfl (mul_le_mul_right hcontr _)
      _ = 4 * (∫⁻ x, ‖g x - dyadicAvg g k x‖ₑ ^ 2) + 6 * A := by ring

end PrimeCarleson.Proof.Oplus
