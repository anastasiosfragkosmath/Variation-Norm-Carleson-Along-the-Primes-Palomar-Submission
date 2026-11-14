module

public import PrimeCarleson.Proof.Oplus.External.THGood
public import PrimeCarleson.Proof.Oplus.External.THSums

/-!
# The bad parts `b_J = (f₀ - ⨍_J f₀) 1_J` against a wave packet

Source: Grafakos–Tao–Terwilleger, L789–L1231 and L896-L920 (the estimates (122), (142), (132)).
For a packet `ψ` adapted to the dyadic
interval `I`
(`PacketBounds A I ψ`: `|ψ| ≲ |I|^{-1/2} ω^{-4}` and `|ψ'| ≲ |I|^{-3/2} ω^{-4}`,
`ω = 1 + |y - c(I)|/|I|`), `J ∈ czFam` inside `3 I_T` and `I ⊄ Ω_λ`:
`|⟨b_J, ψ⟩| ≤ 22 A λ √|I| m(I, J)` where `m = kerM` of `THSums.lean`:
mean zero of `b_J` gives the factor `(|J|/|I|)²` for `|J| ≤ |I|` (cancellation), the maximal
function bound at a point of `I` outside `Ω_λ` gives the factor `1` for `|J| > |I|`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- The bounds of a (modulated) wave packet adapted to the dyadic interval `I`:
`|ψ| ≤ A |I|^{-1/2} ω^{-4}`, `|ψ'| ≤ A |I|^{-3/2} ω^{-4}`, `ω = 1 + |y - c(I)|/|I|`. -/
structure PacketBounds (A : ℝ) (I : Dyadic) (ψ : ℝ → ℂ) : Prop where
  /-- `ψ` is differentiable. -/
  differentiable : Differentiable ℝ ψ
  /-- The size bound. -/
  bound0 : ∀ y, ‖ψ y‖ ≤ A * (√I.length)⁻¹ * (1 + |y - I.center| / I.length) ^ (-4 : ℤ)
  /-- The derivative bound. -/
  bound1 : ∀ y, ‖deriv ψ y‖ ≤
    A * (I.length * √I.length)⁻¹ * (1 + |y - I.center| / I.length) ^ (-4 : ℤ)

/-! ### Two general estimates for `∫_J b ψ̄` -/

/-- **Cancellation**: if `∫_J b = 0` and `|ψ'| ≤ D` on `J` then
`|∫_J b ψ̄| ≤ (|J|/2) D ∫_J |b|`. -/
theorem norm_integral_mul_conj_le_of_mean_zero {J : Dyadic} {b ψ : ℝ → ℂ} {D : ℝ}
    (hb : IntegrableOn b J.toSet) (hbψ : IntegrableOn (fun y => b y * conj (ψ y)) J.toSet)
    (hb0 : ∫ y in J.toSet, b y = 0)
    (hd : ∀ y ∈ J.toSet, DifferentiableAt ℝ ψ y) (hD : ∀ y ∈ J.toSet, ‖deriv ψ y‖ ≤ D) :
    ‖∫ y in J.toSet, b y * conj (ψ y)‖ ≤ J.length / 2 * D * ∫ y in J.toSet, ‖b y‖ := by
  have hc : J.center ∈ J.toSet := J.center_mem_toSet
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD _ hc)
  have hψ1 : ∀ y ∈ J.toSet, ‖ψ y - ψ J.center‖ ≤ J.length / 2 * D := by
    intro y hy
    have := (convex_Ico J.left J.right).norm_image_sub_le_of_norm_deriv_le hd hD hc hy
    have h2 := Dyadic.abs_sub_center_le hy
    calc ‖ψ y - ψ J.center‖ ≤ D * ‖y - J.center‖ := by simpa using this
      _ ≤ D * (J.length / 2) := by rw [Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left h2 hD0
      _ = J.length / 2 * D := by ring
  have hbc : IntegrableOn (fun y => b y * conj (ψ J.center)) J.toSet := hb.mul_const _
  have hconst : ∫ y in J.toSet, b y * conj (ψ J.center) = 0 := by
    rw [integral_mul_const, hb0, zero_mul]
  have hsplit : ∫ y in J.toSet, b y * conj (ψ y) =
      ∫ y in J.toSet, b y * (conj (ψ y) - conj (ψ J.center)) := by
    have : ∀ y, b y * (conj (ψ y) - conj (ψ J.center)) =
        b y * conj (ψ y) - b y * conj (ψ J.center) := fun y => by ring
    simp_rw [this]
    rw [integral_sub hbψ hbc, hconst, sub_zero]
  rw [hsplit]
  have hg : IntegrableOn (fun y => ‖b y‖ * (J.length / 2 * D)) J.toSet := hb.norm.mul_const _
  refine (norm_integral_le_of_norm_le hg ?_).trans (le_of_eq ?_)
  · refine (ae_restrict_iff' J.measurableSet_toSet).2 (Filter.Eventually.of_forall fun y hy => ?_)
    rw [norm_mul, ← map_sub, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left (hψ1 y hy) (norm_nonneg _)
  · rw [integral_mul_const]; ring

/-! ### Powers of the weight -/

/-- `ω^{-4} ≤ a^{-2}` for `1 ≤ a ≤ ω`. -/
theorem zpow_neg_four_le_neg_two {a ω : ℝ} (ha : 1 ≤ a) (h : a ≤ ω) :
    ω ^ (-4 : ℤ) ≤ a ^ (-2 : ℤ) := by
  have h0 : 0 < a := by linarith
  have h1 : 0 < ω := by linarith
  rw [zpow_neg, zpow_neg, zpow_ofNat, zpow_ofNat]
  have h2 : a ^ 2 ≤ ω ^ 4 := by
    calc a ^ 2 ≤ ω ^ 2 := pow_le_pow_left₀ h0.le h 2
      _ ≤ ω ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  exact inv_anti₀ (by positivity) h2

/-- `ω^{-4} ≤ a^{-2} ω^{-2}` for `0 < a ≤ ω`. -/
theorem zpow_neg_four_le_mul {a ω : ℝ} (ha : 0 < a) (h : a ≤ ω) :
    ω ^ (-4 : ℤ) ≤ a ^ (-2 : ℤ) * ω ^ (-2 : ℤ) := by
  have h1 : 0 < ω := by linarith
  have h2 : ω ^ (-2 : ℤ) ≤ a ^ (-2 : ℤ) := by
    rw [zpow_neg, zpow_neg, zpow_ofNat, zpow_ofNat]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ ha.le h 2)
  have : ω ^ (-4 : ℤ) = ω ^ (-2 : ℤ) * ω ^ (-2 : ℤ) := by
    rw [← zpow_add₀ h1.ne']; norm_num
  rw [this]
  calc ω ^ (-2 : ℤ) * ω ^ (-2 : ℤ) ≤ a ^ (-2 : ℤ) * ω ^ (-2 : ℤ) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)

/-! ### The bad function -/

section Bad

variable {F : Set ℝ} {lam : ℝ} {IT : Dyadic} {f : ℝ → ℂ}

/-- `f₀` is integrable on every dyadic interval. -/
theorem integrableOn_nearPart (hfm : AEStronglyMeasurable f volume)
    (hf : ∀ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) (J : Dyadic) :
    IntegrableOn (nearPart IT f) J.toSet := by
  have hfin : volume J.toSet ≠ ⊤ := by rw [Dyadic.volume_toSet]; exact ENNReal.ofReal_ne_top
  refine Measure.integrableOn_of_bounded (M := 1) hfin
    (aestronglyMeasurable_nearPart hfm) (Filter.Eventually.of_forall fun y => ?_)
  refine (norm_nearPart_le y).trans ((hf y).trans ?_)
  by_cases hy : y ∈ F <;> simp [hy]

/-- `∫_J (f₀ - ⨍_J f₀) = 0`. -/
theorem integral_nearPart_sub_czAvg (hfm : AEStronglyMeasurable f volume)
    (hf : ∀ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) (J : Dyadic) :
    ∫ y in J.toSet, (nearPart IT f y - czAvg IT f J) = 0 := by
  have hfin : volume J.toSet ≠ ⊤ := by rw [Dyadic.volume_toSet]; exact ENNReal.ofReal_ne_top
  have hJl := J.length_pos
  rw [integral_sub (integrableOn_nearPart hfm hf J) (integrableOn_const hfin), setIntegral_const,
    sub_eq_zero]
  unfold czAvg
  rw [setAverage_eq, Dyadic.volume_real_toSet, smul_inv_smul₀ hJl.ne']

/-- `∫_J 1_F = |F ∩ J|`. -/
theorem integral_indicator_one_set (hF : MeasurableSet F) (J : Dyadic) :
    ∫ z in J.toSet, F.indicator (fun _ => (1 : ℝ)) z = (volume (F ∩ J.toSet)).toReal := by
  rw [setIntegral_indicator hF, setIntegral_const, smul_eq_mul, mul_one, Measure.real, inter_comm]

/-- `1_F` is integrable on every dyadic interval. -/
theorem integrableOn_indicator_one (hF : MeasurableSet F) (J : Dyadic) :
    IntegrableOn (F.indicator (fun _ => (1 : ℝ))) J.toSet := by
  have hfin : volume J.toSet ≠ ⊤ := by rw [Dyadic.volume_toSet]; exact ENNReal.ofReal_ne_top
  exact (integrable_indicator_iff hF).2 (integrableOn_const (μ := volume.restrict J.toSet)
    (s := F) (C := (1 : ℝ)) (by
      rw [Measure.restrict_apply hF]
      exact ne_top_of_le_ne_top hfin (measure_mono inter_subset_right)))

end Bad

/-! ### The coefficient of the bad part -/

section Term

variable {F : Set ℝ} {lam : ℝ} {IT : Dyadic} {f : ℝ → ℂ}

/-- The coefficient `⟨b_J, ψ⟩ = ∫_J (f₀ - ⨍_J f₀) ψ̄`. -/
def czTerm (IT : Dyadic) (f : ℝ → ℂ) (ψ : ℝ → ℂ) (J : Dyadic) : ℂ :=
  ∫ y in J.toSet, (nearPart IT f y - czAvg IT f J) * conj (ψ y)

/-- If `x' ∈ I` and `x' ∉ Ω_λ` then `|F ∩ [c(I) - 2^n |I|, c(I) + 2^n |I|]| ≤ 2 λ 2^n |I|`
(`volume_inter_Icc_le_of_notMem` at the good point `x'`). -/
theorem volume_inter_Icc_two_pow_le (hF : MeasurableSet F) (hlam : 0 ≤ lam) {I : Dyadic}
    {x' : ℝ} (hx'I : x' ∈ I.toSet) (hx'Ω : x' ∉ maxSuperlevel F lam) (n : ℕ) :
    volume (F ∩ Icc (I.center - 2 ^ n * I.length) (I.center + 2 ^ n * I.length)) ≤
      ENNReal.ofReal (lam * (2 * (2 ^ n * I.length))) := by
  have hL := I.length_pos
  have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hc := I.center_eq
  have hr := I.right_eq
  have hx1 := hx'I.1
  have hx2 := hx'I.2
  have hp := mul_nonneg (sub_nonneg.2 h2n) hL.le
  have := volume_inter_Icc_le_of_notMem hF hlam hx'Ω (a := I.center - 2 ^ n * I.length)
    (b := I.center + 2 ^ n * I.length) (by linarith) (by linarith) (by linarith)
  convert this using 3
  ring

/-- The coefficient vanishes for a Calderón–Zygmund interval not inside `3 I_T`. -/
theorem czTerm_eq_zero {J : Dyadic} (hJ : J ∈ czFam F lam IT) (hJ3 : ¬ J.toSet ⊆ IT.dilate 3)
    (ψ : ℝ → ℂ) : czTerm IT f ψ J = 0 := by
  have hmiss : ∀ y ∈ J.toSet, y ∉ IT.dilate 3 := by
    intro y hy hy3
    exact hJ3 (subset_dilate_three_of_meets (czFam_k_le hJ) ⟨y, hy, hy3⟩)
  unfold czTerm
  rw [setIntegral_congr_fun J.measurableSet_toSet (g := fun _ => (0 : ℂ))]
  · simp
  · intro y hy
    simp only [nearPart_eq_zero (hmiss y hy), czAvg_eq_zero hJ hJ3, sub_self, zero_mul]

/-- **The bad part against an adapted packet**: for `I ⊄ Ω_λ` (a point `x'` of `I` outside
`Ω_λ`), `J ∈ czFam` inside `3 I_T`,
`|⟨b_J, ψ⟩| ≤ 22 A λ √|I| m(I, J)`. -/
theorem norm_czTerm_le (hF : MeasurableSet F) (hlam : 0 < lam) {x₀ : ℝ} (hx₀ : x₀ ∈ IT.toSet)
    (hx₀Ω : x₀ ∉ maxSuperlevel F lam) (hfm : AEStronglyMeasurable f volume)
    (hf : ∀ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) {A : ℝ} (hA : 0 ≤ A) {I : Dyadic}
    {ψ : ℝ → ℂ} (hψ : PacketBounds A I ψ) {x' : ℝ} (hx'I : x' ∈ I.toSet)
    (hx'Ω : x' ∉ maxSuperlevel F lam) {J : Dyadic} (hJ : J ∈ czFam F lam IT)
    (hJ3 : J.toSet ⊆ IT.dilate 3) :
    ‖czTerm IT f ψ J‖ ≤ 22 * A * lam * √I.length * kerM I J := by
  have hL := I.length_pos
  have hJl := J.length_pos
  have hsL : 0 < √I.length := Real.sqrt_pos.2 hL
  have hs : √I.length * √I.length = I.length := Real.mul_self_sqrt hL.le
  have hWpos := kerW_pos I J
  have hd0 := I.dist_nonneg J
  have ha1 : 1 ≤ 1 + I.dist J / I.length := by
    have : 0 ≤ I.dist J / I.length := by positivity
    linarith
  have hωa : ∀ y ∈ J.toSet, 1 + I.dist J / I.length ≤ 1 + |y - I.center| / I.length :=
    fun y hy => Dyadic.one_add_dist_div_le hy
  have hfinJ : volume J.toSet ≠ ⊤ := by rw [Dyadic.volume_toSet]; exact ENNReal.ofReal_ne_top
  -- the bad function
  set b : ℝ → ℂ := fun y => nearPart IT f y - czAvg IT f J with hbdef
  have hbm : AEStronglyMeasurable b volume :=
    (aestronglyMeasurable_nearPart hfm).sub aestronglyMeasurable_const
  have hbJ : ∀ y ∈ J.toSet, ‖b y‖ ≤ F.indicator (fun _ => (1 : ℝ)) y + 3 * lam := by
    intro y hy
    calc ‖b y‖ ≤ ‖nearPart IT f y‖ + ‖czAvg IT f J‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add ((norm_nearPart_le y).trans (hf y))
            (norm_czAvg_le hF hlam.le hx₀ hx₀Ω hf hJ)
  have hbI : IntegrableOn b J.toSet :=
    (integrableOn_nearPart hfm hf J).sub (integrableOn_const hfinJ)
  have hind := integrableOn_indicator_one hF J
  have hbnorm : ∫ y in J.toSet, ‖b y‖ ≤ 6 * lam * J.length := by
    have h1 : ∫ y in J.toSet, ‖b y‖ ≤ ∫ y in J.toSet,
        (F.indicator (fun _ => (1 : ℝ)) y + 3 * lam) :=
      setIntegral_mono_on hbI.norm (hind.add (integrableOn_const hfinJ)) J.measurableSet_toSet hbJ
    refine h1.trans ?_
    rw [integral_add hind (integrableOn_const hfinJ), integral_indicator_one_set hF,
      setIntegral_const, smul_eq_mul, Dyadic.volume_real_toSet]
    have := measureReal_inter_czFam_le hF hlam.le hx₀ hx₀Ω hJ hJ3
    linarith
  -- the packet is bounded
  have hψbd : ∀ y, ‖ψ y‖ ≤ A * (√I.length)⁻¹ := by
    intro y
    refine (hψ.bound0 y).trans ?_
    have : (1 + |y - I.center| / I.length) ^ (-4 : ℤ) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by have : 0 ≤ |y - I.center| / I.length := by positivity
                                 linarith) (by norm_num)
    calc A * (√I.length)⁻¹ * (1 + |y - I.center| / I.length) ^ (-4 : ℤ)
        ≤ A * (√I.length)⁻¹ * 1 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := mul_one _
  have hbψ : IntegrableOn (fun y => b y * conj (ψ y)) J.toSet := by
    refine Measure.integrableOn_of_bounded (M := (1 + 3 * lam) * (A * (√I.length)⁻¹)) hfinJ
      (hbm.mul (Complex.continuous_conj.comp hψ.differentiable.continuous).aestronglyMeasurable)
      ((ae_restrict_iff' J.measurableSet_toSet).2 (Filter.Eventually.of_forall fun y hy => ?_))
    rw [norm_mul, Complex.norm_conj]
    refine mul_le_mul ?_ (hψbd y) (norm_nonneg _) (by positivity)
    refine (hbJ y hy).trans ?_
    have : F.indicator (fun _ => (1 : ℝ)) y ≤ 1 := by by_cases hy : y ∈ F <;> simp [hy]
    linarith
  by_cases hle : J.length ≤ I.length
  · -- cancellation
    set W := kerW I J with hW
    have hD : ∀ y ∈ J.toSet, ‖deriv ψ y‖ ≤ A * (I.length * √I.length)⁻¹ * W := by
      intro y hy
      refine (hψ.bound1 y).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact zpow_neg_four_le_neg_two ha1 (hωa y hy)
    have hcan := norm_integral_mul_conj_le_of_mean_zero hbI hbψ
      (integral_nearPart_sub_czAvg hfm hf J) (fun y _ => hψ.differentiable y) hD
    have hk : kerM I J = (J.length / I.length) ^ 2 * W := by
      rw [hW]; simp only [kerM, hle, ↓reduceIte]
    rw [hk]
    have hD0 : 0 ≤ A * (I.length * √I.length)⁻¹ * W := by positivity
    calc ‖czTerm IT f ψ J‖ ≤ J.length / 2 * (A * (I.length * √I.length)⁻¹ * W) *
          ∫ y in J.toSet, ‖b y‖ := hcan
      _ ≤ J.length / 2 * (A * (I.length * √I.length)⁻¹ * W) * (6 * lam * J.length) :=
          mul_le_mul_of_nonneg_left hbnorm (by positivity)
      _ = 3 * (A * lam * √I.length * (J.length / I.length) ^ 2 * W) := by
          have : (I.length * √I.length)⁻¹ = √I.length / I.length ^ 2 := by
            field_simp
            linarith [hs]
          rw [this]; field_simp; ring
      _ ≤ 22 * A * lam * √I.length * ((J.length / I.length) ^ 2 * W) := by
          have : 0 ≤ A * lam * √I.length * ((J.length / I.length) ^ 2 * W) := by positivity
          linarith
  · -- size
    rw [not_le] at hle
    have hk : kerM I J = kerW I J := by simp [kerM, not_le.2 hle]
    rw [hk]
    set W := kerW I J with hW
    set w : ℝ → ℝ := fun y => (1 + |y - I.center| / I.length) ^ (-2 : ℤ) with hw
    have hwint : Integrable w := by
      have := integrable_one_add_abs_div_zpow (N := 2) (le_refl 2) I.center hL
      simpa [hw] using this
    have hwnn : ∀ y, 0 ≤ w y := fun y => by simp only [hw]; positivity
    -- the maximal function bound at the good point `x'`
    have hgood := volume_inter_Icc_two_pow_le hF hlam.le hx'I hx'Ω
    have hF16 := integral_indicator_mul_weight_le (F := F) hlam.le hL hgood
    have hpt : ∀ y ∈ J.toSet, ‖b y‖ * ‖ψ y‖ ≤
        (F.indicator (fun _ => (1 : ℝ)) y + 3 * lam) * (A * (√I.length)⁻¹ * W * w y) := by
      intro y hy
      have h1 := hbJ y hy
      have h2 : ‖ψ y‖ ≤ A * (√I.length)⁻¹ * W * w y := by
        refine (hψ.bound0 y).trans ?_
        have := zpow_neg_four_le_mul (by linarith : 0 < 1 + I.dist J / I.length) (hωa y hy)
        calc A * (√I.length)⁻¹ * (1 + |y - I.center| / I.length) ^ (-4 : ℤ)
            ≤ A * (√I.length)⁻¹ * ((1 + I.dist J / I.length) ^ (-2 : ℤ) *
                (1 + |y - I.center| / I.length) ^ (-2 : ℤ)) :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = A * (√I.length)⁻¹ * W * w y := by simp only [hW, hw, kerW]; ring
      exact mul_le_mul h1 h2 (norm_nonneg _)
        (add_nonneg (indicator_nonneg (fun _ _ => zero_le_one) y) (by positivity))
    have hfin : ∀ y, F.indicator (fun _ => (1 : ℝ)) y * w y = F.indicator w y := by
      intro y; by_cases hy : y ∈ F <;> simp [hy]
    set K := A * (√I.length)⁻¹ * W with hK
    have hK0 : 0 ≤ K := by positivity
    have hFw : IntegrableOn (F.indicator w) J.toSet := (hwint.indicator hF).integrableOn
    have hw3 : IntegrableOn (fun y => 3 * lam * w y) J.toSet :=
      (hwint.const_mul (3 * lam)).integrableOn
    have hg : IntegrableOn (fun y => K * (F.indicator w y + 3 * lam * w y)) J.toSet :=
      (hFw.add hw3).const_mul K
    have hbound : ‖czTerm IT f ψ J‖ ≤ ∫ y in J.toSet, K * (F.indicator w y + 3 * lam * w y) := by
      refine norm_integral_le_of_norm_le hg ?_
      refine (ae_restrict_iff' J.measurableSet_toSet).2 (Filter.Eventually.of_forall fun y hy => ?_)
      rw [norm_mul, Complex.norm_conj]
      calc ‖b y‖ * ‖ψ y‖ ≤ (F.indicator (fun _ => (1 : ℝ)) y + 3 * lam) * (K * w y) := by
            have := hpt y hy
            simpa only [hK, mul_assoc] using this
        _ = K * (F.indicator w y + 3 * lam * w y) := by rw [← hfin y]; ring
    have hint1 : ∫ y in J.toSet, F.indicator w y ≤ 16 * lam * I.length := by
      rw [setIntegral_indicator hF]
      exact (setIntegral_mono_set hwint.integrableOn (Filter.Eventually.of_forall hwnn)
        (Filter.Eventually.of_forall fun y hy => hy.2)).trans hF16
    have hint2 : ∫ y in J.toSet, w y ≤ 2 * I.length := by
      refine (setIntegral_le_integral hwint (Filter.Eventually.of_forall hwnn)).trans (le_of_eq ?_)
      have := integral_one_add_abs_div_zpow (N := 2) (le_refl 2) I.center hL
      simp only [hw]
      rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, this]
      norm_num
      ring
    calc ‖czTerm IT f ψ J‖ ≤ ∫ y in J.toSet, K * (F.indicator w y + 3 * lam * w y) := hbound
      _ = K * ((∫ y in J.toSet, F.indicator w y) + 3 * lam * ∫ y in J.toSet, w y) := by
          rw [integral_const_mul, integral_add hFw hw3, integral_const_mul]
      _ ≤ K * (16 * lam * I.length + 3 * lam * (2 * I.length)) := by
          gcongr
      _ = 22 * A * lam * √I.length * W := by
          have h1 : (√I.length)⁻¹ * I.length = √I.length := by
            field_simp
            linarith [hs]
          calc K * (16 * lam * I.length + 3 * lam * (2 * I.length))
              = 22 * A * lam * W * ((√I.length)⁻¹ * I.length) := by simp only [hK]; ring
            _ = 22 * A * lam * √I.length * W := by rw [h1]; ring

end Term

end PrimeCarleson.Proof.Oplus
