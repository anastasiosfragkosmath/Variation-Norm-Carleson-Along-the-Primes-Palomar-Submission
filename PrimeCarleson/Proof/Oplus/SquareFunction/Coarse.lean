module

public import PrimeCarleson.Proof.Oplus.SquareFunction.Convolution

/-!
# Coarse scales: `‖A_k D_j f‖₂ ≲ 2^{j-k} ‖D_j f‖₂` for `j ≤ k`

The coarse-scale decay in the proof of the square-function estimate of
Jones–Kaufman–Rosenblatt–Wierdl (proved here). One could integrate by parts against the
tent-function primitive of the Haar expansion; here the same gain `2^{j-k}` is obtained by
subtracting the value `ψ_k(x - a_m)` at the left end point `a_m` of the dyadic interval `I_m` of
length `2^j`: since `g` has zero mean on `I_m`,
`∫_{I_m} ψ_k(x - y) g(y) dy = ∫_{I_m} (ψ_k(x - y) - ψ_k(x - a_m)) g(y) dy`, and the mean value
theorem gives `|ψ_k(x - y) - ψ_k(x - a_m)| ≤ 2^{j-k} Φ_k(x - y)` for `j ≤ k` with
`Φ_k(t) = 2^{-k} Θ(2^{-k} t)`, `Θ(τ) = 4 C (1 + |τ|)^{-2}` an integrable majorant of `|ψ'|`
(`C = sup (1 + |u|)² |ψ'(u)|`).  The Schur test (`sqn_conv_le`) then closes the estimate. -/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal SchwartzMap

open PrimeCarleson.Proof.Lepingle

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- The decay majorant `Θ(τ) = 4 C (1 + |τ|)^{-2}`. -/
def decayKernel (C : ℝ) (τ : ℝ) : ℝ≥0∞ := ENNReal.ofReal (4 * C * ((1 + |τ|) ^ 2)⁻¹)

/-- The decay majorant is measurable. -/
theorem measurable_decayKernel (C : ℝ) : Measurable (decayKernel C) := by
  unfold decayKernel
  refine ENNReal.measurable_ofReal.comp ?_
  fun_prop

/-- The decay majorant `Θ` is integrable. -/
theorem lintegral_decayKernel_lt_top (C : ℝ) : ∫⁻ τ, decayKernel C τ < ∞ := by
  have hint : Integrable (fun τ : ℝ => (1 + ‖τ‖) ^ (-(2 : ℝ))) volume :=
    integrable_one_add_norm (by simp)
  have h2 : Integrable (fun τ : ℝ => 4 * C * ((1 + |τ|) ^ 2)⁻¹) volume := by
    refine (hint.const_mul (4 * C)).congr (Filter.Eventually.of_forall fun τ => ?_)
    simp only [Real.norm_eq_abs]
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
  refine lt_of_le_of_lt (lintegral_mono fun τ => ?_) h2.hasFiniteIntegral
  unfold decayKernel
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (le_abs_self _)

/-- Decay of the derivative of a Schwartz function. -/
theorem exists_deriv_decay (ψ : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, (1 + |u|) ^ 2 * ‖deriv ψ u‖ ≤ C := by
  set ψ' : 𝓢(ℝ, ℂ) := SchwartzMap.derivCLM ℝ ℂ ψ with hψ'
  refine ⟨2 ^ 2 * ((Finset.Iic ((2 : ℕ), (0 : ℕ))).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) ψ',
    by positivity, fun u => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := ((2 : ℕ), (0 : ℕ)))
    (k := 2) (n := 0) le_rfl le_rfl ψ' u
  rw [norm_iteratedFDeriv_zero, hψ', SchwartzMap.derivCLM_apply, Real.norm_eq_abs] at h
  exact h

/-- The derivative of `ψ_k = 2^{-k} ψ(2^{-k} ·)` is `2^{-2k} ψ'(2^{-k} ·)`. -/
theorem hasDerivAt_schwartzScale (ψ : 𝓢(ℝ, ℂ)) (k : ℤ) (u : ℝ) :
    HasDerivAt (schwartzScale ψ k)
      ((((2 : ℝ) ^ (-k)) ^ 2 : ℝ) • deriv ψ ((2 : ℝ) ^ (-k) * u)) u := by
  set c : ℝ := (2 : ℝ) ^ (-k) with hc
  have h1 : HasDerivAt (fun u : ℝ => c * u) c u := by
    simpa using (hasDerivAt_id u).const_mul c
  have h2 : HasDerivAt (fun u : ℝ => ψ (c * u)) (c • deriv ψ (c * u)) u :=
    HasDerivAt.scomp u (ψ.hasDerivAt (c * u)) h1
  have h3 : HasDerivAt (fun u : ℝ => (c : ℂ) * ψ (c * u)) ((c : ℂ) * (c • deriv ψ (c * u))) u :=
    h2.const_mul (c : ℂ)
  have e : ((c ^ 2 : ℝ) • deriv ψ (c * u)) = (c : ℂ) * (c • deriv ψ (c * u)) := by
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  rw [e]
  exact h3

/-- The mean value bound for `ψ_k` on a segment of length `≤ 2^j ≤ 2^k`:
`|ψ_k(x - y) - ψ_k(x - a)| ≤ 2^{j-k} · 2^{-k} · 4 C / (1 + 2^{-k}|x - y|)²`. -/
theorem norm_schwartzScale_sub_le (ψ : 𝓢(ℝ, ℂ)) {C : ℝ}
    (hC : ∀ u : ℝ, (1 + |u|) ^ 2 * ‖deriv ψ u‖ ≤ C) {k j : ℤ} (hjk : j ≤ k) {x y a : ℝ}
    (hay : a ≤ y) (hya : y - a ≤ (2 : ℝ) ^ j) :
    ‖schwartzScale ψ k (x - y) - schwartzScale ψ k (x - a)‖ ≤
      (2 : ℝ) ^ (j - k) * ((2 : ℝ) ^ (-k) *
        (4 * C * ((1 + (2 : ℝ) ^ (-k) * |x - y|) ^ 2)⁻¹)) := by
  set c : ℝ := (2 : ℝ) ^ (-k) with hc
  have hc0 : 0 < c := by positivity
  have hcj : c * (2 : ℝ) ^ j ≤ 1 := by
    rw [hc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    exact zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  have hC0 : 0 ≤ C := (by positivity : (0 : ℝ) ≤ (1 + |0|) ^ 2 * ‖deriv ψ 0‖).trans (hC 0)
  set D : ℝ := c ^ 2 * (4 * C * ((1 + c * |x - y|) ^ 2)⁻¹) with hD
  have hbound : ∀ s ∈ Icc (x - y) (x - a), ‖(((c ^ 2 : ℝ)) • deriv ψ (c * s))‖ ≤ D := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := hs
    have h1 : c * |x - y| ≤ |c * s| + 1 := by
      have : |x - y| ≤ |s| + (y - a) := by
        calc |x - y| = |s + ((x - y) - s)| := by ring_nf
          _ ≤ |s| + |(x - y) - s| := abs_add_le _ _
          _ ≤ |s| + (y - a) := by
            gcongr
            rw [abs_le]
            constructor <;> linarith
      calc c * |x - y| ≤ c * (|s| + (y - a)) := mul_le_mul_of_nonneg_left this hc0.le
        _ = |c * s| + c * (y - a) := by rw [mul_add, abs_mul, abs_of_pos hc0]
        _ ≤ |c * s| + c * 2 ^ j := by gcongr
        _ ≤ |c * s| + 1 := by linarith
    have h2 : (1 + c * |x - y|) ≤ 2 * (1 + |c * s|) := by
      have := abs_nonneg (c * s)
      linarith
    have hpos : 0 < 1 + |c * s| := by positivity
    have hpos' : 0 < 1 + c * |x - y| := by positivity
    have h3 : ((1 + |c * s|) ^ 2)⁻¹ ≤ 4 * ((1 + c * |x - y|) ^ 2)⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    have h4 : ‖deriv ψ (c * s)‖ ≤ C * ((1 + |c * s|) ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      calc ‖deriv ψ (c * s)‖ * (1 + |c * s|) ^ 2 = (1 + |c * s|) ^ 2 * ‖deriv ψ (c * s)‖ := by
            ring
        _ ≤ C := hC _
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc c ^ 2 * ‖deriv ψ (c * s)‖ ≤ c ^ 2 * (C * ((1 + |c * s|) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ ≤ c ^ 2 * (C * (4 * ((1 + c * |x - y|) ^ 2)⁻¹)) := by gcongr
      _ = D := by rw [hD]; ring
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := schwartzScale ψ k) (f' := fun s => (c ^ 2 : ℝ) • deriv ψ (c * s))
    (s := Icc (x - y) (x - a)) (C := D)
    (fun s _ => (hasDerivAt_schwartzScale ψ k s).hasDerivWithinAt) hbound (convex_Icc _ _)
    (left_mem_Icc.2 (by linarith)) (right_mem_Icc.2 (by linarith))
  rw [norm_sub_rev]
  refine hmvt.trans ?_
  have hD0 : 0 ≤ D := by positivity
  have : ‖(x - a) - (x - y)‖ ≤ (2 : ℝ) ^ j := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  calc D * ‖(x - a) - (x - y)‖ ≤ D * (2 : ℝ) ^ j := mul_le_mul_of_nonneg_left this hD0
    _ = (2 : ℝ) ^ (j - k) * (c * (4 * C * ((1 + c * |x - y|) ^ 2)⁻¹)) := by
      have e : (2 : ℝ) ^ (j - k) = (2 : ℝ) ^ j * c := by
        rw [hc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        rfl
      rw [hD, e]
      ring

/-- The rescaled majorant `Φ_k(t) = 2^{-k} Θ(2^{-k} t)`. -/
def decayKernelScaled (C : ℝ) (k : ℤ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 : ℝ) ^ (-k)) * decayKernel C ((2 : ℝ) ^ (-k) * t)

/-- The rescaled majorant is measurable. -/
theorem measurable_decayKernelScaled (C : ℝ) (k : ℤ) : Measurable (decayKernelScaled C k) := by
  unfold decayKernelScaled
  exact ((measurable_decayKernel C).comp (measurable_const.mul measurable_id)).const_mul _

/-- The rescaling preserves the `L¹` norm: `‖Φ_k‖₁ = ‖Θ‖₁`. -/
theorem lintegral_decayKernelScaled (C : ℝ) (k : ℤ) :
    ∫⁻ t, decayKernelScaled C k t = ∫⁻ τ, decayKernel C τ := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (-k) := by positivity
  unfold decayKernelScaled
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_comp_mul_left_of_pos h2 (h := decayKernel C) (measurable_decayKernel C),
    ← mul_assoc, ← ENNReal.ofReal_mul h2.le, mul_inv_cancel₀ h2.ne', ENNReal.ofReal_one, one_mul]

/-- The pointwise coarse bound: for `g` with zero mean on every dyadic interval of length `2^j`,
`j ≤ k`, `|A_k g(x)| ≤ 2^{j-k} (Φ_k * |g|)(x)`. -/
theorem enorm_schwartzAvg_le_coarse (ψ : 𝓢(ℝ, ℂ)) {C : ℝ}
    (hC : ∀ u : ℝ, (1 + |u|) ^ 2 * ‖deriv ψ u‖ ≤ C) {j k : ℤ} (hjk : j ≤ k) {g : ℝ → ℂ}
    (hg : Measurable g) (hgL : MemLp g 2 volume) (hmean : ∀ m : ℤ, ∫ y in dyadicIco j m, g y = 0)
    (x : ℝ) :
    ‖schwartzAvg ψ k g x‖ₑ ≤ ENNReal.ofReal ((2 : ℝ) ^ (j - k)) *
      ∫⁻ y, decayKernelScaled C k (x - y) * ‖g y‖ₑ := by
  have hgsq := lintegral_sq_lt_top_of_memLp hgL
  have hFi : Integrable (fun y => schwartzScale ψ k (x - y) * g y) :=
    integrable_schwartzScale_mul ψ k hg hgsq x
  have hm : ∀ m : ℤ, ‖∫ y in dyadicIco j m, schwartzScale ψ k (x - y) * g y‖ₑ ≤
      ENNReal.ofReal ((2 : ℝ) ^ (j - k)) *
        ∫⁻ y in dyadicIco j m, decayKernelScaled C k (x - y) * ‖g y‖ₑ := by
    intro m
    set I := dyadicIco j m with hI
    set a : ℝ := (2 : ℝ) ^ j * m with ha
    have hgI : IntegrableOn g I := integrableOn_dyadicIco_of_memLp_two hgL j m
    have hsub : ∫ y in I, schwartzScale ψ k (x - y) * g y =
        ∫ y in I, (schwartzScale ψ k (x - y) * g y - schwartzScale ψ k (x - a) * g y) := by
      rw [integral_sub hFi.integrableOn (hgI.const_mul _), integral_const_mul, hmean m, mul_zero,
        sub_zero]
    rw [hsub]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' (measurableSet_dyadicIco j m) fun y hy => ?_
    obtain ⟨hy1, hy2⟩ := hy
    have hay : a ≤ y := hy1
    have hya : y - a ≤ (2 : ℝ) ^ j := by
      have : y < (2 : ℝ) ^ j * (m + 1) := hy2
      rw [ha]
      nlinarith
    have hb := norm_schwartzScale_sub_le ψ hC hjk (x := x) hay hya
    rw [← sub_mul, enorm_mul, ← mul_assoc]
    refine mul_le_mul_left ?_ _
    rw [← ofReal_norm]
    refine (ENNReal.ofReal_le_ofReal hb).trans (le_of_eq ?_)
    have hc : (0 : ℝ) ≤ (2 : ℝ) ^ (-k) := by positivity
    unfold decayKernelScaled decayKernel
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hc, abs_mul,
      abs_of_nonneg hc]
  have hsum : schwartzAvg ψ k g x =
      ∑' m : ℤ, ∫ y in dyadicIco j m, schwartzScale ψ k (x - y) * g y := by
    have := integral_iUnion (μ := volume) (f := fun y => schwartzScale ψ k (x - y) * g y)
      (fun m => measurableSet_dyadicIco j m) (pairwise_disjoint_dyadicIco_int j)
      (by rw [iUnion_dyadicIco]; exact hFi.integrableOn)
    rw [iUnion_dyadicIco, Measure.restrict_univ] at this
    exact this
  rw [hsum]
  refine enorm_tsum_le_tsum_enorm.trans ?_
  calc ∑' m : ℤ, ‖∫ y in dyadicIco j m, schwartzScale ψ k (x - y) * g y‖ₑ
      ≤ ∑' m : ℤ, ENNReal.ofReal ((2 : ℝ) ^ (j - k)) *
        ∫⁻ y in dyadicIco j m, decayKernelScaled C k (x - y) * ‖g y‖ₑ := ENNReal.tsum_le_tsum hm
    _ = ENNReal.ofReal ((2 : ℝ) ^ (j - k)) *
        ∫⁻ y, decayKernelScaled C k (x - y) * ‖g y‖ₑ := by
      rw [ENNReal.tsum_mul_left, lintegral_eq_tsum_dyadicIco j
        (fun y => decayKernelScaled C k (x - y) * ‖g y‖ₑ)]

/-- **Coarse scales**: for `g ∈ L²` with zero mean on every dyadic interval of length `2^j` and
`j ≤ k`, `‖A_k g‖₂ ≤ 2^{j-k} ‖Θ‖₁ ‖g‖₂`, where `Θ(τ) = 4 C (1 + |τ|)^{-2}` and
`C = sup (1 + |u|)² |ψ'(u)|`. -/
theorem sqn_schwartzAvg_le_coarse (ψ : 𝓢(ℝ, ℂ)) {C : ℝ}
    (hC : ∀ u : ℝ, (1 + |u|) ^ 2 * ‖deriv ψ u‖ ≤ C) {j k : ℤ} (hjk : j ≤ k) {g : ℝ → ℂ}
    (hg : Measurable g) (hgL : MemLp g 2 volume) (hmean : ∀ m : ℤ, ∫ y in dyadicIco j m, g y = 0) :
    ∫⁻ x, ‖schwartzAvg ψ k g x‖ₑ ^ 2 ≤
      (ENNReal.ofReal ((2 : ℝ) ^ (j - k)) * ∫⁻ τ, decayKernel C τ) ^ 2 *
        ∫⁻ y, ‖g y‖ₑ ^ 2 := by
  have hΦ : Measurable fun t => ENNReal.ofReal ((2 : ℝ) ^ (j - k)) * decayKernelScaled C k t :=
    (measurable_decayKernelScaled C k).const_mul _
  have h1 := sqn_conv_le hΦ hg (F := fun x => ‖schwartzAvg ψ k g x‖ₑ) (fun x => by
    refine (enorm_schwartzAvg_le_coarse ψ hC hjk hg hgL hmean x).trans (le_of_eq ?_)
    simp_rw [mul_assoc]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top])
  have h2 : ∫⁻ t, ENNReal.ofReal ((2 : ℝ) ^ (j - k)) * decayKernelScaled C k t =
      ENNReal.ofReal ((2 : ℝ) ^ (j - k)) * ∫⁻ τ, decayKernel C τ := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_decayKernelScaled]
  rwa [h2] at h1

end PrimeCarleson.Proof.Oplus
