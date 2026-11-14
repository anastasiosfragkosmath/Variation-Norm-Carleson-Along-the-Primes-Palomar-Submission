module

public import PrimeCarleson.Proof.Oplus.External.FSDistribution

/-!
# The layer-cake estimate `∫ g^q ≤ K_q b^{q-1} ∫ g`

Step 5 of the proof of the interpolation between `L¹` and dyadic BMO: for
`g ≥ 0` integrable with `g ≤ M_D g` almost everywhere (Step 4; `DyadicDominated`) and a mean
oscillation bound `b > 0`, `q > 1`:
`∫ g^q = q ∫_0^∞ t^{q-1} |{g > t}| dt ≤ q ∫_0^∞ t^{q-1} |Ω_t| dt ≤ K_q b^{q-1} ∫ g`
where the distribution function is bounded by `A/t` (`t ≤ 4b`) and `(A/b) e^{-ct}` (`t ≥ 4b`),
`c = log 2/(4b)`, and `∫_0^∞ t^{q-1} e^{-ct} dt = c^{-q} Γ(q)`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- **Dyadic differentiation at almost every point** (Step 4): for almost every `x` and every
`t < g x` some dyadic interval containing `x` has average `> t`, i.e. `g ≤ M_D g` a.e. -/
def DyadicDominated (g : ℝ → ℝ) : Prop :=
  ∀ᵐ x : ℝ, ∀ t : ℝ, t < g x → ∃ I : Dyadic, x ∈ I.toSet ∧ t < dyadicMean g I

/-- The constant `K_q = q (4^{q-1}/(q-1) + 4^q Γ(q)/(log 2)^q)`. -/
def layerCakeConst (q : ℝ) : ℝ :=
  q * (4 ^ (q - 1) / (q - 1) + 4 ^ q * Real.Gamma q / Real.log 2 ^ q)

variable {g : ℝ → ℝ}

/-- The distribution function of `g` is bounded by that of the dyadic maximal function. -/
theorem volume_lt_le_levelUnion (hdom : DyadicDominated g) (t : ℝ) :
    volume {a | t < g a} ≤ volume (levelUnion g t) := by
  refine measure_mono_ae ?_
  filter_upwards [hdom] with x hx htx
  exact mem_levelUnion.2 (hx t htx)

/-- The scale identity turning the two integrals into `K_q b^{q-1} A`. -/
theorem layerCake_algebra {b : ℝ} (hb0 : 0 < b) {q : ℝ} (hq : 1 < q) (A : ℝ) :
    q * (A * ((4 * b) ^ (q - 1) / (q - 1) +
      b⁻¹ * ((1 / (Real.log 2 / (4 * b))) ^ q * Real.Gamma q))) =
      layerCakeConst q * b ^ (q - 1) * A := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (4 * b) ^ (q - 1) = 4 ^ (q - 1) * b ^ (q - 1) :=
    Real.mul_rpow (by norm_num) hb0.le
  have h2 : (1 / (Real.log 2 / (4 * b))) ^ q = 4 ^ q * b ^ q / Real.log 2 ^ q := by
    rw [one_div, inv_div, Real.div_rpow (by positivity) hlog.le, Real.mul_rpow (by norm_num) hb0.le]
  have h3 : b ^ q = b ^ (q - 1) * b := by
    rw [← Real.rpow_add_one hb0.ne']; ring_nf
  have hq1 : q - 1 ≠ 0 := by linarith
  have hlogq : 0 < Real.log 2 ^ q := Real.rpow_pos_of_pos hlog q
  rw [layerCakeConst, h1, h2, h3]
  field_simp

/-- The integral of `t^{q-2}` over `(0, 4b]`. -/
theorem lintegral_Ioc_rpow {b : ℝ} (hb0 : 0 < b) {q : ℝ} (hq : 1 < q) :
    ∫⁻ t in Ioi (0 : ℝ), (Ioc (0 : ℝ) (4 * b)).indicator
        (fun t => ENNReal.ofReal (t ^ (q - 2))) t =
      ENNReal.ofReal ((4 * b) ^ (q - 1) / (q - 1)) := by
  rw [lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.2 Ioc_subset_Ioi_self]
  have hint : IntegrableOn (fun t : ℝ => t ^ (q - 2)) (Ioc (0 : ℝ) (4 * b)) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 4 * b)
      (by linarith : -1 < q - 2))
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).1 this
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) (4 * b))] fun t : ℝ => t ^ (q - 2) :=
    (ae_restrict_iff' measurableSet_Ioc).2
      (Filter.Eventually.of_forall fun t ht => Real.rpow_nonneg ht.1.le _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn,
    ← intervalIntegral.integral_of_le (by linarith : (0 : ℝ) ≤ 4 * b),
    integral_rpow (Or.inl (by linarith : -1 < q - 2))]
  congr 1
  rw [show q - 2 + 1 = q - 1 by ring, Real.zero_rpow (by linarith : q - 1 ≠ 0)]
  ring

/-- The Gamma integral `∫_0^∞ t^{q-1} e^{-ct} dt = c^{-q} Γ(q)` in `ℝ≥0∞`. -/
theorem lintegral_rpow_mul_exp {c : ℝ} (hc : 0 < c) {q : ℝ} (hq : 0 < q) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q - 1) * Real.exp (-(c * t))) =
      ENNReal.ofReal ((1 / c) ^ q * Real.Gamma q) := by
  have key := Real.integral_rpow_mul_exp_neg_mul_Ioi hq hc
  have hint : IntegrableOn (fun t : ℝ => t ^ (q - 1) * Real.exp (-(c * t))) (Ioi 0) :=
    .of_integral_ne_zero (by rw [key]; positivity)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun t : ℝ => t ^ (q - 1) * Real.exp (-(c * t)) :=
    (ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall fun t ht => mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _)
        (Real.exp_nonneg _))
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, key]

/-- **The `L^q` estimate**: for `g ≥ 0` integrable with `g ≤ M_D g` almost everywhere and mean
oscillation bound `b > 0`, `∫ g^q ≤ K_q b^{q-1} ∫ g` for every `q > 1`. -/
theorem lintegral_ofReal_rpow_le (hg0 : ∀ x, 0 ≤ g x) (hgi : Integrable g)
    (hdom : DyadicDominated g) {b : ℝ} (hb : MeanOscLe g b) (hb0 : 0 < b) {q : ℝ} (hq : 1 < q) :
    ∫⁻ x, ENNReal.ofReal (g x ^ q) ≤
      ENNReal.ofReal (layerCakeConst q * b ^ (q - 1) * ∫ y, g y) := by
  set A := ∫ y, g y with hA
  have hA0 : 0 ≤ A := integral_nonneg hg0
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c := Real.log 2 / (4 * b) with hc
  have hc0 : 0 < c := by positivity
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul volume (Filter.Eventually.of_forall hg0)
    hgi.aemeasurable (by linarith)]
  have hpt : ∀ t ∈ Ioi (0 : ℝ), volume {a | t < g a} * ENNReal.ofReal (t ^ (q - 1)) ≤
      ENNReal.ofReal A * ((Ioc (0 : ℝ) (4 * b)).indicator
        (fun t => ENNReal.ofReal (t ^ (q - 2))) t +
        ENNReal.ofReal (b⁻¹ * (t ^ (q - 1) * Real.exp (-(c * t))))) := by
    intro t ht
    have ht0 : 0 < t := ht
    have h1 := volume_lt_le_levelUnion hdom t
    by_cases h4 : t ≤ 4 * b
    · have h2 := h1.trans (volume_levelUnion_le_inv hg0 hgi ht0)
      have h3 : ENNReal.ofReal (A / t) * ENNReal.ofReal (t ^ (q - 1)) =
          ENNReal.ofReal A * ENNReal.ofReal (t ^ (q - 2)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hA0]
        congr 1
        rw [show q - 1 = (q - 2) + 1 by ring, Real.rpow_add_one ht0.ne']
        field_simp
      calc volume {a | t < g a} * ENNReal.ofReal (t ^ (q - 1))
          ≤ ENNReal.ofReal (A / t) * ENNReal.ofReal (t ^ (q - 1)) := by gcongr
        _ = ENNReal.ofReal A * ENNReal.ofReal (t ^ (q - 2)) := h3
        _ = ENNReal.ofReal A * (Ioc (0 : ℝ) (4 * b)).indicator
              (fun t => ENNReal.ofReal (t ^ (q - 2))) t := by
            rw [indicator_of_mem (show t ∈ Ioc (0 : ℝ) (4 * b) from ⟨ht0, h4⟩)]
        _ ≤ _ := by gcongr; exact le_self_add
    · rw [not_le] at h4
      have h2 := h1.trans (volume_levelUnion_le_exp hg0 hgi hb hb0 h4.le)
      have h3 : ENNReal.ofReal (A / b * Real.exp (-(c) * t)) * ENNReal.ofReal (t ^ (q - 1)) =
          ENNReal.ofReal A * ENNReal.ofReal (b⁻¹ * (t ^ (q - 1) * Real.exp (-(c * t)))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hA0, neg_mul]
        congr 1
        field_simp
      calc volume {a | t < g a} * ENNReal.ofReal (t ^ (q - 1))
          ≤ ENNReal.ofReal (A / b * Real.exp (-(c) * t)) * ENNReal.ofReal (t ^ (q - 1)) := by
            gcongr
        _ = ENNReal.ofReal A * ENNReal.ofReal (b⁻¹ * (t ^ (q - 1) * Real.exp (-(c * t)))) := h3
        _ ≤ _ := by gcongr; exact le_add_self
  have hmeas1 : Measurable fun t : ℝ => (Ioc (0 : ℝ) (4 * b)).indicator
      (fun t => ENNReal.ofReal (t ^ (q - 2))) t := by
    refine Measurable.indicator ?_ measurableSet_Ioc
    exact ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
  calc ENNReal.ofReal q * ∫⁻ t in Ioi (0 : ℝ), volume {a | t < g a} * ENNReal.ofReal (t ^ (q - 1))
      ≤ ENNReal.ofReal q * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal A * ((Ioc (0 : ℝ) (4 * b)).indicator
          (fun t => ENNReal.ofReal (t ^ (q - 2))) t +
          ENNReal.ofReal (b⁻¹ * (t ^ (q - 1) * Real.exp (-(c * t))))) := by
        exact mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_Ioi hpt)
    _ = ENNReal.ofReal q * (ENNReal.ofReal A * (
          (∫⁻ t in Ioi (0 : ℝ), (Ioc (0 : ℝ) (4 * b)).indicator
            (fun t => ENNReal.ofReal (t ^ (q - 2))) t) +
          ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (b⁻¹ * (t ^ (q - 1) * Real.exp (-(c * t)))))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hmeas1]
    _ = ENNReal.ofReal (layerCakeConst q * b ^ (q - 1) * A) := by
        have hI2 : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (b⁻¹ * (t ^ (q - 1) * Real.exp (-(c * t)))) =
            ENNReal.ofReal (b⁻¹ * ((1 / c) ^ q * Real.Gamma q)) := by
          have hbi : (0 : ℝ) ≤ b⁻¹ := by positivity
          simp_rw [ENNReal.ofReal_mul hbi]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_rpow_mul_exp hc0
            (by linarith), ← ENNReal.ofReal_mul hbi]
        have hX1 : (0 : ℝ) ≤ (4 * b) ^ (q - 1) / (q - 1) :=
          div_nonneg (Real.rpow_nonneg (by positivity) _) (by linarith)
        have hX2 : (0 : ℝ) ≤ b⁻¹ * ((1 / c) ^ q * Real.Gamma q) :=
          mul_nonneg (by positivity) (mul_nonneg (Real.rpow_nonneg (by positivity) _)
            (Real.Gamma_pos_of_pos (by linarith)).le)
        rw [lintegral_Ioc_rpow hb0 hq, hI2, ← ENNReal.ofReal_add hX1 hX2,
          ← ENNReal.ofReal_mul hA0, ← ENNReal.ofReal_mul (by linarith)]
        congr 1
        exact layerCake_algebra hb0 hq A

end PrimeCarleson.Proof.Oplus
