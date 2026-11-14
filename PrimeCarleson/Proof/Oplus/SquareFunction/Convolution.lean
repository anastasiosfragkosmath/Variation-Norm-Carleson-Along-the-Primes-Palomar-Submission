module

public import PrimeCarleson.Proof.Oplus.SquareFunction.Convergence
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The Schwartz averages `A_k f = ψ_k * f` on `L²(ℝ)`

`ψ_k = 2^{-k} ψ(2^{-k} ·)` for a Schwartz function `ψ` ([O+] L1975-L1980 and L2011).  We prove the
elementary `L²` facts needed for the square-function estimate of
Jones–Kaufman–Rosenblatt–Wierdl (proved here):

* `lintegral_enorm_schwartzScale`: `‖ψ_k‖₁ = ‖ψ‖₁`;
* `integrable_schwartzScale_mul`: the convolution integral converges for `f ∈ L²`;
* `sqn_schwartzAvg_le`: Young's inequality `‖A_k f‖₂ ≤ ‖ψ‖₁ ‖f‖₂` (via the Schur test);
* linearity and measurability of `A_k f`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal SchwartzMap

open PrimeCarleson.Proof.MswTransference

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- The rescaling `ψ_k = 2^{-k} ψ(2^{-k} ·)`. -/
def schwartzScale (ψ : ℝ → ℂ) (k : ℤ) (x : ℝ) : ℂ :=
  (((2 : ℝ) ^ (-k) : ℝ) : ℂ) * ψ ((2 : ℝ) ^ (-k) * x)

/-- `A_k f = ψ_k * f`, `A_k f(x) = ∫ ψ_k(x - y) f(y) dy`. -/
def schwartzAvg (ψ : ℝ → ℂ) (k : ℤ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, schwartzScale ψ k (x - y) * f y

/-! ### Scaling -/

theorem lintegral_comp_mul_left_of_pos {c : ℝ} (hc : 0 < c) {h : ℝ → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ t, h (c * t) = ENNReal.ofReal c⁻¹ * ∫⁻ t, h t := by
  have hmap := Measure.map_addHaar_smul (volume : Measure ℝ) hc.ne'
  calc ∫⁻ t, h (c * t) = ∫⁻ t, h (c • t) := rfl
    _ = ∫⁻ y, h y ∂(Measure.map (fun x : ℝ => c • x) volume) :=
        (lintegral_map hh (measurable_const_smul c)).symm
    _ = _ := by
        rw [hmap, lintegral_smul_measure]
        simp [abs_of_pos hc]

section Schwartz

variable (ψ : 𝓢(ℝ, ℂ)) (k : ℤ)

/-- Unfolding `ψ_k(x) = 2^{-k} ψ(2^{-k} x)`. -/
theorem schwartzScale_apply (x : ℝ) :
    schwartzScale ψ k x = (((2 : ℝ) ^ (-k) : ℝ) : ℂ) * ψ ((2 : ℝ) ^ (-k) * x) := rfl

/-- `ψ_k` is continuous. -/
theorem continuous_schwartzScale : Continuous (schwartzScale ψ k) := by
  unfold schwartzScale
  exact continuous_const.mul (ψ.continuous.comp (continuous_const.mul continuous_id))

/-- `ψ_k` is measurable. -/
theorem measurable_schwartzScale : Measurable (schwartzScale ψ k) :=
  (continuous_schwartzScale ψ k).measurable

/-- The norm of `ψ_k(t)` in terms of `ψ(2^{-k} t)`. -/
theorem enorm_schwartzScale (t : ℝ) :
    ‖schwartzScale ψ k t‖ₑ = ENNReal.ofReal ((2 : ℝ) ^ (-k)) * ‖ψ ((2 : ℝ) ^ (-k) * t)‖ₑ := by
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (-k) := by positivity
  rw [schwartzScale_apply, enorm_mul, ← ofReal_norm (((2 : ℝ) ^ (-k) : ℝ) : ℂ), Complex.norm_real,
    Real.norm_of_nonneg h2]

/-- `‖ψ_k‖₁ = ‖ψ‖₁`. -/
theorem lintegral_enorm_schwartzScale :
    ∫⁻ t, ‖schwartzScale ψ k t‖ₑ = ∫⁻ t, ‖ψ t‖ₑ := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (-k) := by positivity
  have hmeas : Measurable fun s => ‖ψ s‖ₑ := ψ.continuous.measurable.enorm
  simp_rw [enorm_schwartzScale]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_comp_mul_left_of_pos h2 (h := fun s => ‖ψ s‖ₑ) hmeas, ← mul_assoc,
    ← ENNReal.ofReal_mul h2.le, mul_inv_cancel₀ h2.ne', ENNReal.ofReal_one, one_mul]

/-- `ψ ∈ L¹`. -/
theorem lintegral_enorm_schwartz_lt_top : ∫⁻ t, ‖ψ t‖ₑ < ∞ :=
  (ψ.integrable (μ := volume)).hasFiniteIntegral

/-- `ψ_k ∈ L¹`. -/
theorem lintegral_enorm_schwartzScale_lt_top : ∫⁻ t, ‖schwartzScale ψ k t‖ₑ < ∞ := by
  rw [lintegral_enorm_schwartzScale]
  exact lintegral_enorm_schwartz_lt_top ψ

/-- `∫ ψ_k = ∫ ψ`. -/
theorem integral_schwartzScale : ∫ t, schwartzScale ψ k t = ∫ t, ψ t := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (-k) := by positivity
  simp only [schwartzScale_apply]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun s => ψ s) ((2 : ℝ) ^ (-k)),
    abs_of_pos (inv_pos.2 h2), Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    mul_inv_cancel₀ h2.ne']
  simp

/-- A Schwartz function is bounded. -/
theorem exists_bound_schwartz : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖ψ x‖ ≤ M :=
  ⟨‖ψ.toBoundedContinuousFunction‖, norm_nonneg _, fun x =>
    ψ.toBoundedContinuousFunction.norm_coe_le_norm x⟩

/-- `ψ_k` is bounded (in `ℝ≥0∞`). -/
theorem exists_enorm_bound_schwartzScale : ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ t, ‖schwartzScale ψ k t‖ₑ ≤ M := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_schwartz ψ
  refine ⟨ENNReal.ofReal ((2 : ℝ) ^ (-k)) * ENNReal.ofReal M,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, fun t => ?_⟩
  rw [enorm_schwartzScale]
  refine mul_le_mul_right ?_ _
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hM _)

end Schwartz

/-! ### Cauchy-Schwarz and the Schur test for convolution kernels -/

/-- A convolution against a bounded integrable kernel converges for `g ∈ L²`. -/
theorem lintegral_conv_lt_top {Φ : ℝ → ℝ≥0∞} (hΦ : Measurable Φ) (hΦ1 : ∫⁻ t, Φ t < ∞)
    {M : ℝ≥0∞} (hM : M ≠ ∞) (hΦM : ∀ t, Φ t ≤ M) {g : ℝ → ℂ} (hg : Measurable g)
    (hgL : ∫⁻ y, ‖g y‖ₑ ^ 2 < ∞) (x : ℝ) : ∫⁻ y, Φ (x - y) * ‖g y‖ₑ < ∞ := by
  have hk : Measurable fun y => Φ (x - y) := hΦ.comp (measurable_const.sub measurable_id)
  have hCS := lintegral_mul_sq_le (ν := volume) hk hg.enorm
  have h1 : ∫⁻ y, Φ (x - y) = ∫⁻ t, Φ t := lintegral_sub_left_eq_self Φ x
  have h2 : ∫⁻ y, Φ (x - y) * ‖g y‖ₑ ^ 2 ≤ M * ∫⁻ y, ‖g y‖ₑ ^ 2 := by
    calc ∫⁻ y, Φ (x - y) * ‖g y‖ₑ ^ 2 ≤ ∫⁻ y, M * ‖g y‖ₑ ^ 2 :=
          lintegral_mono fun y => mul_le_mul_left (hΦM _) _
      _ = M * ∫⁻ y, ‖g y‖ₑ ^ 2 := lintegral_const_mul _ (hg.enorm.pow_const 2)
  have h3 : (∫⁻ y, Φ (x - y) * ‖g y‖ₑ) ^ 2 < ∞ := by
    refine lt_of_le_of_lt hCS ?_
    rw [h1]
    exact ENNReal.mul_lt_top hΦ1 (lt_of_le_of_lt h2 (ENNReal.mul_lt_top hM.lt_top hgL))
  by_contra hcon
  rw [not_lt, top_le_iff] at hcon
  rw [hcon] at h3
  simp at h3

/-- **Schur's test for a convolution kernel** (`p = 2`, `F ≤ Φ * |g|`):
`‖F‖₂² ≤ ‖Φ‖₁² ‖g‖₂²`. -/
theorem sqn_conv_le {Φ : ℝ → ℝ≥0∞} (hΦ : Measurable Φ) {g : ℝ → ℂ} (hg : Measurable g)
    {F : ℝ → ℝ≥0∞} (hF : ∀ x, F x ≤ ∫⁻ y, Φ (x - y) * ‖g y‖ₑ) :
    ∫⁻ x, F x ^ 2 ≤ (∫⁻ t, Φ t) ^ 2 * ∫⁻ y, ‖g y‖ₑ ^ 2 := by
  have hK : Measurable (Function.uncurry fun x y : ℝ => Φ (x - y)) :=
    hΦ.comp (measurable_fst.sub measurable_snd)
  have := lintegral_rpow_le_of_le_lintegral_kernel (μ := volume) (ν := volume) hK hg.enorm
    (c := ∫⁻ t, Φ t) (fun x => le_of_eq (lintegral_sub_left_eq_self Φ x))
    (fun y => le_of_eq (lintegral_sub_right_eq_self Φ y)) hF (p := 2) (by norm_num)
  simpa [ENNReal.rpow_two] using this

section Avg

variable (ψ : 𝓢(ℝ, ℂ)) (k : ℤ)

/-- The convolution integral `∫ ψ_k(x - y) g(y) dy` converges absolutely for `g ∈ L²`. -/
theorem integrable_schwartzScale_mul {g : ℝ → ℂ} (hg : Measurable g)
    (hgL : ∫⁻ y, ‖g y‖ₑ ^ 2 < ∞) (x : ℝ) :
    Integrable (fun y => schwartzScale ψ k (x - y) * g y) := by
  obtain ⟨M, hM, hΦM⟩ := exists_enorm_bound_schwartzScale ψ k
  refine ⟨((measurable_schwartzScale ψ k).comp
    (measurable_const.sub measurable_id)).mul hg |>.aestronglyMeasurable, ?_⟩
  have := lintegral_conv_lt_top (Φ := fun t => ‖schwartzScale ψ k t‖ₑ)
    (measurable_schwartzScale ψ k).enorm (lintegral_enorm_schwartzScale_lt_top ψ k) hM hΦM hg hgL x
  change ∫⁻ y, ‖schwartzScale ψ k (x - y) * g y‖ₑ < ∞
  simpa only [enorm_mul] using this

/-- `|A_k g(x)| ≤ ∫ |ψ_k(x - y)| |g(y)| dy`. -/
theorem enorm_schwartzAvg_le {g : ℝ → ℂ} (x : ℝ) :
    ‖schwartzAvg ψ k g x‖ₑ ≤ ∫⁻ y, ‖schwartzScale ψ k (x - y)‖ₑ * ‖g y‖ₑ := by
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  simp only [enorm_mul]

/-- **Young's inequality**: `‖A_k g‖₂² ≤ ‖ψ‖₁² ‖g‖₂²`. -/
theorem sqn_schwartzAvg_le {g : ℝ → ℂ} (hg : Measurable g) :
    ∫⁻ x, ‖schwartzAvg ψ k g x‖ₑ ^ 2 ≤ (∫⁻ t, ‖ψ t‖ₑ) ^ 2 * ∫⁻ y, ‖g y‖ₑ ^ 2 := by
  have := sqn_conv_le (Φ := fun t => ‖schwartzScale ψ k t‖ₑ)
    (measurable_schwartzScale ψ k).enorm hg (F := fun x => ‖schwartzAvg ψ k g x‖ₑ)
    (fun x => enorm_schwartzAvg_le ψ k x)
  rwa [lintegral_enorm_schwartzScale] at this

/-- `A_k g` is measurable for measurable `g`. -/
theorem measurable_schwartzAvg {g : ℝ → ℂ} (hg : Measurable g) :
    Measurable (schwartzAvg ψ k g) := by
  have h : Measurable fun p : ℝ × ℝ => schwartzScale ψ k (p.1 - p.2) * g p.2 :=
    ((measurable_schwartzScale ψ k).comp (measurable_fst.sub measurable_snd)).mul
      (hg.comp measurable_snd)
  exact (h.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

/-- Additivity of `A_k` on `L²`. -/
theorem schwartzAvg_add {g h : ℝ → ℂ} (hg : Measurable g) (hgL : ∫⁻ y, ‖g y‖ₑ ^ 2 < ∞)
    (hh : Measurable h) (hhL : ∫⁻ y, ‖h y‖ₑ ^ 2 < ∞) (x : ℝ) :
    schwartzAvg ψ k (g + h) x = schwartzAvg ψ k g x + schwartzAvg ψ k h x := by
  simp only [schwartzAvg, Pi.add_apply, mul_add]
  exact integral_add (integrable_schwartzScale_mul ψ k hg hgL x)
    (integrable_schwartzScale_mul ψ k hh hhL x)

/-- `A_k g` only depends on the a.e. class of `g`. -/
theorem schwartzAvg_congr_ae {g h : ℝ → ℂ} (hgh : g =ᵐ[volume] h) (x : ℝ) :
    schwartzAvg ψ k g x = schwartzAvg ψ k h x := by
  simp only [schwartzAvg]
  refine integral_congr_ae ?_
  filter_upwards [hgh] with y hy
  rw [hy]

end Avg

end PrimeCarleson.Proof.Oplus
