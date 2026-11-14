module

public import PrimeCarleson.Proof.Common.FourierR
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Schwartz bumps and the `L¹` norm of their inverse Fourier transforms

Helper for the Fourier cutoff of [O+] `linearizedtheorem` ([O+] L921-L926). With `θ` a smooth bump,
`θ = 1` on `[-1, 1]`, `supp θ ⊆ [-2, 2]`, `0 ≤ θ ≤ 1`:

* `bumpS a s` is the Schwartz function `η ↦ θ((η - a)/s)`, for `s > 0` (compactly supported);
* `fourierInv_bumpS`: `𝓕⁻(bumpS a s)(y) = s e(a y) 𝓕⁻(bumpS 0 1)(s y)` (dilation and modulation
  of the inverse Fourier transform);
* `integral_norm_fourierInv_bumpS`: `‖𝓕⁻(bumpS a s)‖_{L¹} = ‖𝓕⁻(bumpS 0 1)‖_{L¹}` for every `a`
  and every `s > 0`: the `L¹` norm of the kernel does not depend on the position and the scale.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped FourierTransform SchwartzMap ContDiff ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

/-- The bump `θ`: `θ = 1` on `[-1, 1]`, supported in `[-2, 2]`, with values in `[0, 1]`. -/
def cutTheta : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The complex-valued bump `η ↦ θ((η - a)/s)`. -/
def bumpFn (a s η : ℝ) : ℂ := ((cutTheta ((η - a) / s) : ℝ) : ℂ)

/-- The bump `η ↦ θ((η - a)/s)` is smooth. -/
theorem contDiff_bumpFn (a s : ℝ) : ContDiff ℝ ∞ (bumpFn a s) :=
  Complex.ofRealCLM.contDiff.comp
    (cutTheta.contDiff.comp ((contDiff_id.sub contDiff_const).div_const s))

/-- The bump `η ↦ θ((η - a)/s)` has compact support for `s > 0`. -/
theorem hasCompactSupport_bumpFn (a : ℝ) {s : ℝ} (hs : 0 < s) : HasCompactSupport (bumpFn a s) := by
  refine HasCompactSupport.intro (isCompact_closedBall a (2 * s)) fun η hη => ?_
  have h1 : 2 * s < |η - a| := by
    simpa [Metric.mem_closedBall, Real.dist_eq] using hη
  have h2 : cutTheta.rOut ≤ dist ((η - a) / s) 0 := by
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hs, le_div_iff₀ hs]
    change 2 * s ≤ |η - a|
    linarith
  simp [bumpFn, cutTheta.zero_of_le_dist h2]

/-- The Schwartz bump `η ↦ θ((η - a)/s)` for `s > 0` (and `0` for `s ≤ 0`). -/
def bumpS (a s : ℝ) : 𝓢(ℝ, ℂ) :=
  if h : 0 < s then (hasCompactSupport_bumpFn a h).toSchwartzMap (contDiff_bumpFn a s) else 0

/-- The Schwartz bump is the function `bumpFn` for `s > 0`. -/
theorem bumpS_apply (a : ℝ) {s : ℝ} (hs : 0 < s) (η : ℝ) : bumpS a s η = bumpFn a s η := by
  simp only [bumpS, hs, ↓reduceDIte]
  rfl

/-- `|θ((η - a)/s)| ≤ 1`. -/
theorem norm_bumpFn_le_one (a s η : ℝ) : ‖bumpFn a s η‖ ≤ 1 := by
  simp only [bumpFn, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg cutTheta.nonneg]
  exact cutTheta.le_one

/-- `θ((η - a)/s) = 1` for `|η - a| ≤ s`. -/
theorem bumpFn_eq_one {a s η : ℝ} (hs : 0 < s) (h : |η - a| ≤ s) : bumpFn a s η = 1 := by
  have : cutTheta ((η - a) / s) = 1 := by
    refine cutTheta.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_div, abs_of_pos hs, div_le_iff₀ hs]
    change |η - a| ≤ 1 * s
    linarith
  simp [bumpFn, this]

/-- `θ((η - a)/s) = 0` for `|η - a| ≥ 2s`. -/
theorem bumpFn_eq_zero {a s η : ℝ} (hs : 0 < s) (h : 2 * s ≤ |η - a|) : bumpFn a s η = 0 := by
  have : cutTheta ((η - a) / s) = 0 := by
    refine cutTheta.zero_of_le_dist ?_
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hs, le_div_iff₀ hs]
    change 2 * s ≤ |η - a|
    linarith
  simp [bumpFn, this]

/-- **Dilation and modulation of the inverse Fourier transform of a bump**:
`𝓕⁻(bumpS a s)(y) = s e(a y) 𝓕⁻(bumpS 0 1)(s y)` for `s > 0`. -/
theorem fourierInv_bumpS (a : ℝ) {s : ℝ} (hs : 0 < s) (y : ℝ) :
    𝓕⁻ (⇑(bumpS a s)) y = (s : ℂ) * e (a * y) * 𝓕⁻ (⇑(bumpS 0 1)) (s * y) := by
  have hfun : ⇑(bumpS a s) = bumpFn a s := funext (bumpS_apply a hs)
  have hfun1 : ⇑(bumpS 0 1) = bumpFn 0 1 := funext (bumpS_apply 0 one_pos)
  rw [hfun, hfun1, fourierInv_eq_integral_e, fourierInv_eq_integral_e]
  set G : ℝ → ℂ := fun η => e (η * y) * bumpFn a s η with hG
  have h1 : ∫ η, G η = ∫ η, G (η + a) := (integral_add_right_eq_self G a).symm
  set H : ℝ → ℂ := fun η => G (η + a) with hH
  have h2 := Measure.integral_comp_mul_left H s
  have hs' : |s⁻¹| = s⁻¹ := abs_of_pos (inv_pos.2 hs)
  rw [hs'] at h2
  have h3 : ∫ η, H η = s • ∫ u, H (s * u) := by
    rw [h2, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  have h4 : ∀ u : ℝ, H (s * u) = e (a * y) * (e (u * (s * y)) * bumpFn 0 1 u) := by
    intro u
    simp only [hH, hG, bumpFn]
    have e1 : (s * u + a) * y = a * y + u * (s * y) := by ring
    have e2 : (s * u + a - a) / s = u := by field_simp; ring
    have e3 : (u - 0) / 1 = u := by ring
    rw [e1, e_add, e2, e3]
    ring
  calc ∫ η, e (η * y) * bumpFn a s η = ∫ η, G η := rfl
    _ = ∫ η, H η := h1
    _ = s • ∫ u, H (s * u) := h3
    _ = (s : ℂ) * e (a * y) * ∫ u, e (u * (s * y)) * bumpFn 0 1 u := by
        simp_rw [h4]
        rw [integral_const_mul, Complex.real_smul]
        ring

/-- The `L¹` norm of `𝓕⁻(bumpS a s)` is independent of `a` and `s > 0`. -/
theorem integral_norm_fourierInv_bumpS (a : ℝ) {s : ℝ} (hs : 0 < s) :
    ∫ y, ‖𝓕⁻ (⇑(bumpS a s)) y‖ = ∫ y, ‖𝓕⁻ (⇑(bumpS 0 1)) y‖ := by
  have h1 : ∀ y, ‖𝓕⁻ (⇑(bumpS a s)) y‖ = s * ‖𝓕⁻ (⇑(bumpS 0 1)) (s * y)‖ := by
    intro y
    rw [fourierInv_bumpS a hs, norm_mul, norm_mul, norm_e, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hs]
  simp_rw [h1]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun y => ‖𝓕⁻ (⇑(bumpS 0 1)) y‖) s,
    abs_of_pos (inv_pos.2 hs), smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]

end PrimeCarleson.Proof.Oplus
