module

public import PrimeCarleson.Proof.Paper.P6a.Basic
public import PrimeCarleson.Proof.Paper.P9.GlobalShell
public import PrimeCarleson.Proof.Paper.P9.VarTools
public import PrimeCarleson.Proof.Paper.P7.Adapter

/-!
# The `ℓ²` power saving for `V^{Q,r}` from the cheap bound and the maximal saving

Source: main paper `s:red`, L1747–L1753 and L1754–L1760. Fix `0 < α < 1 - 2/r` and `ρ = r(1-α) > 2`.

* `scalar_interpolation_pointwise`: `V^{Q,r} f ≤ 2 (V^{Q,ρ} f)^{1-α} (C^Q f)^α` pointwise;
* `eLpNorm_two_holder`: Hölder in `ℓ²`, `‖A^{1-α} B^α‖₂ ≤ ‖A‖₂^{1-α} ‖B‖₂^α`;
* `holder_l2_saving`: the two `ℓ²` inputs give `‖V^{Q,r} f‖₂ ≲ Q^{δ(1-α) - εα/2} ‖f‖₂`;
* `var_l2_power_saving`: the inputs are `p:global-shell-var` (`P9/`, `global_shell_var`, with the
  loss `Q^δ`) and the named `Prop` `CQL2Saving` (the `ℓ²`
  saving for `C^Q`, a hypothesis here, proved in `P10/BlockSum.lean`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Common

/-- **The `ℓ²` saving for `C^Q`** (Source: main paper `s:number`, L1742–L1746, as the input of the
Hölder step below): the `ℓ²` saving of the maximal operator, `‖C^Q f‖₂ ≤ C Q^{-ε/2} ‖f‖₂` for every
dyadic `Q = 2^j` and finitely supported `f`, `ε = S.P.ε`. A named `Prop`: it is proved in
`P10/BlockSum.lean` and is a hypothesis of the theorems below. -/
def CQL2Saving (S : KQSetup) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (f : ℤ →₀ ℂ),
    eLpNorm (S.CQ (2 ^ j) (⇑f)) (ENNReal.ofReal 2) Measure.count ≤
      ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ (-(S.P.ε / 2))) *
        eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count

/-- **The pointwise interpolation** (Source: main paper `s:red`, L1747–L1753): for `r > 2`,
`0 < α < 1 - 2/r`, `ρ = r(1-α) > 2`: `V^{Q,r} f(x) ≤ 2 (V^{Q,ρ} f(x))^{1-α} (C^Q f(x))^α`. -/
theorem scalar_interpolation_pointwise (S : KQSetup) {r α : ℝ} (hr : 2 < r) (hα0 : 0 < α)
    (hα1 : α < 1 - 2 / r) (Q : ℕ) (f : ℤ →₀ ℂ) (x : ℤ) :
    S.VQr r Q (⇑f) x ≤
      2 * (S.VQr (r * (1 - α)) Q (⇑f) x ^ (1 - α) * S.CQ Q (⇑f) x ^ α) := by
  have hr0 : 0 < r := by linarith
  have hα1' : α < 1 := by
    have : 0 < 2 / r := by positivity
    linarith
  have hρ : 0 < r * (1 - α) := mul_pos hr0 (by linarith)
  have hρr : r * (1 - α) ≤ r := by nlinarith
  have h := rVariationOn_le_interpolate (r := r) hρ hρr (Set.Ico (0 : ℝ) 1)
    (fun t => S.TQ Q t (⇑f) x)
  have hq : r * (1 - α) / r = 1 - α := by field_simp
  rw [hq] at h
  have h1 : 1 - (1 - α) = α := by ring
  rw [h1] at h
  have hVQ : ∀ ρ' : ℝ, S.VQr ρ' Q (⇑f) x =
      rVariationOn ρ' (Set.Ico 0 1) (fun t => S.TQ Q t (⇑f) x) := fun _ => rfl
  have hCQ : S.CQ Q (⇑f) x = ⨆ t ∈ Set.Ico (0 : ℝ) 1, ‖S.TQ Q t (⇑f) x‖ₑ := rfl
  rw [hVQ, hVQ, hCQ]
  refine h.trans ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ hα0.le]
  have h2 : (2 : ℝ≥0∞) ^ α ≤ 2 := by
    calc (2 : ℝ≥0∞) ^ α ≤ 2 ^ (1 : ℝ) :=
          ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hα1'.le
      _ = 2 := ENNReal.rpow_one 2
  calc _ = (2 : ℝ≥0∞) ^ α * (rVariationOn (r * (1 - α)) (Set.Ico 0 1) (fun t => S.TQ Q t (⇑f) x) ^
        (1 - α) * (⨆ t ∈ Set.Ico (0 : ℝ) 1, ‖S.TQ Q t (⇑f) x‖ₑ) ^ α) := by ring
    _ ≤ _ := mul_le_mul_left h2 _

/-- **Hölder in `ℓ²`** (L1760): for `0 < α < 1`,
`‖A^{1-α} B^α‖₂ ≤ ‖A‖₂^{1-α} ‖B‖₂^α` for `ℝ≥0∞`-valued sequences on `ℤ`. -/
theorem eLpNorm_two_holder (A B : ℤ → ℝ≥0∞) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    eLpNorm (fun x => A x ^ (1 - α) * B x ^ α) (ENNReal.ofReal 2) Measure.count ≤
      eLpNorm A (ENNReal.ofReal 2) Measure.count ^ (1 - α) *
        eLpNorm B (ENNReal.ofReal 2) Measure.count ^ α := by
  have h1α : 0 < 1 - α := by linarith
  have hpq : Real.HolderConjugate (1 / (1 - α)) (1 / α) := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ h1α]; linarith
    · field_simp
      ring
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.count : Measure ℤ) hpq
    (f := fun x => A x ^ (2 * (1 - α))) (g := fun x => B x ^ (2 * α))
    measurable_from_top.aemeasurable measurable_from_top.aemeasurable
  simp only [lintegral_count, Pi.mul_apply] at h
  have e1 : ∀ x, (A x ^ (2 * (1 - α))) ^ (1 / (1 - α)) = A x ^ (2 : ℝ) := fun x => by
    rw [← ENNReal.rpow_mul]
    congr 1
    field_simp
  have e2 : ∀ x, (B x ^ (2 * α)) ^ (1 / α) = B x ^ (2 : ℝ) := fun x => by
    rw [← ENNReal.rpow_mul]
    congr 1
    field_simp
  simp only [e1, e2, one_div_one_div] at h
  rw [eLpNorm_count_eq_tsum_enn _ two_pos, eLpNorm_count_eq_tsum_enn A two_pos,
    eLpNorm_count_eq_tsum_enn B two_pos]
  have e3 : ∀ x, (A x ^ (1 - α) * B x ^ α) ^ (2 : ℝ) = A x ^ (2 * (1 - α)) * B x ^ (2 * α) := by
    intro x
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    ring_nf
  simp_rw [e3]
  refine (ENNReal.rpow_le_rpow h (by norm_num)).trans (le_of_eq ?_)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  congr 2 <;> ring

/-- The exponent bookkeeping of the Hölder step. -/
theorem rpow_holder_combo {C₁ C₂ Q δ ε' α : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hQ : 0 < Q) :
    (C₁ * Q ^ δ) ^ (1 - α) * (C₂ * Q ^ (-ε')) ^ α =
      C₁ ^ (1 - α) * C₂ ^ α * Q ^ (δ * (1 - α) - ε' * α) := by
  rw [Real.mul_rpow hC₁ (Real.rpow_nonneg hQ.le _), Real.mul_rpow hC₂ (Real.rpow_nonneg hQ.le _),
    ← Real.rpow_mul hQ.le, ← Real.rpow_mul hQ.le]
  have h : Q ^ (δ * (1 - α)) * Q ^ (-ε' * α) = Q ^ (δ * (1 - α) - ε' * α) := by
    rw [← Real.rpow_add hQ]
    congr 1
    ring
  calc C₁ ^ (1 - α) * Q ^ (δ * (1 - α)) * (C₂ ^ α * Q ^ (-ε' * α))
      = C₁ ^ (1 - α) * C₂ ^ α * (Q ^ (δ * (1 - α)) * Q ^ (-ε' * α)) := by ring
    _ = _ := by rw [h]

/-- **The Hölder step** (Source: main paper `s:red`, L1754–L1760): for `0 < α < 1 - 2/r` and
`ρ = r(1-α)`, if `‖V^{Q,ρ} f‖₂ ≤ C₁ Q^δ ‖f‖₂` and `‖C^Q f‖₂ ≤ C₂ Q^{-ε'} ‖f‖₂` for all dyadic `Q`,
then `‖V^{Q,r} f‖₂ ≤ 2 C₁^{1-α} C₂^α Q^{δ(1-α) - ε' α} ‖f‖₂` (Hölder in `ℓ²` after the pointwise
interpolation); with `ε' = ε/2` this is the paper's `Q^{o(1) - εα/2}`. -/
theorem holder_l2_saving (S : KQSetup) {r α C₁ δ C₂ ε' : ℝ} (hr : 2 < r) (hα0 : 0 < α)
    (hα1 : α < 1 - 2 / r) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (h1 : ∀ (j : ℕ) (f : ℤ →₀ ℂ),
      eLpNorm (S.VQr (r * (1 - α)) (2 ^ j) (⇑f)) (ENNReal.ofReal 2) Measure.count ≤
        ENNReal.ofReal (C₁ * ((2 : ℝ) ^ j) ^ δ) *
          eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count)
    (h2 : ∀ (j : ℕ) (f : ℤ →₀ ℂ),
      eLpNorm (S.CQ (2 ^ j) (⇑f)) (ENNReal.ofReal 2) Measure.count ≤
        ENNReal.ofReal (C₂ * ((2 : ℝ) ^ j) ^ (-ε')) *
          eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count)
    (j : ℕ) (f : ℤ →₀ ℂ) :
    eLpNorm (S.VQr r (2 ^ j) (⇑f)) (ENNReal.ofReal 2) Measure.count ≤
      ENNReal.ofReal (2 * C₁ ^ (1 - α) * C₂ ^ α * ((2 : ℝ) ^ j) ^ (δ * (1 - α) - ε' * α)) *
        eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count := by
  have hα1' : α < 1 := by
    have hr0 : 0 < r := by linarith
    have : 0 < 2 / r := by positivity
    linarith
  have hQ : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  set X := eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count with hX
  have hpt : ∀ x : ℤ, S.VQr r (2 ^ j) (⇑f) x ≤
      2 * (S.VQr (r * (1 - α)) (2 ^ j) (⇑f) x ^ (1 - α) * S.CQ (2 ^ j) (⇑f) x ^ α) :=
    fun x => scalar_interpolation_pointwise S hr hα0 hα1 (2 ^ j) f x
  refine (eLpNorm_count_mono_enn hpt _).trans ?_
  rw [eLpNorm_count_const_mul _ _ two_pos]
  refine (mul_le_mul_right (eLpNorm_two_holder _ _ hα0 hα1') _).trans ?_
  have hA := ENNReal.rpow_le_rpow (h1 j f) (by linarith : 0 ≤ 1 - α)
  have hB := ENNReal.rpow_le_rpow (h2 j f) hα0.le
  refine (mul_le_mul_right (mul_le_mul' hA hB) _).trans (le_of_eq ?_)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ 1 - α),
    ENNReal.mul_rpow_of_nonneg _ _ hα0.le,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith : 0 ≤ 1 - α),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) hα0.le]
  rw [← hX]
  have hXX : X ^ (1 - α) * X ^ α = X := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by linarith : 0 ≤ 1 - α) hα0.le]
    simp
  have hreal := rpow_holder_combo (C₁ := C₁) (C₂ := C₂) (δ := δ) (ε' := ε') (α := α) hC₁ hC₂ hQ
  have hnn : (0 : ℝ) ≤ 2 := by norm_num
  calc (2 : ℝ≥0∞) * (ENNReal.ofReal ((C₁ * ((2 : ℝ) ^ j) ^ δ) ^ (1 - α)) * X ^ (1 - α) *
        (ENNReal.ofReal ((C₂ * ((2 : ℝ) ^ j) ^ (-ε')) ^ α) * X ^ α))
      = (2 : ℝ≥0∞) * (ENNReal.ofReal ((C₁ * ((2 : ℝ) ^ j) ^ δ) ^ (1 - α)) *
          ENNReal.ofReal ((C₂ * ((2 : ℝ) ^ j) ^ (-ε')) ^ α)) * (X ^ (1 - α) * X ^ α) := by ring
    _ = ENNReal.ofReal (2 * C₁ ^ (1 - α) * C₂ ^ α *
          ((2 : ℝ) ^ j) ^ (δ * (1 - α) - ε' * α)) * X := by
        rw [hXX, ← ENNReal.ofReal_mul (by positivity), hreal, ← ENNReal.ofReal_ofNat 2,
          ← ENNReal.ofReal_mul hnn]
        congr 2
        ring

/-- **The `ℓ²` power saving for `V^{Q,r}`** (Source: main paper `s:red`, L1735–L1760): for `r > 2`,
`0 < α < 1 - 2/r` and every `δ > 0` there is `C` with `‖V^{Q,r} f‖₂ ≤ C Q^{δ - εα/2} ‖f‖₂` for every
dyadic `Q = 2^j` (`ε = S.P.ε`; the paper's `Q^{o(1) - εα/2}`). Inputs: `p:global-shell-var` of `P9/`
(through `hO : OplusVariationBound` and `l:varcarZ`, `lVarCarZ_of_oplus`) under the support
conditions `SupportBlock` and `SupportScale (1/16)` on the cutoff `φ`, and `CQL2Saving S` (the `ℓ²`
saving for `C^Q`). -/
theorem var_l2_power_saving (hO : OplusVariationBound) (S : KQSetup)
    (hS : S.P.SupportBlock S.δ) (hSc : S.P.SupportScale S.δ (1 / 16)) (hC : CQL2Saving S)
    {r α : ℝ} (hr : 2 < r) (hα0 : 0 < α) (hα1 : α < 1 - 2 / r) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (f : ℤ →₀ ℂ),
      eLpNorm (S.VQr r (2 ^ j) (⇑f)) (ENNReal.ofReal 2) Measure.count ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ (δ - S.P.ε * α / 2)) *
          eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count := by
  have hr0 : 0 < r := by linarith
  have hα1' : α < 1 := by
    have : 0 < 2 / r := by positivity
    linarith
  have hρ : 2 < r * (1 - α) := by
    have h1 : 2 / r < 1 - α := by linarith
    rw [div_lt_iff₀ hr0] at h1
    linarith
  obtain ⟨C₁, hC₁0, hC₁⟩ := global_shell_var S hS hSc hρ hδ (lVarCarZ_of_oplus hO)
  obtain ⟨C₂, hC₂0, hC₂⟩ := hC
  have h1 : ∀ (j : ℕ) (f : ℤ →₀ ℂ),
      eLpNorm (S.VQr (r * (1 - α)) (2 ^ j) (⇑f)) (ENNReal.ofReal 2) Measure.count ≤
        ENNReal.ofReal (C₁ * ((2 : ℝ) ^ j) ^ δ) *
          eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count := by
    intro j f
    rw [eLpNorm_two_eq_tsum_sq, eLpNorm_two_eq_tsum_sq']
    exact hC₁ j f
  refine ⟨2 * C₁ ^ (1 - α) * C₂ ^ α, by positivity, fun j f => ?_⟩
  refine (holder_l2_saving S hr hα0 hα1 hC₁0 hC₂0 h1 hC₂ j f).trans ?_
  refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
  have hQ1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hε := S.P.ε_pos
  have h2 : ((2 : ℝ) ^ j) ^ (δ * (1 - α) - S.P.ε / 2 * α) ≤
      ((2 : ℝ) ^ j) ^ (δ - S.P.ε * α / 2) := by
    refine Real.rpow_le_rpow_of_exponent_le hQ1 ?_
    nlinarith
  have h3 : 0 ≤ 2 * C₁ ^ (1 - α) * C₂ ^ α := by positivity
  exact mul_le_mul_of_nonneg_left h2 h3

end PrimeCarleson.Proof.Paper
