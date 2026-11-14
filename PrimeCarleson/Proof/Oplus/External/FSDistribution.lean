module

public import PrimeCarleson.Proof.Oplus.External.FSLevelSets
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# The distribution function of the dyadic maximal function and the `L^q` estimate

Steps 4-5 of the proof of the interpolation between `L¹` and dyadic BMO (see `FSLevelSets.lean` for
Steps 1-3). With `D(t) = |Ω_t|` (`levelUnion`), `A = ∫ g` and the mean oscillation bound `b > 0`:

* `volume_levelUnion_le_inv`: `D(t) ≤ A/t` (Step 1);
* `volume_levelUnion_le_exp`: `D(t) ≤ (A/b) exp(-(log 2/(4b)) t)` for `t ≥ 4b` (Step 3, iterated);
* `lintegral_ofReal_rpow_le`: if `g ≥ 0` is integrable with `g ≤ M_D g` almost everywhere
  (`DyadicDominated`), then for `q > 1`
  `∫ g^q ≤ K_q b^{q-1} ∫ g` with
  `K_q = q (4^{q-1}/(q-1) + 4^q Γ(q)/(log 2)^q)`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

variable {g : ℝ → ℝ}

/-- **Step 1**: `|Ω_t| ≤ (∫ g)/t`. -/
theorem volume_levelUnion_le_inv (hg0 : ∀ x, 0 ≤ g x) (hgi : Integrable g) {t : ℝ} (ht : 0 < t) :
    volume (levelUnion g t) ≤ ENNReal.ofReal ((∫ y, g y) / t) := by
  have h := mul_volume_levelUnion_le hg0 hgi ht
  rw [ENNReal.ofReal_div_of_pos ht, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using ht))
    (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact h

/-- **Exponential decay of the level sets** (Step 3 iterated):
`|Ω_t| ≤ (A/b) exp(-(log 2/(4b)) t)` for `t ≥ 4b`. -/
theorem volume_levelUnion_le_exp (hg0 : ∀ x, 0 ≤ g x) (hgi : Integrable g) {b : ℝ}
    (hb : MeanOscLe g b) (hb0 : 0 < b) {t : ℝ} (ht : 4 * b ≤ t) :
    volume (levelUnion g t) ≤
      ENNReal.ofReal ((∫ y, g y) / b * Real.exp (-(Real.log 2 / (4 * b)) * t)) := by
  set A := ∫ y, g y with hA
  have h4b : 0 < 4 * b := by linarith
  set x := t / (4 * b) with hx
  have hx1 : 1 ≤ x := by rw [hx, le_div_iff₀ h4b]; linarith
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx1)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ⌊x⌋₊ = n + 1 := ⟨⌊x⌋₊ - 1, by omega⟩
  have hn1 : (n : ℝ) + 1 ≤ x := by
    have := Nat.floor_le (by linarith : 0 ≤ x)
    rw [hn] at this; push_cast at this; linarith
  have hn2 : x < n + 2 := by
    have := Nat.lt_floor_add_one x
    rw [hn] at this; push_cast at this; linarith
  set lam0 := t - 4 * b * n with hlam0
  have htx : t = 4 * b * x := by rw [hx]; field_simp
  have hlam0b : 4 * b ≤ lam0 := by
    rw [hlam0, htx]; nlinarith
  have hlam0pos : 0 < lam0 := by linarith
  have hit := two_pow_mul_volume_levelUnion_le hg0 hgi hb hb0 hlam0pos n
  have e : lam0 + 4 * b * n = t := by rw [hlam0]; ring
  rw [e] at hit
  have hD0 : volume (levelUnion g lam0) ≤ ENNReal.ofReal (A / (4 * b)) := by
    refine (volume_levelUnion_le_inv hg0 hgi hlam0pos).trans (ENNReal.ofReal_le_ofReal ?_)
    exact div_le_div_of_nonneg_left (integral_nonneg hg0) h4b hlam0b
  have hit2 : (2 : ℝ≥0∞) ^ n * volume (levelUnion g t) ≤ ENNReal.ofReal (A / (4 * b)) :=
    hit.trans hD0
  have h2n : ((2 : ℝ≥0∞) ^ n)⁻¹ * (2 ^ n * volume (levelUnion g t)) = volume (levelUnion g t) := by
    rw [← mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
  have hD : volume (levelUnion g t) ≤ ((2 : ℝ≥0∞) ^ n)⁻¹ * ENNReal.ofReal (A / (4 * b)) := by
    calc volume (levelUnion g t)
        = ((2 : ℝ≥0∞) ^ n)⁻¹ * (2 ^ n * volume (levelUnion g t)) := h2n.symm
      _ ≤ _ := by gcongr
  refine hD.trans ?_
  have hinv : ((2 : ℝ≥0∞) ^ n)⁻¹ = ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_div_of_pos (by norm_num)]
    simp [ENNReal.inv_pow]
  rw [hinv, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  -- `(1/2)^n ≤ 4 exp(-x log 2)`
  have hA0 : 0 ≤ A := integral_nonneg hg0
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hct : -(Real.log 2 / (4 * b)) * t = -(x * Real.log 2) := by
    rw [htx]; field_simp
  have h1 : ((1 : ℝ) / 2) ^ n = Real.exp (-(n * Real.log 2)) := by
    rw [one_div, inv_pow, ← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul,
      ← Real.exp_neg]
    simp [Real.exp_log]
  have h2 : Real.exp (-(n * Real.log 2)) ≤ 4 * Real.exp (-(x * Real.log 2)) := by
    have : -(n * Real.log 2) ≤ Real.log 4 + -(x * Real.log 2) := by
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      rw [h4]; nlinarith
    calc Real.exp (-(n * Real.log 2)) ≤ Real.exp (Real.log 4 + -(x * Real.log 2)) :=
          Real.exp_le_exp.2 this
      _ = 4 * Real.exp (-(x * Real.log 2)) := by
          rw [Real.exp_add, Real.exp_log (by norm_num)]
  rw [hct, h1]
  calc Real.exp (-(n * Real.log 2)) * (A / (4 * b))
      ≤ 4 * Real.exp (-(x * Real.log 2)) * (A / (4 * b)) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = A / b * Real.exp (-(x * Real.log 2)) := by field_simp

end PrimeCarleson.Proof.Oplus
