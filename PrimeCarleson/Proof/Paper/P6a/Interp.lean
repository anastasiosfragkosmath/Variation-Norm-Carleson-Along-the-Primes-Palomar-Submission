module

public import PrimeCarleson.Proof.Paper.P6a.Basic

/-!
# The auxiliary exponent and the interpolation of `varOp`

Source: main paper `p:red-var`, L1324 (the auxiliary exponent) and the three interpolations of the
proof (L1374–L1375, L1456–L1457, L1504–L1507), done by the Marcinkiewicz theorem
(`PrimeCarleson.Proof.Common.Interpolation`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- **The auxiliary exponent** (Source: main paper `p:red-var`, L1324): for `r > 2`, `r' = r/(r-1)`,
`p > r'`, `p ≠ 2`, there are `s ≥ r'` on the other side of `p` from `2` (`s < p` if `p < 2`, `s > p`
if `p > 2`, i.e. `p` lies strictly between `2` and `s`) and `θ ∈ (0, 1)` with
`1/p = θ/2 + (1 - θ)/s`. -/
theorem auxiliary_exponent {r p : ℝ} (hr : 2 < r) (hp : r / (r - 1) < p) (hp2 : p ≠ 2) :
    ∃ s θ : ℝ, r / (r - 1) ≤ s ∧ (p < 2 → s < p) ∧ (2 < p → p < s) ∧ 0 < θ ∧ θ < 1 ∧
      1 / p = θ / 2 + (1 - θ) / s := by
  have hr1 : 0 < r - 1 := by linarith
  have hr'2 : r / (r - 1) < 2 := by rw [div_lt_iff₀ hr1]; linarith
  have hr'1 : 1 < r / (r - 1) := by rw [lt_div_iff₀ hr1]; linarith
  have hp0 : 0 < p := by linarith
  rcases lt_or_gt_of_ne hp2 with hlt | hgt
  · -- `r' < p < 2`: `s ∈ [r', p)`
    set s : ℝ := (r / (r - 1) + p) / 2 with hs
    have hs1 : r / (r - 1) ≤ s := by rw [hs]; linarith
    have hs2 : s < p := by rw [hs]; linarith
    have hs0 : 0 < s := by linarith
    have hden : 1 / 2 - 1 / s < 0 := by
      have : 1 / 2 < 1 / s := by
        rw [div_lt_div_iff₀ (by norm_num) hs0]; linarith
      linarith
    have hnum : 1 / p - 1 / s < 0 := by
      have : 1 / p < 1 / s := one_div_lt_one_div_of_lt hs0 hs2
      linarith
    set θ : ℝ := (1 / p - 1 / s) / (1 / 2 - 1 / s) with hθ
    have hθ1 : θ * (1 / 2 - 1 / s) = 1 / p - 1 / s := div_mul_cancel₀ _ hden.ne
    refine ⟨s, θ, hs1, fun _ => hs2, fun h => absurd h (by linarith),
      div_pos_of_neg_of_neg hnum hden, ?_, ?_⟩
    · rw [hθ, div_lt_one_of_neg hden]
      have : 1 / 2 < 1 / p := by rw [div_lt_div_iff₀ (by norm_num) hp0]; linarith
      linarith
    · linear_combination (-1 : ℝ) * hθ1
  · -- `p > 2`: `s = p + 1 > p`
    set s : ℝ := p + 1 with hs
    have hs1 : r / (r - 1) ≤ s := by rw [hs]; linarith
    have hs0 : 0 < s := by linarith
    have hden : 0 < 1 / 2 - 1 / s := by
      have : 1 / s < 1 / 2 := by rw [div_lt_div_iff₀ hs0 (by norm_num)]; linarith
      linarith
    have hnum : 0 < 1 / p - 1 / s := by
      have : 1 / s < 1 / p := one_div_lt_one_div_of_lt hp0 (by rw [hs]; linarith)
      linarith
    set θ : ℝ := (1 / p - 1 / s) / (1 / 2 - 1 / s) with hθ
    have hθ1 : θ * (1 / 2 - 1 / s) = 1 / p - 1 / s := div_mul_cancel₀ _ hden.ne'
    refine ⟨s, θ, hs1, fun h => absurd h (by linarith), fun _ => by rw [hs]; linarith,
      div_pos hnum hden, ?_, ?_⟩
    · rw [hθ, div_lt_one hden]
      have : 1 / p < 1 / 2 := by rw [div_lt_div_iff₀ hp0 (by norm_num)]; linarith
      linarith
    · linear_combination (-1 : ℝ) * hθ1

/-- **Interpolation of `varOp`**: for `r > 2`, `p > r'` there are `s ≥ r'` (with `s = 2` if
`p = 2`), `ϑ ∈ (0, 1]` (`ϑ = 1` iff `p = 2`) and `C ≥ 0` such that every weight `u` whose operator
`f ↦ V^r(∑_n f(x-n) u(n) e(λ n) : λ)` is bounded on `ℓ²` with norm `≤ M₀` and on `ℓ^s` with norm
`≤ M₁` (on finitely supported `f`) is bounded on `ℓ^p` with norm `≤ C M₀^ϑ M₁^{1-ϑ}`. -/
theorem varOp_interp {r p : ℝ} (hr : 2 < r) (hp : r / (r - 1) < p) :
    ∃ s ϑ C : ℝ, r / (r - 1) ≤ s ∧ 0 < ϑ ∧ ϑ ≤ 1 ∧ 0 ≤ C ∧
      ∀ (u : ℤ → ℂ) (M₀ M₁ : ℝ), 0 < M₀ → 0 < M₁ →
        (∀ f : ℤ →₀ ℂ, eLpNorm (varOp r u (⇑f)) (ENNReal.ofReal 2) Measure.count ≤
          ENNReal.ofReal M₀ * eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count) →
        (∀ f : ℤ →₀ ℂ, eLpNorm (varOp r u (⇑f)) (ENNReal.ofReal s) Measure.count ≤
          ENNReal.ofReal M₁ * eLpNorm (⇑f) (ENNReal.ofReal s) Measure.count) →
        ∀ f : ℤ →₀ ℂ, eLpNorm (varOp r u (⇑f)) (ENNReal.ofReal p) Measure.count ≤
          ENNReal.ofReal (C * M₀ ^ ϑ * M₁ ^ (1 - ϑ)) *
            eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  have hr1 : 0 < r - 1 := by linarith
  have hr'2 : r / (r - 1) < 2 := by rw [div_lt_iff₀ hr1]; linarith
  have hr'0 : 0 < r / (r - 1) := div_pos (by linarith) hr1
  by_cases hp2 : p = 2
  · subst hp2
    refine ⟨2, 1, 1, hr'2.le, one_pos, le_rfl, zero_le_one, fun u M₀ M₁ hM₀ hM₁ h₀ _ f => ?_⟩
    simpa [Real.rpow_one, Real.rpow_zero] using h₀ f
  · obtain ⟨s, θ, hs, -, -, hθ0, hθ1, hpθ⟩ := auxiliary_exponent hr hp hp2
    have hs0 : 0 < s := lt_of_lt_of_le hr'0 hs
    have hs2 : s ≠ 2 := by
      rintro rfl
      have : 1 / p = 1 / 2 := by rw [hpθ]; ring
      have h3 : p⁻¹ = (2 : ℝ)⁻¹ := by simpa [one_div] using this
      exact hp2 (inv_inj.1 h3)
    have hp0 : 0 < p := lt_trans hr'0 hp
    obtain ⟨Cint, hCint⟩ :=
      PrimeCarleson.Proof.Common.exists_eLpNorm_count_le_interpolation_finsupp_ofReal
      (α := ℤ) (β := ℤ) (E := ℂ) (ε := ℝ≥0∞) (p₀ := 2) (p₁ := s) (p := p) (θ := 1 - θ)
      (by norm_num) hs0 (Ne.symm hs2) (by linarith) (by linarith) (by rw [hpθ]; ring_nf)
    refine ⟨s, θ, Cint, hs, hθ0, hθ1.le, Cint.2, fun u M₀ M₁ hM₀ hM₁ h₀ h₁ f => ?_⟩
    have key := hCint (fun g => varOp r u (⇑g)) M₀.toNNReal M₁.toNNReal
      (by simpa using hM₀) (by simpa using hM₁)
      (fun g g' x => by simpa using varOp_add_left_le (by linarith) u g g' x)
      (fun g => by simpa [ENNReal.ofReal] using h₀ g)
      (fun g => by simpa [ENNReal.ofReal] using h₁ g) f
    refine key.trans (le_of_eq ?_)
    rw [show 1 - (1 - θ) = θ by ring]
    congr 1
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_rpow_of_nonneg hM₀.le hθ0.le,
      ← ENNReal.ofReal_rpow_of_nonneg hM₁.le (by linarith), ENNReal.ofReal_coe_nnreal]
    rfl

end PrimeCarleson.Proof.Paper
