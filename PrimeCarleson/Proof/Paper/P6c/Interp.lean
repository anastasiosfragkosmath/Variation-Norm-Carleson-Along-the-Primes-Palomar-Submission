module

public import PrimeCarleson.Proof.Paper.P6c.Basic
public import PrimeCarleson.Proof.Paper.P6b.Interp
public import PrimeCarleson.Proof.Paper.P6b.Weights

/-!
# Interpolation of the maximal operators `supOp`

Source: main paper `s:red`, L1525–L1528 ("the proof of `p:red-var` carries over"): the
interpolations of the residual sum, of the high-denominator sum and of the maximal part of
`l:red-var-l2` for the maximal operator, by the Marcinkiewicz theorem for subadditive operators on
finitely supported sequences (`PrimeCarleson.Proof.Paper.interp_two_s`). Unlike the variational case
there is no restriction `p > r'`: the crude `ℓ^s` bounds of a maximal operator come from Young's
inequality, for every `s ≥ 1`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- **Interpolation of `supOp`**: for `1 < p < ∞` there are `s > 1` (`s = 2` if `p = 2`),
`ϑ ∈ (0, 1]` (`ϑ = 1` iff `p = 2`) and `C ≥ 0` such that every weight `u` whose maximal operator
`f ↦ sup_λ |∑_n f(x-n) u(n) e(λ n)|` is bounded on `ℓ²` with norm `≤ M₀` and on `ℓ^s` with norm
`≤ M₁` (on finitely supported `f`) is bounded on `ℓ^p` with norm `≤ C M₀^ϑ M₁^{1-ϑ}`. -/
theorem supOp_interp {p : ℝ} (hp : 1 < p) :
    ∃ s ϑ C : ℝ, 1 < s ∧ 0 < ϑ ∧ ϑ ≤ 1 ∧ 0 ≤ C ∧
      ∀ (u : ℤ → ℂ) (M₀ M₁ : ℝ), 0 < M₀ → 0 < M₁ →
        (∀ f : ℤ →₀ ℂ, eLpNorm (supOp u (⇑f)) (ENNReal.ofReal 2) Measure.count ≤
          ENNReal.ofReal M₀ * eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count) →
        (∀ f : ℤ →₀ ℂ, eLpNorm (supOp u (⇑f)) (ENNReal.ofReal s) Measure.count ≤
          ENNReal.ofReal M₁ * eLpNorm (⇑f) (ENNReal.ofReal s) Measure.count) →
        ∀ f : ℤ →₀ ℂ, eLpNorm (supOp u (⇑f)) (ENNReal.ofReal p) Measure.count ≤
          ENNReal.ofReal (C * M₀ ^ ϑ * M₁ ^ (1 - ϑ)) *
            eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  have hp0 : 0 < p := by linarith
  by_cases hp2 : p = 2
  · subst hp2
    refine ⟨2, 1, 1, by norm_num, one_pos, le_rfl, zero_le_one,
      fun u M₀ M₁ hM₀ hM₁ h₀ _ f => ?_⟩
    simpa [Real.rpow_one, Real.rpow_zero] using h₀ f
  · obtain ⟨s, hs1, hsp⟩ : ∃ s : ℝ, 1 < s ∧ ((p < 2 ∧ s < p) ∨ (2 < p ∧ p < s)) := by
      rcases lt_or_gt_of_ne hp2 with hlt | hgt
      · exact ⟨(1 + p) / 2, by linarith, Or.inl ⟨hlt, by linarith⟩⟩
      · exact ⟨p + 1, by linarith, Or.inr ⟨hgt, by linarith⟩⟩
    have hs0 : 0 < s := by linarith
    have hs2 : s ≠ 2 := by
      rintro rfl
      rcases hsp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    obtain ⟨θ, hθ0, hθ1, hθ⟩ := exists_interp_theta hp0 hs0 hsp
    obtain ⟨Cint, hCint0, hint⟩ := interp_two_s hs0 hs2 hθ0 hθ1 hθ
    refine ⟨s, θ, Cint, hs1, hθ0, hθ1.le, hCint0, fun u M₀ M₁ hM₀ hM₁ h₀ h₁ f => ?_⟩
    exact hint (fun g => supOp u (⇑g)) M₀ M₁ hM₀ hM₁
      (fun g g' x => supOp_add_left_le u g g' x) h₀ h₁ f

end PrimeCarleson.Proof.Paper
