module

public import PrimeCarleson.Proof.Paper.P9.Representation
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Norm replacement: `(∑_{a/q} ‖f_{a/q}‖²)^{1/2} ≲ ‖f‖`

Source: main paper `p:global-shell-var`, L1998–L2001: the pieces `f_{a/q}` (densities
`ϑ(β) f̂(β + a/q)`, supported in `a/q + 3J`) are orthogonal because the sets `a/q + 3J` are pairwise
disjoint mod `1` (`Γ_Q` is `Q^{-2}`-separated and `|3J| < Q^{-2}`).

`sum_integral_theta_le`: for `3ℓ`-separated frequencies `γ_ξ`,
`∑_ξ ∫_θ^{θ+1} ϑ(β)² |f̂(β + γ_ξ)|² dβ ≤ ∑_k |f(k)|²` (`= ∫_0^1 |f̂|²`), proved with the
`1`-periodic cutoff `Θ(β) = ϑ(θ + {β - θ})`, for which `∑_ξ Θ(g - γ_ξ)² ≤ 1` pointwise.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

/-- The `1`-periodic cutoff `Θ(β) = ϑ(θ + {β - θ})` (the periodization of `ϑ` from the chart). -/
def perTheta (θ : ℝ) (ϑ : ℝ → ℝ) (β : ℝ) : ℝ := ϑ (θ + Int.fract (β - θ))

theorem perTheta_periodic (θ : ℝ) (ϑ : ℝ → ℝ) : Function.Periodic (perTheta θ ϑ) 1 := by
  intro β
  unfold perTheta
  rw [show β + 1 - θ = (β - θ) + 1 by ring, Int.fract_add_one]

theorem perTheta_eq_sub_floor (θ : ℝ) (ϑ : ℝ → ℝ) (β : ℝ) :
    perTheta θ ϑ β = ϑ (β - ⌊β - θ⌋) := by
  unfold perTheta
  rw [Int.fract]
  congr 1
  ring

theorem perTheta_eq (θ : ℝ) (ϑ : ℝ → ℝ) {β : ℝ} (h1 : θ ≤ β) (h2 : β < θ + 1) :
    perTheta θ ϑ β = ϑ β := by
  unfold perTheta
  rw [Int.fract_eq_self.2 ⟨by linarith, by linarith⟩]
  congr 1
  ring

theorem measurable_perTheta {θ : ℝ} {ϑ : ℝ → ℝ} (hc : Continuous ϑ) :
    Measurable (perTheta θ ϑ) :=
  hc.measurable.comp (measurable_const.add (measurable_fract.comp (measurable_id.sub_const θ)))

variable {Ξ : Type*} [Fintype Ξ]

/-- **Orthogonality of the pieces** (Source: main paper `p:global-shell-var`, L1998–L2001):
for `3ℓ`-separated frequencies `γ_ξ` (distinct mod `1`),
`∑_ξ ∫_θ^{θ+1} ϑ(β)² |f̂(β + γ_ξ)|² dβ ≤ ∑_k |f(k)|²`. -/
theorem sum_integral_theta_le (γ : Ξ → ℝ) {θ u ℓ : ℝ} (ϑ : ℝ → ℝ) (hc : Continuous ϑ)
    (hθ1 : θ < u - ℓ) (hθ2 : u + 2 * ℓ < θ + 1) (hℓ : 0 < ℓ)
    (h01 : ∀ x, 0 ≤ ϑ x ∧ ϑ x ≤ 1) (hsupp : ∀ x, x ∉ Set.Icc (u - ℓ) (u + 2 * ℓ) → ϑ x = 0)
    (hsep : ∀ ξ ξ' : Ξ, ξ ≠ ξ' → ∀ v : ℤ, 3 * ℓ < |γ ξ - γ ξ' - v|) (f : ℤ →₀ ℂ) :
    ∑ ξ, ∫ β in θ..θ + 1, ϑ β ^ 2 * ‖fourierZ f (β + γ ξ)‖ ^ 2 ≤ ∑ k ∈ f.support, ‖f k‖ ^ 2 := by
  classical
  set Θ := perTheta θ ϑ with hΘ
  have hΘ01 : ∀ β, 0 ≤ Θ β ∧ Θ β ≤ 1 := fun β => h01 _
  have hΘper : Function.Periodic Θ 1 := perTheta_periodic θ ϑ
  have hΘm : Measurable Θ := measurable_perTheta hc
  have hf2 : Continuous fun g => ‖fourierZ f g‖ ^ 2 := (continuous_fourierZ f).norm.pow 2
  have hfper : ∀ g, ‖fourierZ f (g + 1)‖ ^ 2 = ‖fourierZ f g‖ ^ 2 := fun g => by
    rw [fourierZ_periodic f g]
  -- boundedness of `‖f̂‖²`
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hf2.continuousOn
  have hMper : ∀ g, ‖fourierZ f g‖ ^ 2 ≤ M := by
    intro g
    have h := hM (Int.fract g) ⟨Int.fract_nonneg g, (Int.fract_lt_one g).le⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at h
    have h2 : fourierZ f (Int.fract g) = fourierZ f g := by
      have := (fourierZ_periodic f).sub_int_mul_eq (x := g) ⌊g⌋
      rw [Int.fract, ← this, mul_one]
    rwa [h2] at h
  have hint : ∀ (F : ℝ → ℝ), Measurable F → (∀ g, 0 ≤ F g ∧ F g ≤ M) →
      IntervalIntegrable F volume 0 1 := by
    intro F hF hb
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 ?_
    exact (integrableOn_const (C := M) (by simp)).mono' hF.aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hb g).1]; exact (hb g).2)
  -- the pointwise bound `∑_ξ Θ(g - γ_ξ)² ≤ 1`
  have hpt : ∀ g : ℝ, ∑ ξ, Θ (g - γ ξ) ^ 2 ≤ 1 := by
    intro g
    by_cases h : ∃ ξ₀, Θ (g - γ ξ₀) ≠ 0
    · obtain ⟨ξ₀, h0⟩ := h
      rw [Finset.sum_eq_single ξ₀]
      · have := hΘ01 (g - γ ξ₀)
        nlinarith
      · intro ξ _ hne
        by_contra hne2
        have h1 : Θ (g - γ ξ) ≠ 0 := fun h => hne2 (by rw [h]; ring)
        have key : ∀ ξ', Θ (g - γ ξ') ≠ 0 →
            ∃ k : ℤ, g - γ ξ' - k ∈ Set.Icc (u - ℓ) (u + 2 * ℓ) := by
          intro ξ' hξ'
          rw [hΘ, perTheta_eq_sub_floor] at hξ'
          refine ⟨⌊g - γ ξ' - θ⌋, ?_⟩
          by_contra hn
          exact hξ' (hsupp _ hn)
        obtain ⟨k, hk⟩ := key ξ h1
        obtain ⟨k₀, hk₀⟩ := key ξ₀ h0
        have := hsep ξ ξ₀ hne (k₀ - k)
        have hlt : |γ ξ - γ ξ₀ - ((k₀ - k : ℤ) : ℝ)| ≤ 3 * ℓ := by
          rw [abs_le]
          push_cast
          constructor <;> linarith [hk.1, hk.2, hk₀.1, hk₀.2]
        linarith
      · intro h; exact absurd (Finset.mem_univ ξ₀) h
    · push Not at h
      simp [h]
  -- step A, B, C: each integral is `∫_0^1 Θ(g - γ_ξ)² ‖f̂(g)‖² dg`
  have hA : ∀ ξ : Ξ, ∫ β in θ..θ + 1, ϑ β ^ 2 * ‖fourierZ f (β + γ ξ)‖ ^ 2 =
      ∫ g in (0 : ℝ)..1, Θ (g - γ ξ) ^ 2 * ‖fourierZ f g‖ ^ 2 := by
    intro ξ
    have e1 : ∫ β in θ..θ + 1, ϑ β ^ 2 * ‖fourierZ f (β + γ ξ)‖ ^ 2 =
        ∫ β in θ..θ + 1, Θ β ^ 2 * ‖fourierZ f (β + γ ξ)‖ ^ 2 := by
      refine intervalIntegral.integral_congr fun β hβ => ?_
      rw [Set.uIcc_of_le (by linarith)] at hβ
      congr 1
      by_cases hlt : β < θ + 1
      · rw [hΘ, perTheta_eq θ ϑ hβ.1 hlt]
      · have hβe : β = θ + 1 := le_antisymm hβ.2 (not_lt.1 hlt)
        have hz : ϑ β = 0 := hsupp β (fun hh => by linarith [hh.2])
        have hz2 : Θ β = 0 := by
          rw [hβe, hΘ]
          unfold perTheta
          rw [show θ + 1 - θ = 1 by ring, Int.fract_one, add_zero]
          exact hsupp θ (fun hh => by linarith [hh.1])
        rw [hz, hz2]
    have hper : Function.Periodic (fun β => Θ β ^ 2 * ‖fourierZ f (β + γ ξ)‖ ^ 2) 1 := by
      intro β
      simp only
      rw [hΘper β, show β + 1 + γ ξ = (β + γ ξ) + 1 by ring, hfper (β + γ ξ)]
    rw [e1, hper.intervalIntegral_add_eq θ 0, zero_add]
    have := intervalIntegral.integral_comp_add_right
      (fun g => Θ (g - γ ξ) ^ 2 * ‖fourierZ f g‖ ^ 2) (γ ξ) (a := 0) (b := 1)
    simp only [add_sub_cancel_right] at this
    rw [this]
    have hper2 : Function.Periodic (fun g => Θ (g - γ ξ) ^ 2 * ‖fourierZ f g‖ ^ 2) 1 := by
      intro g
      simp only
      rw [show g + 1 - γ ξ = (g - γ ξ) + 1 by ring, hΘper (g - γ ξ), hfper g]
    have := hper2.intervalIntegral_add_eq (0 + γ ξ) 0
    rw [show (1 : ℝ) + γ ξ = 0 + γ ξ + 1 by ring, this, zero_add]
  simp_rw [hA]
  have hmeas : ∀ ξ : Ξ, Measurable fun g => Θ (g - γ ξ) ^ 2 * ‖fourierZ f g‖ ^ 2 := fun ξ =>
    ((hΘm.comp (measurable_id.sub_const _)).pow_const 2).mul hf2.measurable
  have hbd : ∀ ξ : Ξ, ∀ g, 0 ≤ Θ (g - γ ξ) ^ 2 * ‖fourierZ f g‖ ^ 2 ∧
      Θ (g - γ ξ) ^ 2 * ‖fourierZ f g‖ ^ 2 ≤ M := by
    intro ξ g
    refine ⟨by positivity, ?_⟩
    have h1 : Θ (g - γ ξ) ^ 2 ≤ 1 := by
      have := hΘ01 (g - γ ξ); nlinarith
    calc Θ (g - γ ξ) ^ 2 * ‖fourierZ f g‖ ^ 2 ≤ 1 * ‖fourierZ f g‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ M := by rw [one_mul]; exact hMper g
  rw [← intervalIntegral.integral_finsetSum (fun ξ _ => hint _ (hmeas ξ) (hbd ξ)),
    sum_norm_sq_eq_integral f]
  have hsumint : IntervalIntegrable
      (fun g => ∑ ξ, Θ (g - γ ξ) ^ 2 * ‖fourierZ f g‖ ^ 2) volume 0 1 := by
    have := IntervalIntegrable.sum Finset.univ
      (fun ξ _ => hint _ (hmeas ξ) (hbd ξ) : ∀ ξ ∈ (Finset.univ : Finset Ξ),
        IntervalIntegrable (fun g => Θ (g - γ ξ) ^ 2 * ‖fourierZ f g‖ ^ 2) volume 0 1)
    convert this using 1
    ext g
    simp [Finset.sum_apply]
  refine intervalIntegral.integral_mono_on zero_le_one hsumint
    (hf2.intervalIntegrable _ _) fun g _ => ?_
  rw [← Finset.sum_mul]
  exact mul_le_of_le_one_left (by positivity) (hpt g)

end PrimeCarleson.Proof.Paper
