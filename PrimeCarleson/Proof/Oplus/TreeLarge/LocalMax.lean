module

public import PrimeCarleson.Proof.Oplus.TreeLarge.Fourier
public import PrimeCarleson.Proof.Oplus.TreeLarge.Maximal
public import PrimeCarleson.Proof.Oplus.TreeLarge.Variation
public import PrimeCarleson.Proof.Common.VariationIntegral

/-!
# Local constancy: variation at scales `≥ |J|` is dominated by a maximal function ([O+] L2350-L2370)

Source: [O+] `treeestimatelargeintervals`, L2350–L2370: for `log₂|J| ≤ k₁ < k₂` the difference
`ψ_{k₁} * g - ψ_{k₂} * g` is reproduced by `ψ_{C + log₂|J|}` (`schwartzAvg_reproduce`, with
`C = -1`, scale `ℓ₀ - 1` for `|J| = 2^{ℓ₀}`), so by Minkowski's integral inequality for the
`r`-variation (`rVariationOn_integral_sub_le`)
and the domination of the Schwartz kernel by the maximal function
(`lintegral_schwartzScale_le_maximalHLR`), for all `x, x'` with `|x - x'| ≤ |J|`

`V^r_{ℓ ≥ ℓ₀}(ψ_ℓ * g (x)) ≤ κ M[V^r_{ℓ ∈ ℤ}(ψ_ℓ * g)](x')`.

The source writes the supremum over `x ∈ J` on the right (a misplaced quantifier); the
form proved here is the one the integration over `J` uses (the right side does not depend on `x`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal SchwartzMap FourierTransform

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

/-- A function in the class `FNice` is bounded (by `‖𝓕 h‖_{L¹}`, Fourier inversion). -/
theorem FNice.exists_bound {h : ℝ → ℂ} (a : FNice h) : ∃ C : ℝ, ∀ x, ‖h x‖ ≤ C := by
  refine ⟨∫ ξ, ‖𝓕 h ξ‖, fun x => ?_⟩
  have := a.continuous.fourierInv_fourier_eq a.integrable a.integrable_fourier
  rw [← congrFun this x, fourierInv_eq_integral_e]
  calc ‖∫ ξ, e (ξ * x) * 𝓕 h ξ‖ ≤ ∫ ξ, ‖e (ξ * x) * 𝓕 h ξ‖ := norm_integral_le_integral_norm _
    _ = ∫ ξ, ‖𝓕 h ξ‖ := by simp [norm_e]

/-- **`treeestimatelargeintervals`** ([O+] L2350-L2370). For the Schwartz
cutoff `ψ` with `ψ̂ = 1` on `|ξ| ≤ (C₁ + C₃)/4` and `ψ̂ = 0` on `|ξ| ≥ C₁/2`
and `r ≥ 1` there is `κ ≥ 0` (depending on `ψ` only) such that for every `FNice` function `g`, all
`ℓ₀ ∈ ℤ` and `x, x'` with
`|x - x'| ≤ 2^{ℓ₀}`,
`V^r_{ℓ ≥ ℓ₀}(ψ_ℓ * g(x)) ≤ κ · M[V^r_{ℓ ∈ ℤ}(ψ_ℓ * g)](x')`. -/
theorem rVariationOn_schwartzAvg_le_maximalHLR {C₁ C₃ : ℝ} (hC₃ : 0 ≤ C₃) {ψ : 𝓢(ℝ, ℂ)}
    (hψ : IsPsiCutoff (C₁ / 4) (C₃ / 4) ψ) {r : ℝ} (hr : 1 ≤ r) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ {g : ℝ → ℂ}, FNice g → ∀ (ℓ₀ : ℤ) (x x' : ℝ), |x - x'| ≤ (2 : ℝ) ^ ℓ₀ →
      rVariationOn r ((↑) '' {ℓ : ℤ | ℓ₀ ≤ ℓ} : Set ℝ) (fun t => schwartzAvg ψ ⌊t⌋ g x) ≤
        ENNReal.ofReal κ * maximalHLR (fun y => rVariationOn r (Set.range ((↑) : ℤ → ℝ))
          (fun t => schwartzAvg ψ ⌊t⌋ g y)) x' := by
  obtain ⟨κ, hκ0, hκ⟩ := lintegral_schwartzScale_le_maximalHLR ψ
  refine ⟨κ, hκ0, fun {g} hg ℓ₀ x x' hxx => ?_⟩
  set c : ℤ := ℓ₀ - 1 with hc
  set A : ℤ → ℝ → ℂ := fun k y => schwartzAvg ψ k g y with hA
  have hAn : ∀ k, FNice (A k) := fun k => (fnice_schwartzAvg ψ k hg).1
  have hAb : ∀ k, ∃ C : ℝ, ∀ y, ‖A k y‖ ≤ C := fun k => (hAn k).exists_bound
  set S : Set ℝ := (↑) '' {ℓ : ℤ | ℓ₀ ≤ ℓ} with hS
  have hψc : Integrable (schwartzScale ψ c) := integrable_schwartzScale ψ c
  have hψcx : Integrable (fun y => schwartzScale ψ c (x - y)) := hψc.comp_sub_left x
  have hb_int : ∀ k, Integrable (fun y => A k y * schwartzScale ψ c (x - y)) := by
    intro k
    obtain ⟨C, hC⟩ := hAb k
    exact hψcx.bdd_mul (hAn k).continuous.aestronglyMeasurable (Eventually.of_forall hC)
  have step1 : rVariationOn r S (fun t => A ⌊t⌋ x) =
      rVariationOn r S (fun t => ∫ y, A ⌊t⌋ y * schwartzScale ψ c (x - y)) := by
    refine rVariationOn_congr_sub ?_
    rintro s ⟨k₁, hk₁, rfl⟩ t ⟨k₂, hk₂, rfl⟩ hst
    have hk : k₁ ≤ k₂ := by exact_mod_cast hst
    have hk₁' : ℓ₀ ≤ k₁ := hk₁
    simp only [Int.floor_intCast]
    have hrep := congrFun (schwartzAvg_reproduce hC₃ hψ hg (c := c) (k₁ := k₁) (k₂ := k₂)
      (by omega) hk) x
    have e : (∫ y, A k₁ y * schwartzScale ψ c (x - y)) - ∫ y, A k₂ y * schwartzScale ψ c (x - y) =
        schwartzAvg ψ c (fun x => schwartzAvg ψ k₁ g x - schwartzAvg ψ k₂ g x) x := by
      rw [← integral_sub (hb_int k₁) (hb_int k₂)]
      change _ = ∫ y, schwartzScale ψ c (x - y) *
        (schwartzAvg ψ k₁ g y - schwartzAvg ψ k₂ g y)
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [hA]
      ring
    rw [e, ← hrep]
  have hWm : Measurable (fun y => rVariationOn r (Set.range ((↑) : ℤ → ℝ))
      (fun t => schwartzAvg ψ ⌊t⌋ g y)) :=
    measurable_rVariationOn_family r (b := fun k y => schwartzAvg ψ k g y)
      (fun k => (hAn k).continuous.measurable)
  have hmink := rVariationOn_integral_sub_le hr (S := S) (fun t y => A ⌊t⌋ y)
    (schwartzScale ψ c) x
    (fun t _ => (hAn _).continuous.aestronglyMeasurable) (fun t _ => hAb _) hψc
  have hmono : ∀ y, rVariationOn r S (fun t => A ⌊t⌋ y) ≤
      rVariationOn r (Set.range ((↑) : ℤ → ℝ)) (fun t => schwartzAvg ψ ⌊t⌋ g y) := by
    intro y
    refine rVariationOn_mono_set ?_ _
    rintro _ ⟨k, -, rfl⟩
    exact ⟨k, rfl⟩
  have hxx' : |x - x'| ≤ 2 * (2 : ℝ) ^ c := by
    have : (2 : ℝ) * (2 : ℝ) ^ c = (2 : ℝ) ^ ℓ₀ := by
      rw [← zpow_one_add₀ (by norm_num : (2 : ℝ) ≠ 0), hc]
      congr 1; ring
    rw [this]; exact hxx
  calc rVariationOn r S (fun t => A ⌊t⌋ x)
      = rVariationOn r S (fun t => ∫ y, A ⌊t⌋ y * schwartzScale ψ c (x - y)) := step1
    _ ≤ ∫⁻ y, rVariationOn r S (fun t => A ⌊t⌋ y) * ‖schwartzScale ψ c (x - y)‖ₑ := hmink
    _ ≤ ∫⁻ y, ‖schwartzScale ψ c (x - y)‖ₑ * rVariationOn r (Set.range ((↑) : ℤ → ℝ))
          (fun t => schwartzAvg ψ ⌊t⌋ g y) := by
        refine lintegral_mono fun y => ?_
        rw [mul_comm]
        exact mul_le_mul_right (hmono y) _
    _ ≤ _ := hκ c hWm x x' hxx'

end PrimeCarleson.Proof.Oplus
