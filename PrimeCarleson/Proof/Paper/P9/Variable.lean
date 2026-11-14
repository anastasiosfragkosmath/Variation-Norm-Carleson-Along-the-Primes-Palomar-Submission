module

public import PrimeCarleson.Proof.Paper.P9.Sizes
public import PrimeCarleson.Proof.Paper.P9.VarTools

/-!
# `p:variable`, first half: reproducing formula and Cauchy-Schwarz

Source: main paper `p:variable`, L1897–L1913 (the proof of `p:variable`, in the form proved here).

Setting: a chart `[θ, θ + 1]`, the interval `I = [a, b]`, cutoff data `D : CutoffData θ a b c`
(`χ_I`, `φ_I`), a finite index type `Ξ`, coefficients `g : Ξ → ℤ → ℂ`, a finite index set
`T ⊂ ℝ`, multipliers `m t : ℝ → ℂ` (`t ∈ T`) and densities `H ξ` (the Fourier transforms of
`f_ξ`, `ĥ_ξ` supported in `I`): see `VarAdmissible`. Then `K_t * f_ξ = KSeq θ m H t ξ`
(`= invFZ θ (m_t H_ξ)`, `(K_t * f)^ = m_t f̂`) and
`a_t(x) = ∑_ξ g_ξ(x) (K_t * f_ξ)(x) = aSum θ g m H t x`.

* `variation_le_tsum`: by the reproducing formula `(χ_I φ_I) * h = h` applied to
  `h = K_t * f_ξ` and Minkowski's integral inequality for `V^r` (the countable triangle
  inequality, counting measure on `ℤ`),
  `V^r(a_·(x)) ≤ ∑_y |χ_I(y) φ_I(y)| V^r(∑_ξ g_ξ(x) (K_t * f_ξ)(x - y) : t ∈ T)`;
* `variation_sq_le`: Cauchy-Schwarz in `y` and `φ_I ≥ 0`-free homogeneity,
  `V^r(a_·(x))² ≤ ‖χ_I‖² ∑_y V^r(∑_ξ φ_I(y) g_ξ(x) (K_t * f_ξ)(x - y) : t ∈ T)²`;
* `tsum_variation_sq_le`: summation in `x` and the change of variables `x ↦ x + y`:
  `∑_x V^r(a(x))² ≤ ‖χ_I‖² ∑_x ℐ(x)²`, `ℐ(x)² = ∑_y V^r(∑_ξ φ_I(y) g_ξ(x + y) (K_t*f_ξ)(x))²`
  (the printed `≲ |I| ∑_x ℐ(x)²`, with the exact constant `‖χ_I‖²_{ℓ²}`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

variable {θ a b c : ℝ} {Ξ : Type*} [Fintype Ξ]

/-- The data of `p:variable`: a finite family of multipliers `m_t`, `t ∈ T`, measurable and
bounded on `I = [a, b]`, and densities `H_ξ` (`f̂_ξ`) square integrable on the chart and
supported in `I`. -/
structure VarAdmissible (θ a b : ℝ) (T : Set ℝ) (m : ℝ → ℝ → ℂ) (H : Ξ → ℝ → ℂ) : Prop where
  /-- `m_t` is measurable. -/
  meas : ∀ t ∈ T, Measurable (m t)
  /-- `m_t` is bounded on `I`. -/
  bdd : ∀ t ∈ T, ∃ M : ℝ, ∀ β ∈ Set.Icc a b, ‖m t β‖ ≤ M
  /-- `f̂_ξ ∈ L²`. -/
  l2 : ∀ ξ, ChartL2 θ (H ξ)
  /-- `f̂_ξ` is supported in `I`. -/
  supp : ∀ ξ β, β ∉ Set.Icc a b → H ξ β = 0

/-- `(K_t * f_ξ)(z)`: the multiplier operator of `m_t` applied to the sequence with Fourier density
`H_ξ`, `∫ m_t(β) H_ξ(β) e(zβ) dβ` (so `(K_t * f_ξ)^ = m_t f̂_ξ`). -/
def KSeq (θ : ℝ) (m : ℝ → ℝ → ℂ) (H : Ξ → ℝ → ℂ) (t : ℝ) (ξ : Ξ) (z : ℤ) : ℂ :=
  invFZ θ (fun β => m t β * H ξ β) z

/-- `a_t(x) = ∑_ξ g_ξ(x) (K_t * f_ξ)(x)` (L1894-L1896). -/
def aSum (θ : ℝ) (g : Ξ → ℤ → ℂ) (m : ℝ → ℝ → ℂ) (H : Ξ → ℝ → ℂ) (t : ℝ) (x : ℤ) : ℂ :=
  ∑ ξ, g ξ x * KSeq θ m H t ξ x

section Admissible

variable {T : Set ℝ} {m : ℝ → ℝ → ℂ} {H : Ξ → ℝ → ℂ}

omit [Fintype Ξ] in
theorem VarAdmissible.supp_mul (h : VarAdmissible θ a b T m H) (t : ℝ) (ξ : Ξ) {β : ℝ}
    (hβ : β ∉ Set.Icc a b) : m t β * H ξ β = 0 := by
  rw [h.supp ξ β hβ, mul_zero]

omit [Fintype Ξ] in
/-- The density of `K_t * f_ξ` is square integrable. -/
theorem VarAdmissible.chartL2_mul (h : VarAdmissible θ a b T m H) {t : ℝ} (ht : t ∈ T) (ξ : Ξ) :
    ChartL2 θ (fun β => m t β * H ξ β) := by
  obtain ⟨M, hM⟩ := h.bdd t ht
  refine (h.l2 ξ).mul_of_le (M := M) (h.meas t ht).aestronglyMeasurable fun β => ?_
  by_cases hβ : β ∈ Set.Icc a b
  · rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hM β hβ) (norm_nonneg _)
  · rw [h.supp_mul t ξ hβ]; simp [h.supp ξ β hβ]

end Admissible

section FirstHalf

variable {T : Set ℝ} {m : ℝ → ℝ → ℂ} {H : Ξ → ℝ → ℂ} (D : CutoffData θ a b c) (g : Ξ → ℤ → ℂ)

/-- The family `y ↦ ∑_ξ g_ξ(x) (K_t * f_ξ)(x - y)` is bounded. -/
theorem alpha_bound (_hadm : VarAdmissible θ a b T m H) (x : ℤ) :
    ∀ t ∈ T, ∃ C : ℝ, ∀ y : ℤ, ‖∑ ξ, g ξ x * KSeq θ m H t ξ (x - y)‖ ≤ C := by
  intro t _
  refine ⟨∑ ξ, ‖g ξ x‖ * ∫ β in θ..θ + 1, ‖m t β * H ξ β‖, fun y => ?_⟩
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ξ _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_invFZ_le _) (norm_nonneg _)

/-- `y ↦ (∑_ξ g_ξ(x) (K_t * f_ξ)(x - y)) χ_I(y) φ_I(y)` is absolutely summable. -/
theorem summable_alpha_mul (hadm : VarAdmissible θ a b T m H) (x : ℤ) {t : ℝ} (ht : t ∈ T) :
    Summable fun y : ℤ => ‖(∑ ξ, g ξ x * KSeq θ m H t ξ (x - y)) * (D.χ y * D.φ y)‖ := by
  obtain ⟨C, hC⟩ := alpha_bound g hadm x t ht
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun y => ?_)
    (D.summable_norm_chiPhi.mul_left C)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC y) (norm_nonneg _)

omit [Fintype Ξ] in
/-- The reproducing formula for `h = K_t * f_ξ`:
`∑_y χ_I(y) φ_I(y) (K_t * f_ξ)(x - y) = (K_t * f_ξ)(x)`. -/
theorem reproducing_kseq (hadm : VarAdmissible θ a b T m H) {t : ℝ} (ht : t ∈ T) (ξ : Ξ)
    (x : ℤ) : ∑' y : ℤ, (D.χ y * D.φ y) * KSeq θ m H t ξ (x - y) = KSeq θ m H t ξ x :=
  D.reproducing_formula (hadm.chartL2_mul ht ξ) (fun _ hβ => hadm.supp_mul t ξ hβ) x

/-- `a_t(x) = ∑_y (∑_ξ g_ξ(x) (K_t * f_ξ)(x - y)) χ_I(y) φ_I(y)`: the reproducing formula applied
to each `K_t * f_ξ` and summed over `ξ`. -/
theorem aSum_eq_tsum (hadm : VarAdmissible θ a b T m H) (x : ℤ) {t : ℝ} (ht : t ∈ T) :
    aSum θ g m H t x =
      ∑' y : ℤ, (∑ ξ, g ξ x * KSeq θ m H t ξ (x - y)) * (D.χ y * D.φ y) := by
  have hξ : ∀ ξ : Ξ, Summable fun y : ℤ => (D.χ y * D.φ y) * KSeq θ m H t ξ (x - y) := by
    intro ξ
    refine Summable.of_norm_bounded
      (D.summable_norm_chiPhi.mul_right (∫ β in θ..θ + 1, ‖m t β * H ξ β‖)) fun y => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_invFZ_le _) (norm_nonneg _)
  have h1 : aSum θ g m H t x =
      ∑ ξ, ∑' y : ℤ, g ξ x * ((D.χ y * D.φ y) * KSeq θ m H t ξ (x - y)) := by
    unfold aSum
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [tsum_mul_left, reproducing_kseq D hadm ht ξ x]
  rw [h1, ← Summable.tsum_finsetSum fun ξ _ => (hξ ξ).mul_left _]
  refine tsum_congr fun y => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun ξ _ => by ring

/-- **Reproducing formula and Minkowski** (Source: main paper `p:variable`, L1898–L1902, first
two sentences of the proof): for `1 ≤ r`,
`V^r(a_·(x)) ≤ ∑_y |χ_I(y) φ_I(y)| V^r(∑_ξ g_ξ(x) (K_t * f_ξ)(x - y) : t ∈ T)`. -/
theorem variation_le_tsum (hadm : VarAdmissible θ a b T m H) {r : ℝ} (hr : 1 ≤ r) (x : ℤ) :
    rVariationOn r T (fun t => aSum θ g m H t x) ≤
      ∑' y : ℤ, ‖D.χ y * D.φ y‖ₑ *
        rVariationOn r T (fun t => ∑ ξ, g ξ x * KSeq θ m H t ξ (x - y)) := by
  have hid : ∀ t ∈ T, aSum θ g m H t x =
      ∫ y : ℤ, (∑ ξ, g ξ x * KSeq θ m H t ξ (x - y)) * (D.χ y * D.φ y)
        ∂(Measure.count : Measure ℤ) := by
    intro t ht
    have hint : Integrable (fun y : ℤ => (∑ ξ, g ξ x * KSeq θ m H t ξ (x - y)) *
        (D.χ y * D.φ y)) Measure.count :=
      integrable_count_iff.2 (summable_alpha_mul D g hadm x ht)
    rw [integral_countable hint, aSum_eq_tsum D g hadm x ht]
    simp only [Measure.real, Measure.count_singleton, ENNReal.toReal_one, one_smul]
  have hcongr : rVariationOn r T (fun t => aSum θ g m H t x) =
      rVariationOn r T (fun t => ∫ y : ℤ,
        (∑ ξ, g ξ x * KSeq θ m H t ξ (x - y)) * (D.χ y * D.φ y)
          ∂(Measure.count : Measure ℤ)) :=
    rVariationOn_congr hid
  rw [hcongr]
  refine (rVariationOn_integral_le_of_bounded hr
    (fun t y => ∑ ξ, g ξ x * KSeq θ m H t ξ (x - y)) (fun y => D.χ y * D.φ y) ?_
    (alpha_bound g hadm x) ?_).trans ?_
  · intro t _
    exact measurable_from_top.aestronglyMeasurable
  · exact integrable_count_iff.2 D.summable_norm_chiPhi
  · rw [lintegral_count]
    exact le_of_eq (tsum_congr fun y => mul_comm _ _)

/-- **Cauchy-Schwarz in `y`** (Source: main paper `p:variable`, L1902–L1906): for
`1 ≤ r`,
`V^r(a_·(x))² ≤ ‖χ_I‖²_{ℓ²} ∑_y V^r(∑_ξ φ_I(y) g_ξ(x) (K_t * f_ξ)(x - y) : t ∈ T)²`. -/
theorem variation_sq_le (hadm : VarAdmissible θ a b T m H) {r : ℝ} (hr : 1 ≤ r) (x : ℤ) :
    rVariationOn r T (fun t => aSum θ g m H t x) ^ 2 ≤
      (∑' y : ℤ, ‖D.χ y‖ₑ ^ 2) *
        ∑' y : ℤ, rVariationOn r T
          (fun t => ∑ ξ, (D.φ y * g ξ x) * KSeq θ m H t ξ (x - y)) ^ 2 := by
  have h1 := variation_le_tsum D g hadm hr x
  have hW : ∀ y : ℤ, ‖D.χ y * D.φ y‖ₑ *
      rVariationOn r T (fun t => ∑ ξ, g ξ x * KSeq θ m H t ξ (x - y)) =
      ‖D.χ y‖ₑ * rVariationOn r T
        (fun t => ∑ ξ, (D.φ y * g ξ x) * KSeq θ m H t ξ (x - y)) := by
    intro y
    have : (fun t => ∑ ξ, (D.φ y * g ξ x) * KSeq θ m H t ξ (x - y)) =
        D.φ y • (fun t => ∑ ξ, g ξ x * KSeq θ m H t ξ (x - y)) := by
      funext t
      simp [Finset.mul_sum, mul_assoc]
    rw [this, rVariationOn_const_smul (by linarith), enorm_mul]
    ring
  simp_rw [hW] at h1
  calc rVariationOn r T (fun t => aSum θ g m H t x) ^ 2
      ≤ (∑' y : ℤ, ‖D.χ y‖ₑ * rVariationOn r T
          (fun t => ∑ ξ, (D.φ y * g ξ x) * KSeq θ m H t ξ (x - y))) ^ 2 := by gcongr
    _ ≤ ((∑' y : ℤ, ‖D.χ y‖ₑ ^ 2) ^ (1 / 2 : ℝ) * (∑' y : ℤ, rVariationOn r T
          (fun t => ∑ ξ, (D.φ y * g ξ x) * KSeq θ m H t ξ (x - y)) ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
        exact tsum_mul_le_sqrt_mul_sqrt _ _
    _ = _ := by rw [mul_pow, enorm_rpow_half_sq, enorm_rpow_half_sq]

/-- **Summation in `x` and the change of variables `x ↦ x + y`**
(Source: main paper `p:variable`, L1907–L1913): for `1 ≤ r`,
`∑_x V^r(a(x))² ≤ ‖χ_I‖² ∑_x ∑_y V^r(∑_ξ φ_I(y) g_ξ(x + y) (K_t * f_ξ)(x) : t ∈ T)²`. -/
theorem tsum_variation_sq_le (hadm : VarAdmissible θ a b T m H) {r : ℝ} (hr : 1 ≤ r) :
    ∑' x : ℤ, rVariationOn r T (fun t => aSum θ g m H t x) ^ 2 ≤
      (∑' y : ℤ, ‖D.χ y‖ₑ ^ 2) *
        ∑' x : ℤ, ∑' y : ℤ, rVariationOn r T
          (fun t => ∑ ξ, (D.φ y * g ξ (x + y)) * KSeq θ m H t ξ x) ^ 2 := by
  have h1 : ∑' x : ℤ, rVariationOn r T (fun t => aSum θ g m H t x) ^ 2 ≤
      ∑' x : ℤ, (∑' y : ℤ, ‖D.χ y‖ₑ ^ 2) * ∑' y : ℤ, rVariationOn r T
          (fun t => ∑ ξ, (D.φ y * g ξ x) * KSeq θ m H t ξ (x - y)) ^ 2 :=
    ENNReal.tsum_le_tsum fun x => variation_sq_le D g hadm hr x
  rw [ENNReal.tsum_mul_left] at h1
  refine h1.trans (mul_le_mul_right (le_of_eq ?_) _)
  set F : ℤ → ℤ → ℝ≥0∞ := fun x y => rVariationOn r T
    (fun t => ∑ ξ, (D.φ y * g ξ x) * KSeq θ m H t ξ (x - y)) ^ 2 with hF
  set G : ℤ → ℤ → ℝ≥0∞ := fun x y => rVariationOn r T
    (fun t => ∑ ξ, (D.φ y * g ξ (x + y)) * KSeq θ m H t ξ x) ^ 2 with hG
  have key : ∀ y : ℤ, ∑' x : ℤ, F x y = ∑' x' : ℤ, G x' y := by
    intro y
    rw [← (Equiv.addRight y).tsum_eq (fun x => F x y)]
    refine tsum_congr fun x' => ?_
    simp only [hF, hG, Equiv.coe_addRight, add_sub_cancel_right]
  calc ∑' x : ℤ, ∑' y : ℤ, F x y = ∑' y : ℤ, ∑' x : ℤ, F x y := ENNReal.tsum_comm
    _ = ∑' y : ℤ, ∑' x' : ℤ, G x' y := tsum_congr key
    _ = ∑' x' : ℤ, ∑' y : ℤ, G x' y := ENNReal.tsum_comm

end FirstHalf

end PrimeCarleson.Proof.Paper
