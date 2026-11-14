module

public import PrimeCarleson.Proof.Paper.P9.VariableEntropy

/-!
# `p:variable`: variation bound, base point, selector

Source: main paper `p:variable`, L1881–L1930 (statement L1881–L1896, proof L1897–L1930, with the
summed form L1925–L1929), in the form proved here, with the base point and the selector.

Notation: `‖χ_I‖ = chiNorm` (`ℓ²(ℤ)` norm of `χ_I`), `E = entropyConst r s`,
`γ = entropyGamma r s` (`P8/EntropyLemma.lean`), `F = famNorm θ H = (∑_ξ ‖f_ξ‖²_{ℓ²})^{1/2}`; the
`ℓ²` norm of a density sequence is `‖invFZ θ H‖_{ℓ²} = ‖H‖_{L²}` (Parseval).

* `variable_variation_le` (**Theorem B(a)**; `p:variable`):
  `‖V^r(a_t : t ∈ T)‖_{ℓ²_x} ≤ ‖χ_I‖ E C A₁^{1-γ} B₁^γ F`, for `2 < s < r`, under (A), (B) and
  the variational hypothesis `(V_s)`: `‖V^s(K_t * f : t ∈ T)‖_{ℓ²} ≤ C ‖f‖_{ℓ²}` for every `f` with
  `f̂` supported in `I`;
* `variable_base_point` (**Theorem B(b)**, the base point):
  `‖a_{t₀}‖_{ℓ²} ≤ ‖χ_I‖ A₁ M₀ F` with `M₀ ≥ sup_I |m_{t₀}|` (uses only (A));
* `variable_selector` (**Theorem B(c)**, the selector): for every finite `X ⊂ ℤ` and
  `ω : X → T`, `(∑_{x ∈ X} |a_{ω(x)}(x)|²)^{1/2} ≤ ‖a_{t₀}‖_{ℓ²} + ‖V^r(a_t : t)‖_{ℓ²} ≤
  ‖χ_I‖ (A₁ M₀ + E C A₁^{1-γ} B₁^γ) F`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

variable {θ a b c : ℝ} {Ξ : Type*} [Fintype Ξ]

/-- `‖χ_I‖_{ℓ²(ℤ)}`. -/
def CutoffData.chiNorm (D : CutoffData θ a b c) : ℝ := Real.sqrt (∑' y : ℤ, ‖D.χ y‖ ^ 2)

/-- `F = (∑_ξ ‖f_ξ‖²_{ℓ²})^{1/2}` for the family of sequences with densities `H_ξ`. -/
def famNorm (θ : ℝ) (H : Ξ → ℝ → ℂ) : ℝ≥0∞ :=
  (∑ ξ, ∑' x : ℤ, ‖invFZ θ (H ξ) x‖ₑ ^ 2) ^ (1 / 2 : ℝ)

theorem CutoffData.chiNorm_nonneg (D : CutoffData θ a b c) : 0 ≤ D.chiNorm := Real.sqrt_nonneg _

/-- `∑_y ‖χ_I(y)‖ₑ² = ofReal (‖χ_I‖²)`. -/
theorem CutoffData.tsum_enorm_sq_chi (D : CutoffData θ a b c) :
    ∑' y : ℤ, ‖D.χ y‖ₑ ^ 2 = ENNReal.ofReal D.chiNorm ^ 2 := by
  have hs : Summable fun y : ℤ => ‖D.χ y‖ ^ 2 := D.hasSum_norm_sq_chi.summable
  rw [← ENNReal.ofReal_pow D.chiNorm_nonneg, CutoffData.chiNorm,
    Real.sq_sqrt (tsum_nonneg fun _ => by positivity),
    ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hs]
  refine tsum_congr fun y => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

section Main

variable {T : Set ℝ} {m : ℝ → ℝ → ℂ} {H : Ξ → ℝ → ℂ} (D : CutoffData θ a b c) (g : Ξ → ℤ → ℂ)

/-- **Theorem B(a)** (`p:variable`, in the form proved here). For `2 < s < r`, a finite `T`,
`A₁, B₁ ≥ 0` with (A) `∑_y |φ_I(y) ∑_ξ w_ξ g_ξ(x + y)|² ≤ A₁² ∑_ξ |w_ξ|²` and (B)
`∑_y ∑_ξ |φ_I(y) g_ξ(x + y)|² ≤ B₁²` for all `x`, and the variational hypothesis (V_s)
`‖V^s(K_t * f : t ∈ T)‖_{ℓ²} ≤ C ‖f‖_{ℓ²}` for every `f` with `f̂` supported in `I`:

`‖V^r(a_t : t ∈ T)‖_{ℓ²_x} ≤ ‖χ_I‖ E(r, s) C A₁^{1-γ} B₁^γ (∑_ξ ‖f_ξ‖²)^{1/2}`,

`a_t(x) = ∑_ξ g_ξ(x) (K_t * f_ξ)(x)`, `(K_t * f_ξ)^ = m_t f̂_ξ`. -/
theorem variable_variation_le (hadm : VarAdmissible θ a b T m H) {r s : ℝ} (hs : 2 < s)
    (hsr : s < r) (hT : T.Finite) {A₁ B₁ : ℝ} (hA₁ : 0 ≤ A₁) (hB₁ : 0 ≤ B₁)
    (hA : ∀ (x : ℤ) (w : Ξ → ℂ), ∑' y : ℤ, ‖D.φ y * ∑ ξ, w ξ * g ξ (x + y)‖ₑ ^ 2 ≤
      ENNReal.ofReal (A₁ ^ 2 * ∑ ξ, ‖w ξ‖ ^ 2))
    (hB : ∀ x : ℤ, ∑' y : ℤ, ∑ ξ, ‖D.φ y * g ξ (x + y)‖ₑ ^ 2 ≤ ENNReal.ofReal (B₁ ^ 2))
    {C : ℝ} (_hC : 0 ≤ C)
    (hVs : ∀ H' : ℝ → ℂ, ChartL2 θ H' → (∀ β, β ∉ Set.Icc a b → H' β = 0) →
      (∑' x : ℤ, rVariationOn s T (fun t => invFZ θ (fun β => m t β * H' β) x) ^ 2) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal C * l2enorm (invFZ θ H')) :
    (∑' x : ℤ, rVariationOn r T (fun t => aSum θ g m H t x) ^ 2) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (D.chiNorm * entropyConst r s * C * A₁ ^ (1 - entropyGamma r s) *
        B₁ ^ entropyGamma r s) * famNorm θ H := by
  have hr1 : 1 ≤ r := by linarith
  set K : ℝ := entropyConst r s * A₁ ^ (1 - entropyGamma r s) * B₁ ^ entropyGamma r s with hK
  have hK0 : 0 ≤ K := by
    have := entropyConst_pos hs hsr
    positivity
  have h1 := tsum_variation_sq_le D g hadm hr1
  have h2 : ∑' x : ℤ, ∑' y : ℤ, rVariationOn r T
        (fun t => ∑ ξ, (D.φ y * g ξ (x + y)) * KSeq θ m H t ξ x) ^ 2 ≤
      ∑' x : ℤ, ENNReal.ofReal K ^ 2 *
        ∑ ξ, rVariationOn s T (fun t => KSeq θ m H t ξ x) ^ 2 :=
    ENNReal.tsum_le_tsum fun x => pointwise_entropy D g hs hsr hT hA₁ hB₁ hA hB x
  rw [ENNReal.tsum_mul_left, Summable.tsum_finsetSum (fun ξ _ => ENNReal.summable)] at h2
  have h4 : ∀ ξ : Ξ, ∑' x : ℤ, rVariationOn s T (fun t => KSeq θ m H t ξ x) ^ 2 ≤
      ENNReal.ofReal C ^ 2 * ∑' x : ℤ, ‖invFZ θ (H ξ) x‖ₑ ^ 2 := by
    intro ξ
    have h := hVs (H ξ) (hadm.l2 ξ) (hadm.supp ξ)
    calc ∑' x : ℤ, rVariationOn s T (fun t => KSeq θ m H t ξ x) ^ 2
        = ((∑' x : ℤ, rVariationOn s T (fun t => invFZ θ (fun β => m t β * H ξ β) x) ^ 2) ^
            (1 / 2 : ℝ)) ^ 2 := (enorm_rpow_half_sq _).symm
      _ ≤ (ENNReal.ofReal C * l2enorm (invFZ θ (H ξ))) ^ 2 := by gcongr
      _ = ENNReal.ofReal C ^ 2 * ∑' x : ℤ, ‖invFZ θ (H ξ) x‖ₑ ^ 2 := by
          rw [mul_pow, l2enorm, enorm_rpow_half_sq]
  have h5 : ∑ ξ : Ξ, ∑' x : ℤ, rVariationOn s T (fun t => KSeq θ m H t ξ x) ^ 2 ≤
      ENNReal.ofReal C ^ 2 * ∑ ξ : Ξ, ∑' x : ℤ, ‖invFZ θ (H ξ) x‖ₑ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun ξ _ => h4 ξ
  rw [D.tsum_enorm_sq_chi] at h1
  have hS : ∑' x : ℤ, rVariationOn r T (fun t => aSum θ g m H t x) ^ 2 ≤
      (ENNReal.ofReal D.chiNorm * ENNReal.ofReal K * ENNReal.ofReal C) ^ 2 *
        ∑ ξ : Ξ, ∑' x : ℤ, ‖invFZ θ (H ξ) x‖ₑ ^ 2 := by
    calc _ ≤ _ := h1
      _ ≤ ENNReal.ofReal D.chiNorm ^ 2 * (ENNReal.ofReal K ^ 2 *
            (ENNReal.ofReal C ^ 2 * ∑ ξ : Ξ, ∑' x : ℤ, ‖invFZ θ (H ξ) x‖ₑ ^ 2)) := by
          gcongr
          exact h2.trans (by gcongr)
      _ = _ := by ring
  have hP : ENNReal.ofReal (D.chiNorm * entropyConst r s * C * A₁ ^ (1 - entropyGamma r s) *
        B₁ ^ entropyGamma r s) =
      ENNReal.ofReal D.chiNorm * ENNReal.ofReal K * ENNReal.ofReal C := by
    have : D.chiNorm * entropyConst r s * C * A₁ ^ (1 - entropyGamma r s) *
        B₁ ^ entropyGamma r s = D.chiNorm * K * C := by rw [hK]; ring
    rw [this, ENNReal.ofReal_mul (mul_nonneg D.chiNorm_nonneg hK0),
      ENNReal.ofReal_mul D.chiNorm_nonneg]
  rw [hP, famNorm]
  calc _ ≤ ((ENNReal.ofReal D.chiNorm * ENNReal.ofReal K * ENNReal.ofReal C) ^ 2 *
        ∑ ξ : Ξ, ∑' x : ℤ, ‖invFZ θ (H ξ) x‖ₑ ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hS (by norm_num)
    _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), enorm_sq_rpow_half]

/-- Pointwise Cauchy-Schwarz for the base point:
`|a_{t₀}(x)|² ≤ ‖χ_I‖² ∑_y |φ_I(y) ∑_ξ g_ξ(x) (K_{t₀} * f_ξ)(x - y)|²`. -/
theorem base_point_sq_le (hadm : VarAdmissible θ a b T m H) {t₀ : ℝ} (ht₀ : t₀ ∈ T) (x : ℤ) :
    ‖aSum θ g m H t₀ x‖ₑ ^ 2 ≤ ENNReal.ofReal D.chiNorm ^ 2 *
      ∑' y : ℤ, ‖D.φ y * ∑ ξ, g ξ x * KSeq θ m H t₀ ξ (x - y)‖ₑ ^ 2 := by
  rw [aSum_eq_tsum D g hadm x ht₀]
  have h1 : ‖∑' y : ℤ, (∑ ξ, g ξ x * KSeq θ m H t₀ ξ (x - y)) * (D.χ y * D.φ y)‖ₑ ≤
      ∑' y : ℤ, ‖D.χ y‖ₑ * ‖D.φ y * ∑ ξ, g ξ x * KSeq θ m H t₀ ξ (x - y)‖ₑ := by
    refine enorm_tsum_le_tsum_enorm.trans (le_of_eq (tsum_congr fun y => ?_))
    rw [enorm_mul, enorm_mul, enorm_mul]
    ring
  calc _ ≤ (∑' y : ℤ, ‖D.χ y‖ₑ * ‖D.φ y * ∑ ξ, g ξ x * KSeq θ m H t₀ ξ (x - y)‖ₑ) ^ 2 := by
        gcongr
    _ ≤ ((∑' y : ℤ, ‖D.χ y‖ₑ ^ 2) ^ (1 / 2 : ℝ) *
          (∑' y : ℤ, ‖D.φ y * ∑ ξ, g ξ x * KSeq θ m H t₀ ξ (x - y)‖ₑ ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
        exact tsum_mul_le_sqrt_mul_sqrt _ _
    _ = _ := by rw [mul_pow, enorm_rpow_half_sq, enorm_rpow_half_sq, D.tsum_enorm_sq_chi]

/-- **Theorem B(b)** (base point): under (A) alone, for `t₀ ∈ T` and `M₀ ≥ sup_{β ∈ I} |m_{t₀}(β)|`,
`‖a_{t₀}‖_{ℓ²} ≤ ‖χ_I‖ A₁ M₀ (∑_ξ ‖f_ξ‖²)^{1/2}`. -/
theorem variable_base_point (hadm : VarAdmissible θ a b T m H) {t₀ : ℝ} (ht₀ : t₀ ∈ T)
    {A₁ : ℝ} (hA₁ : 0 ≤ A₁)
    (hA : ∀ (x : ℤ) (w : Ξ → ℂ), ∑' y : ℤ, ‖D.φ y * ∑ ξ, w ξ * g ξ (x + y)‖ₑ ^ 2 ≤
      ENNReal.ofReal (A₁ ^ 2 * ∑ ξ, ‖w ξ‖ ^ 2))
    {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (hM : ∀ β ∈ Set.Icc a b, ‖m t₀ β‖ ≤ M₀) :
    (∑' x : ℤ, ‖aSum θ g m H t₀ x‖ₑ ^ 2) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (D.chiNorm * A₁ * M₀) * famNorm θ H := by
  have h1 : ∑' x : ℤ, ‖aSum θ g m H t₀ x‖ₑ ^ 2 ≤ ENNReal.ofReal D.chiNorm ^ 2 *
      ∑' x : ℤ, ∑' y : ℤ, ‖D.φ y * ∑ ξ, g ξ x * KSeq θ m H t₀ ξ (x - y)‖ₑ ^ 2 := by
    rw [ENNReal.tsum_mul_left.symm]
    exact ENNReal.tsum_le_tsum fun x => base_point_sq_le D g hadm ht₀ x
  rw [tsum_tsum_shift (fun x y => ‖D.φ y * ∑ ξ, g ξ x * KSeq θ m H t₀ ξ (x - y)‖ₑ ^ 2)] at h1
  simp only [add_sub_cancel_right] at h1
  have h2 : ∀ x' : ℤ, ∑' y : ℤ, ‖D.φ y * ∑ ξ, g ξ (x' + y) * KSeq θ m H t₀ ξ x'‖ₑ ^ 2 ≤
      ENNReal.ofReal A₁ ^ 2 * ∑ ξ, ‖KSeq θ m H t₀ ξ x'‖ₑ ^ 2 := by
    intro x'
    have h := hA x' (fun ξ => KSeq θ m H t₀ ξ x')
    rw [ofReal_sq_mul_sum_norm_sq hA₁] at h
    refine le_trans (le_of_eq (tsum_congr fun y => ?_)) h
    have : ∑ ξ, g ξ (x' + y) * KSeq θ m H t₀ ξ x' =
        ∑ ξ, KSeq θ m H t₀ ξ x' * g ξ (x' + y) :=
      Finset.sum_congr rfl fun ξ _ => mul_comm _ _
    rw [this]
  have h3 : ∀ ξ : Ξ, ∑' x : ℤ, ‖KSeq θ m H t₀ ξ x‖ₑ ^ 2 ≤
      ENNReal.ofReal M₀ ^ 2 * ∑' x : ℤ, ‖invFZ θ (H ξ) x‖ₑ ^ 2 := by
    intro ξ
    have hb : ∀ β, ‖m t₀ β * H ξ β‖ ≤ M₀ * ‖H ξ β‖ := by
      intro β
      by_cases hβ : β ∈ Set.Icc a b
      · rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hM β hβ) (norm_nonneg _)
      · rw [hadm.supp_mul t₀ ξ hβ]; simp [hadm.supp ξ β hβ]
    have h := l2enorm_invFZ_mul_le hM₀ (hadm.meas t₀ ht₀).aestronglyMeasurable hb (hadm.l2 ξ)
    calc ∑' x : ℤ, ‖KSeq θ m H t₀ ξ x‖ₑ ^ 2
        = (l2enorm (invFZ θ (fun β => m t₀ β * H ξ β))) ^ 2 := by
          rw [l2enorm, enorm_rpow_half_sq]; rfl
      _ ≤ (ENNReal.ofReal M₀ * l2enorm (invFZ θ (H ξ))) ^ 2 := by gcongr
      _ = _ := by rw [mul_pow, l2enorm, enorm_rpow_half_sq]
  have h4 : ∑' x' : ℤ, ∑' y : ℤ, ‖D.φ y * ∑ ξ, g ξ (x' + y) * KSeq θ m H t₀ ξ x'‖ₑ ^ 2 ≤
      ENNReal.ofReal A₁ ^ 2 * (ENNReal.ofReal M₀ ^ 2 *
        ∑ ξ : Ξ, ∑' x : ℤ, ‖invFZ θ (H ξ) x‖ₑ ^ 2) := by
    calc _ ≤ ∑' x' : ℤ, ENNReal.ofReal A₁ ^ 2 * ∑ ξ, ‖KSeq θ m H t₀ ξ x'‖ₑ ^ 2 :=
          ENNReal.tsum_le_tsum h2
      _ = ENNReal.ofReal A₁ ^ 2 * ∑ ξ : Ξ, ∑' x : ℤ, ‖KSeq θ m H t₀ ξ x‖ₑ ^ 2 := by
          rw [ENNReal.tsum_mul_left, Summable.tsum_finsetSum (fun ξ _ => ENNReal.summable)]
      _ ≤ ENNReal.ofReal A₁ ^ 2 * ∑ ξ : Ξ, ENNReal.ofReal M₀ ^ 2 *
            ∑' x : ℤ, ‖invFZ θ (H ξ) x‖ₑ ^ 2 := by
          gcongr with ξ _
          exact h3 ξ
      _ = _ := by rw [← Finset.mul_sum]
  have hS : ∑' x : ℤ, ‖aSum θ g m H t₀ x‖ₑ ^ 2 ≤
      (ENNReal.ofReal D.chiNorm * ENNReal.ofReal A₁ * ENNReal.ofReal M₀) ^ 2 *
        ∑ ξ : Ξ, ∑' x : ℤ, ‖invFZ θ (H ξ) x‖ₑ ^ 2 := by
    calc _ ≤ _ := h1
      _ ≤ ENNReal.ofReal D.chiNorm ^ 2 * (ENNReal.ofReal A₁ ^ 2 * (ENNReal.ofReal M₀ ^ 2 *
            ∑ ξ : Ξ, ∑' x : ℤ, ‖invFZ θ (H ξ) x‖ₑ ^ 2)) := by gcongr
      _ = _ := by ring
  rw [ENNReal.ofReal_mul (mul_nonneg D.chiNorm_nonneg hA₁), ENNReal.ofReal_mul D.chiNorm_nonneg,
    famNorm]
  calc _ ≤ ((ENNReal.ofReal D.chiNorm * ENNReal.ofReal A₁ * ENNReal.ofReal M₀) ^ 2 *
        ∑ ξ : Ξ, ∑' x : ℤ, ‖invFZ θ (H ξ) x‖ₑ ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hS (by norm_num)
    _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), enorm_sq_rpow_half]

/-- **Theorem B(c)** (selector): for `t₀ ∈ T`, a finite `X ⊂ ℤ` and `ω : ℤ → ℝ` with `ω(x) ∈ T` for
`x ∈ X`, `(∑_{x ∈ X} |a_{ω(x)}(x)|²)^{1/2} ≤ ‖χ_I‖ (A₁ M₀ + E C A₁^{1-γ} B₁^γ) (∑_ξ ‖f_ξ‖²)^{1/2}`,
by the two-point chain `|a_{ω(x)}(x)| ≤ |a_{t₀}(x)| + V^r(a_t(x) : t ∈ T)`, Minkowski in `ℓ²(X)`,
Theorem B(a) and B(b). -/
theorem variable_selector (hadm : VarAdmissible θ a b T m H) {t₀ : ℝ} (ht₀ : t₀ ∈ T)
    {r s : ℝ} (hs : 2 < s) (hsr : s < r) (hT : T.Finite) {A₁ B₁ : ℝ} (hA₁ : 0 ≤ A₁)
    (hB₁ : 0 ≤ B₁)
    (hA : ∀ (x : ℤ) (w : Ξ → ℂ), ∑' y : ℤ, ‖D.φ y * ∑ ξ, w ξ * g ξ (x + y)‖ₑ ^ 2 ≤
      ENNReal.ofReal (A₁ ^ 2 * ∑ ξ, ‖w ξ‖ ^ 2))
    (hB : ∀ x : ℤ, ∑' y : ℤ, ∑ ξ, ‖D.φ y * g ξ (x + y)‖ₑ ^ 2 ≤ ENNReal.ofReal (B₁ ^ 2))
    {C : ℝ} (hC : 0 ≤ C)
    (hVs : ∀ H' : ℝ → ℂ, ChartL2 θ H' → (∀ β, β ∉ Set.Icc a b → H' β = 0) →
      (∑' x : ℤ, rVariationOn s T (fun t => invFZ θ (fun β => m t β * H' β) x) ^ 2) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal C * l2enorm (invFZ θ H'))
    {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (hM : ∀ β ∈ Set.Icc a b, ‖m t₀ β‖ ≤ M₀)
    (X : Finset ℤ) (ω : ℤ → ℝ) (hω : ∀ x ∈ X, ω x ∈ T) :
    (∑ x ∈ X, ‖aSum θ g m H (ω x) x‖ₑ ^ 2) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (D.chiNorm * (A₁ * M₀ + entropyConst r s * C * A₁ ^ (1 - entropyGamma r s) *
        B₁ ^ entropyGamma r s)) * famNorm θ H := by
  have hr0 : 0 < r := by linarith
  have hpt : ∀ x ∈ X, ‖aSum θ g m H (ω x) x‖ₑ ≤
      ‖aSum θ g m H t₀ x‖ₑ + rVariationOn r T (fun t => aSum θ g m H t x) := fun x hx =>
    enorm_le_enorm_add_rVariationOnH (h := fun t => aSum θ g m H t x) hr0 (hω x hx) ht₀
  have h1 : ∑ x ∈ X, ‖aSum θ g m H (ω x) x‖ₑ ^ 2 ≤ ∑' x : ℤ,
      (‖aSum θ g m H t₀ x‖ₑ + rVariationOn r T (fun t => aSum θ g m H t x)) ^ 2 :=
    (Finset.sum_le_sum fun x hx => by gcongr; exact hpt x hx).trans
      (ENNReal.sum_le_tsum (f := fun x => (‖aSum θ g m H t₀ x‖ₑ +
        rVariationOn r T (fun t => aSum θ g m H t x)) ^ 2) X)
  have hb := variable_base_point D g hadm ht₀ hA₁ hA hM₀ hM
  have ha := variable_variation_le D g hadm hs hsr hT hA₁ hB₁ hA hB hC hVs
  have hc1 : ENNReal.ofReal (D.chiNorm * (A₁ * M₀ + entropyConst r s * C *
      A₁ ^ (1 - entropyGamma r s) * B₁ ^ entropyGamma r s)) =
      ENNReal.ofReal (D.chiNorm * A₁ * M₀) + ENNReal.ofReal (D.chiNorm * entropyConst r s * C *
        A₁ ^ (1 - entropyGamma r s) * B₁ ^ entropyGamma r s) := by
    have hE := entropyConst_pos hs hsr
    rw [← ENNReal.ofReal_add (by have := D.chiNorm_nonneg; positivity)
      (by have := D.chiNorm_nonneg; positivity)]
    congr 1
    ring
  rw [hc1, add_mul]
  calc _ ≤ (∑' x : ℤ, (‖aSum θ g m H t₀ x‖ₑ +
        rVariationOn r T (fun t => aSum θ g m H t x)) ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow h1 (by norm_num)
    _ ≤ _ := (tsum_sq_add_le _ _).trans (add_le_add hb ha)

end Main

end PrimeCarleson.Proof.Paper
