module

public import PrimeCarleson.Proof.Paper.P9.Variable

/-!
# `p:variable`, second half: the entropy lemma at each `x` and the variational hypothesis

Source: main paper `p:variable`, L1914–L1929 (the entropy lemma at each `x`, L1914–L1924, and the
summed variational hypothesis, L1925–L1929), in the form proved here (Theorem B(a)).

* `pointwise_entropy` (the application of the entropy lemma, L1914–L1924): for fixed `x`, apply
  Theorem A(a) (`entropy_variation_le_of_rVariationOnH`, `P8/EntropyLemma.lean`) with `H = ℓ²(Ξ)`,
  `c_t = (K_t * f_ξ(x))_ξ`, `(Y, ν) = (ℤ, counting)`, `g_x(y) = (φ_I(y) g_ξ(x + y))_ξ`,
  `A₀ = A₁`, `B₀ = B₁` (so (H1) is (A), (H2) is (B)), and
  `λ(x) = (∑_ξ V^{s}(K_t * f_ξ(x) : t ∈ T)²)^{1/2}`; the hypothesis (V) for `λ(x)` is the
  chain-wise Minkowski inequality `rVariationOnH_euclid_le`
  (L1925–L1929, first half):
  `∑_y V^r(∑_ξ φ_I(y) g_ξ(x + y) (K_t * f_ξ)(x) : t)² ≤ (E A₁^{1-γ} B₁^γ)² ∑_ξ V^s(K_t * f_ξ(x))²`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

variable {θ a b c : ℝ} {Ξ : Type*} [Fintype Ξ]

section Entropy

variable {T : Set ℝ} {m : ℝ → ℝ → ℂ} {H : Ξ → ℝ → ℂ} (D : CutoffData θ a b c) (g : Ξ → ℤ → ℂ)

/-- **The application of the entropy lemma** (Source: main paper `p:variable`, L1914–L1924, in the
form proved here): for `2 < s < r`, finite `T`, `A₁, B₁ ≥ 0` with (A) `∑_y
|φ_I(y) ∑_ξ w_ξ g_ξ(x + y)|² ≤ A₁² ∑_ξ |w_ξ|²` and (B) `∑_y ∑_ξ |φ_I(y) g_ξ(x + y)|² ≤ B₁²`, `∑_y
V^r(∑_ξ φ_I(y) g_ξ(x + y) (K_t * f_ξ)(x) : t ∈ T)² ≤ (E(r,s) A₁^{1-γ} B₁^γ)² ∑_ξ V^s((K_t * f_ξ)(x)
: t ∈ T)²`. -/
theorem pointwise_entropy {r s : ℝ} (hs : 2 < s) (hsr : s < r) (hT : T.Finite)
    {A₁ B₁ : ℝ} (hA₁ : 0 ≤ A₁) (hB₁ : 0 ≤ B₁)
    (hA : ∀ (x : ℤ) (w : Ξ → ℂ), ∑' y : ℤ, ‖D.φ y * ∑ ξ, w ξ * g ξ (x + y)‖ₑ ^ 2 ≤
      ENNReal.ofReal (A₁ ^ 2 * ∑ ξ, ‖w ξ‖ ^ 2))
    (hB : ∀ x : ℤ, ∑' y : ℤ, ∑ ξ, ‖D.φ y * g ξ (x + y)‖ₑ ^ 2 ≤ ENNReal.ofReal (B₁ ^ 2))
    (x : ℤ) :
    ∑' y : ℤ, rVariationOn r T
        (fun t => ∑ ξ, (D.φ y * g ξ (x + y)) * KSeq θ m H t ξ x) ^ 2 ≤
      ENNReal.ofReal (entropyConst r s * A₁ ^ (1 - entropyGamma r s) *
          B₁ ^ entropyGamma r s) ^ 2 *
        ∑ ξ, rVariationOn s T (fun t => KSeq θ m H t ξ x) ^ 2 := by
  classical
  have hs1 : 1 ≤ s := by linarith
  set V : Ξ → ℝ≥0∞ := fun ξ => rVariationOn s T (fun t => KSeq θ m H t ξ x) with hV
  set Λ : ℝ≥0∞ := ∑ ξ, V ξ ^ 2 with hΛ
  have hVfin : ∀ ξ, V ξ < ⊤ := fun ξ => rVariationOn_lt_top hT hs1 _
  have hΛfin : Λ ≠ ⊤ := (ENNReal.sum_lt_top.2 fun ξ _ => ENNReal.pow_lt_top (hVfin ξ)).ne
  let c' : ℝ → EuclideanSpace ℂ Ξ := fun t => WithLp.toLp 2 (fun ξ => KSeq θ m H t ξ x)
  let g' : ℤ → EuclideanSpace ℂ Ξ := fun y => WithLp.toLp 2 (fun ξ => D.φ y * g ξ (x + y))
  let lam : ℝ := (Λ ^ (1 / 2 : ℝ)).toReal
  have hlam0 : 0 ≤ lam := ENNReal.toReal_nonneg
  have hlam : ENNReal.ofReal lam = Λ ^ (1 / 2 : ℝ) :=
    ENNReal.ofReal_toReal (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hΛfin)
  have hVc : rVariationOnH s T c' ≤ ENNReal.ofReal lam := by
    rw [hlam]
    exact rVariationOnH_euclid_le hs.le c'
  have hH1 : ∀ w : EuclideanSpace ℂ Ξ,
      ∫⁻ y, ‖pairing w (g' y)‖ₑ ^ 2 ∂(Measure.count : Measure ℤ) ≤
        ENNReal.ofReal (A₁ ^ 2 * ‖w‖ ^ 2) := by
    intro w
    rw [lintegral_count, EuclideanSpace.norm_sq_eq]
    have hpt : ∀ y : ℤ, pairing w (g' y) = D.φ y * ∑ ξ, w.ofLp ξ * g ξ (x + y) := by
      intro y
      simp only [pairing, g', Finset.mul_sum]
      exact Finset.sum_congr rfl fun ξ _ => by ring
    simp_rw [hpt]
    exact hA x w.ofLp
  have hH2 : ∫⁻ y, ‖g' y‖ₑ ^ 2 ∂(Measure.count : Measure ℤ) ≤ ENNReal.ofReal (B₁ ^ 2) := by
    rw [lintegral_count]
    simp_rw [enorm_euclid_sq]
    exact hB x
  have hmain := entropy_variation_le_of_rVariationOnH hs hsr hT c' hlam0 hVc
    (Measure.count : Measure ℤ) g' (fun ξ => measurable_from_top) hA₁ hB₁ hH1 hH2
  rw [lintegral_count] at hmain
  have hfun : ∀ y : ℤ, (fun t => pairing (c' t) (g' y)) =
      fun t => ∑ ξ, (D.φ y * g ξ (x + y)) * KSeq θ m H t ξ x := by
    intro y
    funext t
    exact Finset.sum_congr rfl fun ξ _ => mul_comm _ _
  simp_rw [hfun] at hmain
  set K : ℝ := entropyConst r s * A₁ ^ (1 - entropyGamma r s) * B₁ ^ entropyGamma r s with hK
  have hK0 : 0 ≤ K := by
    have := entropyConst_pos hs hsr
    positivity
  calc ∑' y : ℤ, rVariationOn r T
        (fun t => ∑ ξ, (D.φ y * g ξ (x + y)) * KSeq θ m H t ξ x) ^ 2
      = ((∑' y : ℤ, rVariationOn r T
        (fun t => ∑ ξ, (D.φ y * g ξ (x + y)) * KSeq θ m H t ξ x) ^ 2) ^ (1 / 2 : ℝ)) ^ 2 :=
        (enorm_rpow_half_sq _).symm
    _ ≤ (ENNReal.ofReal (K * lam)) ^ 2 := by gcongr
    _ = ENNReal.ofReal K ^ 2 * Λ := by
        rw [ENNReal.ofReal_mul hK0, mul_pow, hlam, enorm_rpow_half_sq]

end Entropy

end PrimeCarleson.Proof.Paper
