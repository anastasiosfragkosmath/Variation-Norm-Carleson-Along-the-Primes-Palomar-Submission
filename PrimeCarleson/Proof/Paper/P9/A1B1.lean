module

public import PrimeCarleson.Proof.Paper.P9.Sizes

/-!
# The hypotheses (A) and (B) of `p:variable` for `g_ξ(x) = e(γ_ξ x)`

Source: main paper `p:global-shell-var`, L2031–L2048 and L2049–L2063.

Let `Ξ` be a finite type, `γ : Ξ → ℝ` frequencies with `‖γ_ξ - γ_ξ'‖_𝕋 > 2c` for `ξ ≠ ξ'`
(`c` the scale of the cutoff `φ_I`; for `Γ_Q` this is `Q^{-2} > 2c`), and `g_ξ(x) = e(γ_ξ x)`.

* `A1_bound`: `∑_y |φ_I(y) ∑_ξ w_ξ e(γ_ξ (x + y))|² ≤ (∑_y |φ_I(y)|²) ∑_ξ |w_ξ|² ≤ (2/c) ∑_ξ |w_ξ|²`
  (the Fourier series of `φ_I²` vanishes on `‖τ‖_𝕋 > 2c`, `CutoffData.phi_sq_series_eq_zero`, so
  the off-diagonal terms cancel: `A₁² = 2/c ≈ |I|^{-1}`);
* `B1_bound`: `∑_y ∑_ξ |φ_I(y) e(γ_ξ (x + y))|² ≤ |Ξ| (2/c)` (`B₁² = |Ξ| A₁²`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

namespace CutoffData

variable {θ a b c : ℝ} (D : CutoffData θ a b c) {Ξ : Type*} [Fintype Ξ] (γ : Ξ → ℝ)

theorem summable_norm_sq_phi : Summable fun y : ℤ => ‖D.φ y‖ ^ 2 := D.hasSum_norm_sq_phi.summable

/-- The complex identity behind `A₁`: `|φ_I(y) S(y)|² = ∑_{ξ,ξ'} w_ξ \bar w_{ξ'} e((γ_ξ - γ_ξ') x)
(|φ_I(y)|² e((γ_ξ - γ_ξ') y))` for `S(y) = ∑_ξ w_ξ e(γ_ξ (x + y))`. -/
theorem norm_sq_expand (x y : ℤ) (w : Ξ → ℂ) :
    ((‖D.φ y * ∑ ξ, w ξ * e (γ ξ * ((x + y : ℤ) : ℝ))‖ ^ 2 : ℝ) : ℂ) =
      ∑ ξ, ∑ ξ', (w ξ * conj (w ξ') * e ((γ ξ - γ ξ') * (x : ℝ))) *
        (((‖D.φ y‖ ^ 2 : ℝ) : ℂ) * e ((γ ξ - γ ξ') * (y : ℝ))) := by
  have hS2 : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := fun z => by
    rw [← Complex.normSq_eq_norm_sq, Complex.mul_conj]
  rw [norm_mul, mul_pow, Complex.ofReal_mul,
    hS2 (∑ ξ, w ξ * e (γ ξ * ((x + y : ℤ) : ℝ))), map_sum, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ξ' _ => ?_
  have h1 : e (γ ξ * ((x + y : ℤ) : ℝ)) * conj (e (γ ξ' * ((x + y : ℤ) : ℝ))) =
      e ((γ ξ - γ ξ') * (x : ℝ)) * e ((γ ξ - γ ξ') * (y : ℝ)) := by
    rw [← e_neg, ← e_add, ← e_add]
    congr 1
    push_cast
    ring
  simp only [map_mul]
  calc ((‖D.φ y‖ ^ 2 : ℝ) : ℂ) * (w ξ * e (γ ξ * ((x + y : ℤ) : ℝ)) *
        (conj (w ξ') * conj (e (γ ξ' * ((x + y : ℤ) : ℝ)))))
      = (w ξ * conj (w ξ')) * (e (γ ξ * ((x + y : ℤ) : ℝ)) *
          conj (e (γ ξ' * ((x + y : ℤ) : ℝ)))) * ((‖D.φ y‖ ^ 2 : ℝ) : ℂ) := by ring
    _ = _ := by rw [h1]; ring

/-- **The `A₁` computation** (Source: main paper `p:global-shell-var`, L2031–L2048): for
`2c`-separated frequencies, `∑_y |φ_I(y) ∑_ξ w_ξ e(γ_ξ (x + y))|² ≤ (2/c) ∑_ξ |w_ξ|²` (so
`A₁² = 2/c`). -/
theorem A1_bound (hsep : ∀ ξ ξ' : Ξ, ξ ≠ ξ' → ∀ v : ℤ, 2 * c < |γ ξ - γ ξ' - v|) (x : ℤ)
    (w : Ξ → ℂ) :
    ∑' y : ℤ, ‖D.φ y * ∑ ξ, w ξ * e (γ ξ * ((x + y : ℤ) : ℝ))‖ₑ ^ 2 ≤
      ENNReal.ofReal ((2 / c) * ∑ ξ, ‖w ξ‖ ^ 2) := by
  classical
  set a : ℤ → ℝ := fun y => ‖D.φ y * ∑ ξ, w ξ * e (γ ξ * ((x + y : ℤ) : ℝ))‖ ^ 2 with ha
  have hsum : Summable fun y : ℤ => ‖D.φ y‖ ^ 2 := D.summable_norm_sq_phi
  have hterm : ∀ ξ ξ' : Ξ, Summable fun y : ℤ => (w ξ * conj (w ξ') * e ((γ ξ - γ ξ') * (x : ℝ))) *
      (((‖D.φ y‖ ^ 2 : ℝ) : ℂ) * e ((γ ξ - γ ξ') * (y : ℝ))) := by
    intro ξ ξ'
    refine Summable.of_norm_bounded ((hsum.mul_left (‖w ξ‖ * ‖w ξ'‖))) fun y => ?_
    have h : ‖(w ξ * conj (w ξ') * e ((γ ξ - γ ξ') * (x : ℝ))) *
        (((‖D.φ y‖ ^ 2 : ℝ) : ℂ) * e ((γ ξ - γ ξ') * (y : ℝ)))‖ =
        ‖w ξ‖ * ‖w ξ'‖ * ‖D.φ y‖ ^ 2 := by
      simp only [norm_mul, norm_e, RCLike.norm_conj, Complex.norm_real, norm_pow, norm_norm,
        mul_one]
    exact h.le
  have ha_sum : Summable a := by
    have : ∀ y, a y = (∑ ξ, ∑ ξ', (w ξ * conj (w ξ') * e ((γ ξ - γ ξ') * (x : ℝ))) *
        (((‖D.φ y‖ ^ 2 : ℝ) : ℂ) * e ((γ ξ - γ ξ') * (y : ℝ)))).re := by
      intro y
      rw [← D.norm_sq_expand γ x y w, Complex.ofReal_re]
    rw [summable_congr this]
    exact (Complex.reCLM.summable
      (summable_sum fun ξ _ => summable_sum fun ξ' _ => hterm ξ ξ'))
  -- the complex value of the sum
  have hC : ((∑' y : ℤ, a y : ℝ) : ℂ) = (((∑ ξ, ‖w ξ‖ ^ 2) * ∑' y : ℤ, ‖D.φ y‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    have h1 : ∀ y, ((a y : ℝ) : ℂ) = ∑ ξ, ∑ ξ', (w ξ * conj (w ξ') * e ((γ ξ - γ ξ') * (x : ℝ))) *
        (((‖D.φ y‖ ^ 2 : ℝ) : ℂ) * e ((γ ξ - γ ξ') * (y : ℝ))) := fun y =>
      D.norm_sq_expand γ x y w
    simp_rw [h1]
    rw [Summable.tsum_finsetSum (fun ξ _ => summable_sum fun ξ' _ => hterm ξ ξ')]
    have h2 : ∀ ξ : Ξ, ∑' y : ℤ, ∑ ξ', (w ξ * conj (w ξ') * e ((γ ξ - γ ξ') * (x : ℝ))) *
        (((‖D.φ y‖ ^ 2 : ℝ) : ℂ) * e ((γ ξ - γ ξ') * (y : ℝ))) =
        ((‖w ξ‖ ^ 2 : ℝ) : ℂ) * ((∑' y : ℤ, ‖D.φ y‖ ^ 2 : ℝ) : ℂ) := by
      intro ξ
      rw [Summable.tsum_finsetSum (fun ξ' _ => hterm ξ ξ')]
      rw [Finset.sum_eq_single ξ]
      · rw [tsum_mul_left]
        simp only [sub_self, zero_mul, e_zero, mul_one]
        rw [Complex.ofReal_tsum, Complex.mul_conj']
        push_cast
        ring
      · intro ξ' _ hne
        rw [tsum_mul_left, D.phi_sq_series_eq_zero (τ := (γ ξ - γ ξ')) (fun v => by
          exact hsep ξ ξ' (Ne.symm hne) v), mul_zero]
      · intro h; exact absurd (Finset.mem_univ ξ) h
    simp_rw [h2]
    push_cast
    rw [← Finset.sum_mul]
  have hR : ∑' y : ℤ, a y = (∑ ξ, ‖w ξ‖ ^ 2) * ∑' y : ℤ, ‖D.φ y‖ ^ 2 := by
    exact_mod_cast hC
  have hE : ∑' y : ℤ, ‖D.φ y * ∑ ξ, w ξ * e (γ ξ * ((x + y : ℤ) : ℝ))‖ₑ ^ 2 =
      ENNReal.ofReal (∑' y : ℤ, a y) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun y => by positivity) ha_sum]
    refine tsum_congr fun y => ?_
    simp only [ha]
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [hE]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hR, mul_comm (2 / c)]
  exact mul_le_mul_of_nonneg_left D.sum_norm_sq_phi_le (Finset.sum_nonneg fun _ _ => by positivity)

/-- **The `B₁` computation** (Source: main paper `p:global-shell-var`, L2049–L2063):
`∑_y ∑_ξ |φ_I(y) e(γ_ξ (x + y))|² ≤ |Ξ| (2/c)` (so `B₁² = |Ξ| (2/c)`). -/
theorem B1_bound (x : ℤ) :
    ∑' y : ℤ, ∑ ξ, ‖D.φ y * e (γ ξ * ((x + y : ℤ) : ℝ))‖ₑ ^ 2 ≤
      ENNReal.ofReal ((Fintype.card Ξ : ℝ) * (2 / c)) := by
  have he : ∀ t : ℝ, ‖e t‖ₑ = 1 := fun t => by rw [← ofReal_norm, norm_e]; simp
  have h1 : ∀ y : ℤ, ∑ ξ, ‖D.φ y * e (γ ξ * ((x + y : ℤ) : ℝ))‖ₑ ^ 2 =
      (Fintype.card Ξ : ℝ≥0∞) * ‖D.φ y‖ₑ ^ 2 := by
    intro y
    simp [enorm_mul, he]
  simp_rw [h1]
  rw [ENNReal.tsum_mul_left]
  have h2 : ∑' y : ℤ, ‖D.φ y‖ₑ ^ 2 = ENNReal.ofReal (∑' y : ℤ, ‖D.φ y‖ ^ 2) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun y => by positivity) D.summable_norm_sq_phi]
    refine tsum_congr fun y => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [h2, show ((Fintype.card Ξ : ℝ≥0∞)) = ENNReal.ofReal (Fintype.card Ξ : ℝ) by simp,
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left D.sum_norm_sq_phi_le (by positivity))

end CutoffData

end PrimeCarleson.Proof.Paper
