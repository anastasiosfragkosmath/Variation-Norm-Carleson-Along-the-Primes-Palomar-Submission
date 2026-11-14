module

public import PrimeCarleson.Proof.Paper.P9.Sizes

/-!
# The size of `φ_I` on residue classes (scale `N`)

Source: main paper `s:MFanalysis`, L2042–L2053 (second part) and L2170:
`sup_{s ∈ ℤ/N} ∑_{y ≡ s mod N} φ_I(y)² ≲ 1` when `φ_I` has scale `c ≈ 1/N`.

`sum_phi_sq_residue_le`: if `2 c N < 1`, then for every residue class
`∑_{y ≡ s (N)} |φ_I(y)|² ≤ 2/(N c)`: the indicator of `y ≡ s (N)` is the character sum
`N⁻¹ ∑_{l < N} e(l (y - s)/N)`, and `∑_y |φ_I(y)|² e((l/N) y) = 0` for `1 ≤ l < N`
(`phi_sq_series_eq_zero`, since `‖l/N‖_𝕋 ≥ 1/N > 2c`), so only the term `l = 0`,
`N⁻¹ ∑_y |φ_I(y)|²`,
survives.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

namespace CutoffData

variable {θ a b c : ℝ} (D : CutoffData θ a b c)

/-- **The size of `φ_I`, scale `N`** (Source: main paper, L2170):
`∑_{y ≡ s (N)} |φ_I(y)|² ≤ 2/(N c)` if `2 c N < 1`. -/
theorem sum_phi_sq_residue_le (N : ℕ) (hN : 0 < N) (hcN : 2 * c * N < 1) (s : ℤ) :
    ∑' y : ℤ, (if (N : ℤ) ∣ y - s then ‖D.φ y‖ ^ 2 else 0) ≤ 2 / (N * c) := by
  classical
  set a : ℤ → ℝ := fun y => if (N : ℤ) ∣ y - s then ‖D.φ y‖ ^ 2 else 0 with ha
  have hsum : Summable fun y : ℤ => ‖D.φ y‖ ^ 2 := D.hasSum_norm_sq_phi.summable
  have ha_sum : Summable a := hsum.of_nonneg_of_le
    (fun y => by simp only [ha]; split_ifs <;> positivity)
    (fun y => by simp only [ha]; split_ifs <;> simp)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hind : ∀ y : ℤ, ((a y : ℝ) : ℂ) = (1 / (N : ℂ)) * ∑ l ∈ Finset.range N,
      e (-((l : ℝ) * s / N)) * (((‖D.φ y‖ ^ 2 : ℝ) : ℂ) * e (((l : ℝ) / N) * (y : ℝ))) := by
    intro y
    have h1 := sum_range_e_mul_div hN (y - s)
    have h2 : ∀ l ∈ Finset.range N, e (-((l : ℝ) * s / N)) *
        (((‖D.φ y‖ ^ 2 : ℝ) : ℂ) * e (((l : ℝ) / N) * (y : ℝ))) =
        ((‖D.φ y‖ ^ 2 : ℝ) : ℂ) * e ((l : ℝ) * ((y - s : ℤ) : ℝ) / N) := by
      intro l _
      have : e (-((l : ℝ) * s / N)) * e (((l : ℝ) / N) * (y : ℝ)) =
          e ((l : ℝ) * ((y - s : ℤ) : ℝ) / N) := by
        rw [← e_add]; congr 1; push_cast; ring
      calc e (-((l : ℝ) * s / N)) * (((‖D.φ y‖ ^ 2 : ℝ) : ℂ) * e (((l : ℝ) / N) * (y : ℝ)))
          = ((‖D.φ y‖ ^ 2 : ℝ) : ℂ) * (e (-((l : ℝ) * s / N)) * e (((l : ℝ) / N) * (y : ℝ))) := by
            ring
        _ = _ := by rw [this]
    rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, h1]
    simp only [ha]
    split_ifs with h
    · field_simp
    · simp
  have hterm : ∀ l : ℕ, Summable fun y : ℤ =>
      e (-((l : ℝ) * s / N)) * (((‖D.φ y‖ ^ 2 : ℝ) : ℂ) * e (((l : ℝ) / N) * (y : ℝ))) := by
    intro l
    refine Summable.of_norm_bounded hsum fun y => ?_
    simp [norm_e, Complex.norm_real]
  have hterm' : ∀ l : ℕ, Summable fun y : ℤ =>
      ((‖D.φ y‖ ^ 2 : ℝ) : ℂ) * e (((l : ℝ) / N) * (y : ℝ)) := by
    intro l
    refine Summable.of_norm_bounded hsum fun y => ?_
    simp [norm_e, Complex.norm_real]
  have hC : ((∑' y : ℤ, a y : ℝ) : ℂ) = (1 / (N : ℂ)) * ((∑' y : ℤ, ‖D.φ y‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    simp_rw [hind]
    rw [tsum_mul_left, Summable.tsum_finsetSum (fun l _ => hterm l)]
    congr 1
    rw [Finset.sum_eq_single 0]
    · simp only [Nat.cast_zero, zero_mul, zero_div, neg_zero, e_zero, one_mul]
      rw [Complex.ofReal_tsum]
      exact tsum_congr fun y => by simp
    · intro l hl hl0
      rw [tsum_mul_left]
      have hl1 : 1 ≤ l := Nat.one_le_iff_ne_zero.2 hl0
      have hlN : l < N := Finset.mem_range.1 hl
      have := D.phi_sq_series_eq_zero (τ := (l : ℝ) / N) (fun v => by
        have hne : (l : ℤ) - v * N ≠ 0 := by
          intro h0
          have : (N : ℤ) ∣ l := ⟨v, by linarith⟩
          have := Int.le_of_dvd (by exact_mod_cast hl1) this
          omega
        have h1 : (1 : ℝ) ≤ |(((l : ℤ) - v * N : ℤ) : ℝ)| := by
          have := Int.one_le_abs hne
          exact_mod_cast this
        have h2 : |(l : ℝ) / N - v| = |(((l : ℤ) - v * N : ℤ) : ℝ)| / N := by
          have : (l : ℝ) / N - v = (((l : ℤ) - v * N : ℤ) : ℝ) / N := by
            push_cast; field_simp
          rw [this, abs_div, abs_of_pos hN0]
        rw [h2, lt_div_iff₀ hN0]
        nlinarith)
      rw [this, mul_zero]
    · intro h; exact absurd (Finset.mem_range.2 hN) h
  have hR : ∑' y : ℤ, a y = (1 / (N : ℝ)) * ∑' y : ℤ, ‖D.φ y‖ ^ 2 := by
    have hC' : ((∑' y : ℤ, a y : ℝ) : ℂ) =
        (((1 / (N : ℝ)) * ∑' y : ℤ, ‖D.φ y‖ ^ 2 : ℝ) : ℂ) := by
      rw [hC]; push_cast; ring
    exact_mod_cast hC'
  rw [hR]
  calc (1 / (N : ℝ)) * ∑' y : ℤ, ‖D.φ y‖ ^ 2 ≤ (1 / (N : ℝ)) * (2 / c) :=
        mul_le_mul_of_nonneg_left D.sum_norm_sq_phi_le (by positivity)
    _ = 2 / (N * c) := by field_simp

end CutoffData

end PrimeCarleson.Proof.Paper
