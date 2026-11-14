module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import PrimeCarleson.Proof.Goal0.Divisors

/-!
# Exponent bookkeeping for the proof of `p:goal0`

The last step of the proof of Proposition `p:goal0` (`sources/Variational_Carleson.tex`, the
corollary at L2804–L2816; Source: main paper `p:goal0`, L2545–L2550), in the form formalized here.
With the divisor-bound constant `C` (`τ(n) ≤ C n^ε`), the energy decrement is run with
`η = Q^{-3ε}/(2C²)`, atom bound `σ = 2C⁴Q^{4ε-1}` and remainder level `X = Q^{-1-ε}|B|`. Its output
`X + σ √(3/η³)` is at most `(A + 48 C^{10}) Q^{κ-1-ε}` when `|B| ≤ A Q^κ` and `14 ε ≤ κ` (the paper
assumes `ε ≤ κ/100`, e:epskappa). The bound `√y ≤ y` for `y ≥ 1` replaces the square root, at the
cost of `Q^{13ε-1}` instead of `Q^{8.5ε-1}`; there is no threshold `Q ≥ Q₀`. Also: elements of a
dyadic block lie in `[Q/2, Q]` (`mem_block_bounds`), and `1/φ(q) ≤ 2 C Q^{ε-1}` there
(`inv_totient_le`).
-/

@[expose] public noncomputable section

open Finset Real

set_option autoImplicit false

namespace PrimeCarleson.Proof.Goal0

/-- Exponent bookkeeping of the proof of `p:goal0`: with `η = Q^{-3ε}/(2C²)`, `σ = 2C⁴Q^{4ε-1}` and
`X = Q^{-1-ε} b`, `b ≤ A Q^κ`, one has `X + σ √(3/η³) ≤ (A + 48 C^{10}) Q^{κ-1-ε}`. -/
theorem exponent_bound {κ ε A C Q b : ℝ} (hε : 0 < ε) (hεκ : 14 * ε ≤ κ) (hC : 1 ≤ C)
    (hQ : 1 ≤ Q) (hb : b ≤ A * Q ^ κ) :
    Q ^ (-1 - ε) * b + 2 * C ^ 4 * Q ^ (4 * ε - 1) *
        √(3 / (Q ^ (-3 * ε) / (2 * C ^ 2)) ^ 3) ≤
      (A + 48 * C ^ 10) * Q ^ (κ - 1 - ε) := by
  have hQ0 : 0 < Q := by linarith
  have hC0 : 0 < C := by linarith
  set η := Q ^ (-3 * ε) / (2 * C ^ 2) with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 := by
    rw [hη, div_le_one (by positivity)]
    calc Q ^ (-3 * ε) ≤ 1 := rpow_le_one_of_one_le_of_nonpos hQ (by linarith)
      _ ≤ 2 * C ^ 2 := by nlinarith
  -- `√(3/η³) ≤ 3/η³`
  have hy : 1 ≤ 3 / η ^ 3 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [pow_le_one₀ hη0.le hη1 (n := 3)]
  have hsqrt : √(3 / η ^ 3) ≤ 3 / η ^ 3 := by
    calc √(3 / η ^ 3) ≤ √(3 / η ^ 3) * √(3 / η ^ 3) :=
          le_mul_of_one_le_right (sqrt_nonneg _) (one_le_sqrt.2 hy)
      _ = 3 / η ^ 3 := mul_self_sqrt (by positivity)
  have hη3 : 3 / η ^ 3 = 24 * C ^ 6 * Q ^ (9 * ε) := by
    rw [hη, div_pow, ← rpow_natCast (Q ^ (-3 * ε)), ← rpow_mul hQ0.le]
    have : (-3 * ε) * ((3 : ℕ) : ℝ) = -(9 * ε) := by push_cast; ring
    rw [this, rpow_neg hQ0.le]
    field_simp
    ring
  -- the atom part
  have hatom : 2 * C ^ 4 * Q ^ (4 * ε - 1) * √(3 / η ^ 3) ≤
      48 * C ^ 10 * Q ^ (κ - 1 - ε) := by
    calc 2 * C ^ 4 * Q ^ (4 * ε - 1) * √(3 / η ^ 3)
        ≤ 2 * C ^ 4 * Q ^ (4 * ε - 1) * (24 * C ^ 6 * Q ^ (9 * ε)) := by
          rw [← hη3]; gcongr
      _ = 48 * C ^ 10 * Q ^ (13 * ε - 1) := by
          rw [show (13 * ε - 1) = (4 * ε - 1) + 9 * ε by ring, rpow_add hQ0]; ring
      _ ≤ 48 * C ^ 10 * Q ^ (κ - 1 - ε) :=
          mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le hQ (by linarith)) (by positivity)
  -- the remainder part
  have hX : Q ^ (-1 - ε) * b ≤ A * Q ^ (κ - 1 - ε) := by
    calc Q ^ (-1 - ε) * b ≤ Q ^ (-1 - ε) * (A * Q ^ κ) := by gcongr
      _ = A * Q ^ (κ - 1 - ε) := by
          rw [show κ - 1 - ε = κ + (-1 - ε) by ring, rpow_add hQ0]; ring
  linarith

/-- Members of a dyadic block lie in `[Q/2, Q]`. -/
theorem mem_block_bounds {j q : ℕ} (hq : q ∈ (Finset.Ioc (2 ^ j / 2) (2 ^ j)).filter Squarefree) :
    0 < q ∧ Squarefree q ∧ (2 : ℝ) ^ j / 2 ≤ q ∧ (q : ℝ) ≤ 2 ^ j := by
  rw [Finset.mem_filter, Finset.mem_Ioc] at hq
  obtain ⟨⟨hlo, hhi⟩, hsq⟩ := hq
  have h2 : 2 ^ j < q * 2 := (Nat.div_lt_iff_lt_mul (by norm_num)).1 hlo
  refine ⟨by omega, hsq, ?_, by exact_mod_cast hhi⟩
  have : ((2 ^ j : ℕ) : ℝ) ≤ (q : ℝ) * 2 := by exact_mod_cast h2.le
  push_cast at this
  linarith

/-- `1/φ(q) ≤ 2 C Q^{ε-1}` for `q ∈ [Q/2, Q]`, from `q ≤ τ(q) φ(q)` and `τ(q) ≤ C q^ε`. -/
theorem inv_totient_le {C ε Q : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ n : ℕ, 0 < n →
    (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε) {q : ℕ} (hq : 0 < q) (hQq : Q / 2 ≤ q)
    (hQ : 1 ≤ Q) : ((q.totient : ℝ))⁻¹ ≤ 2 * C * Q ^ (ε - 1) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq
  have h1 : (q : ℝ) ≤ q.divisors.card * q.totient := by
    exact_mod_cast le_card_divisors_mul_totient q
  have hQ0 : 0 < Q := by linarith
  calc ((q.totient : ℝ))⁻¹ ≤ q.divisors.card / q := by
        rw [inv_eq_one_div, div_le_div_iff₀ hφ hq', one_mul]; exact h1
    _ ≤ C * (q : ℝ) ^ ε / q := by gcongr; exact hC q hq
    _ = C * (q : ℝ) ^ (ε - 1) := by rw [rpow_sub_one hq'.ne']; ring
    _ ≤ C * (Q / 2) ^ (ε - 1) := by
        have hC0 : 0 ≤ C := by
          have := hC 1 one_pos; simp at this; linarith
        exact mul_le_mul_of_nonneg_left
          (rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < Q / 2) hQq
            (by linarith : ε - 1 ≤ 0)) hC0
    _ = C * (Q ^ (ε - 1) * 2 ^ (1 - ε)) := by
        rw [div_rpow hQ0.le (by norm_num), div_eq_mul_inv, ← rpow_neg (by norm_num)]; ring_nf
    _ ≤ C * (Q ^ (ε - 1) * 2) := by
        have hC0 : 0 ≤ C := by
          have := hC 1 one_pos; simp at this; linarith
        gcongr
        calc (2 : ℝ) ^ (1 - ε) ≤ 2 ^ (1 : ℝ) :=
              rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 2 := rpow_one 2
    _ = 2 * C * Q ^ (ε - 1) := by ring

end PrimeCarleson.Proof.Goal0
