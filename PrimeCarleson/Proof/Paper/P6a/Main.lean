module

public import PrimeCarleson.Proof.Paper.P6a.Triangle
public import PrimeCarleson.Proof.Paper.P6a.Residual
public import PrimeCarleson.Proof.Paper.P6a.HighQ
public import PrimeCarleson.Proof.Paper.P6a.Leftover
public import PrimeCarleson.Proof.Paper.P6a.KQReplace
public import PrimeCarleson.Proof.Paper.P6a.Series

/-!
# The sum over dyadic `Q` in the proof of `p:red-var`

Source: main paper `p:red-var`, L1227–L1242 (statement) and L1517–L1518 (end of the proof).

* `dyadic_Q_sum` (L1517-L1518): the hypothesis `e:red-var` (with one exponent `c_{p,r}` for all
  `Q`) makes `∑_Q ‖V^{Q,r} f‖_{ℓ^p} ≲ ‖f‖_{ℓ^p}` converge.

The combination of the pieces (`triangle_split`, `main_term_split`, `low_Q_reindex`,
`KQ_replacement`) and Proposition `p:red-var` itself are in `Main/RedVar.lean`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- **The sum over dyadic `Q`** (Source: main paper `p:red-var`, L1517–L1518): if
`‖V^{Q,r} f‖_{ℓ^p} ≤ C Q^{-c} ‖f‖_{ℓ^p}` for all dyadic `Q = 2^j` with one exponent `c > 0`
(`e:red-var`), then `∑_Q ‖V^{Q,r} f‖_{ℓ^p} ≤ C (1 - 2^{-c})^{-1} ‖f‖_{ℓ^p}` (with `C` replaced by
`max C 0`). -/
theorem dyadic_Q_sum (S : KQSetup) {r p c C : ℝ} (hc : 0 < c)
    (h : ∀ (j : ℕ) (f : ℤ →₀ ℂ), eLpNorm (S.VQr r (2 ^ j) (⇑f)) (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ (-c)) * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count)
    (f : ℤ →₀ ℂ) :
    ∑' j : ℕ, eLpNorm (S.VQr r (2 ^ j) (⇑f)) (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal (max C 0 * (1 - (2 : ℝ) ^ (-c))⁻¹) *
        eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  have h1 : ∀ j : ℕ, eLpNorm (S.VQr r (2 ^ j) (⇑f)) (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal (max C 0 * ((2 : ℝ) ^ j) ^ (-c)) *
        eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := fun j =>
    (h j f).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))) le_rfl)
  refine (ENNReal.tsum_le_tsum h1).trans ?_
  rw [ENNReal.tsum_mul_right]
  exact mul_le_mul' (tsum_ofReal_dyadic_le _ _ (le_max_right _ _) hc) le_rfl

end PrimeCarleson.Proof.Paper
