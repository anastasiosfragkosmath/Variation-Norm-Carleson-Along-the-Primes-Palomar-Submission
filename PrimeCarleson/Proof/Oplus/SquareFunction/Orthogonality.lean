module

public import PrimeCarleson.Proof.Oplus.SquareFunction.Convergence

/-!
# Orthogonality of the martingale differences and almost orthogonality in the scale parameter

The martingale-difference expansion and the almost orthogonality in the proof of the
square-function estimate of Jones–Kaufman–Rosenblatt–Wierdl (proved here).

* `tsum_sqn_dyadicDiff_le` (Bessel): `∑_j ‖D_j f‖₂² ≤ ‖f‖₂²` with `D_j f = E_{j-1} f - E_j f`;
* `tsum_sq_le_of_convolution_bound` (Young's inequality `ℓ¹ * ℓ² ⊆ ℓ²` on `ℤ`):
  `S_k ≤ ∑_j ρ(k - j) a_j` for all `k` implies `∑_k S_k² ≤ (∑ ρ)² ∑_j a_j²`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

open PrimeCarleson.Proof.Lepingle

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-! ### Almost orthogonality: Young's inequality on `ℤ` -/

/-- **Young's inequality `ℓ¹ * ℓ² ⊆ ℓ²` on `ℤ`**, in `ℝ≥0∞`. -/
theorem tsum_sq_le_of_convolution_bound {ρ a S : ℤ → ℝ≥0∞}
    (hS : ∀ k, S k ≤ ∑' j, ρ (k - j) * a j) :
    ∑' k, S k ^ 2 ≤ (∑' m, ρ m) ^ 2 * ∑' j, a j ^ 2 := by
  have hCS : ∀ k, (∑' j, ρ (k - j) * a j) ^ 2 ≤
      (∑' j, ρ (k - j)) * ∑' j, ρ (k - j) * a j ^ 2 := by
    intro k
    have := lintegral_mul_sq_le (ν := (Measure.count : Measure ℤ)) (k := fun j => ρ (k - j))
      (G := a) (measurable_of_countable _) (measurable_of_countable _)
    simpa only [lintegral_count] using this
  have hshift : ∀ k, ∑' j, ρ (k - j) = ∑' m, ρ m := fun k =>
    (Equiv.subLeft k).tsum_eq ρ
  have hshift' : ∀ j, ∑' k, ρ (k - j) = ∑' m, ρ m := fun j =>
    (Equiv.subRight j).tsum_eq ρ
  calc ∑' k, S k ^ 2 ≤ ∑' k, (∑' j, ρ (k - j) * a j) ^ 2 :=
        ENNReal.tsum_le_tsum fun k => pow_le_pow_left' (hS k) 2
    _ ≤ ∑' k, (∑' m, ρ m) * ∑' j, ρ (k - j) * a j ^ 2 :=
        ENNReal.tsum_le_tsum fun k => by rw [← hshift k]; exact hCS k
    _ = (∑' m, ρ m) * ∑' k, ∑' j, ρ (k - j) * a j ^ 2 := ENNReal.tsum_mul_left
    _ = (∑' m, ρ m) * ∑' j, ∑' k, ρ (k - j) * a j ^ 2 := by rw [ENNReal.tsum_comm]
    _ = (∑' m, ρ m) * ∑' j, (∑' m, ρ m) * a j ^ 2 := by
        congr 1
        refine tsum_congr fun j => ?_
        rw [ENNReal.tsum_mul_right, hshift' j]
    _ = (∑' m, ρ m) ^ 2 * ∑' j, a j ^ 2 := by
        rw [ENNReal.tsum_mul_left, ← mul_assoc, sq]

/-! ### Bessel's inequality for the martingale differences -/

/-- Telescoping upwards: `u(c) = u(c + b) + ∑_{i < b} A(c + i + 1)`. -/
theorem telescope_up {u A : ℤ → ℝ≥0∞} (h : ∀ j, u (j - 1) = u j + A j) (c : ℤ) (b : ℕ) :
    (∑ i ∈ Finset.range b, A (c + i + 1)) + u (c + b) = u c := by
  induction b with
  | zero => simp
  | succ b ih =>
    have e : c + ((b + 1 : ℕ) : ℤ) = c + b + 1 := by push_cast; ring
    rw [Finset.sum_range_succ, e]
    have := h (c + b + 1)
    simp only [add_sub_cancel_right] at this
    calc (∑ i ∈ Finset.range b, A (c + i + 1)) + A (c + b + 1) + u (c + b + 1)
        = (∑ i ∈ Finset.range b, A (c + i + 1)) + (A (c + b + 1) + u (c + b + 1)) := by
          rw [add_assoc]
      _ = (∑ i ∈ Finset.range b, A (c + i + 1)) + u (c + b) := by
          rw [this, add_comm (u (c + b + 1))]
      _ = u c := ih

/-- Telescoping downwards: `u(c - b) = u(c) + ∑_{i < b} A(c - i)`. -/
theorem telescope_down {u A : ℤ → ℝ≥0∞} (h : ∀ j, u (j - 1) = u j + A j) (c : ℤ) (b : ℕ) :
    u c + (∑ i ∈ Finset.range b, A (c - i)) = u (c - b) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ]
    have := h (c - b)
    push_cast
    calc u c + ((∑ i ∈ Finset.range b, A (c - i)) + A (c - b))
        = (u c + ∑ i ∈ Finset.range b, A (c - i)) + A (c - b) := by rw [add_assoc]
      _ = u (c - b) + A (c - b) := by rw [ih]
      _ = u (c - (b + 1)) := by rw [← sub_sub, this, add_comm]

/-- The Pythagorean relation between consecutive averages:
`‖E_{j-1} f‖² = ‖E_j f‖² + ‖D_j f‖²`. -/
theorem sqn_dyadicAvg_pred_eq {f : ℝ → ℂ} (hf : MemLp f 2 volume) (j : ℤ) :
    ∫⁻ x, ‖dyadicAvg f (j - 1) x‖ₑ ^ 2 =
      (∫⁻ x, ‖dyadicAvg f j x‖ₑ ^ 2) + ∫⁻ x, ‖dyadicDiff f j x‖ₑ ^ 2 := by
  have hL : MemLp (dyadicAvg f (j - 1)) 2 volume := by
    refine memLp_two_of_lintegral_sq_lt_top (measurable_dyadicAvg f _).aestronglyMeasurable ?_
    exact lt_of_le_of_lt (sqn_dyadicAvg_le hf _) (lintegral_sq_lt_top_of_memLp hf)
  have h := sqn_eq_add_dyadicAvg hL j
  have e1 : ∀ x, dyadicAvg (dyadicAvg f (j - 1)) j x = dyadicAvg f j x := fun x =>
    dyadicAvg_dyadicAvg_of_ge (by omega) hf x
  simp_rw [e1] at h
  exact h

/-- **Bessel's inequality** for the martingale differences:
`∑_j ‖D_j f‖₂² ≤ ‖f‖₂²`. -/
theorem tsum_sqn_dyadicDiff_le {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    ∑' j : ℤ, ∫⁻ x, ‖dyadicDiff f j x‖ₑ ^ 2 ≤ ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  set u : ℤ → ℝ≥0∞ := fun j => ∫⁻ x, ‖dyadicAvg f j x‖ₑ ^ 2 with hu
  set A : ℤ → ℝ≥0∞ := fun j => ∫⁻ x, ‖dyadicDiff f j x‖ₑ ^ 2 with hA
  have h : ∀ j, u (j - 1) = u j + A j := fun j => sqn_dyadicAvg_pred_eq hf j
  rw [tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
  rw [Finset.sum_add_distrib]
  have h1 := telescope_up h (-1) N
  have h2 := telescope_down h (-1) N
  have e1 : ∀ i : ℕ, A (-1 + (i : ℤ) + 1) = A i := fun i => by
    congr 1; ring
  have e2 : ∀ i : ℕ, A (-1 - (i : ℤ)) = A (-((i : ℤ) + 1)) := fun i => by
    congr 1; ring
  simp_rw [e1] at h1
  simp_rw [e2] at h2
  calc (∑ i ∈ Finset.range N, A i) + ∑ i ∈ Finset.range N, A (-((i : ℤ) + 1))
      ≤ ((∑ i ∈ Finset.range N, A i) + u (-1 + N)) + ∑ i ∈ Finset.range N, A (-((i : ℤ) + 1)) :=
        add_le_add le_self_add le_rfl
    _ = u (-1) + ∑ i ∈ Finset.range N, A (-((i : ℤ) + 1)) := by rw [h1]
    _ = u (-1 - N) := h2
    _ ≤ ∫⁻ x, ‖f x‖ₑ ^ 2 := sqn_dyadicAvg_le hf _

end PrimeCarleson.Proof.Oplus
