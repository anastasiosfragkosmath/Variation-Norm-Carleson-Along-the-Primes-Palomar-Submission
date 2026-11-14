module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Bounded weighted trigonometric sums

Helper estimates for the unboundedness half of the Appendix A.1 lemma. For `q₀ ≥ 3` the sums
`∑_{m ≤ M} sin(2π m / q₀) / m` and `∑_{m ≤ M} cos(4π m / q₀) / m` are bounded uniformly in `M`:
the partial sums of the numerators are bounded (geometric series), and the weights `1 / m`
are monotone (Abel summation, proved here by a direct induction).

Sums over `m ≥ 1` are written over `Finset.range M` with the index shifted by one.
-/

public section

namespace PrimeCarleson.Proof

/-- Abel summation: if the partial sums of `a` are bounded by `B`, then so are the partial sums
of `a m / (m + 1)`. -/
theorem abel_bound (a : ℕ → ℝ) (B : ℝ) (hB : ∀ M : ℕ, |∑ m ∈ Finset.range M, a m| ≤ B)
    (M : ℕ) : |∑ m ∈ Finset.range M, a m / ((m : ℝ) + 1)| ≤ B := by
  have hB0 : 0 ≤ B := by simpa using hB 0
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simpa using hB0
  have key : ∀ N : ℕ, 1 ≤ N →
      |∑ m ∈ Finset.range N, a m / ((m : ℝ) + 1) - (∑ m ∈ Finset.range N, a m) / N|
        ≤ B - B / N := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => simp
    | succ N hN ih =>
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      have h1 : ∑ m ∈ Finset.range (N + 1), a m / ((m : ℝ) + 1) -
          (∑ m ∈ Finset.range (N + 1), a m) / ((N + 1 : ℕ) : ℝ) =
          (∑ m ∈ Finset.range N, a m / ((m : ℝ) + 1) - (∑ m ∈ Finset.range N, a m) / N) +
            (∑ m ∈ Finset.range N, a m) * (1 / N - 1 / (N + 1)) := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        push_cast
        field_simp
        ring
      rw [h1]
      have h2 : |(∑ m ∈ Finset.range N, a m) * (1 / (N : ℝ) - 1 / (N + 1))| ≤
          B * (1 / N - 1 / (N + 1)) := by
        rw [abs_mul]
        have : 0 ≤ (1 / (N : ℝ) - 1 / (N + 1)) := by
          rw [sub_nonneg]; gcongr; linarith
        rw [abs_of_nonneg this]
        exact mul_le_mul_of_nonneg_right (hB N) this
      calc _ ≤ |∑ m ∈ Finset.range N, a m / ((m : ℝ) + 1) - (∑ m ∈ Finset.range N, a m) / N| +
            |(∑ m ∈ Finset.range N, a m) * (1 / (N : ℝ) - 1 / (N + 1))| := abs_add_le _ _
        _ ≤ (B - B / N) + B * (1 / N - 1 / (N + 1)) := add_le_add ih h2
        _ = B - B / ((N + 1 : ℕ) : ℝ) := by push_cast; field_simp; ring
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have h3 := key M hM
  calc |∑ m ∈ Finset.range M, a m / ((m : ℝ) + 1)|
      = |(∑ m ∈ Finset.range M, a m / ((m : ℝ) + 1) - (∑ m ∈ Finset.range M, a m) / M) +
          (∑ m ∈ Finset.range M, a m) / M| := by ring_nf
    _ ≤ |∑ m ∈ Finset.range M, a m / ((m : ℝ) + 1) - (∑ m ∈ Finset.range M, a m) / M| +
          |(∑ m ∈ Finset.range M, a m) / M| := abs_add_le _ _
    _ ≤ (B - B / M) + B / M := by
        refine add_le_add h3 ?_
        rw [abs_div, abs_of_pos hMpos]
        exact div_le_div_of_nonneg_right (hB M) hMpos.le
    _ = B := by ring

/-- The partial sums of `e^{i m φ}`, `m ≥ 1`, are bounded for `0 < φ < 2π`. -/
theorem sum_cis_bound (φ : ℝ) (h0 : 0 < φ) (h1 : φ < 2 * Real.pi) (M : ℕ) :
    ‖∑ m ∈ Finset.range M, Complex.exp (((m + 1 : ℕ) * φ : ℝ) * Complex.I)‖ ≤
      2 / ‖Complex.exp (φ * Complex.I) - 1‖ := by
  set z : ℂ := Complex.exp (φ * Complex.I) with hz
  have hz1 : z ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [hz, Complex.exp_ofReal_mul_I_re] at hre
    have := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos]) h1).1
      (by simpa using hre)
    exact h0.ne' this
  have hzn : ‖z‖ = 1 := by
    rw [hz, Complex.norm_exp_ofReal_mul_I]
  have hz1' : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hz1)
  have hterm : ∀ m : ℕ, Complex.exp (((m + 1 : ℕ) * φ : ℝ) * Complex.I) = z * z ^ m := by
    intro m
    rw [hz, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, geom_sum_eq hz1, norm_mul, hzn, one_mul, norm_div]
  refine div_le_div_of_nonneg_right ?_ hz1'.le
  calc ‖z ^ M - 1‖ ≤ ‖z ^ M‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hzn, one_pow, norm_one]; norm_num

/-- The partial sums of `sin (m φ)` and `cos (m φ)`, `m ≥ 1`, are bounded for `0 < φ < 2π`. -/
theorem sum_sin_cos_bound (φ : ℝ) (h0 : 0 < φ) (h1 : φ < 2 * Real.pi) (M : ℕ) :
    |∑ m ∈ Finset.range M, Real.sin (((m + 1 : ℕ) : ℝ) * φ)| ≤
        2 / ‖Complex.exp (φ * Complex.I) - 1‖ ∧
      |∑ m ∈ Finset.range M, Real.cos (((m + 1 : ℕ) : ℝ) * φ)| ≤
        2 / ‖Complex.exp (φ * Complex.I) - 1‖ := by
  have h := sum_cis_bound φ h0 h1 M
  constructor
  · calc _ = |(∑ m ∈ Finset.range M, Complex.exp (((m + 1 : ℕ) * φ : ℝ) * Complex.I)).im| := by
          rw [Complex.im_sum]
          simp_rw [Complex.exp_ofReal_mul_I_im]
      _ ≤ _ := (Complex.abs_im_le_norm _).trans h
  · calc _ = |(∑ m ∈ Finset.range M, Complex.exp (((m + 1 : ℕ) * φ : ℝ) * Complex.I)).re| := by
          rw [Complex.re_sum]
          simp_rw [Complex.exp_ofReal_mul_I_re]
      _ ≤ _ := (Complex.abs_re_le_norm _).trans h

/-- For `q₀ ≥ 3` the sums `∑_{m ≤ M} sin(2π m / q₀) / m` and `∑_{m ≤ M} cos(4π m / q₀) / m`
are bounded uniformly in `M`. -/
theorem exists_bound_sin_cos_sums (q₀ : ℕ) (hq₀ : 3 ≤ q₀) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ,
      |∑ m ∈ Finset.range M, Real.sin (2 * Real.pi * ((m : ℝ) + 1) / q₀) / ((m : ℝ) + 1)| ≤ B ∧
      |∑ m ∈ Finset.range M, Real.cos (4 * Real.pi * ((m : ℝ) + 1) / q₀) / ((m : ℝ) + 1)| ≤ B := by
  have hq : (3 : ℝ) ≤ q₀ := by exact_mod_cast hq₀
  have hq0 : (0 : ℝ) < q₀ := by linarith
  have hφ1 : 0 < 2 * Real.pi / q₀ := by positivity
  have hφ1' : 2 * Real.pi / q₀ < 2 * Real.pi := by
    rw [div_lt_iff₀ hq0]; nlinarith [Real.pi_pos]
  have hφ2 : 0 < 2 * (2 * Real.pi / q₀) := by positivity
  have hφ2' : 2 * (2 * Real.pi / q₀) < 2 * Real.pi := by
    rw [mul_div_assoc', div_lt_iff₀ hq0]; nlinarith [Real.pi_pos]
  refine ⟨max (2 / ‖Complex.exp (↑(2 * Real.pi / q₀) * Complex.I) - 1‖)
      (2 / ‖Complex.exp (↑(2 * (2 * Real.pi / q₀)) * Complex.I) - 1‖), ?_, fun M => ?_⟩
  · positivity
  · constructor
    · refine (abel_bound _ _ ?_ M).trans (le_max_left _ _)
      intro N
      have := (sum_sin_cos_bound _ hφ1 hφ1' N).1
      refine le_of_eq_of_le ?_ this
      congr 1
      refine Finset.sum_congr rfl fun m _ => ?_
      congr 1
      push_cast
      ring
    · refine (abel_bound _ _ ?_ M).trans (le_max_right _ _)
      intro N
      have := (sum_sin_cos_bound _ hφ2 hφ2' N).2
      refine le_of_eq_of_le ?_ this
      congr 1
      refine Finset.sum_congr rfl fun m _ => ?_
      congr 1
      push_cast
      ring

end PrimeCarleson.Proof
