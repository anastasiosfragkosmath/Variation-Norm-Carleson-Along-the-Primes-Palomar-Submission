module

public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.SmoothNumbers
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# A finite Euler product inequality

The Euler product, a standard result, in the form needed by the two Rankin steps of [KMTT]
Lemma 4.6 (L881-L886 and L903-L911), for nonnegative multiplicative functions and finite ranges:

* `sum_Icc_le_prod_primesBelow`: for `F : ℕ → ℝ` nonnegative, `F 1 = 1`, multiplicative on
  coprime arguments and summable on each prime-power sequence,
  `∑_{d ∈ [1, M]} F d ≤ ∏_{p ≤ M} ∑_{a ≥ 0} F (p^a)`. It is the inequality part of Mathlib's
  `EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum` (sum over `(M+1)`-smooth
  numbers), without any global summability of `F`;
* `prod_one_add_le_exp_sum`: `∏ (1 + x_i) ≤ exp (∑ x_i)` for `x_i ≥ 0`.
-/

@[expose] public noncomputable section

open Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.Common

/-- Finite Euler product inequality: for a nonnegative `F` with `F 1 = 1`, multiplicative on
coprime arguments, and summable along each prime-power sequence `n ↦ F (p ^ n)`,
`∑_{d ≤ M} F d ≤ ∏_{p ≤ M} ∑_{n ≥ 0} F (p ^ n)`. -/
theorem sum_Icc_le_prod_primesBelow {F : ℕ → ℝ} (hF0 : ∀ n, 0 ≤ F n) (hF1 : F 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → F (m * n) = F m * F n)
    (hsum : ∀ {p : ℕ}, p.Prime → Summable fun n : ℕ => F (p ^ n)) (M : ℕ) :
    ∑ d ∈ Finset.Icc 1 M, F d ≤ ∏ p ∈ (M + 1).primesBelow, ∑' n : ℕ, F (p ^ n) := by
  have hs := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum hF1 hmul
    (fun {p} hp => by simpa [Real.norm_of_nonneg (hF0 _)] using hsum hp) (M + 1)).2
  classical
  have hmem : ∀ d ∈ Finset.Icc 1 M, d ∈ (M + 1).smoothNumbers := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    exact Nat.mem_smoothNumbers_of_lt (by omega) (by omega)
  rw [← Finset.sum_subtype_of_mem F (p := fun d => d ∈ (M + 1).smoothNumbers) hmem]
  exact sum_le_hasSum _ (fun i _ => hF0 _) hs

/-- `∏ (1 + x_i) ≤ exp (∑ x_i)` for nonnegative `x_i`. -/
theorem prod_one_add_le_exp_sum {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) :
    ∏ i ∈ s, (1 + x i) ≤ Real.exp (∑ i ∈ s, x i) := by
  rw [Real.exp_sum]
  refine Finset.prod_le_prod₀ (fun i hi => ?_) fun i _ => ?_
  · linarith [hx i hi]
  · linarith [Real.add_one_le_exp (x i)]

end PrimeCarleson.Proof.Common
