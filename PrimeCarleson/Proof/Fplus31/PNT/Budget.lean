module

public import PrimeCarleson.Proof.Fplus31.PNT.ApSum
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Analytic budget for the assembly

Elementary real-variable estimates used by the assembly (`PNTSW/Assembly.lean`): with
`L = (log N)^{1/10}`, polynomials in `L` are eventually dominated by `exp(c L)`,
`S^m / m! ≤ exp(-m)` once `m ≥ e² S`, and the facts about the Cramér level `w ∈ [e^L / 2, e^L + 1]`.
-/

@[expose] public noncomputable section

open Filter Asymptotics

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- `C L^n ≤ exp(c L)` for all large `L` (`c > 0`). -/
theorem eventually_poly_le_exp (n : ℕ) (C c : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, C * L ^ n ≤ Real.exp (c * L) := by
  have h := (Real.isLittleO_pow_exp_atTop (n := n)).comp_tendsto
    (tendsto_id.const_mul_atTop hc)
  have hb := h.bound (show 0 < c ^ n / (|C| + 1) by positivity)
  filter_upwards [hb, eventually_ge_atTop 0] with L hL hL0
  simp only [Function.comp_apply, id, Real.norm_eq_abs] at hL
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (Real.exp_pos _).le, mul_pow] at hL
  have hcn : 0 < c ^ n := by positivity
  have h1 : L ^ n ≤ Real.exp (c * L) / (|C| + 1) := by
    have : c ^ n * L ^ n ≤ c ^ n * (Real.exp (c * L) / (|C| + 1)) := by
      refine hL.trans (le_of_eq ?_)
      ring
    exact le_of_mul_le_mul_left this hcn
  have hC1 : 0 < |C| + 1 := by positivity
  have hLn : 0 ≤ L ^ n := by positivity
  calc C * L ^ n ≤ |C| * L ^ n := mul_le_mul_of_nonneg_right (le_abs_self C) hLn
    _ ≤ |C| * (Real.exp (c * L) / (|C| + 1)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
    _ ≤ Real.exp (c * L) := by
        rw [← mul_div_assoc, div_le_iff₀ hC1]
        nlinarith [Real.exp_pos (c * L), abs_nonneg C]

/-- `S^m / m! ≤ exp(-m)` as soon as `e² S ≤ m`. -/
theorem pow_div_factorial_le_exp_neg {S : ℝ} (hS : 0 ≤ S) {m : ℕ} (hm : 1 ≤ m)
    (h : S * Real.exp 2 ≤ m) : S ^ m / (m.factorial : ℝ) ≤ Real.exp (-(m : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hfac : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have h1 : (m : ℝ) ^ m / (m.factorial : ℝ) ≤ Real.exp m := Real.pow_div_factorial_le_exp _ hm0.le m
  have h2 : S / m ≤ Real.exp (-2) := by
    rw [div_le_iff₀ hm0, Real.exp_neg, inv_mul_eq_div, le_div_iff₀ (Real.exp_pos 2)]
    exact h
  have h3 : (S / m) ^ m ≤ Real.exp (-2) ^ m := pow_le_pow_left₀ (by positivity) h2 m
  have h4 : Real.exp (-2) ^ m = Real.exp (-2 * m) := by
    rw [← Real.exp_nat_mul]; ring_nf
  have e : S ^ m / (m.factorial : ℝ) = (S / m) ^ m * ((m : ℝ) ^ m / (m.factorial : ℝ)) := by
    rw [div_pow]
    field_simp
  rw [e]
  calc (S / m) ^ m * ((m : ℝ) ^ m / (m.factorial : ℝ)) ≤ Real.exp (-2 * m) * Real.exp m :=
        mul_le_mul (h3.trans h4.le) h1 (by positivity) (Real.exp_pos _).le
    _ = Real.exp (-(m : ℝ)) := by rw [← Real.exp_add]; ring_nf

/-- Facts about the Cramér level `w ∈ [e^L / 2, e^L + 1]` for `L ≥ 4`. -/
theorem level_facts {L : ℝ} (hL : 4 ≤ L) {w : ℕ} (h1 : Real.exp L / 2 ≤ w)
    (h2 : (w : ℝ) ≤ Real.exp L + 1) :
    2 ≤ w ∧ 0 < Real.log w ∧ Real.log w ≤ L + 1 ∧ (w : ℝ) ≤ Real.exp (L + 1) := by
  have hE : L + 1 ≤ Real.exp L := Real.add_one_le_exp L
  have hw2 : (2 : ℝ) ≤ w := by linarith
  have hw2' : 2 ≤ w := by exact_mod_cast hw2
  have hwpos : (0 : ℝ) < w := by linarith
  have hexp1 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hwe : (w : ℝ) ≤ Real.exp (L + 1) := by
    rw [Real.exp_add]
    nlinarith [Real.exp_pos L]
  refine ⟨hw2', Real.log_pos (by linarith), ?_, hwe⟩
  calc Real.log w ≤ Real.log (Real.exp (L + 1)) := Real.log_le_log hwpos hwe
    _ = L + 1 := Real.log_exp _

end PrimeCarleson.Proof.Fplus31
