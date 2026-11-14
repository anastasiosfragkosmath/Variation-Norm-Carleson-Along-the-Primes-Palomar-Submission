/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Dynamics/CandidateFrontSourceLossBudget.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic
@[expose] public section

namespace OAI

section

namespace Erdos3

theorem le_power_budget {p : ℝ} (hp : 0 ≤ p) {a : ℕ} (ha : 1 ≤ a) :
    p ≤ (p + 2) ^ a := by
  have hbase : (1 : ℝ) ≤ p + 2 := by linarith
  calc
    p ≤ p + 2 := by linarith
    _ ≤ (p + 2) ^ a := by simpa only [pow_one] using pow_le_pow_right₀ hbase ha

theorem shifted_power_budget_le {p : ℝ} (hp : 0 ≤ p) (a b : ℕ) :
    ((p + 2) ^ a + 2) ^ b ≤ (p + 2) ^ ((a + 2) * b) := by
  have hbase : (1 : ℝ) ≤ p + 2 := by linarith
  have hpow : (1 : ℝ) ≤ (p + 2) ^ a := one_le_pow₀ hbase
  have hsq : (4 : ℝ) ≤ (p + 2) ^ 2 := by nlinarith
  have hstep : (p + 2) ^ a + 2 ≤ (p + 2) ^ (a + 2) := by
    rw [pow_add]
    nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ (p + 2) ^ a)]
  calc
    _ ≤ ((p + 2) ^ (a + 2)) ^ b := pow_le_pow_left₀ (by positivity) hstep b
    _ = _ := (pow_mul _ _ _).symm

theorem polynomial_budget_comp {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (a b : ℕ) (hpq : q ≤ (p + 2) ^ a) (hqr : r ≤ (q + 2) ^ b) :
    r ≤ (p + 2) ^ ((a + 2) * b) := by
  calc
    r ≤ (q + 2) ^ b := hqr
    _ ≤ ((p + 2) ^ a + 2) ^ b := by gcongr
    _ ≤ _ := shifted_power_budget_le hp a b

def budgetDepthExponent (a : ℕ) : ℕ → ℕ
  | 0 => 1
  | d + 1 => (budgetDepthExponent a d + 2) * a

theorem bounded_depth_budget {p : ℝ} (hp : 0 ≤ p) (a : ℕ) (q : ℕ → ℝ)
    (hq : ∀ d, 0 ≤ q d) (hzero : q 0 ≤ p)
    (hstep : ∀ d, q (d + 1) ≤ (q d + 2) ^ a) (d : ℕ) :
    q d ≤ (p + 2) ^ budgetDepthExponent a d := by
  induction d with
  | zero => simpa only [budgetDepthExponent, pow_one] using hzero.trans (by linarith : p ≤ p + 2)
  | succ d ih => exact polynomial_budget_comp hp (hq d) _ a ih (hstep d)

theorem exponential_budget_comp {p q h : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (a b : ℕ) (hpq : q ≤ (p + 2) ^ a) (hh : h ≤ Real.exp ((q + 2) ^ b)) :
    h ≤ Real.exp ((p + 2) ^ ((a + 2) * b)) := by
  exact hh.trans (Real.exp_le_exp.mpr (polynomial_budget_comp hp hq a b hpq le_rfl))

theorem product_exponential_budget {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {p : ℝ} (hp : 0 ≤ p) (a c : ℕ)
    (hf0 : ∀ i ∈ s, 0 ≤ f i) (hf : ∀ i ∈ s, f i ≤ Real.exp ((p + 2) ^ a))
    (hcard : (s.card : ℝ) ≤ (p + 2) ^ c) :
    (∏ i ∈ s, f i) ≤ Real.exp ((p + 2) ^ (a + c)) := by
  calc
    _ ≤ ∏ _i ∈ s, Real.exp ((p + 2) ^ a) := Finset.prod_le_prod₀ hf0 hf
    _ = Real.exp ((s.card : ℝ) * (p + 2) ^ a) := by
      rw [Finset.prod_const, ← Real.exp_nat_mul]
    _ ≤ Real.exp ((p + 2) ^ (a + c)) := by
      apply Real.exp_le_exp.mpr
      rw [pow_add]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hcard
        (by positivity : 0 ≤ (p + 2) ^ a)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

noncomputable def iteratedPowerBudget (a : ℕ) (p : ℝ) : ℕ → ℝ
  | 0 => p
  | n + 1 => (iteratedPowerBudget a p n + 2) ^ a

@[simp] theorem iteratedPowerBudget_zero (a : ℕ) (p : ℝ) : iteratedPowerBudget a p 0 = p := rfl

@[simp] theorem iteratedPowerBudget_succ (a : ℕ) (p : ℝ) (n : ℕ) :
    iteratedPowerBudget a p (n + 1) = (iteratedPowerBudget a p n + 2) ^ a := rfl

theorem iteratedPowerBudget_nonneg (a : ℕ) {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    0 ≤ iteratedPowerBudget a p n := by
  induction n with
  | zero => exact hp
  | succ n ih => exact pow_nonneg (by linarith) _

theorem iteratedPowerBudget_monotone {a : ℕ} (ha : 1 ≤ a) {p : ℝ} (hp : 0 ≤ p) :
    Monotone (iteratedPowerBudget a p) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_power_budget (iteratedPowerBudget_nonneg a hp n) ha

theorem iteratedPowerBudget_ge {a : ℕ} (ha : 1 ≤ a) {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    p ≤ iteratedPowerBudget a p n :=
  iteratedPowerBudget_monotone ha hp (Nat.zero_le n)

theorem iteratedPowerBudget_le_power (a : ℕ) {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    iteratedPowerBudget a p n ≤ (p + 2) ^ budgetDepthExponent a n :=
  bounded_depth_budget hp a (iteratedPowerBudget a p)
    (iteratedPowerBudget_nonneg a hp) le_rfl (fun _ => le_rfl) n

end Erdos3

end

section

namespace Erdos3

theorem powerCover_index_allowance_le_exp (l m d : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hl : (l : ℝ) ≤ Real.exp p) (hm : (m : ℝ) ≤ Real.exp p) (hd : (d : ℝ) ≤ p) :
    (((l * m) ^ d : ℕ) : ℝ) ≤ Real.exp (2 * p ^ 2) := by
  have hprod : (l : ℝ) * m ≤ Real.exp (2 * p) := by
    calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hl hm (by positivity) (by positivity)
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
  rw [Nat.cast_pow, Nat.cast_mul]
  calc
    _ ≤ (Real.exp (2 * p)) ^ d := pow_le_pow_left₀ (by positivity) hprod d
    _ = Real.exp ((d : ℝ) * (2 * p)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (2 * p ^ 2) := Real.exp_le_exp.mpr (by nlinarith)

theorem powerCover_grid_allowance_le_exp (l m : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hl : (l : ℝ) ≤ Real.exp p) (hm : (m : ℝ) ≤ Real.exp p) :
    (((l * m) * l : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
  push_cast
  calc
    _ ≤ Real.exp p * Real.exp p * Real.exp p :=
      mul_le_mul (mul_le_mul hl hm (by positivity) (by positivity)) hl
        (by positivity) (by positivity)
    _ = Real.exp (3 * p) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

end OAI
