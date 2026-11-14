module

public import PrimeCarleson.Proof.Paper.Defs.Modulated
public import PrimeCarleson.Proof.Paper.Defs.Basic
public import PrimeCarleson.Proof.Common.TotientBound
public import PrimeCarleson.Frozen.PrimeVariation
public import PrimeCarleson.Frozen.CarlesonMax
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# The totient bound

Paper step proved here, with the paper's label:

* `e:totientbound` (L589-L593): `φ(q) ≳ q / log log (10 + q)`: `totientbound`
  (and the reciprocal form `inv_totient_le_loglog`, the shape in which the consumers use it).
-/

@[expose] public noncomputable section

open scoped ENNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0

/-! ### `e:totientbound` -/

/-- **`e:totientbound`**: `φ(q) ≳ q / log log (10 + q)` with an absolute constant, in the form
`q / log log (10 + q) ≤ C φ(q)` for all `q ≥ 1`. -/
theorem totientbound :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) / Real.log (Real.log (10 + (q : ℝ))) ≤ C * (Nat.totient q : ℝ) := by
  refine ⟨Real.exp 8, Real.exp_pos _, fun q hq => ?_⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have h := Common.totient_lower_bound hq
  have hy : 1 < Real.log (10 + (q : ℝ)) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  have hL : 0 < Real.log (Real.log (10 + (q : ℝ))) := Real.log_pos hy
  rw [div_le_iff₀ hL] at h ⊢
  have h8 : Real.exp 8 * Real.exp (-8) = 1 := by rw [← Real.exp_add]; simp
  calc (q : ℝ) = Real.exp 8 * (Real.exp (-8) * q) := by rw [← mul_assoc, h8, one_mul]
    _ ≤ Real.exp 8 * ((Nat.totient q : ℝ) * Real.log (Real.log (10 + (q : ℝ)))) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = Real.exp 8 * (Nat.totient q : ℝ) * Real.log (Real.log (10 + (q : ℝ))) := by ring

/-- **`e:totientbound`, reciprocal form** (the shape of the consumers, where the weights `1/φ(q)`
are bounded by `q⁻¹ log log (10 + q)`): `1 / φ(q) ≤ C log log (10 + q) / q` for all `q ≥ 1`. -/
theorem inv_totient_le_loglog :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 1 ≤ q →
      1 / (Nat.totient q : ℝ) ≤ C * Real.log (Real.log (10 + (q : ℝ))) / (q : ℝ) := by
  obtain ⟨C, hC, h⟩ := totientbound
  refine ⟨C, hC, fun q hq => ?_⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 hq
  have hy : 1 < Real.log (10 + (q : ℝ)) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  have hL : 0 < Real.log (Real.log (10 + (q : ℝ))) := Real.log_pos hy
  have h1 := h q hq
  rw [div_le_iff₀ hL] at h1
  rw [div_le_div_iff₀ hφ hq0]
  nlinarith

end PrimeCarleson.Proof.Paper
