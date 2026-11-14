module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

/-!
# The numerical inequalities of the extrapolation step

Part of the abstract extrapolation (the extrapolation step of the iteration of `C2/CMain.lean`,
proof of [F+] Proposition 3.1). Elementary inequalities among the exponents that appear in the proof
of `symbol_dilation_extrapolation`, with `B = p + λ`, `1 ≤ p`, `0 ≤ λ` (`λ = log (1/c)`), `cv ≥ 1`
the constant of the Vinogradov lemma and `w = cv (1 + λ + 5 p³)` (so that `C δ^{-C} ≤ e^w` for
`δ = e^{-(λ + 5 p³)}`).
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

section Arith

variable {p lam cv B : ℝ}

theorem arith_facts (hp : 1 ≤ p) (hl : 0 ≤ lam) (hB : B = p + lam) :
    1 ≤ B ∧ p ≤ B ∧ lam ≤ B ∧ B ≤ B ^ 3 ∧ B ^ 3 ≤ B ^ 4 ∧ p ^ 3 ≤ B ^ 3 ∧
      1 + lam + 5 * p ^ 3 ≤ 7 * B ^ 3 ∧ p + 1 ≤ 2 * B := by
  have h1 : 1 ≤ B := by linarith
  have h2 : p ≤ B := by linarith
  have h3 : lam ≤ B := by linarith
  have h4 : B ≤ B ^ 3 := by
    calc B = B ^ 1 := (pow_one B).symm
      _ ≤ B ^ 3 := pow_le_pow_right₀ h1 (by norm_num)
  have h5 : B ^ 3 ≤ B ^ 4 := pow_le_pow_right₀ h1 (by norm_num)
  have h6 : p ^ 3 ≤ B ^ 3 := pow_le_pow_left₀ (by linarith) h2 3
  have h7 : 1 ≤ B ^ 3 := h1.trans h4
  exact ⟨h1, h2, h3, h4, h5, h6, by linarith, by linarith⟩

/-- `(p + 1) w + 3 p + 2 p³ ≤ (14 cv + 5) B⁴`. -/
theorem arith_E1 (hcv : 1 ≤ cv) (hp : 1 ≤ p) (hl : 0 ≤ lam) (hB : B = p + lam) :
    (p + 1) * (cv * (1 + lam + 5 * p ^ 3)) + 3 * p + 2 * p ^ 3 ≤ (14 * cv + 5) * B ^ 4 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := arith_facts hp hl hB
  have h9 : (p + 1) * (cv * (1 + lam + 5 * p ^ 3)) ≤ (2 * B) * (cv * (7 * B ^ 3)) := by
    gcongr
  have h10 : (2 * B) * (cv * (7 * B ^ 3)) = 14 * cv * B ^ 4 := by ring
  have h11 : 3 * p + 2 * p ^ 3 ≤ 5 * B ^ 4 := by linarith
  nlinarith

/-- `2 p w + 5 p + 4 p³ ≤ (14 cv + 9) B⁴`. -/
theorem arith_E2 (hcv : 1 ≤ cv) (hp : 1 ≤ p) (hl : 0 ≤ lam) (hB : B = p + lam) :
    2 * p * (cv * (1 + lam + 5 * p ^ 3)) + 5 * p + 4 * p ^ 3 ≤ (14 * cv + 9) * B ^ 4 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := arith_facts hp hl hB
  have h9 : 2 * p * (cv * (1 + lam + 5 * p ^ 3)) ≤ (2 * B) * (cv * (7 * B ^ 3)) := by
    gcongr
  have h10 : (2 * B) * (cv * (7 * B ^ 3)) = 14 * cv * B ^ 4 := by ring
  have h11 : 5 * p + 4 * p ^ 3 ≤ 9 * B ^ 4 := by linarith
  nlinarith

/-- `cv + 3 p + 2 p³ + cv (λ + 5 p³) ≤ (7 cv + 5) B³`. -/
theorem arith_E3 (hcv : 1 ≤ cv) (hp : 1 ≤ p) (hl : 0 ≤ lam) (hB : B = p + lam) :
    cv + 3 * p + 2 * p ^ 3 + cv * (lam + 5 * p ^ 3) ≤ (7 * cv + 5) * B ^ 3 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := arith_facts hp hl hB
  have h9 : cv * (lam + 5 * p ^ 3) ≤ cv * (6 * B ^ 3) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    linarith
  have h10 : cv ≤ cv * B ^ 3 := by nlinarith
  have h11 : 3 * p + 2 * p ^ 3 ≤ 5 * B ^ 3 := by linarith
  nlinarith

/-- `3 p + 2 w ≤ (14 cv + 3) B⁴`. -/
theorem arith_E4 (hcv : 1 ≤ cv) (hp : 1 ≤ p) (hl : 0 ≤ lam) (hB : B = p + lam) :
    3 * p + 2 * (cv * (1 + lam + 5 * p ^ 3)) ≤ (14 * cv + 3) * B ^ 4 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := arith_facts hp hl hB
  have h9 : cv * (1 + lam + 5 * p ^ 3) ≤ cv * (7 * B ^ 3) :=
    mul_le_mul_of_nonneg_left h7 (by linarith)
  have h10 : cv * B ^ 3 ≤ cv * B ^ 4 := mul_le_mul_of_nonneg_left h5 (by linarith)
  have h11 : 3 * p ≤ 3 * B ^ 4 := by linarith
  nlinarith

end Arith

end PrimeCarleson.Proof.Fplus31
