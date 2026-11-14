module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The iteration, the parameters of the Vaughan decomposition at the level `p`

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). For a
state at the level `p` with `log (1 + log N) ≤ p`, the parameter `η = 3 log N e^{-p}` of the Vaughan
decomposition and the quantities `δ = η / (2^13 (1 + log N)^3)` of the type I output,
`x = min (η^4 / (2^20 (1 + log N)^18)) 1` of the type II output and `η / (16 (1 + log N)^5)` are all
at least `e^{-(30 p + 50)}` (up to the numerical factors recorded below), which is the polynomial
budget of the stage.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- `2^n ≤ e^n`. -/
theorem two_pow_le_exp (n : ℕ) : (2 : ℝ) ^ n ≤ Real.exp n := by
  have h : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc (2 : ℝ) ^ n ≤ (Real.exp 1) ^ n := pow_le_pow_left₀ (by norm_num) h n
    _ = Real.exp n := by rw [← Real.exp_nat_mul]; simp

/-- **The parameters of the Vaughan decomposition are polynomially bounded below.** For
`U = log N ≥ 12` and `log (1 + U) ≤ p`: `δ ≤ 1`, `3 e^{-(30 p + 50)} ≤ δ`, `16 e^{-(30 p + 50)} ≤ x`
and `e^{-(30 p + 50)} ≤ η / (16 (1 + U)^5)`. -/
theorem param_bounds {U p η δ : ℝ} (hU : 12 ≤ U) (hp : 0 ≤ p) (hlam : Real.log (1 + U) ≤ p)
    (hη : η = 3 * U * Real.exp (-p)) (hδ : δ = η / (2 ^ 13 * (1 + U) ^ 3)) :
    δ ≤ 1 ∧ 3 * Real.exp (-(30 * p + 50)) ≤ δ ∧
      16 * Real.exp (-(30 * p + 50)) ≤ min (η ^ 4 / (2 ^ 20 * (1 + U) ^ 18)) 1 ∧
      Real.exp (-(30 * p + 50)) ≤ η / (16 * (1 + U) ^ 5) := by
  have hlam1 : 1 ≤ 1 + U := by linarith
  have hlamp : 0 < 1 + U := by linarith
  set a := Real.exp (-p) with ha
  have ha0 : 0 < a := Real.exp_pos _
  have ha1 : a ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have halam : a * (1 + U) ≤ 1 := by
    have h1 : 1 + U ≤ Real.exp p := by
      have := Real.exp_le_exp.mpr hlam
      rwa [Real.exp_log hlamp] at this
    have h2 : a * Real.exp p = 1 := by rw [ha, ← Real.exp_add]; simp
    calc a * (1 + U) ≤ a * Real.exp p := mul_le_mul_of_nonneg_left h1 ha0.le
      _ = 1 := h2
  have hQ : Real.exp (-(30 * p + 50)) ≤ a ^ 30 / 2 ^ 50 := by
    have e1 : Real.exp (-(30 * p + 50)) = a ^ 30 * (Real.exp 50)⁻¹ := by
      rw [neg_add, Real.exp_add, ha]
      have : Real.exp (-(30 * p)) = Real.exp (-p) ^ 30 := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      rw [this, Real.exp_neg 50]
    rw [e1]
    have h50 : (2 : ℝ) ^ 50 ≤ Real.exp 50 := by
      have := two_pow_le_exp 50
      simpa using this
    have : (Real.exp 50)⁻¹ ≤ ((2 : ℝ) ^ 50)⁻¹ := inv_anti₀ (by positivity) h50
    calc a ^ 30 * (Real.exp 50)⁻¹ ≤ a ^ 30 * ((2 : ℝ) ^ 50)⁻¹ :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = a ^ 30 / 2 ^ 50 := by rw [div_eq_mul_inv]
  set Q := Real.exp (-(30 * p + 50)) with hQdef
  have hQ0 : 0 < Q := Real.exp_pos _
  have hη12 : 36 * a ≤ η := by
    rw [hη]; linarith only [mul_nonneg (sub_nonneg.mpr hU) ha0.le]
  have hηpos : 0 < η := lt_of_lt_of_le (by positivity) hη12
  have hηle : η ≤ 3 * U := by
    rw [hη]
    linarith only [mul_le_mul_of_nonneg_left ha1 (by linarith only [hU] : (0 : ℝ) ≤ U)]
  have hpow : ∀ k : ℕ, a ^ k * (1 + U) ^ k ≤ 1 := fun k => by
    rw [← mul_pow]; exact pow_le_one₀ (by positivity) halam
  have hapow : ∀ k : ℕ, k ≠ 0 → a ^ k ≤ a := fun k hk => pow_le_of_le_one ha0.le ha1 hk
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hδ, div_le_one (by positivity)]
    have h1 : 3 * U ≤ 3 * (1 + U) := by linarith
    have h2 : (1 + U) ≤ (1 + U) ^ 3 := le_self_pow₀ hlam1 (by norm_num)
    have h3 : 3 * (1 + U) ≤ 2 ^ 13 * (1 + U) ^ 3 := by linarith only [h2, hlam1]
    linarith only [hηle, h1, h3]
  · rw [hδ, le_div_iff₀ (by positivity)]
    have h1 := hpow 3
    have h2 : 3 * Q * (2 ^ 13 * (1 + U) ^ 3) ≤ 3 * (a ^ 30 / 2 ^ 50) * (2 ^ 13 * (1 + U) ^ 3) := by
      gcongr
    have h3 : 3 * (a ^ 30 / 2 ^ 50) * (2 ^ 13 * (1 + U) ^ 3) =
        3 * a ^ 27 * (a ^ 3 * (1 + U) ^ 3) / 2 ^ 37 := by ring
    have h4 : a ^ 27 * (a ^ 3 * (1 + U) ^ 3) ≤ a := by
      calc a ^ 27 * (a ^ 3 * (1 + U) ^ 3) ≤ a ^ 27 * 1 :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ a := by rw [mul_one]; exact hapow 27 (by norm_num)
    have h5 : 3 * a ^ 27 * (a ^ 3 * (1 + U) ^ 3) / 2 ^ 37 ≤ 36 * a := by
      have : 3 * a ^ 27 * (a ^ 3 * (1 + U) ^ 3) = 3 * (a ^ 27 * (a ^ 3 * (1 + U) ^ 3)) := by ring
      rw [this, div_le_iff₀ (by positivity)]
      linarith only [h4, ha0]
    linarith only [h2, h3, h5, hη12]
  · refine le_min ?_ ?_
    · rw [le_div_iff₀ (by positivity)]
      have h1 : (36 * a) ^ 4 ≤ η ^ 4 := pow_le_pow_left₀ (by positivity) hη12 4
      have h2 := hpow 18
      have h3 : 16 * Q * (2 ^ 20 * (1 + U) ^ 18) ≤
          16 * (a ^ 30 / 2 ^ 50) * (2 ^ 20 * (1 + U) ^ 18) := by gcongr
      have h4 : 16 * (a ^ 30 / 2 ^ 50) * (2 ^ 20 * (1 + U) ^ 18) =
          16 * a ^ 12 * (a ^ 18 * (1 + U) ^ 18) / 2 ^ 30 := by ring
      have h5 : a ^ 12 * (a ^ 18 * (1 + U) ^ 18) ≤ a ^ 12 := by
        calc a ^ 12 * (a ^ 18 * (1 + U) ^ 18) ≤ a ^ 12 * 1 :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = a ^ 12 := mul_one _
      have h6 : 16 * a ^ 12 * (a ^ 18 * (1 + U) ^ 18) / 2 ^ 30 ≤ (36 * a) ^ 4 := by
        have : 16 * a ^ 12 * (a ^ 18 * (1 + U) ^ 18) = 16 * (a ^ 12 * (a ^ 18 * (1 + U) ^ 18)) := by
          ring
        rw [this, div_le_iff₀ (by positivity)]
        have h7 : a ^ 12 ≤ a ^ 4 := pow_le_pow_of_le_one ha0.le ha1 (by norm_num)
        linarith only [h5, h7, pow_pos ha0 4]
      linarith only [h3, h4, h6, h1]
    · have h1 : a ^ 30 ≤ 1 := pow_le_one₀ ha0.le ha1
      calc 16 * Q ≤ 16 * (a ^ 30 / 2 ^ 50) := by gcongr
        _ ≤ 16 * (1 / 2 ^ 50) := by gcongr
        _ ≤ 1 := by norm_num
  · rw [le_div_iff₀ (by positivity)]
    have h1 := hpow 5
    have h2 : Q * (16 * (1 + U) ^ 5) ≤ a ^ 30 / 2 ^ 50 * (16 * (1 + U) ^ 5) := by gcongr
    have h3 : a ^ 30 / 2 ^ 50 * (16 * (1 + U) ^ 5) =
        16 * a ^ 25 * (a ^ 5 * (1 + U) ^ 5) / 2 ^ 50 := by ring
    have h4 : a ^ 25 * (a ^ 5 * (1 + U) ^ 5) ≤ a := by
      calc a ^ 25 * (a ^ 5 * (1 + U) ^ 5) ≤ a ^ 25 * 1 :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ a := by rw [mul_one]; exact hapow 25 (by norm_num)
    have h5 : 16 * a ^ 25 * (a ^ 5 * (1 + U) ^ 5) / 2 ^ 50 ≤ 36 * a := by
      have : 16 * a ^ 25 * (a ^ 5 * (1 + U) ^ 5) = 16 * (a ^ 25 * (a ^ 5 * (1 + U) ^ 5)) := by
        ring
      rw [this, div_le_iff₀ (by positivity)]
      linarith only [h4, ha0]
    linarith only [h2, h3, h5, hη12]

end PrimeCarleson.Proof.Fplus31
