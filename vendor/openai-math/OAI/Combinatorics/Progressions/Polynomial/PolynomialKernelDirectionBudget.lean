/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Polynomial/PolynomialKernelDirectionBudget.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Dynamics.CurrentLayerBudget
public import OAI.Combinatorics.Progressions.Estimates.FormalHorizontalReabsorption
public import OAI.Combinatorics.Progressions.Estimates.FormalLinearLiftReabsorption
@[expose] public section

namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped Matrix TensorProduct

variable {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype κ] {E : Submodule ℚ L}

noncomputable def polynomialKernelDirection (b : Basis μ ℚ L) (Q : Matrix κ μ ℚ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (i : σ) : κ → ℝ :=
  realSubspaceCoordinateMap b Q (coefficients P (Finsupp.single i 1))

theorem polynomialKernelDirection_lift [DecidableEq κ] (b : Basis μ ℚ L) (e : Basis κ ℚ E)
    (Q : Matrix κ μ ℚ) (hQ : Q * bracketLiftMatrix b e = 1)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hP : ∀ α, coefficients P α ∈ E.baseChange ℝ)
    (i : σ) :
    bracketSystemLift e (polynomialKernelDirection b Q P i) = coefficients P (Finsupp.single i 1) :=
  lift_realSubspaceCoordinateMap b e Q hQ _ (hP _)

theorem polynomialKernelDirection_norm (b : Basis μ ℚ L) (Q : Matrix κ μ ℚ)
    {H : ℕ} (hQ : ∀ i j, RationalHeightLE (Q i j) H)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (M : ℝ) (hM : 0 ≤ M) (hP : CoefficientBound (b.baseChange ℝ) T M P) (i : σ) :
    ‖polynomialKernelDirection b Q P i‖ ≤
      (((Fintype.card μ : ℝ) + 1) * (H + 1)) * M / T i := by
  have hp := (coefficientBound_iff_norm (b.baseChange ℝ) T hT hM P).mp hP (Finsupp.single i 1)
  have hs : monomialScale T (Finsupp.single i 1) = T i := by
    simp only [monomialScale, Finsupp.prod_single_index, pow_zero, pow_one]
  rw [hs] at hp
  apply (realSubspaceCoordinateMap_norm b Q hQ _).trans
  calc
    (((Fintype.card μ : ℝ) + 1) * (H + 1)) * ‖(b.baseChange ℝ).equivFun
        (coefficients P (Finsupp.single i 1))‖ ≤
        (((Fintype.card μ : ℝ) + 1) * (H + 1)) * (M / T i) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

theorem polynomialKernelDirection_grid (b : Basis μ ℚ L) (Q : Matrix κ μ ℚ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (l : ℕ)
    (hP : CoefficientGrid (b.baseChange ℝ) l P) (i : σ) :
    polynomialKernelDirection b Q P i ∈ realDenominatorGrid (matrixDenominator Q * l) :=
  realSubspaceCoordinateMap_grid b Q l _ (hP _)

theorem exists_controlled_polynomial_kernel_directions
    (b : Basis μ ℚ L) (e : Basis κ ℚ E) {H l : ℕ}
    (hH : 1 ≤ H) (he : ∀ i j, RationalHeightLE (b.repr (e j : L) i) H)
    (hl : 0 < l) (A B : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hA : ∀ α, coefficients A α ∈ E.baseChange ℝ)
    (hB : ∀ α, coefficients B α ∈ E.baseChange ℝ)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (M : ℝ) (hM : 0 ≤ M)
    (hAbound : CoefficientBound (b.baseChange ℝ) T M A)
    (hBgrid : CoefficientGrid (b.baseChange ℝ) l B) :
    ∃ (a c : σ → κ → ℝ) (d : ℕ),
      0 < d ∧ d ≤ rationalSolveHeight (Fintype.card κ) H ^
        (Fintype.card κ * Fintype.card μ) * l ∧
      ∀ i,
        bracketSystemLift e (a i) = coefficients A (Finsupp.single i 1) ∧
        bracketSystemLift e (c i) = coefficients B (Finsupp.single i 1) ∧
        ‖a i‖ ≤ (((Fintype.card μ : ℝ) + 1) *
          ((rationalSolveHeight (Fintype.card κ) H : ℝ) + 1)) * M / T i ∧
        c i ∈ realDenominatorGrid d := by
  classical
  obtain ⟨Q, hQ, hQheight⟩ := exists_bracketLiftMatrix_leftInverse b e hH he
  refine ⟨polynomialKernelDirection b Q A, polynomialKernelDirection b Q B,
    matrixDenominator Q * l, Nat.mul_pos (matrixDenominator_pos Q) hl,
    Nat.mul_le_mul_right l (matrixDenominator_le Q hQheight), fun i => ?_⟩
  exact ⟨polynomialKernelDirection_lift b e Q hQ A hA i,
    polynomialKernelDirection_lift b e Q hQ B hB i,
    polynomialKernelDirection_norm b Q hQheight A T hT M hM hAbound i,
    polynomialKernelDirection_grid b Q B l hBgrid i⟩

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype κ] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
  {E : Submodule ℚ L}

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

theorem polynomial_kernel_direction_budget (n k H l : ℕ) {p M : ℝ}
    (hp : 0 ≤ p) (hM : 0 ≤ M) (hH : 1 ≤ H)
    (hn : (n : ℝ) ≤ p) (hk : (k : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) (hMp : M ≤ Real.exp p) :
    ((n : ℝ) + 1) * ((rationalSolveHeight k H : ℝ) + 1) * M ≤ Real.exp ((p + 2) ^ 8) ∧
      ((rationalSolveHeight k H ^ (k * n) * l : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 9) := by
  let B := (p + 2) ^ 5
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hB1 : 1 ≤ B := one_le_pow₀ (by linarith : (1 : ℝ) ≤ p + 2)
  have hpB : p ≤ B := le_power_budget hp (by decide : 1 ≤ 5)
  have hq : 0 ≤ p + B := add_nonneg hp hB
  have hheight : (rationalSolveHeight k H : ℝ) ≤ Real.exp (p + B) :=
    (rationalSolveHeight_le_budget k H hp hk hHp).trans
      (Real.exp_le_exp.mpr (by dsimp [B]; linarith))
  have hfactor := current_layer_coordinate_factor_bound hq n (rationalSolveHeight k H)
    (hn.trans (le_add_of_nonneg_right hB)) hheight
  have h8 : (8 : ℝ) ≤ (p + 2) ^ 3 := by
    calc
      (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ (p + 2) ^ 3 :=
        pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by linarith : (2 : ℝ) ≤ p + 2) 3
  have hlog : 2 * (p + B) + 1 + p ≤ (p + 2) ^ 8 := by
    calc
      _ ≤ 6 * B := by linarith
      _ ≤ (p + 2) ^ 3 * B := mul_le_mul_of_nonneg_right (by linarith) hB
      _ = _ := by dsimp [B]; ring
  constructor
  · calc
      _ ≤ Real.exp (2 * (p + B) + 1) * Real.exp p :=
        mul_le_mul hfactor hMp hM (Real.exp_nonneg _)
      _ = Real.exp (2 * (p + B) + 1 + p) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlog
  · have hHpow : (1 : ℕ) ≤ H ^ (n * k) := one_le_pow₀ hH
    have hnat := Nat.mul_le_mul_right (rationalSolveHeight k H ^ (k * n)) hHpow
    simp only [one_mul] at hnat
    have hK : ((rationalSolveHeight k H ^ (k * n) : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 8) :=
      (Nat.cast_le.mpr hnat).trans (rational_grid_height_le_exp n k H hp hn hk hHp)
    have hd := grid_allowance_mul_le_exp hp hl hK
    simpa only [Nat.mul_comm] using hd

theorem exists_uniform_polynomial_kernel_directions
    {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype μ] [Fintype κ]
    {E : Submodule ℚ L} (b : Basis μ ℚ L) (e : Basis κ ℚ E)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (he : ∀ i j, RationalHeightLE (b.repr (e j : L) i) H)
    {p M : ℝ} (hp : 0 ≤ p) (hM : 0 ≤ M)
    (hambient : (Fintype.card μ : ℝ) ≤ p) (hkernel : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) (hMp : M ≤ Real.exp p)
    (A B : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hA : ∀ α, coefficients A α ∈ E.baseChange ℝ)
    (hB : ∀ α, coefficients B α ∈ E.baseChange ℝ)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (hAbound : CoefficientBound (b.baseChange ℝ) T M A)
    (hBgrid : CoefficientGrid (b.baseChange ℝ) l B) :
    ∃ (a c : σ → κ → ℝ) (d : ℕ),
      0 < d ∧ (d : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
      ∀ i,
        bracketSystemLift e (a i) = coefficients A (Finsupp.single i 1) ∧
        bracketSystemLift e (c i) = coefficients B (Finsupp.single i 1) ∧
        ‖a i‖ ≤ Real.exp ((p + 2) ^ 8) / T i ∧ c i ∈ realDenominatorGrid d := by
  obtain ⟨a, c, d, hd, hdbound, hdirs⟩ := exists_controlled_polynomial_kernel_directions
    b e hH he hl A B hA hB T hT M hM hAbound hBgrid
  have hbudget := polynomial_kernel_direction_budget (Fintype.card μ) (Fintype.card κ) H l
    hp hM hH hambient hkernel hHp hlp hMp
  refine ⟨a, c, d, hd, (Nat.cast_le.mpr hdbound).trans hbudget.2, fun i => ?_⟩
  exact ⟨(hdirs i).1, (hdirs i).2.1,
    (hdirs i).2.2.1.trans (div_le_div_of_nonneg_right hbudget.1 (hT i).le), (hdirs i).2.2.2⟩

end Erdos3

end

end OAI
