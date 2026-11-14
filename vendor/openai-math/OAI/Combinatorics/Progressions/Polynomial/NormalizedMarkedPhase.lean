/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Polynomial/NormalizedMarkedPhase.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.MarkedShiftGeneratorBounds
@[expose] public section

namespace OAI

section

namespace Erdos3

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool) (t : ℕ)

noncomputable def markedShiftPhase :
    markedShiftSubalgebra F v w marked t →ₗ⁅ℚ⁆ RationalTorus.Algebra t where
  toFun x := x.val.right
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

noncomputable def markedQuotientPhase :
    MarkedShiftQuotient F v w marked t →ₗ⁅ℚ⁆ RationalTorus.Algebra t :=
  lieQuotientDescend (markedShiftSecondIdeal F v w marked t)
    (markedShiftPhase F v w marked t) (fun _ hx => hx.1)

theorem markedQuotientPhase_direction (a : Fin t → ℚ) :
    markedQuotientPhase F v w marked t (markedQuotientDirection F v w marked t a) = a := rfl

noncomputable def markedQuotientPolynomialAlgebra :
    LieSubalgebra ℚ (MarkedShiftQuotient F v w marked t) :=
  (markedQuotientPhase F v w marked t).ker.toLieSubalgebra

theorem exists_zero_phase_lift (x : MarkedShiftQuotient F v w marked t)
    (hx : markedQuotientPhase F v w marked t x = 0) :
    ∃ p : markedShiftSubalgebra F v w marked t,
      p.val.right = 0 ∧ lieQuotientMap (markedShiftSecondIdeal F v w marked t) p = x := by
  obtain ⟨p, rfl⟩ := lieQuotientMap_surjective (markedShiftSecondIdeal F v w marked t) x
  exact ⟨p, hx, rfl⟩

end Erdos3

end

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool) (t : ℕ)
  (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)
  (hphase : ∀ z : D.filtration.Group, z ∈ D.lattice →
    IntegralVector (markedQuotientPhase F v w marked t z.coord))

variable [TopologicalSpace (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
  [T2Space (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]

end Erdos3

end

section

namespace Erdos3

theorem rationalLogHeight_nat_inv_mul_exp_bound (m : ℕ) (hm : 0 < m)
    {p : ℝ} (hp : 0 ≤ p) (hmp : (m : ℝ) ≤ Real.exp p) {x : ℚ}
    (hx : rationalLogHeight x ≤ p) :
    rationalLogHeight ((m : ℚ)⁻¹ * x) ≤ 2 * p + 1 := by
  have hmheight : RationalHeightLE (m : ℚ) m := by
    simp only [RationalHeightLE, Rat.num_natCast, Rat.den_natCast, Int.natAbs_natCast]
    exact ⟨le_rfl, hm⟩
  have hinv := hmheight.inv (by exact_mod_cast hm.ne')
  apply rationalLogHeight_le_of_height (hinv.mul (rationalHeightLE_ceil_exp hx))
  rw [Nat.cast_mul]
  calc
    (m : ℝ) * ⌈Real.exp p⌉₊ ≤ Real.exp p * Real.exp (p + 1) :=
      mul_le_mul hmp (ceil_exp_le_exp_add_one hp) (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (2 * p + 1) := by rw [← Real.exp_add]; congr 1; ring

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool) (t m : ℕ)

noncomputable def normalizedMarkedPhase :
    MarkedShiftQuotient F v w marked t →ₗ⁅ℚ⁆ RationalTorus.Algebra t where
  toLinearMap := (m : ℚ)⁻¹ • (markedQuotientPhase F v w marked t).toLinearMap
  map_lie' {x y} := by
    change (m : ℚ)⁻¹ • markedQuotientPhase F v w marked t ⁅x, y⁆ = 0
    rw [(markedQuotientPhase F v w marked t).map_lie, RationalTorus.lie_eq_zero, smul_zero]

theorem normalizedMarkedPhase_apply (x : MarkedShiftQuotient F v w marked t) :
    normalizedMarkedPhase F v w marked t m x =
      (m : ℚ)⁻¹ • markedQuotientPhase F v w marked t x := rfl

theorem normalizedMarkedPhase_scaled_direction (hm : 0 < m) (a : Fin t → ℚ) :
    normalizedMarkedPhase F v w marked t m
      ((m : ℚ) • markedQuotientDirection F v w marked t a) = a := by
  rw [normalizedMarkedPhase_apply, map_smul, markedQuotientPhase_direction]
  change (m : ℚ)⁻¹ • ((m : ℚ) • a) = a
  rw [smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast hm.ne' : (m : ℚ) ≠ 0), one_smul]

theorem normalizedMarkedPhase_height {p : ℝ} (hm : 0 < m) (hp : 0 ≤ p)
    (hmp : (m : ℝ) ≤ Real.exp p) (x : MarkedShiftQuotient F v w marked t) (i : Fin t)
    (hx : rationalLogHeight (markedQuotientPhase F v w marked t x i) ≤ p) :
    rationalLogHeight (normalizedMarkedPhase F v w marked t m x i) ≤ 2 * p + 1 :=
  rationalLogHeight_nat_inv_mul_exp_bound m hm hp hmp hx

end Erdos3

end

end OAI
