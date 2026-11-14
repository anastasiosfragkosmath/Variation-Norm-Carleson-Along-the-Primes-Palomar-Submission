/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Geometry/NormalizedMarkedChart.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Lattices.LocalMarkedLatticeCorrection
public import OAI.Combinatorics.Progressions.Polynomial.LocalPhaseMarkedObservable
@[expose] public section

namespace OAI

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool) (t m : ℕ)

theorem normalizedMarkedPhase_real_parameter (a : Fin t → ℝ) :
    torusPhaseLinear (normalizedMarkedPhase F v w marked t m)
      (realMarkedParameterDirection F v w marked t a) = fun i => (m : ℝ)⁻¹ * a i := by
  classical
  have hsingle (j i : Fin t) :
      torusPhaseLinear (normalizedMarkedPhase F v w marked t m)
        (realMarkedDirection F v w marked t (Pi.single j 1)) i =
          (m : ℝ)⁻¹ * (if j = i then 1 else 0) := by
    change torusPhaseLinear (normalizedMarkedPhase F v w marked t m)
      ((1 : ℝ) ⊗ₜ[ℚ] markedQuotientDirection F v w marked t (Pi.single j 1)) i = _
    rw [torusPhaseLinear_tmul, _root_.one_mul, normalizedMarkedPhase_apply,
      markedQuotientPhase_direction]
    change (((m : ℚ)⁻¹ * (Pi.single j (1 : ℚ) : Fin t → ℚ) i : ℚ) : ℝ) = _
    by_cases hji : j = i
    · subst j
      simp
    · have hij : i ≠ j := Ne.symm hji
      simp [hji, hij]
  rw [realMarkedParameterDirection_apply, map_sum]
  funext i
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, hsingle]
  simp [mul_comm]

theorem normalizedMarkedPhase_real_scaled_parameter (hm : 0 < m) (a : Fin t → ℝ) :
    torusPhaseLinear (normalizedMarkedPhase F v w marked t m)
      (realMarkedParameterDirection F v w marked t ((m : ℝ) • a)) = a := by
  rw [normalizedMarkedPhase_real_parameter]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast hm.ne' : (m : ℝ) ≠ 0), _root_.one_mul]

theorem normalizedMarkedPhase_real_pure
    (z : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)
    (hz : z ∈ (markedQuotientPolynomialAlgebra F v w marked t).toSubmodule.baseChange ℝ) :
    torusPhaseLinear (normalizedMarkedPhase F v w marked t m) z = 0 := by
  have hker : (markedQuotientPolynomialAlgebra F v w marked t).toSubmodule ≤
      LinearMap.ker (normalizedMarkedPhase F v w marked t m).toLinearMap := by
    intro x hx
    change markedQuotientPhase F v w marked t x = 0 at hx
    change normalizedMarkedPhase F v w marked t m x = 0
    rw [normalizedMarkedPhase_apply, hx, smul_zero]
  have h := Submodule.baseChange_mono ℝ hker hz
  rw [realification_ker, LinearMap.mem_ker] at h
  change ((RationalTorus.basis t).baseChange ℝ).equivFun
    ((normalizedMarkedPhase F v w marked t m).toLinearMap.baseChange ℝ z) = 0
  rw [h, map_zero]

end Erdos3

namespace Erdos3.NativeRankRelation.CommonData

open NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

end Erdos3.NativeRankRelation.CommonData

end

end OAI
