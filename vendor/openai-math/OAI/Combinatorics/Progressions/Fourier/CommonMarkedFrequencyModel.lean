/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Fourier/CommonMarkedFrequencyModel.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Dynamics.MarkedEvaluationHeightBudget
public import OAI.Combinatorics.Progressions.Estimates.CommonMarkedMultidegree
public import OAI.Combinatorics.Progressions.Estimates.MultidegreeIntegralModel
@[expose] public section

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open Module

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

end Erdos3

end

section

namespace Erdos3

theorem integral_frequency_grid_allowance_le_exp (K d H l : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    ((K * H ^ (d ^ 3) * (l * H ^ d) : ℕ) : ℝ) ≤
      Real.exp (((p + 2) ^ 2 + (K + 5 : ℕ)) ^ (K + 5)) := by
  have hpQ : p ≤ (p + 2) ^ 2 := le_power_budget hp (by decide)
  have hlQ : ((l * H ^ d : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
    rw [Nat.cast_mul, Nat.cast_pow]
    calc
      _ ≤ Real.exp p * Real.exp p ^ d :=
        mul_le_mul hl (pow_le_pow_left₀ (Nat.cast_nonneg _) hH _) (by positivity) (Real.exp_nonneg _)
      _ = Real.exp (p + (d : ℝ) * p) := by rw [← Real.exp_nat_mul, ← Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [hp, hd, sq_nonneg p])
  exact integral_grid_allowance_le_exp K d H (l * H ^ d) (hp.trans hpQ) (hd.trans hpQ)
    (hH.trans (Real.exp_le_exp.mpr hpQ)) hlQ

end Erdos3

end

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

end Erdos3.NativeRankRelation.CommonData

end

end OAI
