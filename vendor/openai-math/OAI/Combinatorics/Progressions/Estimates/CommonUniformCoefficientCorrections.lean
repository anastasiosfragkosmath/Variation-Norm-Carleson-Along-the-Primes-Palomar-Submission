/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/CommonUniformCoefficientCorrections.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Linear.CommonRankCoefficientCorrections
@[expose] public section

namespace OAI

section

namespace Erdos3

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeRankInterval.SunflowerWitness

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q}

theorem mono_projectedDenominator (D : I.SunflowerWitness P) (hPQ : P ≤ Q) :
    (D.mono hPQ).projectedDenominator = D.projectedDenominator := rfl

end NativeRankInterval.SunflowerWitness

namespace NativeRankRelation.CommonData

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

theorem exists_common_projected_denominator (D : R.CommonData P) (hP : 0 ≤ P) :
    ∃ (E : R.CommonData ((P + 2) ^ 3 + 2 * P)) (l : ℕ),
      E.quadruples ⊆ D.quadruples ∧ E.spaces = D.spaces ∧ 0 < l ∧
      (l : ℝ) ≤ Real.exp ((P + 2) ^ 3 + P) ∧
      ∀ t (ht : t ∈ E.quadruples), (E.witness t ht).projectedDenominator = l := by
  classical
  let B := (P + 2) ^ 3 + P
  let code (t : ZMod N × ZMod N × ZMod N) :=
    if ht : t ∈ D.quadruples then (D.witness t ht).projectedDenominator else 1
  let A := (Finset.Icc 1 ⌊Real.exp B⌋₊ : Finset ℕ)
  have hcode (t) (ht : t ∈ D.quadruples) : code t ∈ (A : Set ℕ) := by
    simp only [code, dite_eq_left ht, Finset.mem_coe, A, Finset.mem_Icc]
    exact ⟨(D.witness t ht).projectedDenominator_pos,
      Nat.le_floor ((D.witness t ht).projectedDenominator_bound hP)⟩
  have hcount : ((A : Set ℕ).ncard : ℝ) ≤ Real.exp B := by
    simpa only [Set.ncard_coe_finset, A, Nat.card_Icc, Nat.add_sub_cancel] using
      Nat.floor_le (Real.exp_pos B).le
  obtain ⟨l, hl, T, hTD, hT, hconst, hsize⟩ := exists_exponential_constant_fiber
    D.quadruples D.nonempty code A A.finite_toSet hcode hcount
  have hPP : P ≤ (P + 2) ^ 3 + 2 * P := by
    have hcube : 0 ≤ (P + 2) ^ 3 := by positivity
    linarith
  let E : R.CommonData ((P + 2) ^ 3 + 2 * P) := {
    quadruples := T
    subset := hTD.trans D.subset
    nonempty := hT
    density := by
      calc
        Real.exp (-((P + 2) ^ 3 + 2 * P)) * (Fintype.card (ZMod N) : ℝ) ^ 3 =
            Real.exp (-B) * (Real.exp (-P) * (Fintype.card (ZMod N) : ℝ) ^ 3) := by
          rw [← mul_assoc, ← Real.exp_add]
          congr 2
          dsimp only [B]
          ring
        _ ≤ Real.exp (-B) * D.quadruples.card :=
          mul_le_mul_of_nonneg_left D.density (Real.exp_pos _).le
        _ ≤ T.card := hsize
    spaces := D.spaces
    witness := fun t ht => (D.witness t (hTD ht)).mono hPP
    projection := fun t ht d => D.projection t (hTD ht) d }
  have hl' : 1 ≤ l ∧ l ≤ ⌊Real.exp B⌋₊ := Finset.mem_Icc.mp hl
  refine ⟨E, l, hTD, rfl, hl'.1,
    (Nat.cast_le.mpr hl'.2).trans (Nat.floor_le (Real.exp_pos B).le), ?_⟩
  intro t ht
  change ((D.witness t (hTD ht)).mono hPP).projectedDenominator = l
  rw [NativeRankInterval.SunflowerWitness.mono_projectedDenominator]
  simpa only [code, dite_eq_left (hTD ht)] using hconst t ht

end NativeRankRelation.CommonData

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

end Erdos3.NativeRankRelation.CommonData

end

end OAI
