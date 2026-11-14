/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/NativeResidualMultiplier.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.NativeCrossFactorization
public import OAI.Combinatorics.Progressions.Lattices.NativeIntegerAffinePullbackHom
public import OAI.Combinatorics.Progressions.Polynomial.NativeDegreeRankFamily
@[expose] public section

namespace OAI

section

namespace Erdos3.NativeIntegerVectorEquivalence

open scoped BigOperators

variable {σ J K : Type*} [Fintype J] [Fintype K] {s : ℕ} {p : ℝ}
  {chi : J → (σ → ℤ) → ℂ} {eta : K → (σ → ℤ) → ℂ}
  (E : NativeIntegerVectorEquivalence s p chi eta)

abbrev ExpansionIndex := Σ j : J, Σ k : K, Fin (E.selectedExpansion j k).count

theorem expansionIndex_card_bound {a b : ℝ}
    (hJ : (Fintype.card J : ℝ) ≤ Real.exp a)
    (hK : (Fintype.card K : ℝ) ≤ Real.exp b) :
    (Fintype.card E.ExpansionIndex : ℝ) ≤ Real.exp (a + b + p) := by
  classical
  simp only [ExpansionIndex, Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
  calc
    (∑ j : J, ∑ k : K, ((E.selectedExpansion j k).count : ℝ)) ≤
        ∑ _j : J, ∑ _k : K, Real.exp p :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ =>
        (E.selectedExpansion j k).count_bound
    _ = (Fintype.card J : ℝ) * ((Fintype.card K : ℝ) * Real.exp p) := by simp
    _ ≤ Real.exp a * (Real.exp b * Real.exp p) :=
      mul_le_mul hJ (mul_le_mul_of_nonneg_right hK (Real.exp_nonneg _))
        (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (a + b + p) := by rw [← mul_assoc, ← Real.exp_add, ← Real.exp_add]

end Erdos3.NativeIntegerVectorEquivalence

end

section

namespace Erdos3

def correlationInput {A : Type*} (h n : A) : Fin 2 → A := Fin.cases h (fun _ => n)

def mixedCorrelationDegree (s : ℕ) : Fin 2 → ℕ := correlationInput 1 s

noncomputable def nativeCorrelationResidual {s r N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (mixed : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p)
    (family : NativeDegreeRankFamily s r (ZMod N) p) (h : ZMod N)
    (ij : Fin mixed.outputDim × Fin family.outputDim) (x : ZMod N) : ℂ :=
  multiplicativeDerivative f h x * star (mixed.evalCyclic N ij.1 (correlationInput h x)) *
    star (family.evalCyclic N ij.2 h x)

structure NativeCorrelationStructure (s r N : ℕ) [NeZero N] (p : ℝ) (f : ZMod N → ℂ) where
  shifts : Finset (ZMod N)
  nonempty : shifts.Nonempty
  density : Real.exp (-p) * Fintype.card (ZMod N) ≤ (shifts.card : ℝ)
  mixed : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p
  family : NativeDegreeRankFamily s r (ZMod N) p
  correlation : ∀ h ∈ shifts, Nonempty (NativeVectorCorrelation (s - 1) N p
    (nativeCorrelationResidual f mixed family h))

namespace NativeCorrelationStructure

variable {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

noncomputable def mono (hpq : p ≤ q) : NativeCorrelationStructure s r N q f where
  shifts := W.shifts
  nonempty := W.nonempty
  density := (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpq))
    (Nat.cast_nonneg _)).trans W.density
  mixed := W.mixed.mono hpq
  family := W.family.mono hpq
  correlation h hh := by
    obtain ⟨V⟩ := W.correlation h hh
    exact ⟨V.mono hpq⟩

end NativeCorrelationStructure

end Erdos3

end

section

namespace Erdos3.NativeCorrelationStructure

open scoped BigOperators TensorProduct

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

noncomputable def selectedWitness (h : W.shifts) :
    NativeVectorCorrelation (s - 1) N p (nativeCorrelationResidual f W.mixed W.family h) :=
  Classical.choice (W.correlation h h.property)

noncomputable def selectedProduct (h : W.shifts) (x : ZMod N) : ℂ :=
  W.mixed.evalCyclic N (W.selectedWitness h).coordinate.1 (correlationInput h.val x) *
    W.family.evalCyclic N (W.selectedWitness h).coordinate.2 h.val x *
    (W.selectedWitness h).test.evalCyclic N (fun _ => x)

theorem selectedProduct_correlation (h : W.shifts) :
    Real.exp (-p) ≤ ‖𝔼 x, multiplicativeDerivative f h.val x * star (W.selectedProduct h x)‖ := by
  simpa only [selectedProduct, nativeCorrelationResidual, star_mul, mul_assoc, mul_left_comm, mul_comm]
    using (W.selectedWitness h).correlation

end Erdos3.NativeCorrelationStructure

end

section

namespace Erdos3

noncomputable def nativeMixedResidual {s N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (mixed : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p)
    (h : ZMod N) (i : Fin mixed.outputDim) (x : ZMod N) : ℂ :=
  multiplicativeDerivative f h x * star (mixed.evalCyclic N i (correlationInput h x))

structure NativeMixedCorrelation (s N : ℕ) [NeZero N] (p : ℝ) (f : ZMod N → ℂ) where
  shifts : Finset (ZMod N)
  nonempty : shifts.Nonempty
  density : Real.exp (-p) * Fintype.card (ZMod N) ≤ (shifts.card : ℝ)
  mixed : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p
  correlation : ∀ h ∈ shifts, Nonempty (NativeVectorCorrelation (s - 1) N p
    (nativeMixedResidual f mixed h))

namespace NativeMixedCorrelation

variable {s N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  (W : NativeMixedCorrelation s N p f)

noncomputable def mono (hpq : p ≤ q) : NativeMixedCorrelation s N q f where
  shifts := W.shifts
  nonempty := W.nonempty
  density := (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpq))
    (Nat.cast_nonneg _)).trans W.density
  mixed := W.mixed.mono hpq
  correlation h hh := by
    obtain ⟨V⟩ := W.correlation h hh
    exact ⟨V.mono hpq⟩

end NativeMixedCorrelation

end Erdos3

end

section

namespace Erdos3.NativeCorrelationStructure

open scoped BigOperators

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

end Erdos3.NativeCorrelationStructure

end

section

namespace Erdos3.NativeCorrelationStructure

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

noncomputable def normalizedLower (b : ℝ) (h x : ZMod N) : ℂ :=
  if hh : h ∈ W.shifts then
    ((W.selectedWitness ⟨h, hh⟩).test.expNormalize b).evalCyclic N (fun _ => x)
  else 0

theorem normalizedLower_of_mem (b : ℝ) (h : ZMod N) (hh : h ∈ W.shifts) (x : ZMod N) :
    W.normalizedLower b h x =
      ((W.selectedWitness ⟨h, hh⟩).test.expNormalize b).evalCyclic N (fun _ => x) := by
  simp only [normalizedLower, dite_eq_left hh]

theorem normalizedLower_norm {b : ℝ} (hpb : p ≤ b) (h x : ZMod N) :
    ‖W.normalizedLower b h x‖ ≤ 1 := by
  by_cases hh : h ∈ W.shifts
  · rw [W.normalizedLower_of_mem b h hh]
    exact (((W.selectedWitness ⟨h, hh⟩).test.expNormalize b).norm_evalCyclic_le N _).trans
      ((W.selectedWitness ⟨h, hh⟩).test.expNormalize_norm
        ((W.selectedWitness ⟨h, hh⟩).complexity.mono hpb))
  · simp only [normalizedLower, dite_eq_right hh, norm_zero, zero_le_one]

end Erdos3.NativeCorrelationStructure

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

namespace RationalFilteredNilmanifold.Niltest

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {N : ℕ} [NeZero N]

end RationalFilteredNilmanifold.Niltest

namespace NativeIntegerVectorEquivalence

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

end NativeIntegerVectorEquivalence
end Erdos3

end

section

namespace Erdos3

namespace NativeMultidegreeNilcharacter

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3.NativeMixedCorrelation

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (M : NativeMixedCorrelation s N p f)

noncomputable def residualWitness (h : {h // h ∈ M.shifts}) :
    NativeVectorCorrelation (s - 1) N p (nativeMixedResidual f M.mixed h.val) :=
  Classical.choice (M.correlation h.val h.property)

noncomputable def normalizedResidualRow (h n : ZMod N) : ℂ :=
  if hh : h ∈ M.shifts then
    multiplicativeDerivative f h n *
      star (((M.residualWitness ⟨h, hh⟩).test.expNormalize p).evalCyclic N (fun _ => n))
  else 0

theorem normalizedResidualRow_norm (hf : ∀ n, ‖f n‖ ≤ 1) (h n : ZMod N) :
    ‖M.normalizedResidualRow h n‖ ≤ 1 := by
  classical
  by_cases hh : h ∈ M.shifts
  · rw [normalizedResidualRow, dite_eq_left hh, norm_mul, norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _)
      (multiplicativeDerivative_norm_le_one f hf h n)).trans
    apply (((M.residualWitness ⟨h, hh⟩).test.expNormalize p).norm_eval_le _).trans
    exact_mod_cast (M.residualWitness ⟨h, hh⟩).test.expNormalize_norm
      (M.residualWitness ⟨h, hh⟩).complexity
  · simp only [normalizedResidualRow, dite_eq_right hh, norm_zero, zero_le_one]

theorem normalizedResidualRow_correlation (h : ZMod N) (hh : h ∈ M.shifts) :
    Real.exp (-(2 * p)) ≤ ‖𝔼 n : ZMod N, M.normalizedResidualRow h n *
      star (M.mixed.evalCyclic N (M.residualWitness ⟨h, hh⟩).coordinate (correlationInput h n))‖ := by
  classical
  let V := M.residualWitness ⟨h, hh⟩
  have heval (n : ZMod N) : (V.test.expNormalize p).evalCyclic N (fun _ => n) =
      (Real.exp (-p) : ℂ) * V.test.evalCyclic N (fun _ => n) := rfl
  have hmean : (𝔼 n : ZMod N, M.normalizedResidualRow h n *
      star (M.mixed.evalCyclic N V.coordinate (correlationInput h n))) =
      (Real.exp (-p) : ℂ) * (𝔼 n : ZMod N,
        nativeMixedResidual f M.mixed h V.coordinate n * star (V.test.evalCyclic N (fun _ => n))) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro n _
    rw [normalizedResidualRow, dite_eq_left hh]
    change (multiplicativeDerivative f h n * star ((V.test.expNormalize p).evalCyclic N (fun _ => n))) *
      star (M.mixed.evalCyclic N V.coordinate (correlationInput h n)) = _
    rw [heval, star_mul]
    simp only [nativeMixedResidual, Complex.star_def, Complex.conj_ofReal]
    ring
  change Real.exp (-(2 * p)) ≤ ‖𝔼 n : ZMod N, M.normalizedResidualRow h n *
    star (M.mixed.evalCyclic N V.coordinate (correlationInput h n))‖
  rw [hmean, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ = Real.exp (-p) * Real.exp (-p) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left V.correlation (Real.exp_nonneg _)

theorem exists_fixed_normalized_residual_coordinate :
    ∃ out : Fin M.mixed.outputDim, ∃ H : Finset (ZMod N), H ⊆ M.shifts ∧ H.Nonempty ∧
      Real.exp (-(2 * p)) * N ≤ (H.card : ℝ) ∧
      ∀ h ∈ H, Real.exp (-(2 * p)) ≤ ‖𝔼 n : ZMod N, M.normalizedResidualRow h n *
        star (M.mixed.evalCyclic N out (correlationInput h n))‖ := by
  classical
  let rel := fun (h : ZMod N) (_ : Unit) (out : Fin M.mixed.outputDim) =>
    Real.exp (-(2 * p)) ≤ ‖𝔼 n : ZMod N, M.normalizedResidualRow h n *
      star (M.mixed.evalCyclic N out (correlationInput h n))‖
  have hc : ∀ h ∈ M.shifts, ∀ z : Unit, ∃ out, rel h z out := by
    intro h hh _
    exact ⟨(M.residualWitness ⟨h, hh⟩).coordinate, M.normalizedResidualRow_correlation h hh⟩
  have hcount : (Fintype.card (Fin M.mixed.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using M.mixed.output_bound
  obtain ⟨out, H, hsub, hH, hsize, hcorr⟩ :=
    exists_large_fixed_choices M.shifts M.nonempty rel hc hcount
  have hsize' : Real.exp (-p) * (M.shifts.card : ℝ) ≤ (H.card : ℝ) := by
    simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hsize
  have hdensity : Real.exp (-p) * N ≤ (M.shifts.card : ℝ) := by
    simpa only [ZMod.card] using M.density
  refine ⟨out (), H, hsub, hH, ?_, fun h hh => hcorr h hh ()⟩
  calc
    _ = Real.exp (-p) * (Real.exp (-p) * N) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-p) * (M.shifts.card : ℝ) :=
      mul_le_mul_of_nonneg_left hdensity (Real.exp_nonneg _)
    _ ≤ _ := hsize'

end Erdos3.NativeMixedCorrelation

end

section

namespace Erdos3.NativeMixedCorrelation

open scoped TensorProduct

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (M : NativeMixedCorrelation s N p f)

noncomputable def residualMultiplier (h : ZMod N) (x : Unit → ℤ) : ℂ :=
  if hh : h ∈ M.shifts then ((M.residualWitness ⟨h, hh⟩).test.expNormalize p).eval x else 0

theorem residualMultiplier_norm (h : ZMod N) (x : Unit → ℤ) :
    ‖M.residualMultiplier h x‖ ≤ 1 := by
  classical
  by_cases hh : h ∈ M.shifts
  · rw [residualMultiplier, dite_eq_left hh]
    apply (((M.residualWitness ⟨h, hh⟩).test.expNormalize p).norm_eval_le x).trans
    exact_mod_cast (M.residualWitness ⟨h, hh⟩).test.expNormalize_norm
      (M.residualWitness ⟨h, hh⟩).complexity
  · simp only [residualMultiplier, dite_eq_right hh, norm_zero, zero_le_one]

theorem normalizedResidualRow_factor (h n : ZMod N) :
    M.normalizedResidualRow h n =
      multiplicativeDerivative f h n * star (M.residualMultiplier h (fun _ => (n.val : ℤ))) := by
  classical
  by_cases hh : h ∈ M.shifts
  · simp only [normalizedResidualRow, residualMultiplier, dite_eq_left hh]
    rfl
  · simp only [normalizedResidualRow, residualMultiplier, dite_eq_right hh, star_zero, mul_zero]

theorem residualMultiplier_expansion (h : ZMod N) :
    Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) p (M.residualMultiplier h)) := by
  classical
  by_cases hh : h ∈ M.shifts
  · let V := M.residualWitness ⟨h, hh⟩
    refine ⟨NativeIntegerExpansion.ofTest (V.test.expNormalize p)
      (V.test.expNormalize_complexity V.complexity) ?_⟩
    intro x
    simp only [residualMultiplier, dite_eq_left hh]
    rfl
  · obtain ⟨h₀, hh₀⟩ := M.nonempty
    let V := M.residualWitness ⟨h₀, hh₀⟩
    refine ⟨NativeIntegerExpansion.ofTest (V.test.scaleComplex 0)
      (V.test.scaleComplex_complexity (by simp) V.complexity) ?_⟩
    intro x
    simp only [residualMultiplier, dite_eq_right hh,
      RationalFilteredNilmanifold.Niltest.scaleComplex_eval, zero_mul]

end Erdos3.NativeMixedCorrelation

end

end OAI
