/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Linear/NativeRankIteration.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.MixedPairComparison
@[expose] public section

namespace OAI

section

namespace Erdos3.NativeCorrelationStructure

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

variable {s N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}

noncomputable def absorbRankZero (W : NativeCorrelationStructure (s + 1) 0 N p f) (hp : 0 ≤ p) :
    NativeMixedCorrelation (s + 1) N (productNiltestBudget (p + 4)) f := by
  have hq : 0 ≤ p + 4 := by linarith
  have hpq : p ≤ productNiltestBudget (p + 4) :=
    (show p ≤ p + 4 by linarith).trans (le_productNiltestBudget hq)
  refine {
    shifts := W.shifts
    nonempty := W.nonempty
    density := (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpq))
      (Nat.cast_nonneg _)).trans W.density
    mixed := W.mixed.mono hpq
    correlation := ?_
  }
  intro h hh
  have hin : Nonempty (NativeVectorCorrelation s N p
      (fun ij : Fin W.mixed.outputDim × Fin W.family.outputDim => fun x =>
        nativeMixedResidual f W.mixed h ij.1 x *
          star ((W.family.lowerComponent ij.2 h).evalCyclic N (fun _ => x)))) := by
    have hc := W.correlation h hh
    change Nonempty (NativeVectorCorrelation s N p
      (fun (ij : Fin W.mixed.outputDim × Fin W.family.outputDim) x =>
        multiplicativeDerivative f h x * star (W.mixed.evalCyclic N ij.1 (correlationInput h x)) *
          star (W.family.evalCyclic N ij.2 h x))) at hc
    simpa only [nativeMixedResidual, NativeDegreeRankFamily.lowerComponent_evalCyclic] using hc
  obtain ⟨V⟩ := hin
  exact NativeVectorCorrelation.exists_absorb
    (W.family.model.dropTop W.family.rankZero_top_eq_bot)
    (fun j => W.family.lowerComponent j h) (nativeMixedResidual f W.mixed h)
    (by linarith : 2 ≤ p + 4) (fun j => W.family.lowerComponent_complexity hp j h)
    (V.mono (by linarith))

end Erdos3.NativeCorrelationStructure

end

section

namespace Erdos3

theorem exists_native_rank_descent (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (_W : NativeCorrelationStructure s (r + 1) N p f), (∀ x, ‖f x‖ ≤ 1) →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativeCorrelationStructure s r N ((p + C) ^ C) f) := by
  obtain ⟨a, _, hproduct⟩ := exists_native_product_correlation s hs
  obtain ⟨b, _, hvertical⟩ := exists_native_product_verticalization s
  let X : Polynomial ℕ := Polynomial.X
  let R : Polynomial ℕ := X + (X + Polynomial.C a) ^ a + 2
  let Q : Polynomial ℕ := (R + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + Q)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let p₀ := (p + a) ^ a
  let p₁ := p + p₀ + 2
  let p₂ := (p₁ + b) ^ b
  have hp₀ : 0 ≤ p₀ := by dsimp [p₀]; positivity
  have hp₁ : 0 ≤ p₁ := by dsimp [p₁]; positivity
  have hp₂ : 0 ≤ p₂ := by dsimp [p₂]; positivity
  have htotal : p₁ + p₂ ≤ (p + C) ^ C := by
    simpa [X, R, Q, p₀, p₁, p₂, Polynomial.eval₂_pow] using hbudget p hp
  have hpp₁ : p ≤ p₁ := by dsimp [p₁]; linarith
  have hp₀p₁ : p₀ ≤ p₁ := by dsimp [p₁]; linarith
  have hp₀C : p₀ ≤ (p + C) ^ C := by linarith
  have hp₂C : p₂ ≤ (p + C) ^ C := by linarith
  obtain ⟨J, _, hJ, hdense, hcorr⟩ :=
    hproduct W hf ((Real.exp_le_exp.mpr hp₀C).trans hN)
  have hdense' : Real.exp (-p₁) * N ≤ (J.card : ℝ) :=
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hp₀p₁))
      (Nat.cast_nonneg _)).trans hdense
  have hdim : (W.mixed.outputDim : ℝ) ≤ Real.exp p₁ :=
    W.mixed.output_bound.trans (Real.exp_le_exp.mpr hpp₁)
  have hI : (Fintype.card (Fin W.family.outputDim) : ℝ) ≤ Real.exp p₁ := by
    simpa only [Fintype.card_fin] using W.family.output_bound.trans (Real.exp_le_exp.mpr hpp₁)
  obtain ⟨V⟩ := hvertical J W.mixed.outputDim hp₁ hf hJ hdense' hdim hI
    (hcorr.mono hp₀p₁ hp₀p₁ hp₀p₁)
  exact ⟨V.mono hp₂C⟩

end Erdos3

end

section

namespace Erdos3

theorem exists_native_rank_zero_reduction (s : ℕ) (hs : 2 ≤ s) (r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (_W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativeCorrelationStructure s 0 N ((p + C) ^ C) f) := by
  induction r with
  | zero =>
      refine ⟨2, le_rfl, ?_⟩
      intro N _ p f W _ _
      have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
      exact ⟨W.mono (by norm_num; nlinarith [sq_nonneg p])⟩
  | succ r ih =>
      obtain ⟨a, _, hstep⟩ := exists_native_rank_descent s hs
      obtain ⟨b, _, hiterate⟩ := ih
      let X : Polynomial ℕ := Polynomial.X
      let Q : Polynomial ℕ := (X + Polynomial.C a) ^ a
      obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
        (Q + (Q + Polynomial.C b) ^ b)
      refine ⟨C, hC, ?_⟩
      intro N _ p f W hf hN
      have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
      let q := (p + a) ^ a
      let q₂ := (q + b) ^ b
      have hq : 0 ≤ q := by dsimp [q]; positivity
      have hq₂ : 0 ≤ q₂ := by dsimp [q₂]; positivity
      have htotal : q + q₂ ≤ (p + C) ^ C := by
        simpa [X, Q, q, q₂, Polynomial.eval₂_pow] using hbudget p hp
      have hqC : q ≤ (p + C) ^ C := by linarith
      have hq₂C : q₂ ≤ (p + C) ^ C := by linarith
      obtain ⟨W₁⟩ := hstep W hf ((Real.exp_le_exp.mpr hqC).trans hN)
      obtain ⟨W₀⟩ := hiterate W₁ hf ((Real.exp_le_exp.mpr hq₂C).trans hN)
      exact ⟨W₀.mono hq₂C⟩

end Erdos3

end

end OAI
