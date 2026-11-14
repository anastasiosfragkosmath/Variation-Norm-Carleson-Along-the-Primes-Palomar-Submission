/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/AxisCompression.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Nilpotent.MixedPrimitiveNiltest
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_native_cyclic_small_modulus_correlation (s : ℕ) (hs : 1 ≤ s)
    {N : ℕ} [NeZero N] {p q : ℝ}
    (hN : (N : ℝ) ≤ Real.exp q) (f : ZMod N → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hGowers : Real.exp (-p) ≤ gowersNorm (s + 1) f) :
    ∃ g ∈ nativeCyclicFunctions s N 211,
      Real.exp (-(((2 ^ (s + 1) : ℕ) : ℝ) * p + q)) ≤ ‖𝔼 n, f n * star (g n)‖ := by
  have hmass : Real.exp (-(((2 ^ (s + 1) : ℕ) : ℝ) * p)) ≤
      ∑ χ : AddChar (ZMod N) ℂ, ‖finiteFourierCoeff f χ‖ := by
    calc
      _ = Real.exp (-p) ^ (2 ^ (s + 1)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ gowersNorm (s + 1) f ^ (2 ^ (s + 1)) :=
        pow_le_pow_left₀ (Real.exp_nonneg _) hGowers _
      _ ≤ 𝔼 n, ‖f n‖ := gowersNorm_pow_le_mean_norm s f hf
      _ ≤ _ := mean_norm_le_fourier_sum f
  obtain ⟨χ, hχ⟩ := exists_large_nonnegative_weighted_term
    (fun _ : AddChar (ZMod N) ℂ => (1 : ℝ)) (fun χ => ‖finiteFourierCoeff f χ‖)
    (fun _ => by norm_num) (fun _ => norm_nonneg _) (Real.exp_pos _) (Real.exp_pos q)
    (by simpa using hN) (by simpa only [one_mul] using hmass)
  have hcorr : Real.exp (-(((2 ^ (s + 1) : ℕ) : ℝ) * p + q)) ≤
      ‖finiteFourierCoeff f χ‖ := by
    have heq : Real.exp (-(((2 ^ (s + 1) : ℕ) : ℝ) * p)) / Real.exp q =
        Real.exp (-(((2 ^ (s + 1) : ℕ) : ℝ) * p + q)) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    rwa [heq] at hχ
  obtain ⟨T, hTnorm, hT, hTeval⟩ := exists_cyclic_character_niltest χ
  refine ⟨fun n => χ n, ⟨{
    L := RationalTorus.Algebra 1
    dim := 1
    model := (RationalTorus.nilmanifold 1).raiseStep hs
    test := T.raiseStep hs
    norm := hTnorm
    complexity := ?_
    eval := ?_ }⟩, hcorr⟩
  · have hh := T.raiseStep_complexity hs (by norm_num) hT
    convert hh using 1
    norm_num [raisedNiltestBudget]
  · intro n
    rw [RationalFilteredNilmanifold.Niltest.raiseStep_evalCyclic]
    exact (hTeval n).symm

end Erdos3

end

section

universe u

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology
  NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem exists_mixed_primitive_correlation_large_modulus (d : ℕ) {I : ℕ}
    (hI : CyclicNativeInverse (d + 2) I) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ g ∈ nativeCyclicFunctions (d + 3) N ((p + C) ^ C),
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 n, f n * star (g n)‖ := by
  obtain ⟨A, _, hprimitive⟩ := exists_mixed_primitive_gowers d hI
  let B := I
  have hinverse : CyclicNativeInverse (d + 2) B := hI
  obtain ⟨D, _, hmodel⟩ := NativeMultidegreeNilcharacter.exists_mixed_primitive_niltest_budget d
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let V := (U + 2 + Polynomial.C B) ^ B
  let R := U + V + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + V + (R + Polynomial.C D) ^ D)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let u := (p + A) ^ A
  let v := (u + 2 + B) ^ B
  let r := u + v + 2
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htotal : u + v + (r + D) ^ D ≤ (p + C) ^ C := by
    simpa [X, U, V, R, u, v, r, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (r + D) ^ D := by positivity
  have huC : u ≤ (p + C) ^ C := by linarith
  have hvC : v ≤ (p + C) ^ C := by linarith
  have hmC : (r + D) ^ D ≤ (p + C) ^ C := by linarith
  obtain ⟨q, hq, hqu, W, i, hW⟩ :=
    hprimitive hp ((Real.exp_le_exp.mpr huC).trans hN) f hf hGowers
  obtain ⟨g, ⟨G⟩, hg⟩ := hinverse (by linarith : 2 ≤ u + 2)
    (W.mixedPrimitiveFactor f i) (W.mixedPrimitiveFactor_norm f hf i)
    ((Real.exp_le_exp.mpr (by linarith : -(u + 2) ≤ -u)).trans hW)
  have hqr : q ≤ r := by dsimp [r]; linarith
  have hvr : v ≤ r := by dsimp [r]; linarith
  have hgmodel : g ∈ nativeCyclicFunctions (d + 2) N r :=
    ⟨{ G with complexity := G.complexity.mono hvr }⟩
  have hm := hmodel hr (W.mono hqr) i g hgmodel
  have hm' : (fun n : ZMod N => star (W.eval i (fun _ => (n.val : ℤ))) * g n) ∈
      nativeCyclicFunctions (d + 3) N ((r + D) ^ D) := by
    simpa only [NativeMultidegreeNilcharacter.mono_eval] using hm
  obtain ⟨M⟩ := hm'
  refine ⟨fun n => star (W.eval i (fun _ => (n.val : ℤ))) * g n,
    ⟨{ M with complexity := M.complexity.mono hmC }⟩, ?_⟩
  have heq : (𝔼 n : ZMod N, f n * star (star (W.eval i (fun _ => (n.val : ℤ))) * g n)) =
      𝔼 n : ZMod N, W.mixedPrimitiveFactor f i n * star (g n) := by
    apply Finset.expect_congr rfl
    intro n _
    simp only [NativeMultidegreeNilcharacter.mixedPrimitiveFactor, star_mul, star_star]
    ring
  rw [heq]
  exact (Real.exp_le_exp.mpr (neg_le_neg hvC)).trans hg

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology
  NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem exists_cyclicNativeInverse_step (d : ℕ) {I : ℕ}
    (hI : CyclicNativeInverse (d + 2) I) :
    ∃ C : ℕ, 2 ≤ C ∧ CyclicNativeInverse (d + 3) C := by
  obtain ⟨A, _, hlarge⟩ := exists_mixed_primitive_correlation_large_modulus d hI
  let L := 2 ^ (d + 4)
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + Polynomial.C L * X + 211)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hGowers
  have hp0 : 0 ≤ p := by linarith
  let u := (p + A) ^ A
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hLp : 0 ≤ (L : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp0
  have hsum : u + (L : ℝ) * p + 211 ≤ (p + C) ^ C := by
    simpa [X, u, Polynomial.eval₂_pow] using hbudget p hp0
  have huC : u ≤ (p + C) ^ C := by linarith
  by_cases hN : Real.exp u ≤ (N : ℝ)
  · obtain ⟨g, ⟨M⟩, hcorr⟩ := hlarge hp0 hN f hf hGowers
    exact ⟨g, ⟨{ M with complexity := M.complexity.mono huC }⟩,
      (Real.exp_le_exp.mpr (neg_le_neg huC)).trans hcorr⟩
  · obtain ⟨g, ⟨M⟩, hcorr⟩ :=
      exists_native_cyclic_small_modulus_correlation (d + 3) (by omega) (not_le.mp hN).le f hf hGowers
    have h211 : (211 : ℝ) ≤ (p + C) ^ C := by linarith
    have hc : (L : ℝ) * p + u ≤ (p + C) ^ C := by linarith
    exact ⟨g, ⟨{ M with complexity := M.complexity.mono h211 }⟩,
      (Real.exp_le_exp.mpr (neg_le_neg hc)).trans hcorr⟩

theorem exists_cyclicNativeInverse_add_two (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ CyclicNativeInverse (d + 2) C := by
  induction d with
  | zero => exact exists_cyclicNativeInverse_two
  | succ d ih =>
      obtain ⟨I, _, hI⟩ := ih
      exact exists_cyclicNativeInverse_step d hI

end Erdos3

end

section

namespace Erdos3

theorem exists_cyclicNativeInverse_positive (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ CyclicNativeInverse s C := by
  cases s with
  | zero => omega
  | succ s =>
      cases s with
      | zero => exact ⟨2, le_rfl, cyclicNativeInverse_one⟩
      | succ s => exact exists_cyclicNativeInverse_add_two s

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology
  NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_native_inverse_on_cyclic_encoding (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} [Fintype σ] [DecidableEq σ] {N : ℕ} [NeZero N]
      (Q : Finset (σ → ℤ)), Q.Nonempty → ∀ (φ : (σ → ℤ) →+ ℤ),
      ReflectsPairSums ((Int.castAddHom (ZMod N)).comp φ) (Q : Set (σ → ℤ)) →
      (∀ x ∈ Q, 0 ≤ φ x ∧ φ x < (N : ℤ)) →
      ∀ {p q : ℝ}, 2 ≤ p → 0 ≤ q → Real.exp (-q) ≤ (Q.card : ℝ) / (N : ℝ) →
      ∀ f : (σ → ℤ) → ℂ, (∀ x ∈ Q, ‖f x‖ ≤ 1) →
      Real.exp (-p) ≤ finiteSupportGowersNorm (s + 1) Q f →
      ∃ V : NativeSampleCorrelation (fun _ : σ => 1) s ((p + q + C) ^ C) Q id f,
        V.test.normBound ≤ 1 := by
  obtain ⟨C, hC, hinverse⟩ := exists_cyclicNativeInverse_positive s hs
  refine ⟨C, hC, ?_⟩
  intro σ _ _ N _ Q hQ φ hφ hrep p q hp hq hden f hf hGowers
  let ψ : (σ → ℤ) →+ ZMod N := (Int.castAddHom (ZMod N)).comp φ
  let F := imageExtension ψ Q f
  have hF : ∀ y, ‖F y‖ ≤ 1 := imageExtension_norm_le_one ψ Q f hφ.injOn hf
  have hG : Real.exp (-(p + q)) ≤ gowersNorm (s + 1) F :=
    exp_le_gowers_imageExtension s ψ Q hφ f (by simpa only [ZMod.card] using hden) hGowers
  obtain ⟨g, ⟨M⟩, hcorr⟩ := hinverse (by linarith : 2 ≤ p + q) F hF hG
  let T := M.test.linearPullbackHom (fun _ : Unit => φ)
  have heval (x : σ → ℤ) (hx : x ∈ Q) : T.eval x = g (ψ x) := by
    change (M.test.linearPullbackHom (fun _ : Unit => φ)).eval x = g (ψ x)
    rw [RationalFilteredNilmanifold.Niltest.eval_linearPullbackHom, M.eval]
    change M.test.eval (fun _ => φ x) = M.test.eval (fun _ => (((φ x : ZMod N).val) : ℤ))
    simp only [ZMod.val_intCast, Int.emod_eq_of_lt (hrep x hx).1 (hrep x hx).2]
  refine ⟨{
    L := M.L
    dim := M.dim
    model := M.model
    test := T
    complexity := M.complexity
    correlation := ?_ }, ?_⟩
  · have hmean : (𝔼 x ∈ Q, f x * star (T.eval x)) =
        (𝔼 x ∈ Q, f x * star (g (ψ x))) := by
      apply Finset.expect_congr rfl
      intro x hx
      rw [heval x hx]
    change Real.exp (-((p + q + C) ^ C)) ≤ ‖𝔼 x ∈ Q, f x * star (T.eval x)‖
    rw [hmean]
    exact hcorr.trans (norm_expect_imageExtension_mul_le ψ Q hQ hφ.injOn f (fun y => star (g y)))
  · exact M.norm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology
  NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

end Erdos3

end

section

namespace Erdos3.PositiveShiftBasis

universe u

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open NativeModelingNumerics

universe u

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

universe u

namespace PositiveShiftBasis

end PositiveShiftBasis
end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

end Erdos3

end

end OAI
