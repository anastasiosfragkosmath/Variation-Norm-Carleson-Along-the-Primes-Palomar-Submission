/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/QuarticRootExchange.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.CoefficientTensorApproximation
public import OAI.Combinatorics.Progressions.Estimates.QuarticSurvivorMultilinearization
public import OAI.Combinatorics.Progressions.Lattices.NativeIntegerDivision
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def complexCrossContraction {K L : Type*} [Fintype K] [Fintype L]
    (a b : ℂ) (u : K → ℂ) (v : L → ℂ) (G : K → L → ℂ) : ℂ :=
  ∑ kl : K × L, (a * star (u kl.1)) * star (b * star (v kl.2)) * G kl.1 kl.2

theorem complexCrossContraction_rank_one {K L : Type*} [Fintype K] [Fintype L]
    (a b : ℂ) (u f : K → ℂ) (v g : L → ℂ) :
    complexCrossContraction a b u v (fun k l => f k * star (g l)) =
      (a * star b) * (∑ k, star (u k) * f k) * star (∑ l, star (v l) * g l) := by
  simp only [complexCrossContraction, Fintype.sum_prod_type, star_sum,
    star_mul, star_star, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem complexCrossContraction_unit {K L : Type*} [Fintype K] [Fintype L]
    (a b : ℂ) (u : K → ℂ) (v : L → ℂ)
    (hu : ∑ k, ‖u k‖ ^ 2 = 1) (hv : ∑ l, ‖v l‖ ^ 2 = 1) :
    complexCrossContraction a b u v (fun k l => u k * star (v l)) = a * star b := by
  rw [complexCrossContraction_rank_one]
  have hU : ∑ k, star (u k) * u k = (1 : ℂ) := by
    simpa only [one_mul] using (complex_unit_vector_resolution u hu 1).symm
  have hV : ∑ l, star (v l) * v l = (1 : ℂ) := by
    simpa only [one_mul] using (complex_unit_vector_resolution v hv 1).symm
  rw [hU, hV, star_one, mul_one, mul_one]

theorem norm_sub_complexCrossContraction_le_sum {K L : Type*} [Fintype K] [Fintype L]
    (a b : ℂ) (u : K → ℂ) (v : L → ℂ) (G : K → L → ℂ)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hu : ∑ k, ‖u k‖ ^ 2 = 1) (hv : ∑ l, ‖v l‖ ^ 2 = 1)
    (hucap : ∀ k, ‖u k‖ ≤ 1) (hvcap : ∀ l, ‖v l‖ ≤ 1) :
    ‖a * star b - complexCrossContraction a b u v G‖ ≤
      ∑ kl : K × L, ‖u kl.1 * star (v kl.2) - G kl.1 kl.2‖ := by
  have hid : a * star b - complexCrossContraction a b u v G =
      ∑ kl : K × L, ((a * star (u kl.1)) * star (b * star (v kl.2))) *
        (u kl.1 * star (v kl.2) - G kl.1 kl.2) := by
    rw [← complexCrossContraction_unit a b u v hu hv]
    simp only [complexCrossContraction, mul_sub, Finset.sum_sub_distrib]
  rw [hid]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro kl _
  rw [norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  rw [norm_mul, norm_mul, norm_star, norm_star, norm_mul, norm_star]
  refine (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_).trans ?_
  · exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans (hucap kl.1)
  · exact (mul_le_of_le_one_left (norm_nonneg _) hb).trans (hvcap kl.2)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem norm_complexCrossContraction_le_card {K L : Type*} [Fintype K] [Fintype L]
    (a b : ℂ) (u : K → ℂ) (v : L → ℂ) (G : K → L → ℂ) {B : ℝ}
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hu : ∀ k, ‖u k‖ ≤ 1) (hv : ∀ l, ‖v l‖ ≤ 1) (hG : ∀ k l, ‖G k l‖ ≤ B) :
    ‖complexCrossContraction a b u v G‖ ≤ (Fintype.card (K × L) : ℝ) * B := by
  unfold complexCrossContraction
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _ : K × L, B := by
      apply Finset.sum_le_sum
      intro kl _
      rw [norm_mul]
      apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hG kl.1 kl.2)
      rw [norm_mul, norm_star, norm_mul, norm_star, norm_mul, norm_star]
      refine (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_).trans ?_
      · exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans (hu kl.1)
      · exact (mul_le_of_le_one_left (norm_nonneg _) hb).trans (hv kl.2)
    _ = _ := by simp

theorem mean_complexCrossContraction_error_le_card {K L X : Type*}
    [Fintype K] [Fintype L] [Fintype X]
    (a b : X → ℂ) (u : K → X → ℂ) (v : L → X → ℂ) (G : K → L → X → ℂ) {ε : ℝ}
    (ha : ∀ x, ‖a x‖ ≤ 1) (hb : ∀ x, ‖b x‖ ≤ 1)
    (hu : ∀ x, ∑ k, ‖u k x‖ ^ 2 = 1) (hv : ∀ x, ∑ l, ‖v l x‖ ^ 2 = 1)
    (hucap : ∀ k x, ‖u k x‖ ≤ 1) (hvcap : ∀ l x, ‖v l x‖ ≤ 1)
    (herr : ∀ k l, (𝔼 x, ‖u k x * star (v l x) - G k l x‖) ≤ ε) :
    (𝔼 x, ‖a x * star (b x) - complexCrossContraction (a x) (b x)
      (fun k => u k x) (fun l => v l x) (fun k l => G k l x)‖) ≤
      (Fintype.card (K × L) : ℝ) * ε := by
  calc
    _ ≤ 𝔼 x, ∑ kl : K × L, ‖u kl.1 x * star (v kl.2 x) - G kl.1 kl.2 x‖ := by
      apply Finset.expect_le_expect
      intro x _
      exact norm_sub_complexCrossContraction_le_sum (a x) (b x)
        (fun k => u k x) (fun l => v l x) (fun k l => G k l x)
        (ha x) (hb x) (hu x) (hv x) (fun k => hucap k x) (fun l => hvcap l x)
    _ = ∑ kl : K × L, 𝔼 x, ‖u kl.1 x * star (v kl.2 x) - G kl.1 kl.2 x‖ :=
      Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _ : K × L, ε := Finset.sum_le_sum (fun kl _ => herr kl.1 kl.2)
    _ = _ := by simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_native_cross_contraction :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ J K L M : Type*}
      [Fintype J] [Fintype K] [Fintype L] [Fintype M] {s : ℕ} {p : ℝ}
      {a : J → (σ → ℤ) → ℂ} {u : K → (σ → ℤ) → ℂ}
      {b : L → (σ → ℤ) → ℂ} {v : M → (σ → ℤ) → ℂ}
      (G : K → M → (σ → ℤ) → ℂ),
      0 ≤ p → NativeIntegerVectorEquivalence s p a u → NativeIntegerVectorEquivalence s p b v →
      (∀ k m, Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s p (G k m))) →
      ∀ j l, Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((p + C) ^ C)
        (fun x => complexCrossContraction (a j x) (b l x)
          (fun k => u k x) (fun m => v m x) (fun k m => G k m x))) := by
  obtain ⟨A, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((T + Polynomial.C A) ^ A + 2 * X)
  refine ⟨C, hC, ?_⟩
  intro σ J K L M _ _ _ _ s p a u b v G hp E F hG j l
  classical
  let t := p + (p + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := le_add_of_nonneg_right (by positivity)
  have hAt : (p + A) ^ A ≤ t := by dsimp [t]; linarith
  have hterm (km : K × M) : Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s
      ((t + A) ^ A) (fun x =>
        (a j x * star (u km.1 x)) * star (b l x * star (v km.2 x)) * G km.1 km.2 x)) := by
    obtain ⟨H⟩ := hmul hp (Classical.choice (E.expansion j km.1))
      (Classical.choice (F.expansion l km.2)).conjugate
    exact hmul ht (H.mono hAt) ((Classical.choice (hG km.1 km.2)).mono hpt)
  have hcard : (Fintype.card (K × M) : ℝ) ≤ Real.exp (2 * p) := by
    rw [Fintype.card_prod, Nat.cast_mul]
    calc
      _ ≤ Real.exp p * Real.exp p :=
        mul_le_mul E.right_dimension F.right_dimension (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, two_mul]
  have hc : (∑ _ : K × M, ‖(1 : ℂ)‖) ≤ Real.exp (2 * p) := by simpa using hcard
  have H := NativeIntegerExpansion.weightedSum (fun km => Classical.choice (hterm km))
    (fun _ => 1) (by positivity : 0 ≤ 2 * p) hcard hc
  have hcost : (t + A) ^ A + 2 * p ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by simpa only [one_mul, complexCrossContraction] using H.mono hcost⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

namespace NativeMultidegreeNilcharacter

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem division_dilation_integer_representative (d : ℕ) [NeZero d]
    {σ : Type*} [Fintype σ] {bound : σ → ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter bound p) (x : σ → ℤ) (j : Fin W.outputDim) :
    (W.rationalDilation ((d : ℚ)⁻¹)).eval j (fun i => x i - ((x i : ZMod d).val : ℤ)) =
      W.eval j (fun i => x i / (d : ℤ)) := by
  have hx : (fun i => x i - ((x i : ZMod d).val : ℤ)) =
      (fun i => (d : ℤ) * (x i / (d : ℤ))) := by
    funext i
    rw [ZMod.val_intCast, sub_eq_iff_eq_add]
    simpa only [add_comm] using (Int.emod_add_mul_ediv (x i) (d : ℤ)).symm
  rw [hx]
  apply W.rationalDilation_eval_rescaled
  rw [Int.cast_natCast]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne d))

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped BigOperators

theorem exists_sampled_rational_division_equivalence (d s : ℕ) [NeZero d] (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} [Fintype σ] (bound : σ → ℕ),
      (∑ k, bound k) = s + 1 → ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter bound p) (ρ : σ → Fin 2),
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun j (x : Fin 2 → ℤ) => (W.rationalDilation ((d : ℚ)⁻¹)).eval j (fun k => x (ρ k)))
        (fun j x => W.eval j (fun k => x (ρ k) / (d : ℤ))) := by
  obtain ⟨A, _, hshift⟩ := exists_multidegree_integer_translation s
  obtain ⟨B, _, hresidue⟩ := exists_pairResidueIndicator_expansion d s hs
  obtain ⟨D, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + Polynomial.C B + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((T + Polynomial.C D) ^ D + T + Polynomial.C (d ^ 2))
  refine ⟨C, hC, ?_⟩
  intro σ _ bound hdegree p W ρ
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let V := W.rationalDilation ((d : ℚ)⁻¹)
  let t : ℝ := (p + A) ^ A + B + p + 2
  have ha : 0 ≤ (p + A) ^ A := by positivity
  have hb : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hat : (p + A) ^ A ≤ t := by dsimp [t]; linarith
  have hbt : (B : ℝ) ≤ t := by dsimp [t]; linarith
  have hbound : (t + D) ^ D + t + (d : ℝ) ^ 2 ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (t + D) ^ D := by positivity
  have hpc : p ≤ (p + C) ^ C := by
    have hpt : p ≤ t := by dsimp [t]; linarith
    linarith [sq_nonneg (d : ℝ)]
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpc)
  refine ⟨hdim, hdim, ?_⟩
  intro i j
  let inp (x : Fin 2 → ℤ) : σ → ℤ := fun k => x (ρ k)
  have hinput (x : Fin 2 → ℤ) : (fun k => x (ρ k)) = inp x := rfl
  let F (r : Fin 2 → ZMod d) (x : Fin 2 → ℤ) :=
    V.eval i (inp x) * star (V.eval j (inp (fun k => x k - ((r k).val : ℤ))))
  have hF (r : Fin 2 → ZMod d) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s t (F r)) := by
    obtain ⟨E⟩ := ((hshift bound hdegree V 0 (fun k => -((r (ρ k)).val : ℤ))).coordinatePullback ρ).expansion i j
    have hr (x : Fin 2 → ℤ) :
        (fun k => x (ρ k)) + (fun k => -((r (ρ k)).val : ℤ)) =
          inp (fun k => x k - ((r k).val : ℤ)) := by
      calc
        _ = (fun k => x (ρ k) - ((r (ρ k)).val : ℤ)) := by
          funext k
          simp only [Pi.add_apply, sub_eq_add_neg]
        _ = _ := hinput (fun k => x k - ((r k).val : ℤ))
    have heq : (fun x : Fin 2 → ℤ => V.eval i ((fun k => x (ρ k)) + 0) *
        star (V.eval j ((fun k => x (ρ k)) + (fun k => -((r (ρ k)).val : ℤ))))) = F r := by
      funext x
      rw [add_zero, hr, hinput]
    exact ⟨heq ▸ E.mono hat⟩
  have hterm (r : Fin 2 → ZMod d) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s
      ((t + D) ^ D) (fun x => pairResidueIndicator r x * F r x)) :=
    hmul ht ((Classical.choice (hresidue r)).mono hbt) (Classical.choice (hF r))
  have hcoeff : (∑ _ : Fin 2 → ZMod d, ‖(1 : ℂ)‖) ≤ Real.exp ((d : ℝ) ^ 2) := by
    simpa using card_pairResidue_le_exp d
  let S := NativeIntegerExpansion.weightedSum (fun r => Classical.choice (hterm r)) (fun _ => 1)
    (sq_nonneg (d : ℝ)) (card_pairResidue_le_exp d) hcoeff
  have hrep (x : Fin 2 → ℤ) :
      V.eval j (inp (fun k => x k - ((x k : ZMod d).val : ℤ))) =
        W.eval j (inp (fun k => x k / (d : ℤ))) := by
    exact division_dilation_integer_representative d W (inp x) j
  have heq : (fun x => ∑ r : Fin 2 → ZMod d, (1 : ℂ) * (pairResidueIndicator r x * F r x)) =
      (fun x => V.eval i (inp x) * star (W.eval j (inp (fun k => x k / (d : ℤ))))) := by
    funext x
    let r : Fin 2 → ZMod d := fun k => (x k : ZMod d)
    rw [Finset.sum_eq_single r]
    · simp only [pairResidueIndicator, r, ite_true, one_mul, F, hrep]
    · intro z _ hz
      have hne : (fun k => (x k : ZMod d)) ≠ z := fun h => hz h.symm
      simp only [pairResidueIndicator, hne, ite_false, zero_mul, mul_zero]
    · simp
  rw [heq] at S
  exact ⟨S.mono (by linarith)⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
