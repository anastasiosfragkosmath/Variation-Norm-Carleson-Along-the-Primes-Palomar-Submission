/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Fourier/NativeMixedFourierProfiles.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.NativeMixedCubeResiduals
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def cyclicRealLinearPhase {N : ℕ} (β : ℝ) (n : ZMod N) : ℂ :=
  CircleFourier.character (((n.val : ℝ) * β : ℝ) : CircleFourier.Circle)

@[simp] theorem norm_cyclicRealLinearPhase {N : ℕ} (β : ℝ) (n : ZMod N) :
    ‖cyclicRealLinearPhase β n‖ = 1 := CircleFourier.norm_character _

theorem cyclicRealLinearPhase_unit_shift_error {N : ℕ} [NeZero N] (β : ℝ) :
    (𝔼 n : ZMod N, ‖cyclicRealLinearPhase β (n + 1) -
      CircleFourier.character (β : CircleFourier.Circle) * cyclicRealLinearPhase β n‖) ≤ 2 / N := by
  classical
  let b : ZMod N := ((N - 1 : ℕ) : ZMod N)
  have hpoint (n : ZMod N) :
      ‖cyclicRealLinearPhase β (n + 1) -
        CircleFourier.character (β : CircleFourier.Circle) * cyclicRealLinearPhase β n‖ ≤
        if n = b then 2 else 0 := by
    by_cases hn : n = b
    · rw [ite_eq_left hn]
      calc
        _ ≤ ‖cyclicRealLinearPhase β (n + 1)‖ +
            ‖CircleFourier.character (β : CircleFourier.Circle) * cyclicRealLinearPhase β n‖ := norm_sub_le _ _
        _ = 2 := by simp only [norm_mul, norm_cyclicRealLinearPhase, CircleFourier.norm_character]; norm_num
    · rw [ite_eq_right hn]
      have hnlt : n.val + 1 < N := by
        have hv := n.val_lt
        by_contra h
        have he : n.val = N - 1 := by omega
        apply hn
        rw [← ZMod.natCast_zmod_val n, he]
      have hval : (n + 1).val = n.val + 1 := by
        have he : n + 1 = ((n.val + 1 : ℕ) : ZMod N) := by simp
        rw [he, ZMod.val_natCast_of_lt hnlt]
      have heq : cyclicRealLinearPhase β (n + 1) =
          CircleFourier.character (β : CircleFourier.Circle) * cyclicRealLinearPhase β n := by
        simp only [cyclicRealLinearPhase, hval, Nat.cast_add, Nat.cast_one, add_mul,
          one_mul, AddCircle.coe_add, CircleFourier.character_add]
        ring
      rw [heq, sub_self, norm_zero]
  calc
    _ ≤ 𝔼 n : ZMod N, if n = b then (2 : ℝ) else 0 :=
      Finset.expect_le_expect (fun n _ => hpoint n)
    _ = 2 / N := by rw [Fintype.expect_eq_sum_div_card]; simp

theorem mean_twisted_nat_translate_error {N : ℕ} [NeZero N]
    (q : ZMod N → ℂ) (ζ : ℂ) (hζ : ‖ζ‖ ≤ 1) {ε : ℝ}
    (hstep : (𝔼 n : ZMod N, ‖q (n + 1) - ζ * q n‖) ≤ ε) (m : ℕ) :
    (𝔼 n : ZMod N, ‖q (n + m) - ζ ^ m * q n‖) ≤ (m : ℝ) * ε := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hpoint (n : ZMod N) :
        ‖q (n + (m + 1 : ℕ)) - ζ ^ (m + 1) * q n‖ ≤
          ‖q ((n + m) + 1) - ζ * q (n + m)‖ + ‖q (n + m) - ζ ^ m * q n‖ := by
      calc
        _ = ‖(q ((n + m) + 1) - ζ * q (n + m)) +
            ζ * (q (n + m) - ζ ^ m * q n)‖ := by
          simp only [Nat.cast_add, Nat.cast_one, add_assoc, pow_succ]
          congr 1
          ring
        _ ≤ ‖q ((n + m) + 1) - ζ * q (n + m)‖ +
            ‖ζ * (q (n + m) - ζ ^ m * q n)‖ := norm_add_le _ _
        _ ≤ _ := by
          rw [norm_mul]
          exact add_le_add le_rfl (mul_le_of_le_one_left (norm_nonneg _) hζ)
    have hshift : (𝔼 n : ZMod N, ‖q ((n + m) + 1) - ζ * q (n + m)‖) =
        𝔼 n : ZMod N, ‖q (n + 1) - ζ * q n‖ := by
      exact Fintype.expect_equiv (Equiv.addRight (m : ZMod N)) _ _ (fun _ => rfl)
    calc
      _ ≤ (𝔼 n : ZMod N, ‖q ((n + m) + 1) - ζ * q (n + m)‖) +
          (𝔼 n : ZMod N, ‖q (n + m) - ζ ^ m * q n‖) := by
        rw [← Finset.expect_add_distrib]
        exact Finset.expect_le_expect (fun n _ => hpoint n)
      _ ≤ ε + (m : ℝ) * ε := by rw [hshift]; exact add_le_add hstep ih
      _ = ((m + 1 : ℕ) : ℝ) * ε := by push_cast; ring

theorem exists_fourier_of_twisted_unit_shift {N : ℕ} [NeZero N]
    (q f : ZMod N → ℂ) (ζ : ℂ) (hq : ∀ n, ‖q n‖ ≤ 1) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hζ : ‖ζ‖ = 1) (hstep : (𝔼 n : ZMod N, ‖q (n + 1) - ζ * q n‖) ≤ 2 / N)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hcorr : ρ ≤ ‖𝔼 n, f n * star (q n)‖) :
    ∃ χ : AddChar (ZMod N) ℂ, ρ ^ 2 / 16 ≤ ‖finiteFourierCoeff f χ‖ := by
  let C (h : ZMod N) := 𝔼 n : ZMod N, q n * star (f (n + h))
  let c := 𝔼 n : ZMod N, q n * star (f n)
  have hc : ρ ≤ ‖c‖ := by
    have heq : c = star (𝔼 n : ZMod N, f n * star (q n)) := by
      rw [← expect_star]
      apply Finset.expect_congr rfl
      intro n _
      simp only [star_mul, star_star]
    rw [heq, norm_star]
    exact hcorr
  have hrow (m : ℕ) : ρ - (m : ℝ) * (2 / N) ≤ ‖C (m : ZMod N)‖ := by
    have hshift : c = 𝔼 n : ZMod N, q (n + m) * star (f (n + m)) :=
      (Fintype.expect_equiv (Equiv.addRight (m : ZMod N)) _ _ (fun _ => rfl)).symm
    have hmul : ζ ^ m * C (m : ZMod N) =
        𝔼 n : ZMod N, (ζ ^ m * q n) * star (f (n + m)) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro n _
      ring
    have herr : ‖c - ζ ^ m * C (m : ZMod N)‖ ≤ (m : ℝ) * (2 / N) := by
      rw [hshift, hmul, ← Finset.expect_sub_distrib]
      apply (RCLike.norm_expect_le (K := ℂ)).trans
      apply le_trans _ (mean_twisted_nat_translate_error q ζ hζ.le hstep m)
      apply Finset.expect_le_expect
      intro n _
      rw [← sub_mul, norm_mul, norm_star]
      exact mul_le_of_le_one_right (norm_nonneg _) (hf _)
    have hnorm : ‖ζ ^ m * C (m : ZMod N)‖ = ‖C (m : ZMod N)‖ := by
      rw [norm_mul, norm_pow, hζ, one_pow, one_mul]
    have htriangle : ‖c‖ ≤ ‖c - ζ ^ m * C (m : ZMod N)‖ + ‖C (m : ZMod N)‖ := by
      rw [← hnorm]
      exact norm_le_norm_sub_add _ _
    linarith
  let δ := ρ / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by dsimp [δ]; linarith
  obtain ⟨K, hK, hKN, hsmall, hratio⟩ := exists_smoothing_scale (NeZero.pos N) hδ hδ1
  let H := cyclicInterval (0 : ZMod N) K
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hdense : (ρ / 8) * Fintype.card (ZMod N) ≤ (H.card : ℝ) := by
    have hh := (div_le_div_iff₀ hKpos hδ).mp hratio
    dsimp only [δ] at hh
    rw [show H.card = K from cyclicInterval_card 0 hKN, ZMod.card]
    nlinarith
  have hlarge (h : ZMod N) (hh : h ∈ H) : ρ / 2 ≤ ‖C h‖ := by
    obtain ⟨m, hm, he⟩ := Finset.mem_image.mp hh
    have hmK : m ≤ K - 1 := by have := Finset.mem_range.mp hm; omega
    have hmreal : (m : ℝ) ≤ δ * N := (Nat.cast_le.mpr hmK).trans hsmall
    have he' : (m : ZMod N) = h := by simpa using he
    have heps : (m : ℝ) * (2 / N) ≤ ρ / 2 := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hNpos).mpr
      dsimp only [δ] at hmreal
      nlinarith
    rw [← he']
    linarith [hrow m]
  have hmass := dense_set_mean_lower_bound H (fun h => ‖C h‖) (fun _ => norm_nonneg _)
    (show 0 ≤ ρ / 2 by positivity) hdense hlarge
  obtain ⟨χ, hχ⟩ := exists_large_fourier_of_mean_cross_correlation q f hq
  refine ⟨χ, ?_⟩
  have heq : (ρ / 8) * (ρ / 2) = ρ ^ 2 / 16 := by ring
  rw [heq] at hmass
  exact hmass.trans hχ

theorem exists_fourier_of_real_linear_phase {N : ℕ} [NeZero N]
    (f : ZMod N → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (β : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hcorr : ρ ≤ ‖𝔼 n, f n * star (cyclicRealLinearPhase β n)‖) :
    ∃ χ : AddChar (ZMod N) ℂ, ρ ^ 2 / 16 ≤ ‖finiteFourierCoeff f χ‖ :=
  exists_fourier_of_twisted_unit_shift (cyclicRealLinearPhase β) f
    (CircleFourier.character (β : CircleFourier.Circle))
    (fun n => (norm_cyclicRealLinearPhase β n).le) hf (CircleFourier.norm_character _)
    (cyclicRealLinearPhase_unit_shift_error β) hρ hρ1 hcorr

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_fourier_of_stepOne_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ {g : (Unit → ℤ) → ℂ} (_E : NativeIntegerExpansion (fun _ : Unit => 1) 1 p g)
        (f : ZMod N → ℂ), (∀ n, ‖f n‖ ≤ 1) →
      Real.exp (-p) ≤ ‖𝔼 n : ZMod N, f n * star (g (fun _ => (n.val : ℤ)))‖ →
      ∃ χ : AddChar (ZMod N) ℂ, Real.exp (-((p + C) ^ C)) ≤ ‖finiteFourierCoeff f χ‖ := by
  obtain ⟨A, _, hphase⟩ := exists_stepOne_scalar_phase_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (2 * (2 * X + Polynomial.C A) ^ A + 16)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp g E f hf hc
  obtain ⟨i, hi⟩ := E.select_sample_correlation Finset.univ
    (fun n : ZMod N => fun _ => (n.val : ℤ)) f hc
  obtain ⟨β, hβ⟩ := hphase (E.model i) (by positivity : 0 ≤ 2 * p) (E.test i)
    ((E.complexity i).mono (by linarith)) f hf (by
      change Real.exp (-(2 * p)) ≤
        ‖𝔼 n : ZMod N, f n * star ((E.test i).eval (fun _ => (n.val : ℤ)))‖
      simpa only [two_mul] using hi)
  let t := (2 * p + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; positivity
  obtain ⟨χ, hχ⟩ := exists_fourier_of_real_linear_phase f hf β
    (Real.exp_pos (-t)) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)) hβ
  have hsmall : Real.exp (-(2 * t + 16)) ≤ Real.exp (-t) ^ 2 / 16 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
    calc
      _ ≤ Real.exp (-(2 * t + 16)) * Real.exp 16 :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (16 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_nat_mul]; congr 1; norm_num
  have hcost : 2 * t + 16 ≤ (p + C) ^ C := by
    simpa [X, t, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨χ, (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans (hsmall.trans hχ)⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.NativeMixedCorrelation

open scoped BigOperators TensorProduct

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_cube_residual_fourier_profiles (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) →
      ∀ M : NativeMixedCorrelation (d + 2) N p f,
      ∃ i : Fin M.mixed.outputDim, ∃ Q : Finset (Fin (d + 1) → ZMod N), Q.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ (d + 1) ≤ (Q.card : ℝ) ∧
        ∃ χ : (Fin (d + 1) → ZMod N) → AddChar (ZMod N) ℂ,
          ∀ u ∈ Q, u 0 ∈ M.shifts ∧ Real.exp (-((p + C) ^ C)) ≤
            ‖finiteFourierCoeff (nativeMixedCubeResidual f M.mixed i u) (χ u)‖ := by
  obtain ⟨a, _, hresidual⟩ := exists_degree_one_cube_residuals d
  obtain ⟨b, _, hfourier⟩ := exists_fourier_of_stepOne_expansion
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  let R := (P + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + R)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf M
  classical
  let q := (p + a) ^ a
  let r := (q + b) ^ b
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hsum : q + r ≤ (p + C) ^ C := by
    simpa [X, P, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hrC : r ≤ (p + C) ^ C := by linarith
  obtain ⟨i, Q, hQ, hdense, hcorr⟩ := hresidual hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf M
  have hchar (u : Fin (d + 1) → ZMod N) (hu : u ∈ Q) :
      ∃ χ : AddChar (ZMod N) ℂ, Real.exp (-r) ≤
        ‖finiteFourierCoeff (nativeMixedCubeResidual f M.mixed i u) χ‖ := by
    obtain ⟨V⟩ := (hcorr u hu).2
    let E := NativeIntegerExpansion.ofTest V.test V.complexity (fun _ => rfl)
    exact hfourier hq E (nativeMixedCubeResidual f M.mixed i u)
      (nativeMixedCubeResidual_norm_le_one f hf M.mixed i u) V.correlation
  let χ (u : Fin (d + 1) → ZMod N) : AddChar (ZMod N) ℂ :=
    if hu : u ∈ Q then Classical.choose (hchar u hu) else 1
  refine ⟨i, Q, hQ, ?_, χ, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (pow_nonneg (Nat.cast_nonneg N) _)).trans hdense
  · intro u hu
    refine ⟨(hcorr u hu).1, ?_⟩
    dsimp only [χ]
    rw [dite_eq_left hu]
    exact (Real.exp_le_exp.mpr (neg_le_neg hrC)).trans (Classical.choose_spec (hchar u hu))

end Erdos3.NativeMixedCorrelation

end

end OAI
