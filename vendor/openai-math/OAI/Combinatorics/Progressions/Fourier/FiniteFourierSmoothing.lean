/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Fourier/FiniteFourierSmoothing.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.GroupTheory.Index
public import OAI.Combinatorics.Progressions.Estimates.CorrelationDerivative
public import OAI.Combinatorics.Progressions.Estimates.UnitExpansionCorrelation
@[expose] public section

namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

noncomputable def finiteFourierCoeff (f : H → ℂ) (χ : AddChar H ℂ) : ℂ :=
  𝔼 x, f x * star (χ x)

theorem addChar_sub_star (χ : AddChar H ℂ) (x y : H) :
    χ (x - y) = χ x * star (χ y) := by
  rw [AddChar.map_sub_eq_div, div_eq_mul_inv, AddChar.inv_apply_eq_conj]
  rfl

theorem star_finiteFourierCoeff (f : H → ℂ) (χ : AddChar H ℂ) :
    star (finiteFourierCoeff f χ) = 𝔼 x, star (f x) * χ x := by
  rw [finiteFourierCoeff, ← expect_star]
  apply Finset.expect_congr rfl
  intro x _
  simp only [star_mul, star_star]
  ring

theorem finiteFourier_inversion (f : H → ℂ) (x : H) :
    (∑ χ : AddChar H ℂ, finiteFourierCoeff f χ * χ x) = f x := by
  classical
  calc
    _ = 𝔼 y, f y * (∑ χ : AddChar H ℂ, χ (x - y)) := by
      simp only [finiteFourierCoeff, Finset.expect_mul]
      rw [← Finset.expect_sum_comm]
      apply Finset.expect_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _
      rw [addChar_sub_star]
      ring
    _ = 𝔼 y, if x = y then (Fintype.card H : ℂ) * f x else 0 := by
      apply Finset.expect_congr rfl
      intro y _
      rw [AddChar.sum_apply_eq_ite]
      by_cases hxy : x = y
      · subst y
        simp [mul_comm]
      · simp [sub_eq_zero, hxy]
    _ = _ := by
      have hc : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      rw [Fintype.expect_eq_sum_div_card, Finset.sum_eq_single x]
      · simp [hc]
      · intro y _ hy
        simp only [ite_eq_right (Ne.symm hy)]
      · simp

theorem finiteFourier_inner (f g : H → ℂ) :
    (∑ χ : AddChar H ℂ, finiteFourierCoeff f χ * star (finiteFourierCoeff g χ)) =
      𝔼 x, f x * star (g x) := by
  simp_rw [star_finiteFourierCoeff, Finset.mul_expect]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro x _
  calc
    _ = (∑ χ : AddChar H ℂ, finiteFourierCoeff f χ * χ x) * star (g x) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ _
      ring
    _ = _ := by rw [finiteFourier_inversion]

theorem finiteFourier_parseval (f : H → ℂ) :
    (∑ χ : AddChar H ℂ, ‖finiteFourierCoeff f χ‖ ^ 2) = 𝔼 x, ‖f x‖ ^ 2 := by
  have h := congrArg Complex.re (finiteFourier_inner f f)
  simpa only [Complex.re_sum, expect_re, mul_star_re_eq_norm_sq] using h

end Erdos3

end

section

open Finset
open scoped BigOperators

namespace Erdos3

variable {G : Type*} [Fintype G] [AddCommGroup G]

noncomputable def fourierL1 (f : G → ℂ) : ℝ :=
  ∑ ψ : AddChar G ℂ, ‖finiteFourierCoeff f ψ‖

theorem norm_sub_translate_le_fourier_sum (f : G → ℂ) (t x : G) :
    ‖f (x - t) - f x‖ ≤
      ∑ ψ : AddChar G ℂ,
        ‖finiteFourierCoeff f ψ‖ * ‖ψ (-t) - 1‖ := by
  classical
  rw [← finiteFourier_inversion f (x - t),
    ← finiteFourier_inversion f x, ← Finset.sum_sub_distrib]
  calc
    ‖∑ ψ : AddChar G ℂ,
        (finiteFourierCoeff f ψ * ψ (x - t) -
          finiteFourierCoeff f ψ * ψ x)‖
        ≤ ∑ ψ : AddChar G ℂ,
            ‖finiteFourierCoeff f ψ * ψ (x - t) -
              finiteFourierCoeff f ψ * ψ x‖ :=
          norm_sum_le _ _
    _ = ∑ ψ : AddChar G ℂ,
          ‖finiteFourierCoeff f ψ‖ * ‖ψ (-t) - 1‖ := by
      apply sum_congr rfl
      intro ψ _
      have hfactor :
          finiteFourierCoeff f ψ * ψ (x - t) -
              finiteFourierCoeff f ψ * ψ x =
            (finiteFourierCoeff f ψ * ψ x) * (ψ (-t) - 1) := by
        have hmap : ψ (x - t) = ψ x * ψ (-t) := by
          rw [sub_eq_add_neg, ψ.map_add_eq_mul]
        rw [hmap]
        ring
      rw [hfactor, norm_mul, norm_mul, AddChar.norm_apply, mul_one]

omit [Fintype G] in

lemma norm_character_neg_sub_one [Finite G] (psi : AddChar G ℂ) (t : G) :
    ‖psi (-t) - 1‖ = ‖1 - psi t‖ := by
  rw [psi.map_neg_eq_inv]
  have hne : psi t ≠ 0 := by
    intro h
    have := AddChar.norm_apply psi t
    simp [h] at this
  calc
    ‖(psi t)⁻¹ - 1‖ = ‖(psi t)⁻¹ * (1 - psi t)‖ := by
      congr 1
      field_simp
    _ = ‖1 - psi t‖ := by
      rw [norm_mul, norm_inv, AddChar.norm_apply, inv_one, one_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

open Finset Function Real
open scoped BigOperators ComplexConjugate NNReal

namespace Erdos3.Chang

variable {G : Type*} [Fintype G] [AddCommGroup G]

noncomputable def spectrumSum (A : Finset G) (psi : AddChar G ℂ) : ℂ :=
  ∑ x ∈ A, psi x

noncomputable def largeSpectrum (A : Finset G) (eta : ℝ) : Finset (AddChar G ℂ) :=
  Finset.univ.filter fun psi ↦ eta * A.card ≤ ‖spectrumSum A psi‖

@[simp]
theorem mem_largeSpectrum {A : Finset G} {eta : ℝ} {psi : AddChar G ℂ} :
    psi ∈ largeSpectrum A eta ↔ eta * A.card ≤ ‖spectrumSum A psi‖ := by
  simp [largeSpectrum]

end Erdos3.Chang

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

variable [Fintype G]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def finiteSetAverage (A : Finset G) (f : G → ℂ) (x : G) : ℂ :=
  𝔼 a ∈ A, f (x - a)

noncomputable def setFourierMultiplier (A : Finset G) (psi : AddChar G ℂ) : ℂ :=
  𝔼 a ∈ A, star (psi a)

theorem finiteFourierCoeff_translate (f : G → ℂ) (a : G) (psi : AddChar G ℂ) :
    finiteFourierCoeff (fun x => f (x - a)) psi = star (psi a) * finiteFourierCoeff f psi := by
  unfold finiteFourierCoeff
  calc
    (𝔼 x, f (x - a) * star (psi x)) = 𝔼 x, f x * star (psi (x + a)) := by
      apply Fintype.expect_equiv (Equiv.subRight a)
      intro x
      simp
    _ = star (psi a) * 𝔼 x, f x * star (psi x) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      rw [AddChar.map_add_eq_mul, star_mul]
      ring

theorem finiteFourierCoeff_finiteSetAverage
    (A : Finset G) (f : G → ℂ) (psi : AddChar G ℂ) :
    finiteFourierCoeff (finiteSetAverage A f) psi =
      setFourierMultiplier A psi * finiteFourierCoeff f psi := by
  unfold finiteFourierCoeff finiteSetAverage
  simp_rw [Finset.expect_mul]
  rw [Finset.expect_comm]
  change (𝔼 a ∈ A, finiteFourierCoeff (fun x => f (x - a)) psi) = _
  simp_rw [finiteFourierCoeff_translate]
  rw [← Finset.expect_mul]
  rfl

omit [Fintype G] in
theorem setFourierMultiplier_eq (A : Finset G) (psi : AddChar G ℂ) :
    setFourierMultiplier A psi = star (Chang.spectrumSum A psi) / (A.card : ℂ) := by
  simp only [setFourierMultiplier, Finset.expect_eq_sum_div_card, Chang.spectrumSum, star_sum]

omit [Fintype G] in
theorem norm_setFourierMultiplier (A : Finset G) (psi : AddChar G ℂ) :
    ‖setFourierMultiplier A psi‖ = ‖Chang.spectrumSum A psi‖ / A.card := by
  rw [setFourierMultiplier_eq, norm_div, norm_star, Complex.norm_natCast]

theorem norm_setFourierMultiplier_le_one {A : Finset G} (hA : A.Nonempty)
    (psi : AddChar G ℂ) : ‖setFourierMultiplier A psi‖ ≤ 1 := by
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  simp only [norm_star, AddChar.norm_apply, Finset.expect_const hA]
  exact le_rfl

theorem mem_largeSpectrum_iff_le_multiplier {A : Finset G} (hA : A.Nonempty)
    (eta : ℝ) (psi : AddChar G ℂ) :
    psi ∈ Chang.largeSpectrum A eta ↔ eta ≤ ‖setFourierMultiplier A psi‖ := by
  have hcard : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  rw [Chang.mem_largeSpectrum, norm_setFourierMultiplier, le_div_iff₀ hcard]

noncomputable def iteratedFiniteSetAverage (A : Finset G) (f : G → ℂ) : ℕ → G → ℂ
  | 0 => f
  | n + 1 => finiteSetAverage A (iteratedFiniteSetAverage A f n)

theorem finiteFourierCoeff_iteratedFiniteSetAverage
    (A : Finset G) (f : G → ℂ) (psi : AddChar G ℂ) (n : ℕ) :
    finiteFourierCoeff (iteratedFiniteSetAverage A f n) psi =
      setFourierMultiplier A psi ^ n * finiteFourierCoeff f psi := by
  induction n with
  | zero => simp [iteratedFiniteSetAverage]
  | succ n ih =>
      rw [iteratedFiniteSetAverage, finiteFourierCoeff_finiteSetAverage, ih, pow_succ]
      ring

end Erdos3

end

section

noncomputable section

open Finset Function Real
open scoped BigOperators ComplexConjugate NNReal

namespace Erdos3.RelativeChangSanders

variable {G : Type*} [Fintype G] [AddCommGroup G]

def IsWeightedDissociated (mu : G → ℝ) (K : ℝ)
    (Delta : Finset (AddChar G ℂ)) : Prop :=
  ∀ u : AddChar G ℂ → ℂ,
    (∀ psi ∈ Delta, ‖u psi‖ ≤ 1) →
      ∑ x : G, mu x *
        ∏ psi ∈ Delta, (1 + (u psi * psi x).re) ≤ exp K

def relativeLargeSpectrum (mu f : G → ℝ) (eta : ℝ) :
    Finset (AddChar G ℂ) :=
    Finset.univ.filter fun psi ↦
    eta * (∑ x : G, f x * mu x) ≤
      ‖∑ x : G, (f x * mu x : ℝ) * psi x‖

@[simp] theorem mem_relativeLargeSpectrum {mu f : G → ℝ} {eta : ℝ}
    {psi : AddChar G ℂ} :
    psi ∈ relativeLargeSpectrum mu f eta ↔
      eta * (∑ x : G, f x * mu x) ≤
        ‖∑ x : G, (f x * mu x : ℝ) * psi x‖ := by
  simp [relativeLargeSpectrum]

end Erdos3.RelativeChangSanders

end

end

section

namespace Erdos3.Chang

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

omit [Fintype G] in
theorem spectrumSum_map_subRight (T : Finset G) (z : G) (psi : AddChar G ℂ) :
    spectrumSum (T.map (Equiv.subRight z).toEmbedding) psi =
      spectrumSum T psi * psi (-z) := by
  unfold spectrumSum
  rw [Finset.sum_map]
  simp only [Equiv.toEmbedding_apply, Equiv.subRight_apply,
    sub_eq_add_neg, AddChar.map_add_eq_mul]
  rw [Finset.sum_mul]

theorem norm_spectrumSum_map_subRight (T : Finset G) (z : G) (psi : AddChar G ℂ) :
    ‖spectrumSum (T.map (Equiv.subRight z).toEmbedding) psi‖ = ‖spectrumSum T psi‖ := by
  rw [spectrumSum_map_subRight, norm_mul, AddChar.norm_apply, mul_one]

theorem mem_largeSpectrum_map_subRight_iff
    (T : Finset G) (z : G) (eta : ℝ) (psi : AddChar G ℂ) :
    psi ∈ largeSpectrum (T.map (Equiv.subRight z).toEmbedding) eta ↔
      psi ∈ largeSpectrum T eta := by
  rw [mem_largeSpectrum, mem_largeSpectrum, Finset.card_map, norm_spectrumSum_map_subRight]

end Erdos3.Chang

end

section

open scoped BigOperators

namespace Erdos3

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem iteratedFiniteSetAverage_translate_le
    {X : Finset G} (hX : X.Nonempty) (m : ℕ) (f : G → ℂ)
    {eta theta : ℝ} (heta : 0 ≤ eta) (htheta : 0 ≤ theta) (t x : G)
    (hphase : ∀ psi ∈ Chang.largeSpectrum X eta, ‖1 - psi t‖ ≤ theta) :
    ‖iteratedFiniteSetAverage X f m (x - t) - iteratedFiniteSetAverage X f m x‖ ≤
      (theta + 2 * eta ^ m) * fourierL1 f := by
  apply (norm_sub_translate_le_fourier_sum (iteratedFiniteSetAverage X f m) t x).trans
  calc
    (∑ psi : AddChar G ℂ,
        ‖finiteFourierCoeff (iteratedFiniteSetAverage X f m) psi‖ * ‖psi (-t) - 1‖) ≤
        ∑ psi : AddChar G ℂ, (theta + 2 * eta ^ m) * ‖finiteFourierCoeff f psi‖ := by
      apply Finset.sum_le_sum
      intro psi _
      rw [finiteFourierCoeff_iteratedFiniteSetAverage, norm_mul, norm_pow,
        norm_character_neg_sub_one]
      have hmu := norm_setFourierMultiplier_le_one hX psi
      by_cases hlarge : eta ≤ ‖setFourierMultiplier X psi‖
      · have hpow : ‖setFourierMultiplier X psi‖ ^ m ≤ 1 :=
          pow_le_one₀ (norm_nonneg _) hmu
        have hp := hphase psi ((mem_largeSpectrum_iff_le_multiplier hX eta psi).2 hlarge)
        calc
          ‖setFourierMultiplier X psi‖ ^ m * ‖finiteFourierCoeff f psi‖ * ‖1 - psi t‖ ≤
              1 * ‖finiteFourierCoeff f psi‖ * theta := by gcongr
          _ ≤ (theta + 2 * eta ^ m) * ‖finiteFourierCoeff f psi‖ := by
            have hepow : 0 ≤ eta ^ m := pow_nonneg heta m
            have hf : 0 ≤ ‖finiteFourierCoeff f psi‖ := norm_nonneg _
            nlinarith
      · have htail : ‖setFourierMultiplier X psi‖ ^ m ≤ eta ^ m :=
          pow_le_pow_left₀ (norm_nonneg _) (le_of_not_ge hlarge) m
        have hchord : ‖1 - psi t‖ ≤ 2 := by
          calc
            ‖1 - psi t‖ ≤ ‖(1 : ℂ)‖ + ‖psi t‖ := norm_sub_le _ _
            _ = 2 := by norm_num
        calc
          ‖setFourierMultiplier X psi‖ ^ m * ‖finiteFourierCoeff f psi‖ * ‖1 - psi t‖ ≤
              eta ^ m * ‖finiteFourierCoeff f psi‖ * 2 := by gcongr
          _ ≤ (theta + 2 * eta ^ m) * ‖finiteFourierCoeff f psi‖ := by
            have hf : 0 ≤ ‖finiteFourierCoeff f psi‖ := norm_nonneg _
            nlinarith
    _ = (theta + 2 * eta ^ m) * fourierL1 f := by rw [fourierL1, Finset.mul_sum]

theorem translate_le_of_iteratedFiniteSetAverage_approx
    {X : Finset G} (hX : X.Nonempty) (m : ℕ) (f : G → ℂ)
    {delta eta theta : ℝ} (heta : 0 ≤ eta) (htheta : 0 ≤ theta) (t x : G)
    (happrox : ∀ y, ‖iteratedFiniteSetAverage X f m y - f y‖ ≤ delta)
    (hphase : ∀ psi ∈ Chang.largeSpectrum X eta, ‖1 - psi t‖ ≤ theta) :
    ‖f (x - t) - f x‖ ≤ 2 * delta + (theta + 2 * eta ^ m) * fourierL1 f := by
  let p := iteratedFiniteSetAverage X f m
  have hdecomp : f (x - t) - f x =
      (f (x - t) - p (x - t)) + (p (x - t) - p x) + (p x - f x) := by ring
  rw [hdecomp]
  calc
    ‖(f (x - t) - p (x - t)) + (p (x - t) - p x) + (p x - f x)‖ ≤
        ‖f (x - t) - p (x - t)‖ + ‖p (x - t) - p x‖ + ‖p x - f x‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ delta + ((theta + 2 * eta ^ m) * fourierL1 f) + delta := by
      apply add_le_add
      · apply add_le_add
        · simpa only [norm_sub_rev] using happrox (x - t)
        · exact iteratedFiniteSetAverage_translate_le hX m f heta htheta t x hphase
      · exact happrox x
    _ = 2 * delta + (theta + 2 * eta ^ m) * fourierL1 f := by ring

end Erdos3

end

end OAI
