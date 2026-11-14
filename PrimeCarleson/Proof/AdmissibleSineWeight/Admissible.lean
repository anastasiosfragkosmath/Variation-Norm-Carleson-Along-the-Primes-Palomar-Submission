module

public import PrimeCarleson.Frozen.Admissible
public import PrimeCarleson.Frozen.SineWeight

/-!
# The sine weight is admissible

First conjunct of the Appendix A.1 lemma (`sources/Variational_Carleson.tex`, lines 2826–2886):
for `0 < α < 1` and an integer `q₀ ≥ 3`, the weight `v(n) = 1 + α sin(2πn/q₀)` is admissible.

The weight is a trigonometric polynomial, and the sine is a combination of the two characters
`e(±n/q₀)`. Hence it equals, exactly, the major-arc model with coefficients
`S(a/q) = 1` for `q = 1`, `S(1/q₀) = α/(2i)`, `S((q₀ - 1)/q₀) = -α/(2i)` and `S = 0` elsewhere,
truncated at `M ≡ q₀`, and the Gowers-norm error vanishes identically.

The witnesses are `C = 2` for the upper normalization, and `C = 1`, `ν = 5`, `s = 3`,
`M ≡ q₀` for the approximation.
-/

public section

namespace PrimeCarleson.Proof

open Filter

/-- The number of integers in the half-open window `(⌊C₀ N⌋, ⌊C₀ N + N⌋]` is `N`. -/
theorem card_Ioc_floor_window (C₀ : ℝ) (h : 0 ≤ C₀) (N : ℕ) :
    (Finset.Ioc ⌊C₀ * N⌋₊ ⌊C₀ * N + N⌋₊).card = N := by
  have h0 : (0 : ℝ) ≤ C₀ * N := by positivity
  rw [Nat.card_Ioc, Nat.floor_add_natCast h0]
  omega

/-- `e` is trivial on integers. -/
theorem e_intCast (n : ℤ) : e (n : ℝ) = 1 := by
  unfold e
  have : 2 * (Real.pi : ℂ) * Complex.I * ((n : ℝ) : ℂ) = (n : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

/-- The reduced fraction `a / q` of a coprime pair has denominator `q` and numerator `a`. -/
theorem den_num_natCast_div (a q : ℕ) (hq : 0 < q) (h : Nat.Coprime a q) :
    ((a : ℚ) / q).den = q ∧ ((a : ℚ) / q).num = a := by
  have h' : Nat.Coprime (a : ℤ).natAbs (q : ℤ).natAbs := by simpa using h
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have h1 := Rat.den_div_eq_of_coprime hq' h'
  have h2 := Rat.num_div_eq_of_coprime hq' h'
  push_cast at h1 h2
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- The coefficients `S` with `S(x) = 1` if `x.den = 1`, `S(1/q₀) = α/(2i)`,
`S((q₀ - 1)/q₀) = -α/(2i)` and `S(x) = 0` otherwise. -/
@[expose] noncomputable def sineWeightCoeff (α : ℝ) (q₀ : ℕ) (x : ℚ) : ℂ :=
  if x.den = 1 then 1
  else if x.den = q₀ then
    (if x.num = 1 then (α : ℂ) / (2 * Complex.I)
     else if x.num = (q₀ : ℤ) - 1 then -((α : ℂ) / (2 * Complex.I)) else 0)
  else 0

/-- The major-arc model with the coefficients `sineWeightCoeff` and truncation `q₀` is exactly
the sine weight. -/
theorem majorArcModel_sineWeightCoeff (α : ℝ) (q₀ : ℕ) (hq₀ : 3 ≤ q₀) (n : ℤ) :
    majorArcModel (sineWeightCoeff α q₀) q₀ n =
      ((1 + α * Real.sin (2 * Real.pi * n / q₀) : ℝ) : ℂ) := by
  unfold majorArcModel
  have hne : (1 : ℕ) ≠ q₀ := by omega
  rw [Finset.sum_eq_add 1 q₀ hne]
  · have h1 : ∑ a ∈ (Finset.Icc 1 1).filter (fun a => Nat.Coprime a 1),
        sineWeightCoeff α q₀ ((a : ℚ) / ((1 : ℕ) : ℚ)) * e ((n : ℝ) * a / ((1 : ℕ) : ℝ)) = 1 := by
      simp [sineWeightCoeff, e_intCast]
    rw [h1]
    have hc1 : Nat.Coprime 1 q₀ := Nat.coprime_one_left _
    have hc2 : Nat.Coprime (q₀ - 1) q₀ := by
      obtain ⟨k, hk⟩ : ∃ k, q₀ = k + 1 := ⟨q₀ - 1, by omega⟩
      subst hk
      simp
    have d1 := den_num_natCast_div 1 q₀ (by omega) hc1
    have d2 := den_num_natCast_div (q₀ - 1) q₀ (by omega) hc2
    have hne2 : (1 : ℕ) ≠ q₀ - 1 := by omega
    have m1 : (1 : ℕ) ∈ (Finset.Icc 1 q₀).filter (fun a => Nat.Coprime a q₀) :=
      Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨le_rfl, by omega⟩, hc1⟩
    have m2 : (q₀ - 1 : ℕ) ∈ (Finset.Icc 1 q₀).filter (fun a => Nat.Coprime a q₀) :=
      Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, by omega⟩, hc2⟩
    have h2 : ∑ a ∈ (Finset.Icc 1 q₀).filter (fun a => Nat.Coprime a q₀),
        sineWeightCoeff α q₀ ((a : ℚ) / (q₀ : ℚ)) * e ((n : ℝ) * a / (q₀ : ℝ)) =
        (α : ℂ) / (2 * Complex.I) * e ((n : ℝ) * ((1 : ℕ) : ℝ) / q₀)
          - (α : ℂ) / (2 * Complex.I) * e ((n : ℝ) * ((q₀ - 1 : ℕ) : ℝ) / q₀) := by
      rw [Finset.sum_eq_add 1 (q₀ - 1) hne2]
      · have s1 : sineWeightCoeff α q₀ (((1 : ℕ) : ℚ) / (q₀ : ℚ)) = (α : ℂ) / (2 * Complex.I) := by
          have : ¬ q₀ = 1 := by omega
          unfold sineWeightCoeff
          rw [d1.1, d1.2]
          simp [this]
        have s2 : sineWeightCoeff α q₀ (((q₀ - 1 : ℕ) : ℚ) / (q₀ : ℚ)) =
            -((α : ℂ) / (2 * Complex.I)) := by
          have h3 : ¬ q₀ = 1 := by omega
          have h5 : ((q₀ - 1 : ℕ) : ℤ) = (q₀ : ℤ) - 1 := by omega
          have h6 : ¬ ((q₀ : ℤ) - 1 = 1) := by omega
          unfold sineWeightCoeff
          rw [d2.1, d2.2]
          simp [h3, h5, h6]
        rw [s1, s2]
        ring
      · intro a ha hne
        obtain ⟨hne1, hne2'⟩ := hne
        simp only [Finset.mem_filter, Finset.mem_Icc] at ha
        have d := den_num_natCast_div a q₀ (by omega) ha.2
        have h3 : ¬ q₀ = 1 := by omega
        have h5 : ¬ (a : ℤ) = 1 := by omega
        have h6 : ¬ (a : ℤ) = (q₀ : ℤ) - 1 := by omega
        have : sineWeightCoeff α q₀ ((a : ℚ) / (q₀ : ℚ)) = 0 := by
          unfold sineWeightCoeff
          rw [d.1, d.2]
          simp [h3, h5, h6]
        rw [this, zero_mul]
      · intro h
        exact absurd m1 h
      · intro h
        exact absurd m2 h
    rw [h2]
    have hq : (0 : ℝ) < q₀ := by exact_mod_cast (by omega : 0 < q₀)
    have hqC : (q₀ : ℂ) ≠ 0 := by exact_mod_cast (by omega : q₀ ≠ 0)
    have key : e ((n : ℝ) * ((q₀ - 1 : ℕ) : ℝ) / q₀) = e (-((n : ℝ) / q₀)) := by
      unfold e
      have hcast : (((q₀ - 1 : ℕ) : ℝ)) = (q₀ : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        simp
      have : 2 * (Real.pi : ℂ) * Complex.I * (((n : ℝ) * ((q₀ - 1 : ℕ) : ℝ) / q₀ : ℝ) : ℂ) =
          (n : ℂ) * (2 * Real.pi * Complex.I) +
            2 * (Real.pi : ℂ) * Complex.I * ((-((n : ℝ) / q₀) : ℝ) : ℂ) := by
        rw [hcast]
        push_cast
        field_simp
        ring
      rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]
    rw [key]
    set x : ℝ := 2 * Real.pi * n / q₀ with hxdef
    have e1 : e ((n : ℝ) * ((1 : ℕ) : ℝ) / q₀) = Complex.exp ((x : ℂ) * Complex.I) := by
      unfold e
      congr 1
      rw [hxdef]
      push_cast
      ring
    have e2 : e (-((n : ℝ) / q₀)) = Complex.exp (-(x : ℂ) * Complex.I) := by
      unfold e
      congr 1
      rw [hxdef]
      push_cast
      ring
    rw [e1, e2]
    have hsin := Complex.two_sin (x : ℂ)
    have hcast : ((1 + α * Real.sin x : ℝ) : ℂ) = 1 + α * Complex.sin x := by
      push_cast
      rfl
    rw [hcast]
    have hI : (2 * Complex.I) ≠ 0 := by simp
    have hs : Complex.sin x =
        (Complex.exp ((x : ℂ) * Complex.I) - Complex.exp (-(x : ℂ) * Complex.I)) /
          (2 * Complex.I) := by
      rw [eq_div_iff hI]
      linear_combination Complex.I * hsin +
        (Complex.exp (-(x : ℂ) * Complex.I) - Complex.exp ((x : ℂ) * Complex.I)) * Complex.I_sq
    rw [hs]
    ring
  · intro q hq hq'
    apply Finset.sum_eq_zero
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha hq
    have hd := (den_num_natCast_div a q (by omega) ha.2).1
    simp [sineWeightCoeff, hd, hq'.1, hq'.2]
  · intro h
    exact absurd (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩) h
  · intro h
    exact absurd (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩) h

/-- Every iterated difference of the zero function vanishes. -/
theorem multDiff_zero (s : ℕ) (h : Fin s → ℤ) (x : ℤ) :
    multDiff s h (0 : ℤ → ℂ) x = 0 := by
  induction s generalizing x with
  | zero => rfl
  | succ k ih => simp [multDiff, ih]

/-- The Gowers norm of the zero sequence is zero. -/
theorem gowersNorm_zero (s : ℕ+) : gowersNorm s 0 = 0 := by
  unfold gowersNorm
  simp only [Finsupp.coe_zero, multDiff_zero, tsum_zero, Complex.zero_re]
  rw [Real.zero_rpow (by positivity)]

/-- **Appendix A.1 lemma, first conjunct.** For `0 < α < 1` and an integer `q₀ ≥ 3`, the weight
`v(n) = 1 + α sin(2πn/q₀)` is admissible. -/
theorem sineWeight_admissible (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1) (q₀ : ℕ) (hq₀ : 3 ≤ q₀) :
    Admissible (sineWeight α q₀) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    unfold sineWeight
    have := Real.neg_one_le_sin (2 * Real.pi * n / q₀)
    nlinarith
  · refine ⟨2, by norm_num, fun C₀ hC₀ => ?_⟩
    refine Filter.limsup_le_of_le (by isBoundedDefault) (Filter.Eventually.of_forall fun N => ?_)
    have hw : ∀ n, sineWeight α q₀ n ≤ 2 := by
      intro n
      unfold sineWeight
      have := Real.sin_le_one (2 * Real.pi * n / q₀)
      nlinarith
    have hsum : ∑ n ∈ Finset.Ioc ⌊C₀ * N⌋₊ ⌊C₀ * N + N⌋₊, sineWeight α q₀ n ≤ 2 * N := by
      calc _ ≤ (Finset.Ioc ⌊C₀ * N⌋₊ ⌊C₀ * N + N⌋₊).card • (2 : ℝ) :=
            Finset.sum_le_card_nsmul _ _ _ (fun n _ => hw n)
        _ = 2 * N := by rw [card_Ioc_floor_window C₀ hC₀ N]; simp [mul_comm]
    apply ENNReal.ofReal_le_ofReal
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      calc (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc ⌊C₀ * N⌋₊ ⌊C₀ * N + N⌋₊, sineWeight α q₀ n
          ≤ (N : ℝ)⁻¹ * (2 * N) := by gcongr
        _ = 2 := by field_simp
  · refine ⟨1, sineWeightCoeff α q₀, ?_, 5, by norm_num, 3, le_rfl, fun _ => q₀, ?_, ?_⟩
    · intro ε hε
      refine ⟨q₀, fun x => ?_⟩
      have hq : (1 : ℝ) ≤ q₀ := by exact_mod_cast (by omega : 1 ≤ q₀)
      have hq0 : (0 : ℝ) < q₀ := by linarith
      have hα2 : ‖(α : ℂ) / (2 * Complex.I)‖ ≤ 1 := by
        simp [abs_of_pos hα₀]
        linarith
      have hden : (0 : ℝ) < (x.den : ℝ) := by exact_mod_cast x.den_pos
      by_cases h1 : x.den = 1
      · have : ‖sineWeightCoeff α q₀ x‖ = 1 := by
          unfold sineWeightCoeff
          rw [ite_eq_left h1]
          simp
        rw [this, h1]
        simpa using hq
      · by_cases h2 : x.den = q₀
        · have hrp : (q₀ : ℝ) * (q₀ : ℝ) ^ (ε - 1) = (q₀ : ℝ) ^ ε := by
            rw [Real.rpow_sub_one hq0.ne']
            field_simp
          have hge : 1 ≤ (q₀ : ℝ) ^ ε := Real.one_le_rpow hq hε.le
          have hden' : (x.den : ℝ) = q₀ := by exact_mod_cast h2
          rw [hden', hrp]
          have hnorm : ‖sineWeightCoeff α q₀ x‖ ≤ 1 := by
            unfold sineWeightCoeff
            rw [ite_eq_right h1, ite_eq_left h2]
            split_ifs
            · exact hα2
            · simpa [norm_neg] using hα2
            · simp
          linarith
        · have : sineWeightCoeff α q₀ x = 0 := by
            unfold sineWeightCoeff
            rw [ite_eq_right h1, ite_eq_right h2]
          rw [this, norm_zero]
          positivity
    · intro ε hε
      refine ⟨q₀, fun N => ?_⟩
      have hN : (1 : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
      have := Real.one_le_rpow hN hε.le
      have hq : (0 : ℝ) ≤ q₀ := Nat.cast_nonneg _
      nlinarith
    · refine Filter.Eventually.of_forall fun N => ?_
      have hzero : restrictInterval N (fun n => ((sineWeight α q₀ n.toNat : ℝ) : ℂ) -
          majorArcModel (sineWeightCoeff α q₀) q₀ n) = 0 := by
        ext n
        simp only [restrictInterval, Finsupp.indicator_apply, Finsupp.coe_zero, Pi.zero_apply]
        split_ifs with hn
        · rw [majorArcModel_sineWeightCoeff α q₀ hq₀ n]
          have hn0 : 0 ≤ n := by
            have := (Finset.mem_Icc.1 hn).1
            omega
          have : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn0
          unfold sineWeight
          rw [this]
          simp
        · rfl
      unfold gowersNormInterval
      rw [hzero, gowersNorm_zero, zero_div]
      exact mul_nonneg zero_le_one (Real.rpow_nonneg (Real.log_natCast_nonneg _) _)

end PrimeCarleson.Proof
