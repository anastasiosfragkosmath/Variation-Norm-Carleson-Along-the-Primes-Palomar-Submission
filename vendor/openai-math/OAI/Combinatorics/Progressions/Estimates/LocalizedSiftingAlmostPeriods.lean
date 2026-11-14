/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/LocalizedSiftingAlmostPeriods.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Fourier.QuarticBohrProgression
public import OAI.Combinatorics.Progressions.Fourier.RationalBohrWidth
public import OAI.Combinatorics.Progressions.Geometry.DifferenceEventSupport
public import OAI.Combinatorics.Progressions.Sampling.QuarticSamplingBudget
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

end Erdos3

end

section

namespace Erdos3.CyclicCrootSisask

theorem sqrt_le_exp_of_le_exp_two_mul {beta p : ℝ} (hbeta : beta ≤ Real.exp (2 * p)) :
    Real.sqrt beta ≤ Real.exp p := by
  apply (Real.sqrt_le_left (Real.exp_pos p).le).mpr
  simpa only [two_mul, Real.exp_add, pow_two] using hbeta

theorem old_frequency_scale_le_regularity {epsilon p d : ℝ}
    (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) (hp : 0 ≤ p) (hd : 0 < d) :
    epsilon * Real.exp (-p) / (6400 * d) ≤ 1 / (200 * d) := by
  have he : Real.exp (-p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hprod : epsilon * Real.exp (-p) ≤ 1 :=
    (mul_le_mul_of_nonneg_left he hepsilon).trans (by simpa using hepsilon1)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem chosen_scales_error_le
    {epsilon p d D dim beta : ℝ} (hepsilon : 0 < epsilon) (hd : 0 < d)
    (hD : 0 ≤ D) (hdim0 : 0 ≤ dim) (hdim : dim ≤ D)
    (hbeta : beta ≤ Real.exp (2 * p)) :
    2 * (epsilon / 8) +
      (dim * (epsilon * Real.exp (-p) / (8 * (D + 1))) +
        800 * d * (epsilon * Real.exp (-p) / (6400 * d)) +
        2 * (1 / 2 : ℝ) ^ spectralIterations epsilon p) * Real.sqrt beta ≤ epsilon := by
  have hcancel : Real.exp (-p) * Real.exp p = 1 := by
    rw [← Real.exp_add]
    simp
  have hDpos : 0 < D + 1 := by linarith
  have hnew : dim * (epsilon * Real.exp (-p) / (8 * (D + 1))) * Real.exp p ≤ epsilon / 8 := by
    calc
      _ ≤ (D + 1) * (epsilon * Real.exp (-p) / (8 * (D + 1))) * Real.exp p := by
        gcongr
        linarith
      _ = epsilon / 8 := by
        field_simp
        nlinarith [hcancel]
  have hold : 800 * d * (epsilon * Real.exp (-p) / (6400 * d)) * Real.exp p = epsilon / 8 := by
    field_simp
    nlinarith [hcancel]
  have htail : 2 * (1 / 2 : ℝ) ^ spectralIterations epsilon p * Real.exp p ≤ epsilon / 8 := by
    have h := half_pow_spectralIterations_mul_exp_le (p := p) hepsilon
    linarith
  have hsqrt := sqrt_le_exp_of_le_exp_two_mul hbeta
  have hfactor : 0 ≤ dim * (epsilon * Real.exp (-p) / (8 * (D + 1))) +
      800 * d * (epsilon * Real.exp (-p) / (6400 * d)) +
      2 * (1 / 2 : ℝ) ^ spectralIterations epsilon p := by positivity
  have hbound := mul_le_mul_of_nonneg_left hsqrt hfactor
  nlinarith

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open RelativeChangSanders
open scoped NNReal Pointwise

variable {N : ℕ} [NeZero N]

theorem exists_quartic_local_almostPeriods
    (B : CyclicBohr.Set N) (hBpos : 0 < B.radius) (hBreg : B.IsRankRegular)
    {A L : Finset (ZMod N)} (hA : A.Nonempty) (hL : L.Nonempty) (M : Finset (ZMod N))
    {epsilon p : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hp : 0 ≤ p)
    (hratio : (M.card : ℝ) / L.card ≤ Real.exp (2 * p))
    (hdoubling : ((A + B.carrier).card : ℝ) ≤ (2 * Real.exp p) * A.card) :
    let D := rankQuarticFactor epsilon * (p + 1) ^ 4
    let d := max B.rank 1
    let a : ℝ≥0 := (100 * ((2 * d : ℕ) : ℝ≥0) * ((2 * (⌈D⌉₊ + 1) + 1 : ℕ) : ℝ≥0))⁻¹
    let sigma := epsilon * Real.exp (-p) / (6400 * (d : ℝ))
    let r := epsilon * Real.exp (-p) / (8 * (D + 1))
    let u := setAverageTranslate L (setAverageTranslate A (realSetIndicator M))
    ∃ R : CyclicBohr.Set N, R.IsRankRegular ∧ (R.rank : ℝ) ≤ B.rank + D ∧
      min (sigma * ((a : ℝ) * B.radius / 2)) r / 2 ≤ R.radius ∧
      R.radius ≤ r ∧
      R.carrier ⊆ B.carrier ∧ ∀ t ∈ R.carrier, ∀ x, |u (x + t) - u x| ≤ epsilon := by
  intro D d a sigma r u
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg (rankQuarticFactor_pos epsilon).le (pow_nonneg (by positivity) _)
  have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by simp [d])
  have hsigma : 0 < sigma := by dsimp [sigma]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  let sigmaN : ℝ≥0 := ⟨sigma, hsigma.le⟩
  let rN : ℝ≥0 := ⟨r, hr.le⟩
  have hsigreg : sigmaN ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0) := by
    have h := old_frequency_scale_le_regularity hepsilon.le hepsilon1 hp hd
    change sigma ≤ ((1 : ℝ) / (100 * ((2 * max B.rank 1 : ℕ) : ℝ)))
    dsimp [sigma, d] at h ⊢
    push_cast at h ⊢
    convert h using 1
    ring
  let q := spectralIterations epsilon p
  let k := crootSisaskSampleSize (convolutionMomentOrder M L) (((epsilon / 8) / q) / Real.exp 1)
  obtain ⟨T, R, hT, hTB, hcount, hRreg, hRrank, hRwidth, hRupper, hRB, hshift⟩ :=
    exists_local_bohr_triple_almostPeriods_relative B hBpos hBreg hA B.carrier_nonempty hL
      (fun _ h => h) M q (spectralIterations_pos epsilon p)
      (by positivity : 0 < epsilon / 8) sigmaN rN hsigma hr hsigreg
  have hcount' : (B.carrier.card : ℝ) / (2 * (2 * Real.exp p) ^ k) ≤ T.card :=
    samplingDensity_le_of_smallDoubling hA B.carrier_nonempty k (by positivity) hdoubling hcount
  have hk : (k : ℝ) ≤ samplingCubicFactor epsilon * (p + 1) ^ 3 :=
    local_sample_size_le_cubic M L hepsilon hepsilon1 hp hratio
  have hdim : localChangDimension B T (1 / 2) ≤ D :=
    local_dimension_le_quartic_of_cubic_sampling B hT hp (samplingCubicFactor_pos epsilon).le k hk hcount'
  have hdim0 : 0 ≤ localChangDimension B T (1 / 2) := by
    have hTpos : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
    have hcard : (T.card : ℝ) ≤ B.carrier.card := by exact_mod_cast Finset.card_le_card hTB
    have hratio1 : 1 ≤ 2 * (B.carrier.card : ℝ) / T.card := by
      rw [le_div_iff₀ hTpos]
      linarith
    have hlog := Real.log_nonneg hratio1
    unfold localChangDimension
    positivity
  have ha : a ≤ localChangBaseScale B T (1 / 2) :=
    localChangBaseScale_ge_of_dimension_le B T (1 / 2) D hdim
  refine ⟨R, hRreg, hRrank.trans (add_le_add le_rfl hdim), ?_, hRupper, hRB, ?_⟩
  · apply le_trans _ hRwidth
    change min (sigma * ((a : ℝ) * B.radius / 2)) r / 2 ≤
      min (sigma * ((localChangBaseScale B T (1 / 2) : ℝ) * B.radius / 2)) r / 2
    gcongr
  · intro t ht x
    apply (hshift t ht x).trans
    exact chosen_scales_error_le hepsilon hd hD hdim0 hdim hratio

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators
open CyclicCrootSisask

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CyclicCrootSisask

open scoped NNReal Pointwise

noncomputable def almostPeriodicityWidthConstant (epsilon : ℝ) : ℝ :=
  10240000000 * (rankQuarticFactor epsilon + 1) / epsilon + 8

theorem almostPeriodicityWidthConstant_pos {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < almostPeriodicityWidthConstant epsilon := by
  have hC := rankQuarticFactor_pos epsilon
  unfold almostPeriodicityWidthConstant
  positivity

theorem rankQuarticFactor_le_widthConstant {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    rankQuarticFactor epsilon ≤ almostPeriodicityWidthConstant epsilon := by
  have hC := rankQuarticFactor_pos epsilon
  have hprod := mul_le_mul_of_nonneg_left hepsilon1 hC.le
  have hquot : rankQuarticFactor epsilon ≤
      10240000000 * (rankQuarticFactor epsilon + 1) / epsilon := by
    rw [le_div_iff₀ hepsilon]
    nlinarith
  unfold almostPeriodicityWidthConstant
  linarith

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open scoped Pointwise NNReal

noncomputable def quarticBogolyubovConstant : ℝ :=
  3 * almostPeriodicityWidthConstant (1 / 2)

theorem quarticBogolyubovConstant_pos : 0 < quarticBogolyubovConstant := by
  exact mul_pos (by norm_num) (almostPeriodicityWidthConstant_pos (by norm_num))

theorem exists_quartic_bogolyubov {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) {p : ℝ} (hp : 0 ≤ p)
    (hdensity : Real.exp (-p) * N ≤ (A.card : ℝ)) :
    ∃ R : CyclicBohr.Set N, R.IsRankRegular ∧ 0 < R.radius ∧ R.radius ≤ 1 ∧
      (R.rank : ℝ) ≤ 1 + quarticBogolyubovConstant * (p + 1) ^ 4 ∧
      Real.exp (-(quarticBogolyubovConstant * (p + 1))) ≤ R.radius ∧
      R.carrier ⊆ 2 • A - 2 • A := by
  have hApos : (0 : ℝ) < A.card :=
    (mul_pos (Real.exp_pos _) (by exact_mod_cast NeZero.pos N)).trans_le hdensity
  have hA : A.Nonempty := Finset.card_pos.mp (by exact_mod_cast hApos)
  have hNle : (N : ℝ) ≤ Real.exp p * A.card := by
    calc
      (N : ℝ) = Real.exp p * (Real.exp (-p) * N) := by
        rw [← mul_assoc, ← Real.exp_add]
        simp
      _ ≤ Real.exp p * A.card := mul_le_mul_of_nonneg_left hdensity (Real.exp_pos p).le
  have hratio : ((A - A).card : ℝ) / (-A).card ≤ Real.exp (2 * p) := by
    rw [Finset.card_neg, div_le_iff₀ hApos]
    calc
      ((A - A).card : ℝ) ≤ N := by
        exact_mod_cast (show (A - A).card ≤ N by
          simpa only [ZMod.card] using Finset.card_le_univ (A - A))
      _ ≤ Real.exp p * A.card := hNle
      _ ≤ Real.exp (2 * p) * A.card :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hApos.le
  have hdoubling : ((A + (CyclicBohr.Set.whole : CyclicBohr.Set N).carrier).card : ℝ) ≤
      (2 * Real.exp p) * A.card := by
    calc
      ((A + (CyclicBohr.Set.whole : CyclicBohr.Set N).carrier).card : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast (show (A + (CyclicBohr.Set.whole : CyclicBohr.Set N).carrier).card ≤ N by
          simpa only [ZMod.card] using Finset.card_le_univ
            (A + (CyclicBohr.Set.whole : CyclicBohr.Set N).carrier))
      _ ≤ Real.exp p * A.card := hNle
      _ ≤ (2 * Real.exp p) * A.card := by nlinarith [Real.exp_pos p]
  obtain ⟨R, hRreg, hRrank, hRwidth, hRupper, _, hshift⟩ :=
    exists_quartic_local_almostPeriods CyclicBohr.Set.whole (by norm_num)
      CyclicBohr.Set.isRankRegular_whole hA hA.neg (A - A)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hp hratio hdoubling
  let C₀ := rankQuarticFactor (1 / 2)
  let D := C₀ * (p + 1) ^ 4
  let a : ℝ≥0 := (100 * 2 * ((2 * (⌈D⌉₊ + 1) + 1 : ℕ) : ℝ≥0))⁻¹
  have hC₀ : 0 < C₀ := rankQuarticFactor_pos _
  have hD : 0 ≤ D := by dsimp [D]; positivity
  simp only [CyclicBohr.Set.rank_whole, CyclicBohr.Set.radius_whole, max_self,
    Nat.cast_one, Nat.cast_ofNat, mul_one] at hRrank hRwidth hRupper
  change (R.rank : ℝ) ≤ 1 + D at hRrank
  change min (((1 / 2 : ℝ) * Real.exp (-p) / 6400) * ((a : ℝ) / 2))
      (((1 / 2 : ℝ) * Real.exp (-p)) / (8 * (D + 1))) / 2 ≤ R.radius at hRwidth
  change R.radius ≤ ((1 / 2 : ℝ) * Real.exp (-p)) / (8 * (D + 1)) at hRupper
  have ha : 1 / (1000 * (1 : ℝ) * (D + 1)) ≤ (a : ℝ) := by
    simpa only [a, NNReal.coe_inv, NNReal.coe_mul, NNReal.coe_natCast,
      NNReal.coe_ofNat, mul_one] using BohrWidthBudget.selector_scale_lower_bound
        (d := 1) (by norm_num) hD
  have hRrat : ((1 / 2 : ℝ) * Real.exp (-p)) /
      (10240000000 * (D + 1)) ≤ R.radius := by
    have h := BohrWidthBudget.rational_width_lower_bound
      (u := (1 / 2 : ℝ) * Real.exp (-p)) (d := 1) (D := D) (w := 1) (v := 1)
      (by positivity) (by norm_num) hD (by norm_num) (by norm_num) (by norm_num) ha
    apply le_trans _ hRwidth
    simpa only [one_pow, mul_one] using h
  have hC : 0 < almostPeriodicityWidthConstant (1 / 2) :=
    almostPeriodicityWidthConstant_pos (by norm_num)
  have hRexp : Real.exp (-(almostPeriodicityWidthConstant (1 / 2) *
      (1 + p + Real.log 3))) ≤ R.radius := by
    have h := BohrWidthBudget.rational_width_ge_exponential
      (epsilon := 1 / 2) (C := C₀) (p := p) (d := 1) (w := 1)
      (by norm_num) hC₀.le hp (by norm_num) (by norm_num)
    apply le_trans _ hRrat
    simpa only [almostPeriodicityWidthConstant, D, C₀, one_pow, mul_one, one_mul,
      show (2 : ℝ) + 1 = 3 by norm_num] using h
  have hlog : Real.log 3 ≤ (2 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at h ⊢
    exact h
  have hbudget : almostPeriodicityWidthConstant (1 / 2) * (1 + p + Real.log 3) ≤
      quarticBogolyubovConstant * (p + 1) := by
    have h := mul_le_mul_of_nonneg_left hlog hC.le
    unfold quarticBogolyubovConstant
    nlinarith [mul_nonneg hC.le hp]
  have hwidth : Real.exp (-(quarticBogolyubovConstant * (p + 1))) ≤ R.radius :=
    (Real.exp_le_exp.mpr (neg_le_neg hbudget)).trans hRexp
  refine ⟨R, hRreg, (Real.exp_pos _).trans_le hwidth, ?_, ?_, hwidth, ?_⟩
  · apply hRupper.trans
    apply (div_le_one (by positivity)).mpr
    have h := Real.exp_le_one_iff.mpr (by linarith : -p ≤ 0)
    nlinarith
  · have hC₀C := rankQuarticFactor_le_widthConstant
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    have hCC : C₀ ≤ quarticBogolyubovConstant := by
      dsimp [C₀, quarticBogolyubovConstant]
      linarith
    have hh : C₀ * (p + 1) ^ 4 ≤ quarticBogolyubovConstant * (p + 1) ^ 4 :=
      mul_le_mul_of_nonneg_right hCC (by positivity)
    exact hRrank.trans (add_le_add le_rfl hh)
  · intro t ht
    have hprob : |differenceEventProbability A A (A - A) t - 1| ≤ (1 / 2 : ℝ) := by
      simpa only [← differenceEventProbability_eq_triple, zero_add,
        differenceEventProbability_self_zero A hA] using hshift t ht 0
    apply mem_fourfold_difference_of_probability_pos A t
    have h := (abs_le.mp hprob).1
    linarith

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal
open CyclicCrootSisask

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CyclicCrootSisask

open scoped Pointwise

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open scoped Pointwise

noncomputable def quarticBogolyubovProgressionConstant : ℝ :=
  11 * (quarticBogolyubovConstant + 2) ^ 2

theorem quarticBogolyubovProgressionConstant_pos :
    0 < quarticBogolyubovProgressionConstant := by
  have h := quarticBogolyubovConstant_pos
  unfold quarticBogolyubovProgressionConstant
  positivity

theorem exists_quartic_bogolyubov_progression {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) {p : ℝ} (hp : 0 ≤ p)
    (hdensity : Real.exp (-p) * N ≤ (A.card : ℝ)) :
    ∃ Q : BohrProgression.CyclicCenteredGAP N,
      (Q.rank : ℝ) ≤ 2 + quarticBogolyubovConstant * (p + 1) ^ 4 ∧
      Q.Proper ∧ Q.carrier ⊆ 2 • A - 2 • A ∧
      Real.exp (-(quarticBogolyubovProgressionConstant * (p + 1) ^ 8)) * N ≤
        (Q.carrier.card : ℝ) := by
  obtain ⟨B, _hreg, hB, hB1, hrank, hwidth, hsub⟩ := exists_quartic_bogolyubov A hp hdensity
  obtain ⟨Q, hr, hQ, hQB, hcard⟩ := BohrProgression.exists_proper_progression_of_quartic_bounds
    B quarticBogolyubovConstant_pos.le hp hB hB1 hrank hwidth
  exact ⟨Q, hr, hQ, hQB.trans hsub, hcard⟩

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal
open CyclicCrootSisask

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

end OAI
