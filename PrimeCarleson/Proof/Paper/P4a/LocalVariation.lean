module

public import PrimeCarleson.Proof.Common.HausdorffYoung
public import PrimeCarleson.Proof.Common.VariationDyadic
public import PrimeCarleson.Proof.Paper.Defs.Basic

/-!
# The local variation of a differentiable family, bounded by the derivative

Source: main paper `e:embed`, L1115–L1127 (proof of `e:embed`).

* `rVariationOn_Ico_le_lintegral`: for `1 ≤ r` and a differentiable `P` with continuous derivative
  `P'`, `V^r(P : [a, b)) ≤ ∫_{[a,b)} |P'|` (the first inequality of L1117: `V^r ≤ V^1` and the
  fundamental theorem of calculus; every chain is bounded by the integrals over disjoint
  intervals);
* `lintegral_enorm_le_hoelder`: `∫_A |g| ≤ |A|^{1/r'} (∫_A |g|^r)^{1/r}` (Hölder);
* `local_variation_hoelder` (the local variation estimate of `e:embed`, L1115–L1127): for the
  intervals `I_j = [j/M, (j+1)/M)`, `0 ≤ j < M`,
  `(∑_j V^r(P : I_j)^r)^{1/r} ≤ M^{-1/r'} ‖P'‖_{L^r(𝕋)}`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- **The first inequality of the local variation estimate of `e:embed`** (L1117): for `1 ≤ r` and
`P` differentiable everywhere with continuous derivative `P'`, `V^r(P : [a, b)) ≤ ∫_{[a,b)} |P'|`.
Every increasing chain `t₀ < ⋯ < t_J` in `[a, b)` has
`(∑ |P(tᵢ) - P(tᵢ₊₁)|^r)^{1/r} ≤ ∑ |P(tᵢ) - P(tᵢ₊₁)|` (`ℓ^r` norms decrease in `r`) and
`|P(tᵢ₊₁) - P(tᵢ)| ≤ ∫_{(tᵢ, tᵢ₊₁]} |P'|`. -/
theorem rVariationOn_Ico_le_lintegral {r : ℝ} (hr : 1 ≤ r) {a b : ℝ} {P P' : ℝ → ℂ}
    (hP : ∀ x, HasDerivAt P (P' x) x) (hP' : Continuous P') :
    rVariationOn r (Ico a b) P ≤ ∫⁻ x in Ico a b, ‖P' x‖ₑ := by
  refine MswTransference.rVariationOn_le fun J t hm hS => ?_
  have h1 : (∑ i : Fin J, ‖P (t i.castSucc) - P (t i.succ)‖ₑ ^ r) ^ (1 / r) ≤
      ∑ i : Fin J, ‖P (t i.castSucc) - P (t i.succ)‖ₑ := by
    have := Common.sum_rpow_rpow_anti_exponent Finset.univ (r := 1) (s := r) one_pos hr
      (fun i : Fin J => ‖P (t i.castSucc) - P (t i.succ)‖ₑ)
    simpa using this
  refine h1.trans ?_
  have h2 : ∀ i : Fin J, ‖P (t i.castSucc) - P (t i.succ)‖ₑ ≤
      ∫⁻ x in Ioc (t i.castSucc) (t i.succ), ‖P' x‖ₑ := by
    intro i
    have hle : t i.castSucc ≤ t i.succ := (hm (Fin.castSucc_lt_succ)).le
    rw [enorm_sub_rev]
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hP x)
      (hP'.intervalIntegrable (t i.castSucc) (t i.succ))
    rw [← this, intervalIntegral.integral_of_le hle]
    exact enorm_integral_le_lintegral_enorm _
  calc _ ≤ ∑ i : Fin J, ∫⁻ x in Ioc (t i.castSucc) (t i.succ), ‖P' x‖ₑ :=
        Finset.sum_le_sum fun i _ => h2 i
    _ = ∫⁻ x in ⋃ i ∈ (Finset.univ : Finset (Fin J)), Ioc (t i.castSucc) (t i.succ), ‖P' x‖ₑ := by
        rw [lintegral_biUnion_finset]
        · intro i _ j _ hij
          simp only [Function.onFun]
          rcases lt_or_gt_of_ne hij with h | h
          · refine Set.disjoint_left.2 fun x hx hx' => ?_
            have : t i.succ ≤ t j.castSucc := hm.monotone (Fin.succ_le_castSucc_iff.2 h)
            linarith [hx.2, hx'.1]
          · refine Set.disjoint_left.2 fun x hx hx' => ?_
            have : t j.succ ≤ t i.castSucc := hm.monotone (Fin.succ_le_castSucc_iff.2 h)
            linarith [hx.1, hx'.2]
        · exact fun i _ => measurableSet_Ioc
    _ ≤ ∫⁻ x in Ico a b, ‖P' x‖ₑ := by
        refine lintegral_mono_set fun x hx => ?_
        simp only [Set.mem_iUnion] at hx
        obtain ⟨i, _, hx⟩ := hx
        exact ⟨((hS i.castSucc).1).trans hx.1.le, lt_of_le_of_lt hx.2 (hS i.succ).2⟩

/-- Hölder's inequality on a set `A`: for a continuous `g` and conjugate exponents `r, r'`,
`∫_A |g| ≤ |A|^{1/r'} (∫_A |g|^r)^{1/r}` (the second inequality of L1117). -/
theorem lintegral_enorm_le_hoelder {r r' : ℝ} (hrr' : r.HolderConjugate r') {A : Set ℝ}
    {g : ℝ → ℂ} (hg : Continuous g) :
    ∫⁻ x in A, ‖g x‖ₑ ≤ volume A ^ (1 / r') * (∫⁻ x in A, ‖g x‖ₑ ^ r) ^ (1 / r) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict A) hrr'
    (f := fun x => ‖g x‖ₑ) (g := fun _ => (1 : ℝ≥0∞)) hg.measurable.enorm.aemeasurable
    aemeasurable_const
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, Measure.restrict_apply_univ,
    one_mul] at h
  rw [mul_comm]
  exact h

/-- The integral over `[0, 1)` is the integral over `(0, 1]`. -/
theorem lintegral_Ico_zero_one_eq_Ioc (f : ℝ → ℝ≥0∞) :
    ∫⁻ x in Ico (0 : ℝ) 1, f x = ∫⁻ x in Ioc (0 : ℝ) 1, f x := by
  rw [Measure.restrict_congr_set Ico_ae_eq_Ioc]

/-- **The local variation estimate of `e:embed`** (L1115–L1127): let `r, r'` be conjugate exponents,
`M ≥ 1`, `I_j = [j/M, (j+1)/M)` for `0 ≤ j < M`, and `P` differentiable with continuous derivative
`P'`. Then `V^r(P : I_j) ≤ ∫_{I_j} |P'| ≤ |I_j|^{1/r'} (∫_{I_j} |P'|^r)^{1/r}` and
`(∑_j V^r(P : I_j)^r)^{1/r} ≤ M^{-1/r'} ‖P'‖_{L^r(𝕋)}`, where `‖P'‖_{L^r(𝕋)}` is the `L^r`
norm over `(0, 1]` (`eLpNorm` for the restriction of Lebesgue measure). Source: main paper
`e:embed`, L1115–L1127; the constant is `1`. -/
theorem local_variation_hoelder {r r' : ℝ} (hrr' : r.HolderConjugate r') {M : ℕ} (hM : 0 < M)
    {P P' : ℝ → ℂ} (hP : ∀ x, HasDerivAt P (P' x) x) (hP' : Continuous P') :
    (∑ j : Fin M, rVariationOn r (Ico ((j : ℝ) / M) (((j : ℝ) + 1) / M)) P ^ r) ^ (1 / r) ≤
      ENNReal.ofReal ((M : ℝ) ^ (-(1 / r'))) *
        eLpNorm P' (ENNReal.ofReal r) (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hr1 : 1 < r := hrr'.lt
  have hr0 : 0 < r := by linarith
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  set I : Fin M → Set ℝ := fun j => Ico ((j : ℝ) / M) (((j : ℝ) + 1) / M) with hI
  have hvol : ∀ j : Fin M, volume (I j) = ENNReal.ofReal (1 / M) := by
    intro j
    rw [hI]
    simp only [Real.volume_Ico]
    congr 1
    field_simp
    ring
  have hV : ∀ j : Fin M, rVariationOn r (I j) P ^ r ≤
      ENNReal.ofReal (1 / M) ^ (r / r') * ∫⁻ x in I j, ‖P' x‖ₑ ^ r := by
    intro j
    have h1 := (rVariationOn_Ico_le_lintegral hr1.le (a := (j : ℝ) / M) (b := ((j : ℝ) + 1) / M)
      hP hP').trans (lintegral_enorm_le_hoelder hrr' (A := I j) hP')
    rw [hvol] at h1
    calc rVariationOn r (I j) P ^ r
        ≤ (ENNReal.ofReal (1 / M) ^ (1 / r') * (∫⁻ x in I j, ‖P' x‖ₑ ^ r) ^ (1 / r)) ^ r :=
          ENNReal.rpow_le_rpow h1 hr0.le
      _ = ENNReal.ofReal (1 / M) ^ (r / r') * ∫⁻ x in I j, ‖P' x‖ₑ ^ r := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
            one_div_mul_cancel hr0.ne', ENNReal.rpow_one, show 1 / r' * r = r / r' by ring]
  have hsum : ∑ j : Fin M, ∫⁻ x in I j, ‖P' x‖ₑ ^ r ≤ ∫⁻ x in Ico (0 : ℝ) 1, ‖P' x‖ₑ ^ r := by
    have hd : (↑(Finset.univ : Finset (Fin M)) : Set (Fin M)).PairwiseDisjoint I := by
      intro j _ j' _ hjj'
      simp only [Function.onFun, hI]
      have key : ∀ j j' : Fin M, j < j' → Disjoint (I j) (I j') := by
        intro j j' h
        refine Set.disjoint_left.2 fun x hx hx' => ?_
        have h1 : (j : ℝ) + 1 ≤ j' := by exact_mod_cast h
        have h2 : ((j : ℝ) + 1) / M ≤ (j' : ℝ) / M := div_le_div_of_nonneg_right h1 hMr.le
        simp only [hI, Set.mem_Ico] at hx hx'
        linarith [hx.2, hx'.1]
      rcases lt_or_gt_of_ne hjj' with h | h
      · exact key j j' h
      · exact (key j' j h).symm
    rw [← lintegral_biUnion_finset (μ := volume) hd (fun j _ => measurableSet_Ico)]
    refine lintegral_mono_set fun x hx => ?_
    simp only [Set.mem_iUnion, hI, Set.mem_Ico] at hx
    obtain ⟨j, _, h1, h2⟩ := hx
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    have hj1 : (j : ℝ) + 1 ≤ M := by exact_mod_cast j.2
    refine ⟨le_trans (div_nonneg hj0 hMr.le) h1, lt_of_lt_of_le h2 ?_⟩
    rw [div_le_one hMr]
    exact hj1
  have hrpow : (ENNReal.ofReal (1 / M) ^ (r / r')) ^ (1 / r) =
      ENNReal.ofReal ((M : ℝ) ^ (-(1 / r'))) := by
    rw [← ENNReal.rpow_mul, show r / r' * (1 / r) = 1 / r' by field_simp,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (one_div_pos.2 hrr'.symm.pos).le,
      Real.rpow_neg hMr.le, ← Real.inv_rpow hMr.le, one_div]
  have hL : eLpNorm P' (ENNReal.ofReal r) (volume.restrict (Ioc (0 : ℝ) 1)) =
      (∫⁻ x in Ico (0 : ℝ) 1, ‖P' x‖ₑ ^ r) ^ (1 / r) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hr0).ne' ENNReal.ofReal_ne_top
      hP'.aestronglyMeasurable, ENNReal.toReal_ofReal hr0.le, lintegral_Ico_zero_one_eq_Ioc]
  calc (∑ j : Fin M, rVariationOn r (I j) P ^ r) ^ (1 / r)
      ≤ (ENNReal.ofReal (1 / M) ^ (r / r') * ∑ j : Fin M, ∫⁻ x in I j, ‖P' x‖ₑ ^ r) ^ (1 / r) := by
        refine ENNReal.rpow_le_rpow ?_ (by positivity)
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun j _ => hV j
    _ ≤ (ENNReal.ofReal (1 / M) ^ (r / r') * ∫⁻ x in Ico (0 : ℝ) 1, ‖P' x‖ₑ ^ r) ^ (1 / r) := by
        gcongr
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), hrpow, hL]

end PrimeCarleson.Proof.Paper
