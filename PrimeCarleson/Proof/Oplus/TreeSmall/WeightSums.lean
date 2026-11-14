module

public import PrimeCarleson.Proof.Oplus.TreeSmall.DensityBound
public import PrimeCarleson.Proof.Oplus.EnergyIncrement.TailWeight

/-!
# Sums of the weights `(1 + |x - c(I)|/|I|)^{-N}` over disjoint intervals of one scale

The elementary estimate behind "`∑_{P ∈ T : |I| = 2^m} (1 + |x - c(I)|/|I|)^{-N} ≤ C`"
(Source: [O+] `treeestimatelargeintervals`, L2201–L2252, here L2242-L2243) and behind the
summation over the tiles of one scale in `treeestimatesmallintervals` ([O+] L2118-L2125):

`sum_one_add_abs_zpow_le`: if `I_i` (`i ∈ F`) are pairwise disjoint dyadic intervals of the same
length `ℓ`, and `|y - x| ≥ d ≥ 0` for every `y ∈ ⋃ I_i`, then
`∑_i (1 + |c(I_i) - x|/ℓ)^{-N} ≤ (3/2)^N (2/(N - 1)) (1 + d/ℓ)^{-(N-1)}` for `N ≥ 2`.
Proof: each term is at most `(3/2)^N ∫_{I_i} ℓ⁻¹ (1 + |y - x|/ℓ)^{-N} dy`; the sum of these
integrals
is the integral over the union, which lies in `{|y - x| ≥ d}`, whose integral is computed from the
two tails of `ℓ⁻¹ (1 + |y - x|/ℓ)^{-N}` (`EnergyIncrement/TailWeight.lean`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- **Sums of weights over disjoint intervals of one scale.** -/
theorem sum_one_add_abs_zpow_le {ι : Type*} (F : Finset ι) (I : ι → Dyadic) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hlen : ∀ i ∈ F, (I i).length = ℓ)
    (hdisj : (F : Set ι).PairwiseDisjoint fun i => (I i).toSet) {N : ℕ} (hN : 2 ≤ N) (x : ℝ)
    {d : ℝ} (hd : 0 ≤ d) (hdist : ∀ i ∈ F, ∀ y ∈ (I i).toSet, d ≤ |y - x|) :
    ∑ i ∈ F, (1 + |(I i).center - x| / ℓ) ^ (-(N : ℤ)) ≤
      (3 / 2) ^ N * (2 * (1 / ((N : ℝ) - 1)) * (1 + d / ℓ) ^ (-((N : ℤ) - 1))) := by
  classical
  set g : ℝ → ℝ := fun y => ℓ⁻¹ * (1 + |y - x| / ℓ) ^ (-(N : ℤ)) with hg
  have hgint : Integrable g := (integrable_one_add_abs_div_zpow hN x hℓ).const_mul _
  have hgnn : ∀ y, 0 ≤ g y := fun y => by simp only [hg]; positivity
  have hA : ∀ i ∈ F, (1 + |(I i).center - x| / ℓ) ^ (-(N : ℤ)) ≤
      (3 / 2) ^ N * ∫ y in (I i).toSet, g y := by
    intro i hi
    have hℓi := hlen i hi
    have hconst : ∀ y ∈ (I i).toSet, ℓ⁻¹ * (1 + |(I i).center - x| / ℓ) ^ (-(N : ℤ)) ≤
        (3 / 2) ^ N * g y := by
      intro y hy
      have hyc : |y - (I i).center| ≤ ℓ / 2 := by
        have := Dyadic.abs_sub_center_le hy
        rwa [hℓi] at this
      have h1 : |y - x| ≤ |(I i).center - x| + ℓ / 2 := by
        calc |y - x| = |(y - (I i).center) + ((I i).center - x)| := by ring_nf
          _ ≤ |y - (I i).center| + |(I i).center - x| := abs_add_le _ _
          _ ≤ _ := by linarith
      have hb : 1 + |y - x| / ℓ ≤ 3 / 2 * (1 + |(I i).center - x| / ℓ) := by
        have : |y - x| / ℓ ≤ |(I i).center - x| / ℓ + 1 / 2 := by
          rw [← sub_le_iff_le_add', ← sub_div, div_le_iff₀ hℓ]
          nlinarith
        have h0 : 0 ≤ |(I i).center - x| / ℓ := by positivity
        linarith
      have hpa : 0 < (1 + |(I i).center - x| / ℓ) ^ N := by positivity
      have hpb : 0 < (1 + |y - x| / ℓ) ^ N := by positivity
      have key : ((1 + |(I i).center - x| / ℓ) ^ N)⁻¹ ≤
          (3 / 2) ^ N * ((1 + |y - x| / ℓ) ^ N)⁻¹ := by
        rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hpa hpb]
        calc 1 * (1 + |y - x| / ℓ) ^ N ≤ (3 / 2 * (1 + |(I i).center - x| / ℓ)) ^ N := by
              rw [one_mul]; exact pow_le_pow_left₀ (by positivity) hb N
          _ = _ := by rw [mul_pow]
      simp only [hg, zpow_neg, zpow_natCast]
      calc ℓ⁻¹ * ((1 + |(I i).center - x| / ℓ) ^ N)⁻¹
          ≤ ℓ⁻¹ * ((3 / 2) ^ N * ((1 + |y - x| / ℓ) ^ N)⁻¹) :=
            mul_le_mul_of_nonneg_left key (by positivity)
        _ = _ := by ring
    have hint : IntegrableOn (fun y => (3 / 2 : ℝ) ^ N * g y) (I i).toSet :=
      (hgint.const_mul _).integrableOn
    have h2 : ∫ y in (I i).toSet, ℓ⁻¹ * (1 + |(I i).center - x| / ℓ) ^ (-(N : ℤ)) =
        (1 + |(I i).center - x| / ℓ) ^ (-(N : ℤ)) := by
      rw [setIntegral_const, smul_eq_mul, Dyadic.volume_real_toSet, hℓi]
      field_simp
    have h3 := setIntegral_mono_on (integrableOn_const (by simp [Dyadic.volume_toSet])) hint
      (I i).measurableSet_toSet hconst
    rw [h2, integral_const_mul] at h3
    exact h3
  have hae : (⋃ i ∈ F, (I i).toSet) ≤ᵐ[volume] (Iio (x - d) ∪ Ioi (x + d)) := by
    have h1 := (Set.countable_singleton (x - d)).ae_notMem volume
    have h2 := (Set.countable_singleton (x + d)).ae_notMem volume
    filter_upwards [h1, h2] with y hy1 hy2 hy
    obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.1 hy
    have h3 := hdist i hi y hyi
    rw [le_abs] at h3
    rcases h3 with h3 | h3
    · right
      refine lt_of_le_of_ne (by linarith) ?_
      intro h; exact hy2 (by simp [← h])
    · left
      refine lt_of_le_of_ne (by linarith) ?_
      intro h; exact hy1 (by simp [h])
  have hdisjLR : Disjoint (Iio (x - d)) (Ioi (x + d)) :=
    Set.disjoint_left.2 fun y hy hy' => by
      have := hy.out; have := hy'.out; linarith
  have hL := integral_Iio_inv_mul_one_add_abs_div_zpow hN x hℓ (p := x - d) (by linarith)
  have hR := integral_Ioi_inv_mul_one_add_abs_div_zpow hN x hℓ (q := x + d) (by linarith)
  calc ∑ i ∈ F, (1 + |(I i).center - x| / ℓ) ^ (-(N : ℤ))
      ≤ ∑ i ∈ F, (3 / 2) ^ N * ∫ y in (I i).toSet, g y := Finset.sum_le_sum hA
    _ = (3 / 2) ^ N * ∫ y in ⋃ i ∈ F, (I i).toSet, g y := by
        rw [← Finset.mul_sum, integral_biUnion_finset F (fun i _ => (I i).measurableSet_toSet)
          hdisj (fun i _ => hgint.integrableOn)]
    _ ≤ (3 / 2) ^ N * ∫ y in Iio (x - d) ∪ Ioi (x + d), g y := by
        exact mul_le_mul_of_nonneg_left
          (setIntegral_mono_set hgint.integrableOn (Eventually.of_forall hgnn) hae)
          (by positivity)
    _ = (3 / 2) ^ N * ((∫ y in Iio (x - d), g y) + ∫ y in Ioi (x + d), g y) := by
        rw [setIntegral_union hdisjLR measurableSet_Ioi hgint.integrableOn hgint.integrableOn]
    _ = (3 / 2) ^ N * (2 * (1 / ((N : ℝ) - 1)) * (1 + d / ℓ) ^ (-((N : ℤ) - 1))) := by
        have e1 : (∫ y in Iio (x - d), g y) =
            1 / ((N : ℝ) - 1) * (1 + d / ℓ) ^ (-((N : ℤ) - 1)) := by
          simp only [hg]
          convert hL using 3
          ring
        have e2 : (∫ y in Ioi (x + d), g y) =
            1 / ((N : ℝ) - 1) * (1 + d / ℓ) ^ (-((N : ℤ) - 1)) := by
          simp only [hg]
          convert hR using 3
          ring
        rw [e1, e2]; ring

end PrimeCarleson.Proof.Oplus
