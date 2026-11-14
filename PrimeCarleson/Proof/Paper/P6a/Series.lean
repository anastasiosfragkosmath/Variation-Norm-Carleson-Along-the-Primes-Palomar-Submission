module

public import PrimeCarleson.Proof.Paper.P6a.Basic
public import PrimeCarleson.Proof.Paper.P4a.LpCount

/-!
# Infinite sums in `V^r` and in `ℓ^p`

Two small general lemmas, used wherever the proof of `p:red-var` sums infinitely many pieces:

* `rVariationOn_tsum_le`: if `G = ∑_i F_i` pointwise (as a `HasSum`), `V^r(G) ≤ ∑_i V^r(F_i)`
  (the chain sums are continuous in the finitely many values, so the finite triangle inequality
  passes to the limit);
* `eLpNorm_count_tsum_le`: Minkowski's inequality in `ℓ^p(ℤ)` for a countable sum of
  `ℝ≥0∞`-valued sequences (monotone convergence from the finite sums).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Common

/-- **Triangle inequality for `V^r` for infinite sums**: if `∑_i F_i(t) = G(t)` for every `t`,
then `V^r(G) ≤ ∑_i V^r(F_i)` (`r ≥ 1`). -/
theorem rVariationOn_tsum_le {ι : Type*} {r : ℝ} (hr : 1 ≤ r) (S : Set ℝ) (F : ι → ℝ → ℂ)
    (G : ℝ → ℂ) (hG : ∀ t, HasSum (fun i => F i t) (G t)) :
    rVariationOn r S G ≤ ∑' i, rVariationOn r S (F i) := by
  classical
  refine MswTransference.rVariationOn_le fun J t ht hS => ?_
  set Φ : (Fin J → ℂ) → ℝ≥0∞ := fun v => (∑ i, ‖v i‖ₑ ^ r) ^ (1 / r) with hΦ
  have hcont : Continuous Φ := by
    refine ENNReal.continuous_rpow_const.comp ?_
    refine continuous_finsetSum _ fun i _ => ?_
    exact ENNReal.continuous_rpow_const.comp ((continuous_apply i).enorm)
  have hlim : Filter.Tendsto (fun s : Finset ι => Φ fun i =>
      (∑ j ∈ s, F j) (t i.castSucc) - (∑ j ∈ s, F j) (t i.succ)) Filter.atTop
      (nhds (Φ fun i => G (t i.castSucc) - G (t i.succ))) := by
    refine (hcont.tendsto _).comp (tendsto_pi_nhds.2 fun i => ?_)
    simp only [Finset.sum_apply]
    have h1 : Filter.Tendsto (fun s : Finset ι => ∑ j ∈ s, F j (t i.castSucc)) Filter.atTop
        (nhds (G (t i.castSucc))) := hG _
    have h2 : Filter.Tendsto (fun s : Finset ι => ∑ j ∈ s, F j (t i.succ)) Filter.atTop
        (nhds (G (t i.succ))) := hG _
    exact h1.sub h2
  refine le_of_tendsto hlim (Filter.Eventually.of_forall fun s => ?_)
  calc Φ (fun i => (∑ j ∈ s, F j) (t i.castSucc) - (∑ j ∈ s, F j) (t i.succ))
      ≤ rVariationOn r S (∑ j ∈ s, F j) := MswTransference.le_rVariationOn ht hS
    _ ≤ ∑ j ∈ s, rVariationOn r S (F j) := rVariationOn_sum_le s hr S F
    _ ≤ ∑' j, rVariationOn r S (F j) := ENNReal.sum_le_tsum s

/-- **Minkowski's inequality in `ℓ^p(ℤ)` for countable sums** of `ℝ≥0∞`-valued sequences,
`p ≥ 1`: `‖∑_i F_i‖_{ℓ^p} ≤ ∑_i ‖F_i‖_{ℓ^p}`. -/
theorem eLpNorm_count_tsum_le {ι : Type*} [Countable ι] (F : ι → ℤ → ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm (fun x => ∑' i, F i x) (ENNReal.ofReal p) Measure.count ≤
      ∑' i, eLpNorm (F i) (ENNReal.ofReal p) Measure.count := by
  classical
  have hp0 : 0 < p := by linarith
  set G : Finset ι → ℤ → ℝ≥0∞ := fun s x => ∑ i ∈ s, F i x with hGdef
  have hGmono : ∀ s t : Finset ι, s ⊆ t → ∀ x, G s x ≤ G t x := fun s t hst x =>
    Finset.sum_le_sum_of_subset hst
  have hdir : Directed (· ≤ ·) (fun s : Finset ι => fun x => (G s x) ^ p) := by
    intro s t
    exact ⟨s ∪ t, fun x => ENNReal.rpow_le_rpow (hGmono _ _ Finset.subset_union_left x) hp0.le,
      fun x => ENNReal.rpow_le_rpow (hGmono _ _ Finset.subset_union_right x) hp0.le⟩
  have hrpow : ∀ (q : ℝ), 0 < q → ∀ (A : Finset ι → ℝ≥0∞), (⨆ s, A s) ^ q = ⨆ s, A s ^ q := by
    intro q hq A
    exact Monotone.map_iSup_of_continuousAt ENNReal.continuous_rpow_const.continuousAt
      (fun a b hab => ENNReal.rpow_le_rpow hab hq.le) (ENNReal.zero_rpow_of_pos hq)
  have hsup : ∀ x, ∑' i, F i x = ⨆ s : Finset ι, G s x := fun x => ENNReal.tsum_eq_iSup_sum
  rw [eLpNorm_count_eq_tsum_enn _ hp0]
  have h1 : ∑' x, (∑' i, F i x) ^ p = ⨆ s : Finset ι, ∑' x, (G s x) ^ p := by
    calc ∑' x, (∑' i, F i x) ^ p = ∫⁻ x, ⨆ s : Finset ι, (G s x) ^ p ∂Measure.count := by
          rw [lintegral_count]
          refine tsum_congr fun x => ?_
          rw [hsup x, hrpow p hp0 (fun s => G s x)]
      _ = ⨆ s : Finset ι, ∫⁻ x, (G s x) ^ p ∂Measure.count :=
          lintegral_iSup_directed (fun s => (measurable_of_countable _).aemeasurable) hdir
      _ = _ := by simp_rw [lintegral_count]
  rw [h1, hrpow (1 / p) (by positivity) (fun s => ∑' x, (G s x) ^ p)]
  refine iSup_le fun s => ?_
  have h2 : (∑' x, (G s x) ^ p) ^ (1 / p) =
      eLpNorm (fun x => ∑ i ∈ s, F i x) (ENNReal.ofReal p) Measure.count := by
    rw [eLpNorm_count_eq_tsum_enn _ hp0]
  rw [h2]
  exact (eLpNorm_count_finset_sum_le s F hp).trans (ENNReal.sum_le_tsum s)

/-- Minkowski's inequality in `ℓ^p(ℤ)` for two `ℝ≥0∞`-valued sequences, `p ≥ 1`. -/
theorem eLpNorm_count_add_le (F G : ℤ → ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm (fun x => F x + G x) (ENNReal.ofReal p) Measure.count ≤
      eLpNorm F (ENNReal.ofReal p) Measure.count + eLpNorm G (ENNReal.ofReal p) Measure.count := by
  have := eLpNorm_count_finset_sum_le (Finset.univ : Finset (Fin 2))
    (fun i => if i = 0 then F else G) hp
  simpa [Fin.sum_univ_two] using this

/-- The geometric series `∑_j C (2^j)^{-c} ≤ C (1 - 2^{-c})^{-1}` in `ℝ≥0∞`, `C ≥ 0`, `c > 0`. -/
theorem tsum_ofReal_dyadic_le (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) :
    ∑' j : ℕ, ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ (-c)) ≤
      ENNReal.ofReal (C * (1 - (2 : ℝ) ^ (-c))⁻¹) := by
  set q : ℝ := (2 : ℝ) ^ (-c) with hq
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hj : ∀ j : ℕ, ((2 : ℝ) ^ j) ^ (-c) = q ^ j := by
    intro j
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num)]
    congr 1; ring
  simp_rw [hj]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
    ((summable_geometric_of_lt_one hq0.le hq1).mul_left C), tsum_mul_left,
    tsum_geometric_of_lt_one hq0.le hq1]

/-- `∑_{k ≥ 1} k^{-2}` converges. -/
theorem summable_shift_rpow_neg_two : Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ)) ^ (-2 : ℝ)) :=
  (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (by norm_num))

/-- The sum over `k ≥ 1` of `K k^{-2} x` in `ℝ≥0∞` is `(K ∑ k^{-2}) x`. -/
theorem tsum_ofReal_shift_sq_mul (K : ℝ) (hK : 0 ≤ K) (x : ℝ≥0∞) :
    ∑' k : ℕ, ENNReal.ofReal (K * (((k + 1 : ℕ) : ℝ)) ^ (-2 : ℝ)) * x =
      ENNReal.ofReal (K * ∑' k : ℕ, (((k + 1 : ℕ) : ℝ)) ^ (-2 : ℝ)) * x := by
  rw [ENNReal.tsum_mul_right]
  congr 1
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
    (summable_shift_rpow_neg_two.mul_left K), tsum_mul_left]

end PrimeCarleson.Proof.Paper
