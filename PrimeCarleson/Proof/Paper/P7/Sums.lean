module

public import PrimeCarleson.Proof.Paper.P7.HalfLine

/-!
# The modulated kernel sums as chart multipliers

`sources/Variational_Carleson.tex` L1769-L1776 (`l:varcarZ`) and L2990-L2999 (`c:disc`): for a
multiplier `k̂ ∈ L¹(ℝ)` with kernel `k(n) = ∫ k̂(ξ) e(nξ) dξ` and `f ∈ ℓ^p`, the modulated sum is

`dilSum k̂ Q f x λ = ∑_n f(x - Q n) e(λ n) k(n)`.

For `Q = 1` it is the multiplier output `∫ k̂(β - λ) f̂(β) e(xβ) dβ` (`dilSum_one_eq_integral`:
`e(λ m) ∫ k̂(ξ) e(mξ) dξ = ∫ k̂(β - λ) e(mβ) dβ` and `∑_k f(k) e((x - k)β) = f̂(β) e(xβ)`).
If `k̂` is supported in the chart `(c - 1/2, c + 1/2]` and `0 ≤ λ ≤ 1`, the integral over `ℝ` folds
onto the chart by the `1`-periodicity of `f̂ e(x ·)` (this is the Poisson summation of the paper,
with the `v`-sum collapsing exactly to `v ∈ {0, 1}`):

`∫ k̂(β - λ) f̂(β) e(xβ) dβ = ∫_{chart} (k̂(β - λ) + k̂(β - λ + 1)) f̂(β) e(xβ) dβ`
(`dilSum_one_eq_chartMult`), i.e. the chart multiplier of `h = k̂ + k̂(· + 1)`, of variation at most
twice that of `k̂` (`eVariationOn_add_shift_le`).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.MswTransference
  PrimeCarleson.Proof.Goal0

/-- The dilated modulated sum `∑_n f(x - Q n) e(λ n) k(n)`, `k(n) = ∫ k̂(ξ) e(nξ) dξ`. -/
def dilSum (khat : ℝ → ℂ) (Q : ℤ) (f : ℤ →₀ ℂ) (x : ℤ) (lam : ℝ) : ℂ :=
  ∑' n : ℤ, f (x - Q * n) * e (lam * (n : ℝ)) * ∫ ξ, khat ξ * e ((n : ℝ) * ξ)

/-- `∑_n f(x - n) F(n) = ∑_{k ∈ supp f} f(k) F(x - k)` for finitely supported `f`. -/
theorem tsum_eq_sum_support (f : ℤ →₀ ℂ) (F : ℤ → ℂ) (x : ℤ) :
    ∑' n : ℤ, f (x - n) * F n = ∑ k ∈ f.support, f k * F (x - k) := by
  rw [← (Equiv.subLeft x).tsum_eq]
  rw [tsum_eq_sum (s := f.support)]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp [Equiv.subLeft_apply]
  · intro k hk
    simp [Finsupp.notMem_support_iff.1 hk]

/-- `λ`-translation of the kernel: `e(λ m) ∫ k̂(ξ) e(mξ) dξ = ∫ k̂(β - λ) e(mβ) dβ`. -/
theorem e_mul_integral_eq (khat : ℝ → ℂ) (m lam : ℝ) :
    e (lam * m) * ∫ ξ, khat ξ * e (m * ξ) = ∫ β, khat (β - lam) * e (m * β) := by
  rw [← integral_add_right_eq_self (fun β => khat (β - lam) * e (m * β)) lam,
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [add_sub_cancel_right]
  rw [mul_add, e_add, mul_comm lam m]
  ring

/-- `β ↦ k(β - λ) e(mβ)` is integrable for integrable `k`. -/
theorem integrable_comp_mul_e {k : ℝ → ℂ} (hk : Integrable k) (m lam : ℝ) :
    Integrable fun β => k (β - lam) * e (m * β) := by
  refine (hk.comp_sub_right lam).norm.mono' ((hk.comp_sub_right lam).aestronglyMeasurable.mul
    (continuous_e.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun β => ?_)
  rw [norm_mul, norm_e, mul_one]

/-- **The modulated sum is a multiplier output** (`Q = 1`): for `k̂ ∈ L¹` and finitely supported
`f`, `∑_n f(x - n) e(λ n) k(n) = ∫ k̂(β - λ) f̂(β) e(xβ) dβ`.

Source: main paper `p:disc`, L2966–L2982. -/
theorem dilSum_one_eq_integral {khat : ℝ → ℂ} (hint : Integrable khat) (f : ℤ →₀ ℂ) (x : ℤ)
    (lam : ℝ) :
    dilSum khat 1 f x lam = ∫ β, khat (β - lam) * (fourierZ f β * e ((x : ℝ) * β)) := by
  unfold dilSum
  simp only [one_mul]
  simp_rw [mul_assoc]
  rw [tsum_eq_sum_support f (fun n => e (lam * (n : ℝ)) * ∫ ξ, khat ξ * e ((n : ℝ) * ξ)) x]
  have h1 : ∀ k ∈ f.support, f k * (e (lam * ((x - k : ℤ) : ℝ)) *
      ∫ ξ, khat ξ * e (((x - k : ℤ) : ℝ) * ξ)) =
      ∫ β, f k * (khat (β - lam) * e (((x - k : ℤ) : ℝ) * β)) := by
    intro k _
    rw [e_mul_integral_eq, integral_const_mul]
  rw [Finset.sum_congr rfl h1, ← integral_finsetSum]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun β => ?_)
    dsimp only
    rw [fourierZ_mul_e, Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  · intro k _
    exact (integrable_comp_mul_e hint _ lam).const_mul _

/-! ### Folding onto the chart -/

/-- **Folding** (the Poisson summation step of `p:disc`, L2966–L2982, with the sum over
`v` collapsing exactly): if `W` vanishes off the chart `(c - 1/2, c + 1/2]`, `0 ≤ λ ≤ 1`, `P` is
`1`-periodic and `W(· - λ) P` is integrable, then
`∫ W(β - λ) P(β) dβ = ∫ (W(β - λ) + W(β - λ + 1)) 1_{chart}(β) P(β) dβ`.

Source: main paper `p:disc`, L2966–L2982. -/
theorem integral_fold_chart {c lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) {W P : ℝ → ℂ}
    (hsupp : ∀ s, W s ≠ 0 → s ∈ chartSet c) (hP : Function.Periodic P 1)
    (hint : Integrable fun β => W (β - lam) * P β) :
    ∫ β, W (β - lam) * P β =
      ∫ β, (W (β - lam) + W (β - lam + 1)) * (chartSet c).indicator P β := by
  set Wl : ℝ → ℂ := fun β => W (β - lam) * P β with hWl
  have hcs : ∀ β, β ∈ chartSet c ↔ c - 1 / 2 < β ∧ β ≤ c + 1 / 2 := fun β => by
    simp [chartSet]
  -- (1) split `Wl` into the chart part and the part to the right of the chart
  have hsplit : Wl = (chartSet c).indicator Wl + (Set.Ioi (c + 1 / 2)).indicator Wl := by
    funext β
    by_cases hβ : β ∈ chartSet c
    · have : β ∉ Set.Ioi (c + 1 / 2) := by
        simp only [Set.mem_Ioi, not_lt]
        exact ((hcs β).1 hβ).2
      rw [Pi.add_apply, Set.indicator_of_mem hβ, Set.indicator_of_notMem this, add_zero]
    · by_cases hβ2 : β ∈ Set.Ioi (c + 1 / 2)
      · rw [Pi.add_apply, Set.indicator_of_notMem hβ, Set.indicator_of_mem hβ2, zero_add]
      · have hWz : W (β - lam) = 0 := by
          by_contra hne
          have := (hcs _).1 (hsupp _ hne)
          apply hβ
          rw [hcs]
          simp only [Set.mem_Ioi, not_lt] at hβ2
          constructor <;> linarith [this.1, this.2]
        rw [Pi.add_apply, Set.indicator_of_notMem hβ, Set.indicator_of_notMem hβ2, add_zero]
        simp [hWl, hWz]
  -- (2) the part to the right of the chart is the shifted chart part of the second term
  have hshift : ∀ β, (Set.Ioi (c + 1 / 2)).indicator Wl (β + 1) =
      (chartSet c).indicator (fun β => W (β - lam + 1) * P β) β := by
    intro β
    have hP1 : P (β + 1) = P β := hP β
    have hW1 : W (β + 1 - lam) = W (β - lam + 1) := by ring_nf
    by_cases hβ : β ∈ chartSet c
    · have hβ1 : β + 1 ∈ Set.Ioi (c + 1 / 2) := by
        simp only [Set.mem_Ioi]
        linarith [((hcs β).1 hβ).1]
      rw [Set.indicator_of_mem hβ1, Set.indicator_of_mem hβ]
      simp only [hWl, hP1, hW1]
    · rw [Set.indicator_of_notMem hβ]
      by_cases hβ1 : β + 1 ∈ Set.Ioi (c + 1 / 2)
      · rw [Set.indicator_of_mem hβ1]
        simp only [hWl, hP1, hW1]
        have hWz : W (β - lam + 1) = 0 := by
          by_contra hne
          have := (hcs _).1 (hsupp _ hne)
          apply hβ
          rw [hcs]
          simp only [Set.mem_Ioi] at hβ1
          constructor <;> linarith [this.1, this.2]
        simp [hWz]
      · rw [Set.indicator_of_notMem hβ1]
  have hI1 : Integrable ((chartSet c).indicator Wl) := hint.indicator (measurableSet_chartSet c)
  have hI2 : Integrable ((Set.Ioi (c + 1 / 2)).indicator Wl) := hint.indicator measurableSet_Ioi
  have hI3 : Integrable (fun β => (Set.Ioi (c + 1 / 2)).indicator Wl (β + 1)) :=
    hI2.comp_add_right 1
  have hshift' : ∫ β, (Set.Ioi (c + 1 / 2)).indicator Wl β =
      ∫ β, (chartSet c).indicator (fun β => W (β - lam + 1) * P β) β := by
    rw [← integral_add_right_eq_self ((Set.Ioi (c + 1 / 2)).indicator Wl) 1]
    exact integral_congr_ae (Filter.Eventually.of_forall hshift)
  have hI3' : Integrable ((chartSet c).indicator fun β => W (β - lam + 1) * P β) := by
    refine hI3.congr (Filter.Eventually.of_forall hshift)
  calc ∫ β, W (β - lam) * P β = ∫ β, Wl β := rfl
    _ = ∫ β, ((chartSet c).indicator Wl β + (Set.Ioi (c + 1 / 2)).indicator Wl β) := by
        rw [← Pi.add_def, ← hsplit]
    _ = (∫ β, (chartSet c).indicator Wl β) + ∫ β, (Set.Ioi (c + 1 / 2)).indicator Wl β :=
        integral_add hI1 hI2
    _ = ∫ β, ((chartSet c).indicator Wl β +
          (chartSet c).indicator (fun β => W (β - lam + 1) * P β) β) := by
        rw [hshift', integral_add hI1 hI3']
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun β => ?_)
        dsimp only
        by_cases hβ : β ∈ chartSet c
        · rw [Set.indicator_of_mem hβ, Set.indicator_of_mem hβ, Set.indicator_of_mem hβ]
          simp only [hWl]
          ring
        · rw [Set.indicator_of_notMem hβ, Set.indicator_of_notMem hβ, Set.indicator_of_notMem hβ]
          ring

/-- A bounded measurable function vanishing off a compact interval is integrable. -/
theorem integrable_of_bound_support {k : ℝ → ℂ} (hk : Measurable k) {B : ℝ}
    (hB : ∀ s, ‖k s‖ ≤ B) {u w : ℝ} (hs : ∀ s, s ∉ Set.Icc u w → k s = 0) : Integrable k := by
  have hI : Integrable ((Set.Icc u w).indicator fun _ => B) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  refine hI.mono' hk.aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
  by_cases h : s ∈ Set.Icc u w
  · rw [Set.indicator_of_mem h]
    exact hB s
  · rw [hs s h]
    simp [Set.indicator_of_notMem h]

/-- **The modulated sum on a chart** (`Q = 1`): for `k̂ ∈ L¹` supported in the chart
`(c - 1/2, c + 1/2]` and `0 ≤ λ ≤ 1`, `∑_n f(x - n) e(λ n) k(n)` is the chart multiplier output
of `h = k̂ + k̂(· + 1)`.

Source: main paper `p:disc`, L2966–L2982. -/
theorem dilSum_one_eq_chartMult {khat : ℝ → ℂ} (hint : Integrable khat) {c : ℝ}
    (hsupp : ∀ s, khat s ≠ 0 → s ∈ chartSet c) (f : ℤ →₀ ℂ) (x : ℤ) {lam : ℝ} (h0 : 0 ≤ lam)
    (h1 : lam ≤ 1) :
    dilSum khat 1 f x lam = chartMult c (fun s => khat s + khat (s + 1)) f x lam := by
  rw [dilSum_one_eq_integral hint]
  have hP : Function.Periodic (fun β => fourierZ f β * e ((x : ℝ) * β)) 1 := by
    intro β
    simp only
    rw [fourierZ_periodic f β, mul_add, mul_one]
    have := e_add_intCast ((x : ℝ) * β) x
    rw [this]
  have hPint : Integrable fun β => khat (β - lam) * (fourierZ f β * e ((x : ℝ) * β)) := by
    have := (integrable_comp_mul_e hint ((x : ℝ)) lam)
    have h2 : (fun β => khat (β - lam) * (fourierZ f β * e ((x : ℝ) * β))) =
        fun β => fourierZ f β * (khat (β - lam) * e ((x : ℝ) * β)) := by
      funext β
      ring
    rw [h2]
    exact this.bdd_mul (c := f.sum fun _ c => ‖c‖) (continuous_fourierZ f).aestronglyMeasurable
      (Filter.Eventually.of_forall fun β => norm_fourierZ_le f β)
  rw [integral_fold_chart h0 h1 hsupp hP hPint]
  unfold chartMult mulInt chartDensity
  refine integral_congr_ae (Filter.Eventually.of_forall fun β => ?_)
  simp only

/-- `h = k̂ + k̂(· + 1)` has variation at most twice the variation of `k̂`. -/
theorem eVariationOn_add_shift_le (k : ℝ → ℂ) :
    eVariationOn (fun s => k s + k (s + 1)) Set.univ ≤ 2 * eVariationOn k Set.univ := by
  have hshift : eVariationOn (fun s => k (s + 1)) Set.univ ≤ eVariationOn k Set.univ :=
    eVariationOn.comp_le_of_monotoneOn k (fun s => s + 1) (fun _ _ _ _ h => by linarith)
      (Set.mapsTo_univ _ _)
  refine iSup_le fun ⟨n, u, hu, hus⟩ => ?_
  calc ∑ i ∈ Finset.range n, edist (k (u (i + 1)) + k (u (i + 1) + 1)) (k (u i) + k (u i + 1))
      ≤ ∑ i ∈ Finset.range n, (edist (k (u (i + 1))) (k (u i)) +
          edist (k (u (i + 1) + 1)) (k (u i + 1))) := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact edist_add_add_le _ _ _ _
    _ = ∑ i ∈ Finset.range n, edist (k (u (i + 1))) (k (u i)) +
          ∑ i ∈ Finset.range n, edist (k (u (i + 1) + 1)) (k (u i + 1)) := Finset.sum_add_distrib
    _ ≤ eVariationOn k Set.univ + eVariationOn k Set.univ := by
        refine add_le_add (eVariationOn.sum_le hu fun _ => Set.mem_univ _) ?_
        exact (eVariationOn.sum_le (f := k) (u := fun i => u i + 1)
          (fun i j hij => by have := hu hij; simp only; linarith) fun _ => Set.mem_univ _)
    _ = 2 * eVariationOn k Set.univ := (two_mul _).symm

end PrimeCarleson.Proof.Paper
