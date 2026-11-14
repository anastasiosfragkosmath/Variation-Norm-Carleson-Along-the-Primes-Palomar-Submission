module

public import PrimeCarleson.Proof.Paper.P4a.SquareFunction
public import PrimeCarleson.Proof.Common.VariationDyadic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Dyadic grids: the limiting argument and the sum over scales

Source: main paper `l:crudeV2lambda`, L1024–L1054 (the proof of `l:crudeV2lambda`: the three steps
L1024–L1042, L1043–L1052 and L1053–L1054).

* `dyadicGrid J = {j / 2^J : 0 ≤ j ≤ 2^J}`;
* `eLpNorm_variation_dyadicGrid_le` (the Rademacher–Menshov step): Rademacher–Menshov
  (`Common.rVariationOn_two_le_sum_dyadic_grid`) pointwise in `x` and Minkowski in `ℓ²_x`,
  `‖V²(A_λ f : λ ∈ grid J)‖_{ℓ²} ≤ 2 ∑_{m=0}^J ‖(∑_{s<2^{J-m}} |D_{2^{J-m},0,s} f|²)^{1/2}‖_{ℓ²}`;
* `sum_min_one_sqrt_le`: `∑_{ℓ=0}^J min{1, (N/2^ℓ)^{1/2}} ≤ 8 log(2N)`, uniformly in `J`;
* `eLpNorm_variation_dyadicGrid_le_log` (the sum over scales): with `e:Dsfbound`, for every `J`,
  `‖V²(A_λ f : λ ∈ grid J)‖_{ℓ²} ≤ 32π log(2N) ‖w‖_{L²([N])} ‖f‖_{ℓ²}`;
* `rVariationOn_Ico_le_iSup_dyadicGrid`, `eLpNorm_variation_Ico_le` (the limiting argument):
  a continuous family has `V^r` over `[0,1)` at most the supremum of the `V^r` over the dyadic
  grids, and a bound for the `ℓ²` norms of the grid variations, uniform in `J`, passes to
  `V²(A_λ f : λ ∈ 𝕋)` (monotone convergence).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

/-- The dyadic grid `{j / 2^J : 0 ≤ j ≤ 2^J}` of `[0, 1]` (L1025). -/
def dyadicGrid (J : ℕ) : Set ℝ := (fun j : ℕ => (j : ℝ) / 2 ^ J) '' Set.Iic (2 ^ J)

/-- The dyadic grids increase with `J`. -/
theorem dyadicGrid_mono {J J' : ℕ} (h : J ≤ J') : dyadicGrid J ⊆ dyadicGrid J' := by
  rintro _ ⟨j, hj, rfl⟩
  refine ⟨j * 2 ^ (J' - J), ?_, ?_⟩
  · rw [Set.mem_Iic] at hj ⊢
    calc j * 2 ^ (J' - J) ≤ 2 ^ J * 2 ^ (J' - J) := Nat.mul_le_mul_right _ hj
      _ = 2 ^ J' := by rw [← pow_add]; congr 1; omega
  · have h2 : (2 : ℝ) ^ J' = 2 ^ J * 2 ^ (J' - J) := by
      rw [← pow_add]; congr 1; omega
    push_cast
    rw [h2, mul_div_mul_right _ _ (by positivity)]

/-! ### The numerical bound for the sum over scales -/

/-- `∑_{ℓ=0}^J min{1, (N/2^ℓ)^{1/2}} ≤ 8 log(2N)` for every `J` and `N ≥ 1` (the sum
`∑_{K = 2^ℓ, 0 ≤ ℓ ≤ J} min{1, (N/K)^{1/2}} ≲ log(2N)` of L1048-L1051, asserted there without
computation). -/
theorem sum_min_one_sqrt_le {N : ℕ} (hN : 0 < N) (J : ℕ) :
    ∑ l ∈ Finset.range (J + 1), min 1 (Real.sqrt ((N : ℝ) / 2 ^ l)) ≤ 8 * Real.log (2 * N) := by
  set L : ℕ := Nat.log 2 N with hL
  have h1 : 2 ^ L ≤ N := Nat.pow_log_le_self 2 hN.ne'
  have h2 : N < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hterm : ∀ x : ℕ, min 1 (Real.sqrt ((N : ℝ) / 2 ^ (L + 1 + x))) ≤ (3 / 4 : ℝ) ^ x := by
    intro x
    refine (min_le_right _ _).trans ?_
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    have h2r : (N : ℝ) < 2 ^ (L + 1) := by exact_mod_cast h2
    calc (N : ℝ) / 2 ^ (L + 1 + x) ≤ 2 ^ (L + 1) / 2 ^ (L + 1 + x) := by
          gcongr
      _ = (1 / 2) ^ x := by
          rw [show (2 : ℝ) ^ (L + 1 + x) = 2 ^ (L + 1) * 2 ^ x from pow_add _ _ _,
            div_mul_cancel_left₀ (by positivity), one_div, inv_pow]
      _ ≤ ((9 : ℝ) / 16) ^ x := pow_le_pow_left₀ (by norm_num) (by norm_num) x
      _ = ((3 / 4 : ℝ) ^ x) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hsum : ∑ l ∈ Finset.range (J + 1), min 1 (Real.sqrt ((N : ℝ) / 2 ^ l)) ≤
      ∑ l ∈ Finset.range (L + 1 + J), min 1 (Real.sqrt ((N : ℝ) / 2 ^ l)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.2 (by omega)) fun l _ _ => ?_
    exact le_min zero_le_one (Real.sqrt_nonneg _)
  have hsplit : ∑ l ∈ Finset.range (L + 1 + J), min 1 (Real.sqrt ((N : ℝ) / 2 ^ l)) =
      ∑ l ∈ Finset.range (L + 1), min 1 (Real.sqrt ((N : ℝ) / 2 ^ l)) +
        ∑ x ∈ Finset.range J, min 1 (Real.sqrt ((N : ℝ) / 2 ^ (L + 1 + x))) :=
    Finset.sum_range_add _ _ _
  have hA : ∑ l ∈ Finset.range (L + 1), min 1 (Real.sqrt ((N : ℝ) / 2 ^ l)) ≤ (L : ℝ) + 1 := by
    calc _ ≤ ∑ l ∈ Finset.range (L + 1), (1 : ℝ) := Finset.sum_le_sum fun l _ => min_le_left _ _
      _ = (L : ℝ) + 1 := by simp
  have hB : ∑ x ∈ Finset.range J, min 1 (Real.sqrt ((N : ℝ) / 2 ^ (L + 1 + x))) ≤ 4 := by
    calc _ ≤ ∑ x ∈ Finset.range J, (3 / 4 : ℝ) ^ x := Finset.sum_le_sum fun x _ => hterm x
      _ = (1 - (3 / 4 : ℝ) ^ J) / (1 - 3 / 4) := by
          rw [geom_sum_eq (by norm_num)]
          rw [← neg_sub, ← neg_sub (1 : ℝ), neg_div_neg_eq]
      _ ≤ 4 := by
          have : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ J := by positivity
          rw [div_le_iff₀ (by norm_num)]
          linarith
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hLlog : ((L : ℝ) + 1) * Real.log 2 ≤ Real.log (2 * N) := by
    have h3 : (2 : ℝ) ^ (L + 1) ≤ 2 * N := by
      have : (2 : ℝ) ^ L ≤ N := by exact_mod_cast h1
      rw [pow_succ]
      linarith
    calc ((L : ℝ) + 1) * Real.log 2 = Real.log ((2 : ℝ) ^ (L + 1)) := by
          rw [Real.log_pow]; push_cast; ring
      _ ≤ Real.log (2 * N) := Real.log_le_log (by positivity) h3
  have hlog1 : Real.log 2 ≤ Real.log (2 * N) := Real.log_le_log (by norm_num) (by linarith)
  calc _ ≤ _ := hsum
    _ = _ := hsplit
    _ ≤ ((L : ℝ) + 1) + 4 := add_le_add hA hB
    _ ≤ 8 * Real.log (2 * N) := by nlinarith

/-! ### Rademacher–Menshov on the grid, pointwise in `x` -/

/-- The square function of the `m`-th scale is the one of `e:Dsfbound` with `K = 2^{J-m}`,
`α = 0`. -/
theorem modIncrementSq_dyadic (N : ℕ+) (w f : ℤ → ℂ) (J m : ℕ) (x : ℤ) :
    modIncrementSq N w f (2 ^ (J - m)) 0 x =
      (∑ s ∈ Finset.range (2 ^ (J - m)),
        ‖modAverage N w f (((s : ℝ) + 1) / 2 ^ (J - m)) x -
          modAverage N w f ((s : ℝ) / 2 ^ (J - m)) x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  simp [modIncrementSq, modIncrement]

/-- **The Rademacher–Menshov step on dyadic grids** (Source: main paper `l:crudeV2lambda`,
L1024–L1042): for every `J ≥ 0`, `N`, `w`, `f`,
`‖V²(A_{j2^{-J}} f : 0 ≤ j ≤ 2^J)‖_{ℓ²_x} ≤
2 ∑_{m=0}^J ‖(∑_{s<2^{J-m}} |A_{(s+1)/2^{J-m}} f - A_{s/2^{J-m}} f|²)^{1/2}‖_{ℓ²_x}`:
Rademacher–Menshov (`Common.rVariationOn_two_le_sum_dyadic_grid`, absolute constant `2`) applied
pointwise in `x` to `a_j(x) = A_{j2^{-J}} f(x)`, then the triangle inequality in `ℓ²`. -/
theorem eLpNorm_variation_dyadicGrid_le (N : ℕ+) (w f : ℤ → ℂ) (J : ℕ) :
    eLpNorm (fun x => rVariationOn 2 (dyadicGrid J) (fun lam => modAverage N w f lam x)) 2
        Measure.count ≤
      2 * ∑ m ∈ Finset.range (J + 1),
        eLpNorm (modIncrementSq N w f (2 ^ (J - m)) 0) 2 Measure.count := by
  have hpt : ∀ x, rVariationOn 2 (dyadicGrid J) (fun lam => modAverage N w f lam x) ≤
      2 * ∑ m ∈ Finset.range (J + 1), modIncrementSq N w f (2 ^ (J - m)) 0 x := by
    intro x
    have h := rVariationOn_two_le_sum_dyadic_grid J (fun lam => modAverage N w f lam x)
    simp_rw [modIncrementSq_dyadic]
    exact h
  have key : eLpNorm (fun x => rVariationOn 2 (dyadicGrid J) (fun lam => modAverage N w f lam x))
        (ENNReal.ofReal 2) Measure.count ≤
      2 * ∑ m ∈ Finset.range (J + 1),
        eLpNorm (modIncrementSq N w f (2 ^ (J - m)) 0) (ENNReal.ofReal 2) Measure.count := by
    calc eLpNorm (fun x => rVariationOn 2 (dyadicGrid J) (fun lam => modAverage N w f lam x))
          (ENNReal.ofReal 2) Measure.count
        ≤ eLpNorm (fun x => 2 * ∑ m ∈ Finset.range (J + 1),
            modIncrementSq N w f (2 ^ (J - m)) 0 x) (ENNReal.ofReal 2) Measure.count :=
          eLpNorm_count_mono_enn hpt _
      _ = 2 * eLpNorm (fun x => ∑ m ∈ Finset.range (J + 1),
            modIncrementSq N w f (2 ^ (J - m)) 0 x) (ENNReal.ofReal 2) Measure.count :=
          eLpNorm_count_const_mul _ _ two_pos
      _ ≤ 2 * ∑ m ∈ Finset.range (J + 1),
            eLpNorm (modIncrementSq N w f (2 ^ (J - m)) 0) (ENNReal.ofReal 2) Measure.count := by
          gcongr
          exact eLpNorm_count_finset_sum_le _ _ (by norm_num)
  simpa only [ENNReal.ofReal_ofNat] using key

/-! ### Sum over scales -/

/-- **The sum over scales** (Source: main paper `l:crudeV2lambda`, L1043–L1052): for every `J ≥ 0`
a finitely supported `f`, `N ≥ 1` and `w : [N] → ℂ`,
`‖V²(A_{j2^{-J}} f : 0 ≤ j ≤ 2^J)‖_{ℓ²} ≤ 2 · 2π ‖w‖_{L²([N])} ‖f‖_{ℓ²}
∑_{ℓ=0}^J min{1, (N/2^ℓ)^{1/2}} ≤ 32π log(2N) ‖w‖_{L²([N])} ‖f‖_{ℓ²}`
(the Rademacher–Menshov step with `e:Dsfbound` at `K = 2^{J-m}`, `α = 0`). Source: main paper
`l:crudeV2lambda`, L1043–L1052; the absolute implicit constant is `32π`. -/
theorem eLpNorm_variation_dyadicGrid_le_log (N : ℕ+) (w f : ℤ → ℂ)
    (hf : (Function.support f).Finite) (J : ℕ) :
    eLpNorm (fun x => rVariationOn 2 (dyadicGrid J) (fun lam => modAverage N w f lam x)) 2
        Measure.count ≤
      ENNReal.ofReal
          (32 * Real.pi * Real.log (2 * ((N : ℕ) : ℝ)) * lpNormOn 2 (bracket N) w) *
        eLpNorm f 2 Measure.count := by
  have hw0 := lpNormOn_nonneg 2 (bracket N) w
  have hN1 : (1 : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hlog : 0 ≤ Real.log (2 * ((N : ℕ) : ℝ)) := Real.log_nonneg (by linarith)
  set a : ℕ → ℝ := fun m => min 1 (Real.sqrt (((N : ℕ) : ℝ) / ((2 ^ (J - m) : ℕ) : ℝ))) with ha
  have ha0 : ∀ m, 0 ≤ a m := fun m => le_min zero_le_one (Real.sqrt_nonneg _)
  have hscale : ∀ m ∈ Finset.range (J + 1),
      eLpNorm (modIncrementSq N w f (2 ^ (J - m)) 0) 2 Measure.count ≤
        ENNReal.ofReal (2 * Real.pi * a m * lpNormOn 2 (bracket N) w) *
          eLpNorm f 2 Measure.count :=
    fun m _ => eLpNorm_modIncrementSq_le N w (by positivity) 0 f hf
  have hrefl : ∑ m ∈ Finset.range (J + 1), a m =
      ∑ l ∈ Finset.range (J + 1), min 1 (Real.sqrt (((N : ℕ) : ℝ) / 2 ^ l)) := by
    rw [← Finset.sum_range_reflect (fun l => min 1 (Real.sqrt (((N : ℕ) : ℝ) / 2 ^ l))) (J + 1)]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp [ha]
  have hbound : 2 * ∑ m ∈ Finset.range (J + 1), 2 * Real.pi * a m * lpNormOn 2 (bracket N) w ≤
      32 * Real.pi * Real.log (2 * ((N : ℕ) : ℝ)) * lpNormOn 2 (bracket N) w := by
    have h1 : ∑ m ∈ Finset.range (J + 1), 2 * Real.pi * a m * lpNormOn 2 (bracket N) w =
        2 * Real.pi * lpNormOn 2 (bracket N) w * ∑ m ∈ Finset.range (J + 1), a m := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [h1, hrefl]
    have h2 := sum_min_one_sqrt_le N.pos J
    have h3 : 0 ≤ 2 * Real.pi * lpNormOn 2 (bracket N) w := by positivity
    calc 2 * (2 * Real.pi * lpNormOn 2 (bracket N) w *
          ∑ l ∈ Finset.range (J + 1), min 1 (Real.sqrt (((N : ℕ) : ℝ) / 2 ^ l)))
        ≤ 2 * (2 * Real.pi * lpNormOn 2 (bracket N) w *
          (8 * Real.log (2 * ((N : ℕ) : ℝ)))) := by gcongr
      _ = _ := by ring
  calc eLpNorm (fun x => rVariationOn 2 (dyadicGrid J) (fun lam => modAverage N w f lam x)) 2
        Measure.count
      ≤ 2 * ∑ m ∈ Finset.range (J + 1),
        eLpNorm (modIncrementSq N w f (2 ^ (J - m)) 0) 2 Measure.count :=
        eLpNorm_variation_dyadicGrid_le N w f J
    _ ≤ 2 * ∑ m ∈ Finset.range (J + 1),
        ENNReal.ofReal (2 * Real.pi * a m * lpNormOn 2 (bracket N) w) *
          eLpNorm f 2 Measure.count := by
        gcongr with m hm
        exact hscale m hm
    _ = ENNReal.ofReal (2 * ∑ m ∈ Finset.range (J + 1),
          2 * Real.pi * a m * lpNormOn 2 (bracket N) w) * eLpNorm f 2 Measure.count := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun m _ => by
          have := ha0 m
          positivity), ENNReal.ofReal_mul (by norm_num), ← mul_assoc]
        norm_num
    _ ≤ ENNReal.ofReal
          (32 * Real.pi * Real.log (2 * ((N : ℕ) : ℝ)) * lpNormOn 2 (bracket N) w) *
        eLpNorm f 2 Measure.count := by
        gcongr


/-! ### The limiting argument -/

/-- The approximation `⌊2^J t⌋ / 2^J` of `t ≥ 0` from below tends to `t`. -/
theorem tendsto_floor_div_two_pow {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun J : ℕ => (⌊(2 : ℝ) ^ J * t⌋₊ : ℝ) / 2 ^ J) atTop (𝓝 t) := by
  have hlo : Tendsto (fun J : ℕ => t - (1 / 2 : ℝ) ^ J) atTop (𝓝 t) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    simpa using (tendsto_const_nhds (x := t)).sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds (fun J => ?_)
    (fun J => ?_)
  · have hp : (0 : ℝ) < 2 ^ J := by positivity
    rw [le_div_iff₀ hp]
    have h := Nat.lt_floor_add_one ((2 : ℝ) ^ J * t)
    have : (1 / 2 : ℝ) ^ J * 2 ^ J = 1 := by rw [← mul_pow]; norm_num
    nlinarith
  · have hp : (0 : ℝ) < 2 ^ J := by positivity
    rw [div_le_iff₀ hp, mul_comm]
    exact Nat.floor_le (by positivity)

/-- For a continuous `a : ℝ → ℂ`, the `r`-variation over `𝕋 = [0, 1)` is at most the supremum
over `J` of the `r`-variations over the dyadic grids: a finite increasing chain in
`[0, 1)` is approximated from below by grid points, and the sums of the increments converge. -/
theorem rVariationOn_Ico_le_iSup_dyadicGrid {r : ℝ} {a : ℝ → ℂ} (ha : Continuous a) :
    rVariationOn r (Set.Ico 0 1) a ≤ ⨆ J : ℕ, rVariationOn r (dyadicGrid J) a := by
  refine rVariationOn_le_iff.2 fun n t ht htS => ?_
  set B : ℝ≥0∞ := ⨆ J : ℕ, rVariationOn r (dyadicGrid J) a with hB
  set u : ℕ → Fin (n + 1) → ℝ := fun J i => (⌊(2 : ℝ) ^ J * t i⌋₊ : ℝ) / 2 ^ J with hu
  have ht0 : ∀ i, 0 ≤ t i := fun i => (htS i).1
  have ht1 : ∀ i, t i < 1 := fun i => (htS i).2
  have hu_lim : ∀ i, Tendsto (fun J => u J i) atTop (𝓝 (t i)) :=
    fun i => tendsto_floor_div_two_pow (ht0 i)
  have hu_mem : ∀ J i, u J i ∈ dyadicGrid J := by
    intro J i
    refine ⟨⌊(2 : ℝ) ^ J * t i⌋₊, ?_, rfl⟩
    rw [Set.mem_Iic]
    refine Nat.floor_le_of_le ?_
    have := ht1 i
    push_cast
    nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) J]
  have hu_mono : ∀ᶠ J in atTop, StrictMono (u J) := by
    have h1 : ∀ᶠ J in atTop, ∀ i : Fin n, u J i.castSucc < u J i.succ := by
      rw [Filter.eventually_all]
      intro i
      exact (hu_lim _).eventually_lt (hu_lim _) (ht (Fin.castSucc_lt_succ))
    filter_upwards [h1] with J hJ
    exact Fin.strictMono_iff_lt_succ.2 hJ
  have hcont : ∀ i : Fin n, Tendsto (fun J => ‖a (u J i.castSucc) - a (u J i.succ)‖ₑ ^ r) atTop
      (𝓝 (‖a (t i.castSucc) - a (t i.succ)‖ₑ ^ r)) := by
    intro i
    have h1 : Tendsto (fun J => a (u J i.castSucc) - a (u J i.succ)) atTop
        (𝓝 (a (t i.castSucc) - a (t i.succ))) :=
      ((ha.tendsto _).comp (hu_lim _)).sub ((ha.tendsto _).comp (hu_lim _))
    exact (ENNReal.continuous_rpow_const.tendsto _).comp ((continuous_enorm.tendsto _).comp h1)
  have hlim : Tendsto (fun J => (∑ i : Fin n, ‖a (u J i.castSucc) - a (u J i.succ)‖ₑ ^ r) ^
      (1 / r)) atTop (𝓝 ((∑ i : Fin n, ‖a (t i.castSucc) - a (t i.succ)‖ₑ ^ r) ^ (1 / r))) :=
    (ENNReal.continuous_rpow_const.tendsto _).comp (tendsto_finsetSum _ fun i _ => hcont i)
  refine le_of_tendsto hlim ?_
  filter_upwards [hu_mono] with J hJ
  exact (MswTransference.le_rVariationOn hJ (fun i => hu_mem J i)).trans
    (le_iSup (fun J : ℕ => rVariationOn r (dyadicGrid J) a) J)

/-- For every `x`, the map `λ ↦ A_λ f(x)` is continuous (a finite trigonometric sum). -/
theorem continuous_modAverage (N : ℕ+) (w f : ℤ → ℂ) (x : ℤ) :
    Continuous fun lam : ℝ => modAverage N w f lam x := by
  have : (fun lam : ℝ => modAverage N w f lam x) = fun lam : ℝ =>
      (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc (1 : ℤ) N, f (x - n) * w n * e (lam * n) :=
    funext fun lam => modAverage_eq N w f lam x
  rw [this]
  exact continuous_const.mul (continuous_finsetSum _ fun n _ =>
    continuous_const.mul (continuous_e.comp (continuous_id.mul continuous_const)))

/-- **The limiting argument** (Source: main paper `l:crudeV2lambda`, L1053–L1054): a bound `B` for
the `ℓ²` norms of the dyadic-grid variations, uniform in `J`, implies the same bound for
`V²(A_λ f : λ ∈ 𝕋)`: `λ ↦ A_λ f(x)` is continuous, so
`V²(A_λ f(x) : λ ∈ 𝕋) ≤ sup_J V²(A_{j 2^{-J}} f(x) : 0 ≤ j ≤ 2^J)` pointwise
(`rVariationOn_Ico_le_iSup_dyadicGrid`), the grid variations increase with `J` (`dyadicGrid_mono`),
and monotone convergence passes the bound to the `ℓ²` norm of the supremum. Source: main paper
`l:crudeV2lambda`, L1053–L1054. -/
theorem eLpNorm_variation_Ico_le (N : ℕ+) (w f : ℤ → ℂ) {B : ℝ≥0∞}
    (hB : ∀ J : ℕ, eLpNorm
      (fun x => rVariationOn 2 (dyadicGrid J) (fun lam => modAverage N w f lam x)) 2
        Measure.count ≤ B) :
    eLpNorm (fun x => rVariationOn 2 (Set.Ico 0 1) (fun lam => modAverage N w f lam x)) 2
        Measure.count ≤ B := by
  set V : ℕ → ℤ → ℝ≥0∞ :=
    fun J x => rVariationOn 2 (dyadicGrid J) (fun lam => modAverage N w f lam x) with hV
  have hmono : Monotone V := fun J J' hJ x => rVariationOn_mono_set (dyadicGrid_mono hJ) _
  have hpt : ∀ x, rVariationOn 2 (Set.Ico 0 1) (fun lam => modAverage N w f lam x) ≤
      ⨆ J, V J x := fun x =>
    rVariationOn_Ico_le_iSup_dyadicGrid (continuous_modAverage N w f x)
  have hsq : ∀ x, (⨆ J, V J x) ^ (2 : ℝ) = ⨆ J, V J x ^ (2 : ℝ) := fun x =>
    Monotone.map_iSup_of_continuousAt (f := fun y : ℝ≥0∞ => y ^ (2 : ℝ))
      ENNReal.continuous_rpow_const.continuousAt
      (ENNReal.monotone_rpow_of_nonneg (by norm_num)) (by simp)
  have hS : ∀ J, ∑' x, V J x ^ (2 : ℝ) ≤ B ^ (2 : ℝ) := by
    intro J
    have h := hB J
    rw [eLpNorm_two_count_enn] at h
    have h2 := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
    rwa [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one] at h2
  calc eLpNorm (fun x => rVariationOn 2 (Set.Ico 0 1) (fun lam => modAverage N w f lam x)) 2
        Measure.count
      ≤ eLpNorm (fun x => ⨆ J, V J x) 2 Measure.count := eLpNorm_count_mono_enn hpt _
    _ = (∑' x, (⨆ J, V J x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := eLpNorm_two_count_enn _
    _ = (⨆ J, ∑' x, V J x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        simp_rw [hsq]
        rw [← lintegral_count, lintegral_iSup (fun J => Measurable.of_discrete)
          (fun J J' hJ x => ENNReal.rpow_le_rpow (hmono hJ x) (by norm_num))]
        simp_rw [lintegral_count]
    _ ≤ (B ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow (iSup_le hS) (by norm_num)
    _ = B := by
        rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]

end PrimeCarleson.Proof.Paper
