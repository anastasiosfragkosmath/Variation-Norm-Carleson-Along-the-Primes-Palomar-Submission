module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Polynomial bound for `L(s, χ)` in the half-plane `re s > 0`, nonprincipal `χ`

The nonprincipal part of the prime number theorem in progressions; it feeds `PNTSW.LogDeriv` (the
logarithmic derivative of `L(s, χ)` near the `1`-line).

* `norm_sum_Icc_character_le`: for a nonprincipal `χ` modulo `q`, every partial sum
  `‖∑_{k ≤ n} χ(k)‖ ≤ q` (a full period sums to zero, `MulChar.sum_eq_zero_of_ne_one`);
* `partialSumIntegral_differentiableOn`: for a sequence with bounded partial sums,
  `s ↦ s ∫_1^∞ S(t) t^{-s-1} dt` is holomorphic on `re s > 0`;
* `norm_LFunction_le`: `‖L(s,χ)‖ ≤ q ‖s‖ / re s` for `re s > 0` and `χ ≠ 1` (partial summation on
  `re s > 1`, then the identity theorem on the half-plane).
-/

@[expose] public noncomputable section

open MeasureTheory Set Complex Filter Asymptotics

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-! ### Partial sums of a nonprincipal character -/

/-- A sum of a `q`-periodic function over a window of length `q` is the sum over `ZMod q`. -/
theorem sum_range_period {q : ℕ} [NeZero q] (g : ZMod q → ℂ) (n : ℕ) :
    ∑ x ∈ Finset.range q, g ((n + x : ℕ) : ZMod q) = ∑ a : ZMod q, g a := by
  refine Finset.sum_bij (fun x _ => ((n + x : ℕ) : ZMod q)) (fun _ _ => Finset.mem_univ _)
    ?_ ?_ (fun _ _ => rfl)
  · intro x hx y hy hxy
    have hx' := Finset.mem_range.mp hx
    have hy' := Finset.mem_range.mp hy
    have h := (ZMod.natCast_eq_natCast_iff' (n + x) (n + y) q).mp hxy
    have h1 : (n + x) % q = (n + y) % q := h
    have h2 : x % q = y % q := by
      have := Nat.ModEq.add_left_cancel' n (show n + x ≡ n + y [MOD q] from h1)
      exact this
    rwa [Nat.mod_eq_of_lt hx', Nat.mod_eq_of_lt hy'] at h2
  · intro a _
    refine ⟨(a - n).val, Finset.mem_range.mpr (ZMod.val_lt _), ?_⟩
    push_cast
    rw [ZMod.natCast_zmod_val]
    ring

/-- The partial sum of a nonprincipal character over a full period added to `n` is unchanged. -/
theorem sum_Icc_character_add_period {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 (n + q), χ k = ∑ k ∈ Finset.Icc 1 n, χ k := by
  have hI : ∀ m : ℕ, Finset.Icc 1 m = Finset.Ico 1 (m + 1) := fun m => by
    ext k; simp
  rw [hI, hI, ← Finset.sum_Ico_consecutive _ (show 1 ≤ n + 1 by omega)
    (show n + 1 ≤ n + q + 1 by omega)]
  have h3 : ∑ i ∈ Finset.Ico (n + 1) (n + q + 1), χ i =
      ∑ x ∈ Finset.range q, χ ((n + 1 + x : ℕ) : ZMod q) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have e : n + q + 1 - (n + 1) = q := by omega
    rw [e]
  have h2 : ∑ x ∈ Finset.range q, χ ((n + 1 + x : ℕ) : ZMod q) = 0 := by
    rw [sum_range_period (fun a : ZMod q => χ a) (n + 1)]
    exact MulChar.sum_eq_zero_of_ne_one hχ
  rw [h3, h2, add_zero]

/-- Every partial sum of a nonprincipal Dirichlet character modulo `q` has norm at most `q`. -/
theorem norm_sum_Icc_character_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (n : ℕ) : ‖∑ k ∈ Finset.Icc 1 n, χ k‖ ≤ q := by
  have hper : ∀ m : ℕ, ∑ k ∈ Finset.Icc 1 (n % q + q * m), χ k =
      ∑ k ∈ Finset.Icc 1 (n % q), χ k := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show n % q + q * (m + 1) = (n % q + q * m) + q by ring,
        sum_Icc_character_add_period hχ, ih]
  have hn : ∑ k ∈ Finset.Icc 1 n, χ k = ∑ k ∈ Finset.Icc 1 (n % q), χ k := by
    rw [← hper (n / q), Nat.mod_add_div]
  rw [hn]
  refine le_trans (norm_sum_le _ _) ?_
  calc ∑ k ∈ Finset.Icc 1 (n % q), ‖(χ k : ℂ)‖ ≤ ∑ _k ∈ Finset.Icc 1 (n % q), (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => DirichletCharacter.norm_le_one χ _
    _ = (n % q : ℕ) := by simp
    _ ≤ q := by exact_mod_cast (Nat.mod_lt n (Nat.pos_of_ne_zero (NeZero.ne q))).le

/-! ### Holomorphy of the partial-summation integral -/

/-- The partial-sum step function `t ↦ ∑_{k ≤ ⌊t⌋} f k`. -/
def partialSumFn (f : ℕ → ℂ) (t : ℝ) : ℂ := ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k

theorem partialSumFn_measurable (f : ℕ → ℂ) : Measurable (partialSumFn f) := by
  unfold partialSumFn
  exact (measurable_from_top
    (f := fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, f k)).comp Nat.measurable_floor

/-- For a bounded measurable `G`, `s ↦ ∫_1^∞ G(t) t^{-(s+1)} dt` is holomorphic on `re s > 0`. -/
theorem differentiableOn_integral_Ioi (G : ℝ → ℂ) (hG : Measurable G) (B : ℝ)
    (hB : ∀ t, ‖G t‖ ≤ B) :
    DifferentiableOn ℂ (fun s : ℂ => ∫ t in Ioi (1 : ℝ), G t * (t : ℂ) ^ (-(s + 1)))
      {s | 0 < s.re} := by
  set g : ℝ → ℂ := Set.indicator (Ioi (1 : ℝ)) G with hg
  have hgm : Measurable g := hG.indicator measurableSet_Ioi
  have hgb : ∀ t, ‖g t‖ ≤ B := by
    intro t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · simp only [hg, Set.indicator_of_mem ht]; exact hB _
    · simp only [hg, Set.indicator_of_notMem ht, norm_zero]
      exact (norm_nonneg _).trans (hB 0)
  have hloc : LocallyIntegrableOn g (Ioi 0) := by
    refine LocallyIntegrable.locallyIntegrableOn ?_ _
    intro x
    refine ⟨Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
    refine Measure.integrableOn_of_bounded (M := B) (by simp) hgm.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun t => by simpa using hgb t)
  have key : ∀ s : ℂ,
      mellin g (-s) = ∫ t in Ioi (1 : ℝ), G t * (t : ℂ) ^ (-(s + 1)) := by
    intro s
    unfold mellin
    have hex : (-s - 1) = -(s + 1) := by ring
    have hpt : ∀ t ∈ Ioi (0 : ℝ), (t : ℂ) ^ (-s - 1) • g t =
        Set.indicator (Ioi (1 : ℝ)) (fun t : ℝ => G t * (t : ℂ) ^ (-(s + 1))) t := by
      intro t ht
      by_cases h1 : t ∈ Ioi (1 : ℝ)
      · simp only [hg, Set.indicator_of_mem h1, smul_eq_mul, hex]
        ring
      · simp [hg, Set.indicator_of_notMem h1]
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_indicator measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi,
      Set.inter_eq_left.mpr (Ioi_subset_Ioi (zero_le_one : (0 : ℝ) ≤ 1))]
  intro s hs
  have hs' : 0 < s.re := hs
  have hmel : DifferentiableAt ℂ (mellin g) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1) hloc ?_
      (by simpa using hs') ?_ (by simp)
    · refine Asymptotics.IsBigO.of_bound B ?_
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
      have := hgb x
      simpa [Real.rpow_zero] using this
    · refine Asymptotics.IsBigO.of_bound 0 ?_
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with x hx
      have hx1 : x ∉ Ioi (1 : ℝ) := fun h => by linarith [hx.2, h.out]
      simp [hg, Set.indicator_of_notMem hx1]
  have hfun : (fun s : ℂ => ∫ t in Ioi (1 : ℝ), G t * (t : ℂ) ^ (-(s + 1))) =
      fun s : ℂ => mellin g (-s) := by
    funext s; rw [key s]
  rw [hfun]
  exact (hmel.comp s (by fun_prop : DifferentiableAt ℂ (fun s : ℂ => -s) s)).differentiableWithinAt

/-- The norm of `∫_1^∞ G(t) t^{-(s+1)} dt` is at most `B / re s`. -/
theorem norm_integral_Ioi_le (G : ℝ → ℂ) (B : ℝ) (hB : ∀ t, ‖G t‖ ≤ B) {s : ℂ}
    (hs : 0 < s.re) : ‖∫ t in Ioi (1 : ℝ), G t * (t : ℂ) ^ (-(s + 1))‖ ≤ B / s.re := by
  have hlt : -s.re - 1 < -1 := by linarith
  have hint : IntegrableOn (fun t : ℝ => B * t ^ (-s.re - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt hlt zero_lt_one).const_mul B
  have h1 : ‖∫ t in Ioi (1 : ℝ), G t * (t : ℂ) ^ (-(s + 1))‖ ≤
      ∫ t in Ioi (1 : ℝ), B * t ^ (-s.re - 1) := by
    refine norm_integral_le_of_norm_le hint ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have : (-(s + 1)).re = -s.re - 1 := by simp; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (hB _) (Real.rpow_nonneg ht0.le _)
  have h2 : ∫ t in Ioi (1 : ℝ), B * t ^ (-s.re - 1) = B / s.re := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt hlt zero_lt_one]
    have : (-s.re - 1 + 1) = -s.re := by ring
    rw [this, Real.one_rpow]
    field_simp
  exact h1.trans h2.le

/-- For a sequence with bounded partial sums, `s ↦ s ∫_1^∞ S(t) t^{-(s+1)} dt` is holomorphic on
`re s > 0`. -/
theorem partialSumIntegral_differentiableOn (f : ℕ → ℂ) (B : ℝ)
    (hB : ∀ n, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ B) :
    DifferentiableOn ℂ
      (fun s : ℂ => s * ∫ t in Ioi (1 : ℝ), partialSumFn f t * (t : ℂ) ^ (-(s + 1)))
      {s | 0 < s.re} :=
  differentiableOn_id.mul
    (differentiableOn_integral_Ioi (partialSumFn f) (partialSumFn_measurable f) B
      fun _ => hB _)

/-- The norm of the partial-summation integral is at most `B ‖s‖ / re s`. -/
theorem norm_partialSumIntegral_le (f : ℕ → ℂ) (B : ℝ)
    (hB : ∀ n, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    ‖s * ∫ t in Ioi (1 : ℝ), partialSumFn f t * (t : ℂ) ^ (-(s + 1))‖ ≤ B * ‖s‖ / s.re := by
  rw [norm_mul]
  calc ‖s‖ * ‖∫ t in Ioi (1 : ℝ), partialSumFn f t * (t : ℂ) ^ (-(s + 1))‖ ≤ ‖s‖ * (B / s.re) :=
        mul_le_mul_of_nonneg_left (norm_integral_Ioi_le (partialSumFn f) B (fun _ => hB _) hs)
          (norm_nonneg _)
    _ = B * ‖s‖ / s.re := by ring

/-! ### The polynomial bound -/

/-- For `re s > 1`, `L(s,χ) = s ∫_1^∞ S(t) t^{-(s+1)} dt` (Abel summation, bounded partial sums). -/
theorem LFunction_eq_partialSumIntegral {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ s =
      s * ∫ t in Ioi (1 : ℝ), partialSumFn (fun n : ℕ => (χ n : ℂ)) t * (t : ℂ) ^ (-(s + 1)) := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  refine LSeries_eq_mul_integral _ le_rfl (lt_trans zero_lt_one hs)
    (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs) ?_
  refine Asymptotics.IsBigO.of_bound q (Filter.Eventually.of_forall fun n => ?_)
  simpa using norm_sum_Icc_character_le hχ n

/-- **Polynomial bound**: for a nonprincipal `χ` modulo `q` and `re s > 0`,
`‖L(s, χ)‖ ≤ q ‖s‖ / re s`. -/
theorem norm_LFunction_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) : ‖DirichletCharacter.LFunction χ s‖ ≤ q * ‖s‖ / s.re := by
  set f : ℕ → ℂ := fun n => (χ n : ℂ) with hf
  set F : ℂ → ℂ := fun s => s * ∫ t in Ioi (1 : ℝ), partialSumFn f t * (t : ℂ) ^ (-(s + 1))
    with hF
  have hFd : DifferentiableOn ℂ F {s : ℂ | 0 < s.re} :=
    partialSumIntegral_differentiableOn f q (fun n => norm_sum_Icc_character_le hχ n)
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
  have hconv : IsPreconnected {s : ℂ | 0 < s.re} :=
    (convex_halfSpace_re_gt 0).isPreconnected
  have hLd : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) {s : ℂ | 0 < s.re} :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
  have h2 : (2 : ℂ) ∈ {s : ℂ | 0 < s.re} := by simp
  have hev : DirichletCharacter.LFunction χ =ᶠ[nhds (2 : ℂ)] F := by
    have hmem : {z : ℂ | 1 < z.re} ∈ nhds (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
    filter_upwards [hmem] with z hz
    exact LFunction_eq_partialSumIntegral hχ hz
  have heq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (hLd.analyticOnNhd hopen) (hFd.analyticOnNhd hopen) hconv h2 hev
  rw [heq (show s ∈ {s : ℂ | 0 < s.re} from hs)]
  exact norm_partialSumIntegral_le f q (fun n => norm_sum_Icc_character_le hχ n) hs

end PrimeCarleson.Proof.Fplus31
