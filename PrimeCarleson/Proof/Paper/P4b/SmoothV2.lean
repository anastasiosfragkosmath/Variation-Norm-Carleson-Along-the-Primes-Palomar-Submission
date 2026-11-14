module

public import PrimeCarleson.Proof.Paper.P4b.Reflection
public import PrimeCarleson.Proof.Paper.P4a.CrudeV2
public import PrimeCarleson.Proof.Paper.P3.TwoSided

/-!
# The `V²` bound for the smooth two-sided cutoff at scale `2^k`

Source: main paper `c:U3modvariation`, L1288–L1303 (the "smooth-cutoff form of Corollary
`c:U3modvariation` at scale `2^k`"), the `V²` endpoint.

For `ψ : PsiData`, `k ≥ 1`, an **even** weight `u : ℤ → ℂ` and finitely supported `f`,

`‖V²(∑_n f(x-n) u(n) ψ_k(n) e(λ n) : λ ∈ 𝕋)‖_{ℓ²(ℤ)} ≤ K k ‖u‖_{L²([2^k])} ‖f‖_{ℓ²(ℤ)}`,

`K = 128 π sup |ψ₊|` depending only on `ψ` (`smooth_V2`). The proof avoids the "convexity"
(sharp-to-smooth) passage of the paper: `u ψ_k = cp - cp(-·)` with `cp = (ψ₊)_{2^k} u` carried by
`[2^k]` (`weight_split` of `P3/TwoSided.lean`); the positive piece is the sharp average
`A_λ f = E_{n ∈ [2^k]} f(x-n) w(n) e(λ n)` with `w = 2^k cp`, `|w| ≤ sup|ψ₊| |u|`, to which
`l:crudeV2lambda` (`P4a/`) applies directly, and the negative piece is the positive piece of the
reflection `f̃(y) = f(-y)` at `-x` (`rVariationOn_weightedModSum_cm_le`, `ℓ²(ℤ)` norms being
invariant under `x ↦ -x`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0

/-- A weight carried by `[N]`: the modulated sum with weight `cp` is the sharp average
`A_λ g = E_{n ∈ [N]} g(x-n) w(n) e(λ n)` with `w = N cp`. -/
theorem modAverage_natCast_mul (N : ℕ+) (cp g : ℤ → ℂ) (hcp : ∀ n, n ∉ bracket N → cp n = 0)
    (lam : ℝ) (x : ℤ) :
    modAverage N (fun n => ((N : ℕ) : ℂ) * cp n) g lam x = weightedModSum cp g lam x := by
  rw [modAverage_eq_weightedModSum]
  have h : (fun n => if n ∈ bracket N then ((N : ℕ) : ℂ) * cp n else 0) =
      fun n => ((N : ℕ) : ℂ) * cp n := by
    funext n
    by_cases hn : n ∈ bracket N
    · simp [hn]
    · simp [hn, hcp n hn]
  rw [h, weightedModSum_const_mul]
  have hN : ((N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast N.ne_zero
  field_simp

/-- **The `V²` bound for a weight carried by `[N]`** (`l:crudeV2lambda` for `T^{cp}_λ`): for
`cp` carried by `[N]` and finitely supported `g`,
`‖V²(T^{cp}_λ g : λ ∈ 𝕋)‖_{ℓ²} ≤ 32π log(2N) ‖N cp‖_{L²([N])} ‖g‖_{ℓ²}`. -/
theorem eLpNorm_variation_two_le_of_bracket (N : ℕ+) (cp g : ℤ → ℂ)
    (hcp : ∀ n, n ∉ bracket N → cp n = 0) (hg : (Function.support g).Finite) :
    eLpNorm (pointwiseVariation 2 (fun lam x => weightedModSum cp g lam x)) 2 Measure.count ≤
      ENNReal.ofReal (32 * Real.pi * Real.log (2 * ((N : ℕ) : ℝ)) *
          lpNormOn 2 (bracket N) (fun n => ((N : ℕ) : ℂ) * cp n)) *
        eLpNorm g 2 Measure.count := by
  have := eLpNorm_variation_le_log N (fun n => ((N : ℕ) : ℂ) * cp n) g hg
  simpa only [modAverage_natCast_mul N cp g hcp] using this

/-- `‖a‖_{L²(X)} ≤ M ‖b‖_{L²(X)}` if `|a| ≤ M |b|` on `X`. -/
theorem lpNormOn_two_le_mul {X : Finset ℤ} {a b : ℤ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ n ∈ X, ‖a n‖ ≤ M * ‖b n‖) : lpNormOn 2 X a ≤ M * lpNormOn 2 X b := by
  rw [lpNormOn_two_eq_sqrt, lpNormOn_two_eq_sqrt]
  have hcard : 0 ≤ (X.card : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg _)
  have hSb : 0 ≤ (X.card : ℝ)⁻¹ * ∑ n ∈ X, ‖b n‖ ^ 2 :=
    mul_nonneg hcard (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt hSb]
  calc (X.card : ℝ)⁻¹ * ∑ n ∈ X, ‖a n‖ ^ 2
      ≤ (X.card : ℝ)⁻¹ * ∑ n ∈ X, (M * ‖b n‖) ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n hn =>
          pow_le_pow_left₀ (norm_nonneg _) (h n hn) 2) hcard
    _ = M ^ 2 * ((X.card : ℝ)⁻¹ * ∑ n ∈ X, ‖b n‖ ^ 2) := by
        simp only [mul_pow, ← Finset.mul_sum]
        ring

/-- `|N φ_N(n) u| ≤ M |u|` when `|φ| ≤ M`. -/
theorem norm_natCast_mul_dilate_le {φ : ℝ → ℂ} {M : ℝ} (h0 : ∀ t, ‖φ t‖ ≤ M) (N : ℕ+) (n : ℤ)
    (z : ℂ) : ‖((N : ℕ) : ℂ) * (dilate ((N : ℕ) : ℝ) φ (n : ℝ) * z)‖ ≤ M * ‖z‖ := by
  have hN : ((N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast N.ne_zero
  have h1 : ((N : ℕ) : ℂ) * dilate ((N : ℕ) : ℝ) φ (n : ℝ) = φ ((n : ℝ) / ((N : ℕ) : ℝ)) := by
    simp only [dilate, Complex.real_smul]
    push_cast
    field_simp
  rw [← mul_assoc, h1, norm_mul]
  exact mul_le_mul_of_nonneg_right (h0 _) (norm_nonneg _)

/-- The modulated sum of a split weight `c = cp - cp(-·)` is the sum of the two pieces. -/
theorem weightedModSum_split (cp f c : ℤ → ℂ) (S : Finset ℤ) (hS : ∀ n, n ∉ S → c n = 0)
    (hS1 : ∀ n, n ∉ S → cp n = 0) (hS2 : ∀ n, n ∉ S → cp (-n) = 0)
    (hsplit : ∀ n, c n = cp n + -(cp (-n))) (lam : ℝ) (x : ℤ) :
    weightedModSum c f lam x =
      weightedModSum cp f lam x + weightedModSum (fun n => -(cp (-n))) f lam x := by
  rw [weightedModSum_eq_sum c f lam x S hS, weightedModSum_eq_sum cp f lam x S hS1,
    weightedModSum_eq_sum (fun n => -(cp (-n))) f lam x S (fun n hn => by simp [hS2 n hn]),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hsplit n]
  ring

/-- **Pointwise split of the variation**: for `c = cp - cp(-·)` with `cp` carried by a finite `S`,
`V²(T^c_λ f(x)) ≤ V²(T^{cp}_λ f(x)) + V²(T^{cp}_λ f̃(-x))`, `f̃(y) = f(-y)`. -/
theorem pointwiseVariation_two_split_le (cp f c : ℤ → ℂ) (S : Finset ℤ)
    (hS : ∀ n, n ∉ S → c n = 0) (hS1 : ∀ n, n ∉ S → cp n = 0)
    (hS2 : ∀ n, n ∉ S → cp (-n) = 0) (hsplit : ∀ n, c n = cp n + -(cp (-n))) (x : ℤ) :
    pointwiseVariation 2 (fun lam y => weightedModSum c f lam y) x ≤
      pointwiseVariation 2 (fun lam y => weightedModSum cp f lam y) x +
        pointwiseVariation 2 (fun lam y => weightedModSum cp (fun z => f (-z)) lam y) (-x) := by
  unfold pointwiseVariation
  rw [Common.rVariation_eq_rVariationOn, Common.rVariation_eq_rVariationOn,
    Common.rVariation_eq_rVariationOn]
  have h : (fun lam => weightedModSum c f lam x) =
      (fun lam => weightedModSum cp f lam x) +
        (fun lam => weightedModSum (fun n => -(cp (-n))) f lam x) := by
    funext lam
    exact weightedModSum_split cp f c S hS hS1 hS2 hsplit lam x
  rw [h]
  exact (Common.rVariationOn_add_le (by norm_num) _ _ _).trans
    (add_le_add le_rfl (rVariationOn_weightedModSum_cm_le two_pos cp f S hS1 x))

/-- **The `V²` bound for the smooth two-sided cutoff at scale `2^k`** (Source: main paper
`c:U3modvariation`, L1288–L1303, `V²` endpoint): for a fixed
`ψ : PsiData` there is `K ≥ 0` such that for every `k ≥ 1`, every **even** `u : ℤ → ℂ` and every
finitely supported `f`,
`‖V²(∑_n f(x-n) u(n) ψ_k(n) e(λ n) : λ ∈ 𝕋)‖_{ℓ²(ℤ)} ≤ K k ‖u‖_{L²([2^k])} ‖f‖_{ℓ²(ℤ)}`. -/
theorem smooth_V2 (ψ : PsiData) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (k : ℕ), 1 ≤ k → ∀ u : ℤ → ℂ, (∀ n, u (-n) = u n) →
      ∀ f : ℤ → ℂ, (Function.support f).Finite →
        eLpNorm (pointwiseVariation 2 (fun lam x =>
            weightedModSum (fun n : ℤ => u n * ((psiK ψ.toFun k (n : ℝ) : ℝ) : ℂ)) f lam x)) 2
            Measure.count ≤
          ENNReal.ofReal (K * (k : ℝ) * lpNormOn 2 (bracket ((2 : ℕ+) ^ k)) u) *
            eLpNorm f 2 Measure.count := by
  obtain ⟨M, hM, hM0, -⟩ := exists_bound_contDiff_two (phiPlus_contDiff ψ)
    (phiPlus_hasCompactSupport ψ)
  refine ⟨128 * Real.pi * M, by positivity, fun k hk u heven f hf => ?_⟩
  set N : ℕ+ := (2 : ℕ+) ^ k with hN
  set cp : ℤ → ℂ := fun n => dilate ((N : ℕ) : ℝ) (phiPlus ψ) (n : ℝ) * u n with hcp
  set c : ℤ → ℂ := fun n => u n * ((psiK ψ.toFun k (n : ℝ) : ℝ) : ℂ) with hc
  have hφ0 : ∀ t, t ∉ Set.Ioo (0 : ℝ) 1 → phiPlus ψ t = 0 := fun t ht =>
    eq_zero_of_notMem_Ioo_of_support_Icc (phiPlus_contDiff ψ).continuous (phiPlus_support ψ) ht
  have hcpN : ∀ n, n ∉ bracket N → cp n = 0 := fun n hn => by
    simp only [hcp]
    rw [dilate_eq_zero_of_notMem_bracket N hφ0 n hn, zero_mul]
  have hsplit : ∀ n, c n = cp n + -(cp (-n)) := fun n => by
    have := weight_split ψ k u heven n
    simpa [hcp, hc, hN] using this
  set S : Finset ℤ := Finset.Icc (-((N : ℕ) : ℤ)) ((N : ℕ) : ℤ) with hS
  have hS1 : ∀ n, n ∉ S → cp n = 0 := fun n hn => by
    refine hcpN n fun h => hn ?_
    rw [mem_bracket] at h
    exact Finset.mem_Icc.2 ⟨by omega, h.2⟩
  have hS2 : ∀ n, n ∉ S → cp (-n) = 0 := fun n hn => by
    refine hcpN (-n) fun h => hn ?_
    rw [mem_bracket] at h
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hS0 : ∀ n, n ∉ S → c n = 0 := fun n hn => by
    rw [hsplit n, hS1 n hn, hS2 n hn]
    simp
  have hf' : (Function.support fun y => f (-y)).Finite := by
    have : (Function.support fun y => f (-y)) = (fun y : ℤ => -y) ⁻¹' Function.support f := rfl
    rw [this]
    exact hf.preimage (neg_injective.injOn)
  -- the `L²` norm of the sharp weight `N cp`
  have hw : lpNormOn 2 (bracket N) (fun n => ((N : ℕ) : ℂ) * cp n) ≤
      M * lpNormOn 2 (bracket N) u :=
    lpNormOn_two_le_mul hM fun n _ => by
      simpa only [hcp] using norm_natCast_mul_dilate_le hM0 N n (u n)
  have hL : 0 ≤ lpNormOn 2 (bracket N) u := lpNormOn_nonneg _ _ _
  have hlog : 0 ≤ Real.log (2 * ((N : ℕ) : ℝ)) := by
    have : (1 : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
    exact Real.log_nonneg (by linarith)
  have hlog2 : Real.log (2 * ((N : ℕ) : ℝ)) ≤ 2 * k := by
    have hN' : ((N : ℕ) : ℝ) = (2 : ℝ) ^ k := by simp [hN]
    rw [hN', Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith
  -- the bound for each of the two pieces
  have hpiece : ∀ g : ℤ → ℂ, (Function.support g).Finite →
      eLpNorm (pointwiseVariation 2 (fun lam x => weightedModSum cp g lam x)) 2 Measure.count ≤
        ENNReal.ofReal (32 * Real.pi * Real.log (2 * ((N : ℕ) : ℝ)) *
            (M * lpNormOn 2 (bracket N) u)) * eLpNorm g 2 Measure.count := fun g hg => by
    refine (eLpNorm_variation_two_le_of_bracket N cp g hcpN hg).trans ?_
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    gcongr
  have hpt : ∀ x, pointwiseVariation 2 (fun lam y => weightedModSum c f lam y) x ≤
      pointwiseVariation 2 (fun lam y => weightedModSum cp f lam y) x +
        pointwiseVariation 2 (fun lam y => weightedModSum cp (fun z => f (-z)) lam y) (-x) :=
    fun x => pointwiseVariation_two_split_le cp f c S hS0 hS1 hS2 hsplit x
  have hmono := eLpNorm_count_mono_enn hpt 2
  have hadd : eLpNorm (fun x =>
        pointwiseVariation 2 (fun lam y => weightedModSum cp f lam y) x +
          pointwiseVariation 2 (fun lam y => weightedModSum cp (fun z => f (-z)) lam y) (-x))
        2 Measure.count ≤
      eLpNorm (pointwiseVariation 2 (fun lam y => weightedModSum cp f lam y)) 2 Measure.count +
        eLpNorm (fun x => pointwiseVariation 2
          (fun lam y => weightedModSum cp (fun z => f (-z)) lam y) (-x)) 2 Measure.count :=
    eLpNorm_add_le (μ := Measure.count) (p := 2)
      (f := pointwiseVariation 2 (fun lam y => weightedModSum cp f lam y))
      (g := fun x => pointwiseVariation 2
        (fun lam y => weightedModSum cp (fun z => f (-z)) lam y) (-x)) (by norm_num)
  rw [eLpNorm_two_count_comp_neg_enn] at hadd
  have h1 := hpiece f hf
  have h2 := hpiece (fun z => f (-z)) hf'
  rw [eLpNorm_two_count_comp_neg] at h2
  set X : ℝ := 32 * Real.pi * Real.log (2 * ((N : ℕ) : ℝ)) * (M * lpNormOn 2 (bracket N) u)
    with hX
  have hX0 : 0 ≤ X := by
    have : 0 ≤ lpNormOn 2 (bracket N) u := hL
    rw [hX]
    have := mul_nonneg hM hL
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 32) Real.pi_pos.le) hlog
    positivity
  calc _ ≤ _ := hmono
    _ ≤ _ := hadd
    _ ≤ ENNReal.ofReal X * eLpNorm f 2 Measure.count +
        ENNReal.ofReal X * eLpNorm f 2 Measure.count := add_le_add h1 h2
    _ = ENNReal.ofReal (2 * X) * eLpNorm f 2 Measure.count := by
        rw [← two_mul, ← mul_assoc, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal (128 * Real.pi * M * (k : ℝ) * lpNormOn 2 (bracket N) u) *
        eLpNorm f 2 Measure.count := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        have hπ : 0 ≤ Real.pi := Real.pi_pos.le
        have h3 : 2 * X = 64 * Real.pi * (M * lpNormOn 2 (bracket N) u) *
            Real.log (2 * ((N : ℕ) : ℝ)) := by rw [hX]; ring
        rw [h3]
        calc 64 * Real.pi * (M * lpNormOn 2 (bracket N) u) * Real.log (2 * ((N : ℕ) : ℝ))
            ≤ 64 * Real.pi * (M * lpNormOn 2 (bracket N) u) * (2 * k) := by
              gcongr
          _ = _ := by ring

end PrimeCarleson.Proof.Paper
