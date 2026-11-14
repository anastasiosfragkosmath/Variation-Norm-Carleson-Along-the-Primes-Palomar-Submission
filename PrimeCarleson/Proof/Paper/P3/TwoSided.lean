module

public import PrimeCarleson.Proof.Paper.P3.Localization
public import PrimeCarleson.Proof.Paper.Defs.Psi
public import PrimeCarleson.Proof.Paper.Defs.Weights

/-!
# The smooth two-sided maximal `U³` estimate at scale `2^k`

Source: main paper `e:U3maxmod`, L1525–L1528 (use of the lemma), and the Piatetski-Shapiro remark
L2927: for the dyadic kernel `ψ_k(n) = 2^{-k} ψ(n 2^{-k})` (`Paper.psiK`, `ψ : PsiData`, odd,
supported in `2^{k-2} < |n| < 2^k`) and an **even** weight `u : ℤ → ℂ` (the printed use needs no
parity hypothesis, but the reflection `n ↦ -n` requires it, and it holds for both uses
`u = w - w_{≤M(k)}` and `u = w_Q`, by `blockWeight_neg` / `wQ_neg`),
`‖sup_λ |∑_n f(x-n) u(n) ψ_k(n) e(λ n)|‖_{ℓ²(ℤ)} ≤ C_ψ ‖u‖_{U³([2^k])} ‖f‖_{ℓ²(ℤ)}`.

*Proof.* `ψ_k = (ψ₊)_{2^k} - (ψ₊)_{2^k}(-·)` with `ψ₊ := ψ 1_{(0,∞)}`, a `C^∞` function supported in
`[0, 1]` (since `ψ = 0` on `[-1/4, 1/4]`). The positive-`n` part is the smooth form
(`U3maxmod_smooth_ell2Z`, which uses the window estimate `smooth_L2_bound`); the negative-`n` part
is, for even `u` and odd `ψ_k`, the positive part for the reflected function `f̃(y) = f(-y)`
at the point `-x` and frequency `-λ`
(`weightedModSum_cm_eq`), and `ℓ²(ℤ)` norms are invariant under `x ↦ -x`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ComplexConjugate ENNReal ContDiff

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0

/-! ### Reflection invariance of `ℓ²(ℤ)` norms -/

/-- `‖F(-·)‖_{ℓ²(ℤ)} = ‖F‖_{ℓ²(ℤ)}` for `ℝ≥0∞`-valued sequences. -/
theorem eLpNorm_two_count_comp_neg_enn (F : ℤ → ℝ≥0∞) :
    eLpNorm (fun x => F (-x)) 2 Measure.count = eLpNorm F 2 Measure.count := by
  rw [eLpNorm_two_count_enn_eq, eLpNorm_two_count_enn_eq]
  congr 1
  exact (Equiv.neg ℤ).tsum_eq (fun x => F x ^ (2 : ℝ))

/-- `‖f(-·)‖_{ℓ²(ℤ)} = ‖f‖_{ℓ²(ℤ)}`. -/
theorem eLpNorm_two_count_comp_neg (f : ℤ → ℂ) :
    eLpNorm (fun x => f (-x)) 2 Measure.count = eLpNorm f 2 Measure.count := by
  rw [eLpNorm_two_count_eq_tsum, eLpNorm_two_count_eq_tsum]
  congr 1
  exact (Equiv.neg ℤ).tsum_eq (fun x => ‖f x‖ₑ ^ (2 : ℝ))

/-! ### The one-sided cutoff `ψ₊` -/

/-- The one-sided cutoff `ψ₊(t) := ψ(t) 1_{t > 0}` (complex-valued). -/
def phiPlus (ψ : PsiData) (t : ℝ) : ℂ := if 0 < t then ((ψ.toFun t : ℝ) : ℂ) else 0

/-- `ψ(t) = 0` for `|t| ≤ 1/4`. -/
theorem PsiData.toFun_eq_zero_of_abs_le (ψ : PsiData) {t : ℝ} (ht : |t| ≤ 1 / 4) :
    ψ.toFun t = 0 := by
  by_contra h
  have := (ψ.abs_bounds h).1
  linarith

/-- `ψ₊ = ψ` on `(-1/4, ∞)`. -/
theorem phiPlus_eq_of_gt (ψ : PsiData) {t : ℝ} (ht : -(1 / 4) < t) :
    phiPlus ψ t = ((ψ.toFun t : ℝ) : ℂ) := by
  unfold phiPlus
  split_ifs with h
  · rfl
  · have : ψ.toFun t = 0 := ψ.toFun_eq_zero_of_abs_le (by
      rw [abs_le]; constructor <;> linarith [not_lt.1 h])
    simp [this]

/-- `ψ₊ = 0` on `(-∞, 1/4)`. -/
theorem phiPlus_eq_zero_of_lt (ψ : PsiData) {t : ℝ} (ht : t < 1 / 4) : phiPlus ψ t = 0 := by
  unfold phiPlus
  split_ifs with h
  · have : ψ.toFun t = 0 := ψ.toFun_eq_zero_of_abs_le (by
      rw [abs_le]; constructor <;> linarith)
    simp [this]
  · rfl

/-- `ψ₊` is `C^∞`, in particular `C²`. -/
theorem phiPlus_contDiff (ψ : PsiData) : ContDiff ℝ 2 (phiPlus ψ) := by
  have hψ : ContDiff ℝ 2 (fun t : ℝ => ((ψ.toFun t : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (ψ.contDiff.of_le (by simp))
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : -(1 / 4) < t
  · refine (hψ.contDiffAt (x := t)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds ht] with s hs using phiPlus_eq_of_gt ψ hs
  · have ht' : t < 1 / 4 := by linarith [not_lt.1 ht]
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds ht'] with s hs using phiPlus_eq_zero_of_lt ψ hs

/-- `supp ψ₊ ⊆ [0, 1]`. -/
theorem phiPlus_support (ψ : PsiData) : Function.support (phiPlus ψ) ⊆ Set.Icc 0 1 := by
  intro t ht
  unfold phiPlus at ht
  by_cases h : 0 < t
  · have hne : ψ.toFun t ≠ 0 := by
      intro h0
      simp [h, h0] at ht
    have := ψ.abs_bounds hne
    rw [abs_of_pos h] at this
    exact ⟨h.le, this.2.le⟩
  · simp [h] at ht

/-- `ψ₊` has compact support. -/
theorem phiPlus_hasCompactSupport (ψ : PsiData) : HasCompactSupport (phiPlus ψ) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal (phiPlus_support ψ) isClosed_Icc)

/-- A `C²` function with compact support has bounded value and second derivative. -/
theorem exists_bound_contDiff_two {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ t, ‖φ t‖ ≤ M) ∧ ∀ t, ‖deriv (deriv φ) t‖ ≤ M := by
  have hb0 := Common.bddAbove_range_norm_of_hasCompactSupport hφ.continuous hc
  have hb2 := Common.bddAbove_range_norm_of_hasCompactSupport (f := deriv (deriv φ))
    (by rw [← Common.iteratedDeriv_two_eq_deriv_deriv]; exact hφ.continuous_iteratedDeriv 2 le_rfl)
    (by rw [← Common.iteratedDeriv_two_eq_deriv_deriv]
        exact Common.hasCompactSupport_iteratedDeriv hc 2)
  obtain ⟨M0, hM0⟩ := hb0
  obtain ⟨M2, hM2⟩ := hb2
  refine ⟨max M0 M2 ⊔ 0, le_sup_right, fun t => ?_, fun t => ?_⟩
  · exact (hM0 ⟨t, rfl⟩).trans ((le_max_left _ _).trans le_sup_left)
  · exact (hM2 ⟨t, rfl⟩).trans ((le_max_right _ _).trans le_sup_left)

/-! ### The dyadic kernel and its one-sided pieces -/

/-- For `N = 2^k`, the dilate of `ψ₊` is `ψ_k` on the positive integers and `0` otherwise. -/
theorem dilate_phiPlus (ψ : PsiData) (k : ℕ) (n : ℤ) :
    dilate ((((2 : ℕ+) ^ k : ℕ+) : ℕ) : ℝ) (phiPlus ψ) (n : ℝ) =
      if 0 < n then ((psiK ψ.toFun k (n : ℝ) : ℝ) : ℂ) else 0 := by
  have hN : ((((2 : ℕ+) ^ k : ℕ+) : ℕ) : ℝ) = (2 : ℝ) ^ k := by
    simp
  rw [hN]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  by_cases hn : 0 < n
  · have hn' : (0 : ℝ) < (n : ℝ) / (2 : ℝ) ^ k := by
      have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      positivity
    simp only [hn, ite_true, dilate, phiPlus, hn', Complex.real_smul]
    simp [psiK, div_eq_mul_inv]
  · have hn' : ¬ (0 : ℝ) < (n : ℝ) / (2 : ℝ) ^ k := by
      rw [not_lt] at hn ⊢
      have : (n : ℝ) ≤ 0 := by exact_mod_cast hn
      exact div_nonpos_of_nonpos_of_nonneg this hpos.le
    simp [dilate, phiPlus, hn, hn']

/-- The weights split: for even `u` and the odd kernel `ψ_k`,
`u(n) ψ_k(n) = cp(n) - cp(-n)`, `cp(n) = (ψ₊)_{2^k}(n) u(n)`. -/
theorem weight_split (ψ : PsiData) (k : ℕ) (u : ℤ → ℂ) (heven : ∀ n, u (-n) = u n) (n : ℤ) :
    u n * ((psiK ψ.toFun k (n : ℝ) : ℝ) : ℂ) =
      dilate ((((2 : ℕ+) ^ k : ℕ+) : ℕ) : ℝ) (phiPlus ψ) (n : ℝ) * u n +
        -(dilate ((((2 : ℕ+) ^ k : ℕ+) : ℕ) : ℝ) (phiPlus ψ) ((-n : ℤ) : ℝ) * u (-n)) := by
  rw [dilate_phiPlus, dilate_phiPlus, heven, Int.cast_neg]
  rcases lt_trichotomy n 0 with h | h | h
  · have h1 : ¬ 0 < n := not_lt.2 h.le
    have h2 : 0 < -n := by omega
    have h3 : psiK ψ.toFun k (n : ℝ) = -psiK ψ.toFun k (-(n : ℝ)) := by
      have := ψ.psiK_odd k (-(n : ℝ))
      simpa using this
    simp only [h1, h2, ↓reduceIte, h3]
    push_cast
    ring
  · subst h
    have : psiK ψ.toFun k 0 = 0 := by
      refine ψ.psiK_eq_zero_of_le ?_
      simp only [abs_zero]
      positivity
    simp [this]
  · have h1 : 0 < n := h
    have h2 : ¬ 0 < -n := by omega
    simp only [h1, h2, ↓reduceIte]
    ring

/-- The reflected piece: `T^{cm}_λ f(x) = -T^{cp}_{-λ} f̃(-x)` for `cm(n) = -cp(-n)`,
`f̃(y) = f(-y)`. -/
theorem weightedModSum_cm_eq (cp f : ℤ → ℂ) (lam : ℝ) (x : ℤ) :
    weightedModSum (fun n => -(cp (-n))) f lam x =
      -weightedModSum cp (fun y => f (-y)) (-lam) (-x) := by
  unfold weightedModSum
  rw [← tsum_neg]
  rw [← (Equiv.neg ℤ).tsum_eq (fun m : ℤ => -(f (-(-x - m)) * cp m * e (-lam * (m : ℝ))))]
  refine tsum_congr fun n => ?_
  simp only [Equiv.neg_apply, Int.cast_neg]
  have h1 : -(-x - -n) = x - n := by ring
  have h2 : e (-lam * -(n : ℝ)) = e (lam * n) := by congr 1; ring
  rw [h1, h2]
  ring

/-- The weighted maximal function of `cp` over the full line is bounded by the sum of the
maximal functions of the positive and the reflected pieces. -/
theorem iSup_enorm_split_le (cp f : ℤ → ℂ) (c : ℤ → ℂ) (S : Finset ℤ)
    (hS : ∀ n, n ∉ S → c n = 0) (hS1 : ∀ n, n ∉ S → cp n = 0)
    (hS2 : ∀ n, n ∉ S → cp (-n) = 0)
    (hsplit : ∀ n, c n = cp n + -(cp (-n))) (x : ℤ) :
    (⨆ lam : ℝ, ‖weightedModSum c f lam x‖ₑ) ≤
      (⨆ lam : ℝ, ‖weightedModSum cp f lam x‖ₑ) +
        ⨆ lam : ℝ, ‖weightedModSum cp (fun y => f (-y)) lam (-x)‖ₑ := by
  refine iSup_le fun lam => ?_
  have hc : weightedModSum c f lam x =
      weightedModSum cp f lam x + weightedModSum (fun n => -(cp (-n))) f lam x := by
    rw [weightedModSum_eq_sum c f lam x S hS, weightedModSum_eq_sum cp f lam x S hS1,
      weightedModSum_eq_sum (fun n => -(cp (-n))) f lam x S (fun n hn => by simp [hS2 n hn]),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hsplit n]
    ring
  rw [hc, weightedModSum_cm_eq]
  calc ‖weightedModSum cp f lam x + -weightedModSum cp (fun y => f (-y)) (-lam) (-x)‖ₑ
      ≤ ‖weightedModSum cp f lam x‖ₑ + ‖-weightedModSum cp (fun y => f (-y)) (-lam) (-x)‖ₑ :=
        enorm_add_le _ _
    _ = ‖weightedModSum cp f lam x‖ₑ + ‖weightedModSum cp (fun y => f (-y)) (-lam) (-x)‖ₑ := by
        rw [enorm_neg]
    _ ≤ _ := add_le_add (le_iSup (fun lam : ℝ => ‖weightedModSum cp f lam x‖ₑ) lam)
        (le_iSup (fun lam : ℝ => ‖weightedModSum cp (fun y => f (-y)) lam (-x)‖ₑ) (-lam))

/-- **The smooth two-sided maximal `U³` estimate at scale `2^k`** (Source: main paper `e:U3maxmod`,
L1525–L1528): for a fixed `ψ : PsiData` there is a constant `C` such that for every scale `k`, every
**even** `u : ℤ → ℂ` and every `f : ℤ → ℂ`,
`‖sup_λ |∑_n f(x-n) u(n) ψ_k(n) e(λ n)|‖_{ℓ²(ℤ)} ≤ C ‖u‖_{U³([2^k])} ‖f‖_{ℓ²(ℤ)}`. -/
theorem U3maxmod_twoSided (ψ : PsiData) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (u : ℤ → ℂ), (∀ n, u (-n) = u n) → ∀ f : ℤ → ℂ,
      eLpNorm (fun x => ⨆ lam : ℝ, ‖weightedModSum
          (fun n : ℤ => u n * ((psiK ψ.toFun k (n : ℝ) : ℝ) : ℂ)) f lam x‖ₑ) 2 Measure.count ≤
        ENNReal.ofReal (C * gowersNormOn 3 (bracket ((2 : ℕ+) ^ k)) u) *
          eLpNorm f 2 Measure.count := by
  obtain ⟨M, hM, hM0, hM2⟩ := exists_bound_contDiff_two (phiPlus_contDiff ψ)
    (phiPlus_hasCompactSupport ψ)
  refine ⟨640 * M, by positivity, fun k u heven f => ?_⟩
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
  -- the smooth ℓ² estimate for the positive piece, applied to f and to the reflection
  have hpos : ∀ g : ℤ → ℂ, eLpNorm (fun x => ⨆ lam : ℝ, ‖weightedModSum cp g lam x‖ₑ) 2
      Measure.count ≤
      ENNReal.ofReal (320 * M * gowersNormOn 3 (bracket N) u) * eLpNorm g 2 Measure.count :=
    fun g => U3maxmod_smooth_ell2Z N (phiPlus_contDiff ψ) (phiPlus_support ψ) hM0 hM2 u g
  have hpt : ∀ x, (⨆ lam : ℝ, ‖weightedModSum c f lam x‖ₑ) ≤
      (⨆ lam : ℝ, ‖weightedModSum cp f lam x‖ₑ) +
        ⨆ lam : ℝ, ‖weightedModSum cp (fun y => f (-y)) lam (-x)‖ₑ :=
    fun x => iSup_enorm_split_le cp f c S hS0 hS1 hS2 hsplit x
  have hmono : eLpNorm (fun x => ⨆ lam : ℝ, ‖weightedModSum c f lam x‖ₑ) 2 Measure.count ≤
      eLpNorm (fun x => (⨆ lam : ℝ, ‖weightedModSum cp f lam x‖ₑ) +
        ⨆ lam : ℝ, ‖weightedModSum cp (fun y => f (-y)) lam (-x)‖ₑ) 2 Measure.count :=
    eLpNorm_mono_enorm StronglyMeasurable.of_discrete.aestronglyMeasurable hpt
  have hadd : eLpNorm (fun x => (⨆ lam : ℝ, ‖weightedModSum cp f lam x‖ₑ) +
        ⨆ lam : ℝ, ‖weightedModSum cp (fun y => f (-y)) lam (-x)‖ₑ) 2 Measure.count ≤
      eLpNorm (fun x => ⨆ lam : ℝ, ‖weightedModSum cp f lam x‖ₑ) 2 Measure.count +
        eLpNorm (fun x => ⨆ lam : ℝ, ‖weightedModSum cp (fun y => f (-y)) lam (-x)‖ₑ) 2
          Measure.count :=
    eLpNorm_add_le (μ := Measure.count) (p := 2)
      (f := fun x => ⨆ lam : ℝ, ‖weightedModSum cp f lam x‖ₑ)
      (g := fun x => ⨆ lam : ℝ, ‖weightedModSum cp (fun y => f (-y)) lam (-x)‖ₑ) (by norm_num)
  have hrefl : eLpNorm (fun x => ⨆ lam : ℝ, ‖weightedModSum cp (fun y => f (-y)) lam (-x)‖ₑ) 2
      Measure.count = eLpNorm (fun x => ⨆ lam : ℝ, ‖weightedModSum cp (fun y => f (-y)) lam x‖ₑ)
        2 Measure.count :=
    eLpNorm_two_count_comp_neg_enn (fun x => ⨆ lam : ℝ,
      ‖weightedModSum cp (fun y => f (-y)) lam x‖ₑ)
  have h1 := hpos f
  have h2 := hpos (fun y => f (-y))
  rw [eLpNorm_two_count_comp_neg] at h2
  rw [hrefl] at hadd
  have hn : 0 ≤ gowersNormOn 3 (bracket N) u := gowersNormOn_nonneg _ _ _
  calc _ ≤ _ := hmono
    _ ≤ _ := hadd
    _ ≤ ENNReal.ofReal (320 * M * gowersNormOn 3 (bracket N) u) * eLpNorm f 2 Measure.count +
        ENNReal.ofReal (320 * M * gowersNormOn 3 (bracket N) u) * eLpNorm f 2 Measure.count :=
        add_le_add h1 h2
    _ = ENNReal.ofReal (640 * M * gowersNormOn 3 (bracket N) u) * eLpNorm f 2 Measure.count := by
        rw [← two_mul, ← mul_assoc]
        congr 1
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

end PrimeCarleson.Proof.Paper
