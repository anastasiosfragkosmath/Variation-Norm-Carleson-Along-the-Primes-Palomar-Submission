module

public import PrimeCarleson.Proof.Paper.P3.Smooth
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# From the window `L²([-N, 2N])` to `ℓ²(ℤ)`

Source: main paper `e:U3maxmod`, L718–L731, used at L1056 and L1525–L1528 (this is the first half of
the two-sided estimate of `TwoSided.lean`). The window estimates of `e:U3maxmod` (`U3maxmod_L2`,
`smooth_L2_bound`) are for `f` carried by `[-N, 2N]`; the consumers need
`‖sup_λ |A_λ f|‖_{ℓ²(ℤ)} ≲ ‖w‖_{U³([N])} ‖f‖_{ℓ²(ℤ)}` for arbitrary `f` (the passage is not written
in the paper).

**Localization** (`eLpNorm_iSup_weightedModSum_le`): let `c : ℤ → ℂ` be carried by `[N]` and
`T_λ f(x) = ∑_n f(x-n) c(n) e(λ n)` (`weightedModSum`). If the window bound
`‖sup_λ |T_λ g|‖_{L²([-N,2N])} ≤ K ‖g‖_{L²([-N,2N])}` holds for all `g` carried by `[-N,2N]`, then
`‖sup_λ |T_λ f|‖_{ℓ²(ℤ)} ≤ 2K ‖f‖_{ℓ²(ℤ)}` for all `f`. Proof: `T_λ f(x + m)` for `x ∈ [N]` only
involves `f` on `[x + m - N, x + m - 1] ⊂ [m - N, m + 2N]`, a translate of the window; summing the
window estimates over all shifts `m ∈ ℤ` counts each `x` `N` times on the left and each `y` `3N + 1`
times on the right, so `N ∑_x S(x)² ≤ (3N+1) K² ∑_y |f(y)|²` and `(3N+1)/N ≤ 4`.

It is applied to `c = φ_N w` (`U3maxmod_smooth_ell2Z`, constant `320 M`). No finite-support
hypothesis on `f` is needed (the sums over `ℤ` are `ℝ≥0∞`-valued, the sums over `[N]` finite).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ComplexConjugate FourierTransform ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0

/-! ### `ℓ²(ℤ)` norms as `ℝ≥0∞` sums -/

/-- `‖F‖_{ℓ²(ℤ)} = (∑' x, F(x)²)^{1/2}` for `ℝ≥0∞`-valued sequences. -/
theorem eLpNorm_two_count_enn_eq (F : ℤ → ℝ≥0∞) :
    eLpNorm F 2 Measure.count = (∑' x, F x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [h2, eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 two_pos).ne'
    ENNReal.ofReal_ne_top StronglyMeasurable.of_discrete.aestronglyMeasurable, lintegral_count,
    ENNReal.toReal_ofReal zero_le_two]
  simp

/-- `‖f‖_{ℓ²(ℤ)} = (∑' x, |f(x)|²)^{1/2}`. -/
theorem eLpNorm_two_count_eq_tsum (f : ℤ → ℂ) :
    eLpNorm f 2 Measure.count = (∑' x, ‖f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [h2, eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 two_pos).ne'
    ENNReal.ofReal_ne_top StronglyMeasurable.of_discrete.aestronglyMeasurable, lintegral_count,
    ENNReal.toReal_ofReal zero_le_two]

/-- `(ofReal r)^2 = ofReal (r²)` for `r ≥ 0`. -/
theorem ofReal_rpow_two_of_nonneg {r : ℝ} (hr : 0 ≤ r) :
    ENNReal.ofReal r ^ (2 : ℝ) = ENNReal.ofReal (r ^ 2) := by
  rw [ENNReal.ofReal_rpow_of_nonneg hr two_pos.le, Real.rpow_two]

/-- `‖z‖ₑ² = ofReal (‖z‖²)`. -/
theorem enorm_rpow_two_eq_ofReal (z : ℂ) : ‖z‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [← ofReal_norm, ofReal_rpow_two_of_nonneg (norm_nonneg _)]

/-! ### The maximal function as a maximum -/

/-- For `c` carried by `[N]`, the extended supremum over `λ` of `|T_λ f(x)|` is `ofReal` of the
real supremum, and both are attained at the same `λ`. -/
theorem iSup_enorm_weightedModSum_eq (N : ℕ+) (c f : ℤ → ℂ) (hc : ∀ n, n ∉ bracket N → c n = 0)
    (x : ℤ) :
    (⨆ lam : ℝ, ‖weightedModSum c f lam x‖ₑ) =
      ENNReal.ofReal (⨆ lam : ℝ, ‖weightedModSum c f lam x‖) := by
  have hcont := continuous_weightedModSum c f x (bracket N) hc
  have hper := periodic_weightedModSum c f x
  obtain ⟨m', hm2, hm2'⟩ := iSup_norm_eq_of_periodic hcont hper
  rw [hm2, ofReal_norm]
  refine le_antisymm (iSup_le fun lam => ?_)
    (le_iSup (fun lam : ℝ => ‖weightedModSum c f lam x‖ₑ) m')
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hm2' lam)

/-- The real supremum `sup_λ |T_λ f(x)|` is nonnegative. -/
theorem iSup_norm_nonneg_real (Φ : ℝ → ℂ) : 0 ≤ ⨆ lam : ℝ, ‖Φ lam‖ :=
  Real.iSup_nonneg fun _ => norm_nonneg _

/-- From an `L²` window bound to a bound of sums: if `‖F‖_{L²(X)} ≤ K ‖G‖_{L²(X)}`
and `X` nonempty, then `∑_{x ∈ X} |F(x)|² ≤ K² ∑_{x ∈ X} |G(x)|²`. -/
theorem sum_sq_le_of_lpNormOn_le {X : Finset ℤ} (hX : X.Nonempty) {F G : ℤ → ℂ} {K : ℝ}
    (h : lpNormOn 2 X F ≤ K * lpNormOn 2 X G) :
    ∑ x ∈ X, ‖F x‖ ^ 2 ≤ K ^ 2 * ∑ x ∈ X, ‖G x‖ ^ 2 := by
  have hc : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have h2 := pow_le_pow_left₀ (lpNormOn_nonneg _ _ _) h 2
  rw [mul_pow, lpNormOn_two_sq, lpNormOn_two_sq] at h2
  have h3 : (X.card : ℝ)⁻¹ * ∑ x ∈ X, ‖F x‖ ^ 2 ≤
      (X.card : ℝ)⁻¹ * (K ^ 2 * ∑ x ∈ X, ‖G x‖ ^ 2) := by
    calc _ ≤ _ := h2
      _ = _ := by ring
  exact le_of_mul_le_mul_left h3 (by positivity)

/-! ### Localization -/

/-- Translation: `T_λ (f(· + m))(x) = T_λ f (x + m)`. -/
theorem weightedModSum_shift (c f : ℤ → ℂ) (m : ℤ) (lam : ℝ) (x : ℤ) :
    weightedModSum c (fun y => f (y + m)) lam x = weightedModSum c f lam (x + m) := by
  unfold weightedModSum
  refine tsum_congr fun n => ?_
  have : x + m - n = x - n + m := by ring
  simp only [this]

/-- Locality: for `c` carried by `[N]` and `x ∈ [N]`, `T_λ g(x)` only depends on `g` on
`[x - N, x - 1] ⊆ [-N, 2N]`. -/
theorem weightedModSum_eq_of_mem_bracket (N : ℕ+) (c g g' : ℤ → ℂ)
    (hc : ∀ n, n ∉ bracket N → c n = 0) (x : ℤ) (hx : x ∈ bracket N)
    (hgg : ∀ y ∈ maxWindow N, g y = g' y) (lam : ℝ) :
    weightedModSum c g lam x = weightedModSum c g' lam x := by
  rw [weightedModSum_eq_sum c g lam x (bracket N) hc,
    weightedModSum_eq_sum c g' lam x (bracket N) hc]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [hgg (x - n) ?_]
  rw [mem_bracket] at hx hn
  exact mem_maxWindow.2 ⟨by omega, by omega⟩

/-- **Localization** (Source: main paper `e:U3maxmod`, L718–L731, used at L1525–L1528): window `L²`
estimate for `T_λ`, `c` carried by `[N]`, implies the `ℓ²(ℤ)` estimate with the constant doubled. -/
theorem eLpNorm_iSup_weightedModSum_le (N : ℕ+) (c : ℤ → ℂ) (hc : ∀ n, n ∉ bracket N → c n = 0)
    {K : ℝ} (hK : 0 ≤ K)
    (hwin : ∀ g : ℤ → ℂ, (∀ y, y ∉ maxWindow N → g y = 0) →
      lpNormOn 2 (maxWindow N)
        (fun x => ((⨆ lam : ℝ, ‖weightedModSum c g lam x‖ : ℝ) : ℂ)) ≤
          K * lpNormOn 2 (maxWindow N) g)
    (f : ℤ → ℂ) :
    eLpNorm (fun x => ⨆ lam : ℝ, ‖weightedModSum c f lam x‖ₑ) 2 Measure.count ≤
      ENNReal.ofReal (2 * K) * eLpNorm f 2 Measure.count := by
  classical
  -- real maximal function
  obtain ⟨Sr, hSr⟩ : ∃ Sr : (ℤ → ℂ) → ℤ → ℝ,
      ∀ g x, Sr g x = ⨆ lam : ℝ, ‖weightedModSum c g lam x‖ := ⟨fun g x => _, fun _ _ => rfl⟩
  have hS : ∀ g x, (⨆ lam : ℝ, ‖weightedModSum c g lam x‖ₑ) = ENNReal.ofReal (Sr g x) :=
    fun g x => by rw [hSr]; exact iSup_enorm_weightedModSum_eq N c g hc x
  have hSr0 : ∀ g x, 0 ≤ Sr g x := fun g x => by rw [hSr]; exact iSup_norm_nonneg_real _
  -- the estimate for one shift
  have hshift : ∀ m : ℤ, ∑ x ∈ bracket N, ENNReal.ofReal (Sr f (x + m) ^ 2) ≤
      ENNReal.ofReal (K ^ 2) * ∑ y ∈ maxWindow N, ENNReal.ofReal (‖f (y + m)‖ ^ 2) := by
    intro m
    set g : ℤ → ℂ := fun y => if y ∈ maxWindow N then f (y + m) else 0 with hg
    have hgsupp : ∀ y, y ∉ maxWindow N → g y = 0 := fun y hy => by simp [hg, hy]
    have hlocal : ∀ x ∈ bracket N, Sr f (x + m) = Sr g x := by
      intro x hx
      have hfun : ∀ lam, weightedModSum c f lam (x + m) = weightedModSum c g lam x := by
        intro lam
        rw [← weightedModSum_shift c f m lam x]
        refine (weightedModSum_eq_of_mem_bracket N c _ _ hc x hx ?_ lam)
        intro y hy
        simp [hg, hy]
      rw [hSr, hSr]
      exact iSup_congr fun lam => by rw [hfun lam]
    have hwg := hwin g hgsupp
    simp only [← hSr] at hwg
    have hw := sum_sq_le_of_lpNormOn_le (maxWindow_nonempty N) hwg
    have hw' : ∑ x ∈ maxWindow N, Sr g x ^ 2 ≤
        K ^ 2 * ∑ y ∈ maxWindow N, ‖f (y + m)‖ ^ 2 := by
      have e1 : ∀ x, ‖((Sr g x : ℝ) : ℂ)‖ ^ 2 = Sr g x ^ 2 := fun x => by
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      have e2 : ∀ y ∈ maxWindow N, ‖g y‖ ^ 2 = ‖f (y + m)‖ ^ 2 := fun y hy => by
        simp [hg, hy]
      simp only [e1] at hw
      rw [Finset.sum_congr rfl e2] at hw
      exact hw
    calc ∑ x ∈ bracket N, ENNReal.ofReal (Sr f (x + m) ^ 2)
        = ∑ x ∈ bracket N, ENNReal.ofReal (Sr g x ^ 2) :=
          Finset.sum_congr rfl fun x hx => by rw [hlocal x hx]
      _ ≤ ∑ x ∈ maxWindow N, ENNReal.ofReal (Sr g x ^ 2) :=
          Finset.sum_le_sum_of_subset (bracket_subset_maxWindow N)
      _ = ENNReal.ofReal (∑ x ∈ maxWindow N, Sr g x ^ 2) :=
          (ENNReal.ofReal_sum_of_nonneg fun x _ => by positivity).symm
      _ ≤ ENNReal.ofReal (K ^ 2 * ∑ y ∈ maxWindow N, ‖f (y + m)‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal hw'
      _ = ENNReal.ofReal (K ^ 2) * ∑ y ∈ maxWindow N, ENNReal.ofReal (‖f (y + m)‖ ^ 2) := by
          rw [ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_sum_of_nonneg fun y _ => by positivity]
  -- sum over all shifts
  have hL : ∑' m : ℤ, ∑ x ∈ bracket N, ENNReal.ofReal (Sr f (x + m) ^ 2) =
      (((N : ℕ) : ℕ) : ℝ≥0∞) * ∑' z, ENNReal.ofReal (Sr f z ^ 2) := by
    rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
    have : ∀ x : ℤ, ∑' m : ℤ, ENNReal.ofReal (Sr f (x + m) ^ 2) =
        ∑' z : ℤ, ENNReal.ofReal (Sr f z ^ 2) := fun x =>
      (Equiv.addLeft x).tsum_eq (fun z => ENNReal.ofReal (Sr f z ^ 2))
    simp_rw [this, Finset.sum_const, card_bracket, nsmul_eq_mul]
  have hR : ∑' m : ℤ, ∑ y ∈ maxWindow N, ENNReal.ofReal (‖f (y + m)‖ ^ 2) =
      ((3 * (N : ℕ) + 1 : ℕ) : ℝ≥0∞) * ∑' z, ENNReal.ofReal (‖f z‖ ^ 2) := by
    rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
    have : ∀ y : ℤ, ∑' m : ℤ, ENNReal.ofReal (‖f (y + m)‖ ^ 2) =
        ∑' z : ℤ, ENNReal.ofReal (‖f z‖ ^ 2) := fun y =>
      (Equiv.addLeft y).tsum_eq (fun z => ENNReal.ofReal (‖f z‖ ^ 2))
    simp_rw [this, Finset.sum_const, card_maxWindow, nsmul_eq_mul]
  have hsum : (((N : ℕ) : ℕ) : ℝ≥0∞) * ∑' z, ENNReal.ofReal (Sr f z ^ 2) ≤
      ENNReal.ofReal (K ^ 2) * (((3 * (N : ℕ) + 1 : ℕ) : ℝ≥0∞) *
        ∑' z, ENNReal.ofReal (‖f z‖ ^ 2)) := by
    rw [← hL, ← hR, ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum hshift
  have hN0 : (((N : ℕ) : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast N.ne_zero
  have hNtop : (((N : ℕ) : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have h4 : ((3 * (N : ℕ) + 1 : ℕ) : ℝ≥0∞) ≤ 4 * (((N : ℕ) : ℕ) : ℝ≥0∞) := by
    have : (3 * (N : ℕ) + 1 : ℕ) ≤ 4 * (N : ℕ) := by have := N.pos; omega
    exact_mod_cast this
  have hA : ∑' z, ENNReal.ofReal (Sr f z ^ 2) ≤
      ENNReal.ofReal (4 * K ^ 2) * ∑' z, ENNReal.ofReal (‖f z‖ ^ 2) := by
    refine (ENNReal.mul_le_mul_iff_right hN0 hNtop).1 ?_
    calc (((N : ℕ) : ℕ) : ℝ≥0∞) * ∑' z, ENNReal.ofReal (Sr f z ^ 2)
        ≤ ENNReal.ofReal (K ^ 2) * (((3 * (N : ℕ) + 1 : ℕ) : ℝ≥0∞) *
            ∑' z, ENNReal.ofReal (‖f z‖ ^ 2)) := hsum
      _ ≤ ENNReal.ofReal (K ^ 2) * ((4 * (((N : ℕ) : ℕ) : ℝ≥0∞)) *
            ∑' z, ENNReal.ofReal (‖f z‖ ^ 2)) := by gcongr
      _ = (((N : ℕ) : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (4 * K ^ 2) *
            ∑' z, ENNReal.ofReal (‖f z‖ ^ 2)) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
          ring
  -- conclude
  have hlhs : ∀ x, (⨆ lam : ℝ, ‖weightedModSum c f lam x‖ₑ) ^ (2 : ℝ) =
      ENNReal.ofReal (Sr f x ^ 2) := fun x => by
    rw [hS f x, ofReal_rpow_two_of_nonneg (hSr0 f x)]
  rw [eLpNorm_two_count_enn_eq, eLpNorm_two_count_eq_tsum]
  simp_rw [hlhs, enorm_rpow_two_eq_ofReal]
  calc (∑' x, ENNReal.ofReal (Sr f x ^ 2)) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (4 * K ^ 2) * ∑' z, ENNReal.ofReal (‖f z‖ ^ 2)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hA (by norm_num)
    _ = ENNReal.ofReal (2 * K) * (∑' z, ENNReal.ofReal (‖f z‖ ^ 2)) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
        have hsq : (4 * K ^ 2 : ℝ) ^ (1 / 2 : ℝ) = 2 * K := by
          have : 4 * K ^ 2 = (2 * K) ^ 2 := by ring
          rw [this, ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
        rw [hsq]

/-- The modulated sum with a constant factor. -/
theorem weightedModSum_const_mul (r : ℂ) (c f : ℤ → ℂ) (lam : ℝ) (x : ℤ) :
    weightedModSum (fun n => r * c n) f lam x = r * weightedModSum c f lam x := by
  unfold weightedModSum
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  ring

/-- **Localization to `ℓ²(ℤ)`, smooth form** (Source: main paper `e:U3maxmod`, L718–L731, used at
L1525–L1528): for `φ ∈ C²`, `supp φ ⊆ [0, 1]`, `|φ|, |φ''| ≤ M`, every `w : ℤ → ℂ` and `f : ℤ → ℂ`,
`‖sup_λ |∑_n φ_N(n) f(x-n) w(n) e(λ n)|‖_{ℓ²(ℤ)} ≤ 320 M ‖w‖_{U³([N])} ‖f‖_{ℓ²(ℤ)}`. -/
theorem U3maxmod_smooth_ell2Z (N : ℕ+) {φ : ℝ → ℂ} {M : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : Function.support φ ⊆ Set.Icc 0 1) (h0 : ∀ t, ‖φ t‖ ≤ M)
    (h2 : ∀ t, ‖deriv (deriv φ) t‖ ≤ M) (w f : ℤ → ℂ) :
    eLpNorm (fun x => ⨆ lam : ℝ,
        ‖weightedModSum (fun n : ℤ => dilate ((N : ℕ) : ℝ) φ (n : ℝ) * w n) f lam x‖ₑ) 2
        Measure.count ≤
      ENNReal.ofReal (320 * M * gowersNormOn 3 (bracket N) w) * eLpNorm f 2 Measure.count := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (h0 0)
  have hφ0 : ∀ t, t ∉ Set.Ioo (0 : ℝ) 1 → φ t = 0 := fun t ht =>
    eq_zero_of_notMem_Ioo_of_support_Icc hφ.continuous hsupp ht
  set c : ℤ → ℂ := fun n => dilate ((N : ℕ) : ℝ) φ (n : ℝ) * w n with hcdef
  have hc : ∀ n, n ∉ bracket N → c n = 0 := fun n hn => by
    simp only [hcdef]
    rw [dilate_eq_zero_of_notMem_bracket N hφ0 n hn, zero_mul]
  have hK : 0 ≤ 160 * M * gowersNormOn 3 (bracket N) w := by
    have := gowersNormOn_nonneg 3 (bracket N) w
    positivity
  have hwin : ∀ g : ℤ → ℂ, (∀ y, y ∉ maxWindow N → g y = 0) →
      lpNormOn 2 (maxWindow N)
        (fun x => ((⨆ lam : ℝ, ‖weightedModSum c g lam x‖ : ℝ) : ℂ)) ≤
          (160 * M * gowersNormOn 3 (bracket N) w) * lpNormOn 2 (maxWindow N) g :=
    fun g hg => smooth_L2_bound N hφ hsupp h0 h2 w g hg
  have := eLpNorm_iSup_weightedModSum_le N c hc hK hwin f
  convert this using 3
  ring

end PrimeCarleson.Proof.Paper
