module

public import PrimeCarleson.Proof.Paper.P3.MaximalBounds
public import PrimeCarleson.Proof.Common.FourierR

/-!
# The smooth-cutoff maximal `U³` estimate

`sources/Variational_Carleson.tex` L727-L730 and L886-L892, the third display of Lemma
`e:U3maxmod` and the paragraph "To conclude the final point". Paper steps proved here:

* the bound on `φ̂` (L892; `phihat_L1_bound`):
  `‖φ̂‖_{L¹(ℝ)} ≤ 4 ‖φ‖_{C²}` for `φ ∈ C²`, `supp φ ⊆ [0, 1]` (`Common/FourierR.lean`);
* Fourier inversion and convexity (L886–L890; `fourier_inversion_convexity`): Fourier inversion
  `φ(n/N) = ∫ φ̂(ξ) e(ξ n / N) dξ` (`weightedModSum_smooth_eq_integral`) gives
  `‖sup_λ |∑_n φ_N(n) f(x-n) w(n) e(λ n)|‖_{L²([-N,2N])} ≤
  ∫ |φ̂(ξ)| ‖sup_λ |E_{[N]} f(x-n) (Mod_{ξ/N} w)(n) e(λ n)|‖_{L²([-N,2N])} dξ ≲
  ‖φ̂‖_{L¹} ‖w‖_{U³([N])} ‖f‖_{L²([-N,2N])}`. The modulation `Mod_{ξ/N}` is absorbed in the
  frequency (`e(ξ n/N) e(λ n) = e((λ + ξ/N) n)`, `iSup_norm_modAverage_modZ`): the maximal function
  of `Mod_{ξ/N} w` is that of `w`, so the integrand is the constant `‖w‖`-maximal function times
  `|φ̂(ξ)|`;
* the third display (L727–L730; `smooth_L2_bound`): with the explicit constant
  `160 M` for `φ ∈ C²`, `supp φ ⊆ [0,1]`, `|φ|, |φ''| ≤ M` (the paper's `‖φ‖_{C²} ≤ 1` is `M = 1`).

The smooth sum `∑_n φ_N(n) f(x-n) w(n) e(λ n)` is
`weightedModSum (fun n => dilate N φ n * w n) f lam x`, `φ_N = dilate N φ` (L568-L571). Since
`φ` is continuous and vanishes outside `[0, 1]`, `φ(0) = φ(1) = 0`, so `φ_N(n) ≠ 0` only for
`n ∈ [N]` (`dilate_eq_zero_of_notMem_bracket`), the set where only `w` is evaluated.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ComplexConjugate FourierTransform

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0

/-! ### `‖φ̂‖_{L¹} ≲ ‖φ‖_{C²}` -/

/-- **The bound `‖φ̂‖_{L¹} ≲ ‖φ‖_{C²}`** (Source: main paper `e:U3maxmod`, L892): for
`φ ∈ C²(ℝ)` supported in `[0, 1]` with `|φ|, |φ''| ≤ M` (in particular whenever `M` bounds the `C²`
norm, however defined), `‖φ̂‖_{L¹(ℝ)} ≤ 4 M`. -/
theorem phihat_L1_bound {φ : ℝ → ℂ} {M : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : Function.support φ ⊆ Set.Icc 0 1) (h0 : ∀ t, ‖φ t‖ ≤ M)
    (h2 : ∀ t, ‖deriv (deriv φ) t‖ ≤ M) : ∫ ξ, ‖𝓕 φ ξ‖ ≤ 4 * M :=
  Common.integral_norm_fourier_le_four_mul hφ hsupp h0 h2

/-! ### The smooth cutoff by Fourier inversion -/

/-- A continuous function supported in `[0, 1]` vanishes outside `(0, 1)`
(`φ(0) = φ(1) = 0` by continuity). -/
theorem eq_zero_of_notMem_Ioo_of_support_Icc {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hsupp : Function.support φ ⊆ Set.Icc 0 1) {t : ℝ} (ht : t ∉ Set.Ioo 0 1) : φ t = 0 := by
  have hcl : IsClosed {t : ℝ | φ t = 0} := isClosed_eq hφ continuous_const
  have h0 : φ 0 = 0 := by
    have hsub : Set.Iio (0 : ℝ) ⊆ {t : ℝ | φ t = 0} := fun y hy => by
      by_contra h
      have := (hsupp (show φ y ≠ 0 from h)).1
      exact absurd hy (not_lt.2 this)
    have := hcl.closure_subset_iff.2 hsub
    rw [closure_Iio' ⟨-1, by norm_num⟩] at this
    exact this (Set.mem_Iic.2 le_rfl)
  have h1 : φ 1 = 0 := by
    have hsub : Set.Ioi (1 : ℝ) ⊆ {t : ℝ | φ t = 0} := fun y hy => by
      by_contra h
      have := (hsupp (show φ y ≠ 0 from h)).2
      exact absurd hy (not_lt.2 this)
    have := hcl.closure_subset_iff.2 hsub
    rw [closure_Ioi' ⟨2, by norm_num⟩] at this
    exact this (Set.mem_Ici.2 le_rfl)
  by_contra h
  have hm := hsupp (show φ t ≠ 0 from h)
  rcases hm with ⟨hm0, hm1⟩
  rcases hm0.eq_or_lt with h' | h'
  · exact h (by rw [← h']; exact h0)
  rcases hm1.eq_or_lt with h'' | h''
  · exact h (by rw [h'']; exact h1)
  exact ht ⟨h', h''⟩

/-- `φ_N(n) = 0` for `n ∉ [N]`, when `φ` vanishes outside `(0, 1)`. -/
theorem dilate_eq_zero_of_notMem_bracket (N : ℕ+) {φ : ℝ → ℂ}
    (hφ0 : ∀ t, t ∉ Set.Ioo (0 : ℝ) 1 → φ t = 0) (n : ℤ) (hn : n ∉ bracket N) :
    dilate ((N : ℕ) : ℝ) φ (n : ℝ) = 0 := by
  have hNr : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hnot : (n : ℝ) / ((N : ℕ) : ℝ) ∉ Set.Ioo (0 : ℝ) 1 := by
    rw [mem_bracket] at hn
    intro ⟨h1, h2⟩
    rw [div_pos_iff_of_pos_right hNr] at h1
    rw [div_lt_one hNr] at h2
    have h1' : 0 < n := by exact_mod_cast h1
    have h2' : n < ((N : ℕ) : ℤ) := by exact_mod_cast h2
    omega
  simp [dilate, hφ0 _ hnot]

/-- **Fourier inversion for the smooth cutoff**: for `φ ∈ C²`, `supp φ ⊆ [0, 1]`,
`∑_n φ_N(n) f(x-n) w(n) e(λ n) = ∫ φ̂(ξ) A_{λ + ξ/N} f(x) dξ`, where
`A_{λ + ξ/N} = E_{n ∈ [N]} f(x-n) (Mod_{ξ/N} w)(n) e(λ n)`
(`φ(n/N) = ∫ φ̂(ξ) e(ξ n/N) dξ`). -/
theorem weightedModSum_smooth_eq_integral (N : ℕ+) {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : Function.support φ ⊆ Set.Icc 0 1) (w f : ℤ → ℂ) (lam : ℝ) (x : ℤ) :
    weightedModSum (fun n : ℤ => dilate ((N : ℕ) : ℝ) φ (n : ℝ) * w n) f lam x =
      ∫ ξ : ℝ, 𝓕 φ ξ * modAverage N w f (lam + ξ / ((N : ℕ) : ℝ)) x := by
  have hc : HasCompactSupport φ :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport φ) (closure_minimal hsupp isClosed_Icc)
  have hN0 : ((N : ℕ) : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
  have hint := Common.integrable_fourier_of_contDiff_two hφ hc
  have hφ0 : ∀ t, t ∉ Set.Ioo (0 : ℝ) 1 → φ t = 0 := fun t ht =>
    eq_zero_of_notMem_Ioo_of_support_Icc hφ.continuous hsupp ht
  rw [weightedModSum_eq_sum _ f lam x (bracket N) (fun n hn => by
    rw [dilate_eq_zero_of_notMem_bracket N hφ0 n hn, zero_mul])]
  have hR : ∀ ξ : ℝ, 𝓕 φ ξ * modAverage N w f (lam + ξ / ((N : ℕ) : ℝ)) x =
      ∑ n ∈ bracket N, ((N : ℂ)⁻¹ * f (x - n) * w n * e (lam * n)) *
        (𝓕 φ ξ * e (ξ * n / ((N : ℕ) : ℝ))) := by
    intro ξ
    rw [modAverage_eq, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have he : e ((lam + ξ / ((N : ℕ) : ℝ)) * n) =
        e (lam * n) * e (ξ * n / ((N : ℕ) : ℝ)) := by
      rw [← e_add]
      congr 1
      ring
    rw [he]
    ring
  simp_rw [hR]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [integral_const_mul]
    have := Common.fourier_inversion_div hφ hc (n : ℝ) ((N : ℕ) : ℝ)
    rw [← this]
    simp only [dilate, Complex.real_smul]
    push_cast
    ring
  · intro n hn
    refine Integrable.const_mul ?_ _
    refine hint.norm.mono' ?_ (ae_of_all _ fun ξ => ?_)
    · exact (hint.aestronglyMeasurable).mul
        (Common.continuous_e.comp (by fun_prop)).aestronglyMeasurable
    · rw [norm_mul, norm_e, mul_one]

/-- The pointwise form of the Fourier-inversion step: for every `λ` and `x`,
`|∑_n φ_N(n) f(x-n) w(n) e(λ n)| ≤ ‖φ̂‖_{L¹} sup_μ |A_μ f(x)|`. -/
theorem norm_weightedModSum_smooth_le (N : ℕ+) {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : Function.support φ ⊆ Set.Icc 0 1) (w f : ℤ → ℂ) (lam : ℝ) (x : ℤ) :
    ‖weightedModSum (fun n : ℤ => dilate ((N : ℕ) : ℝ) φ (n : ℝ) * w n) f lam x‖ ≤
      (∫ ξ : ℝ, ‖𝓕 φ ξ‖) * ⨆ μ : ℝ, ‖modAverage N w f μ x‖ := by
  have hc : HasCompactSupport φ :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport φ) (closure_minimal hsupp isClosed_Icc)
  have hint := Common.integrable_fourier_of_contDiff_two hφ hc
  rw [weightedModSum_smooth_eq_integral N hφ hsupp w f lam x]
  obtain ⟨m, hm, hmle⟩ := iSup_norm_eq_of_periodic (continuous_modAverage_lam N w f x)
    (periodic_modAverage_lam N w f x)
  rw [hm]
  calc ‖∫ ξ : ℝ, 𝓕 φ ξ * modAverage N w f (lam + ξ / ((N : ℕ) : ℝ)) x‖
      ≤ ∫ ξ : ℝ, ‖𝓕 φ ξ‖ * ‖modAverage N w f m x‖ :=
        norm_integral_le_of_norm_le (hint.norm.mul_const _) (ae_of_all _ fun ξ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hmle _) (norm_nonneg _))
    _ = (∫ ξ : ℝ, ‖𝓕 φ ξ‖) * ‖modAverage N w f m x‖ := integral_mul_const _ _

/-- **Fourier inversion and convexity** (Source: main paper `e:U3maxmod`, L886–L890): for `φ ∈ C²`,
`supp φ ⊆ [0, 1]`, every
`w : ℤ → ℂ` and `f` carried by `[-N, 2N]`,
`‖sup_λ |∑_n φ_N(n) f(x-n) w(n) e(λ n)|‖_{L²([-N,2N])} ≤
∫ |φ̂(ξ)| ‖sup_λ |E_{[N]} f(x-n) (Mod_{ξ/N} w)(n) e(λ n)|‖_{L²([-N,2N])} dξ ≤
40 ‖φ̂‖_{L¹} ‖w‖_{U³([N])} ‖f‖_{L²([-N,2N])}`. -/
theorem fourier_inversion_convexity (N : ℕ+) {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : Function.support φ ⊆ Set.Icc 0 1) (w f : ℤ → ℂ)
    (hf : ∀ y, y ∉ maxWindow N → f y = 0) :
    lpNormOn 2 (maxWindow N) (fun x => ((⨆ lam : ℝ, ‖weightedModSum
        (fun n : ℤ => dilate ((N : ℕ) : ℝ) φ (n : ℝ) * w n) f lam x‖ : ℝ) : ℂ)) ≤
      (∫ ξ : ℝ, ‖𝓕 φ ξ‖ * lpNormOn 2 (maxWindow N) (fun x => ((⨆ lam : ℝ,
          ‖modAverage N (modZ (ξ / ((N : ℕ) : ℝ)) w) f lam x‖ : ℝ) : ℂ))) ∧
    (∫ ξ : ℝ, ‖𝓕 φ ξ‖ * lpNormOn 2 (maxWindow N) (fun x => ((⨆ lam : ℝ,
          ‖modAverage N (modZ (ξ / ((N : ℕ) : ℝ)) w) f lam x‖ : ℝ) : ℂ))) ≤
      40 * (∫ ξ : ℝ, ‖𝓕 φ ξ‖) * gowersNormOn 3 (bracket N) w * lpNormOn 2 (maxWindow N) f := by
  set K : ℝ := ∫ ξ : ℝ, ‖𝓕 φ ξ‖ with hK
  have hK0 : 0 ≤ K := integral_nonneg fun _ => norm_nonneg _
  set c₀ : ℝ := lpNormOn 2 (maxWindow N)
    (fun x => ((⨆ lam : ℝ, ‖modAverage N w f lam x‖ : ℝ) : ℂ)) with hc₀
  have hinv : ∀ ξ : ℝ, lpNormOn 2 (maxWindow N) (fun x => ((⨆ lam : ℝ,
      ‖modAverage N (modZ (ξ / ((N : ℕ) : ℝ)) w) f lam x‖ : ℝ) : ℂ)) = c₀ := fun ξ => by
    simp_rw [iSup_norm_modAverage_modZ]
    rfl
  have hint : (∫ ξ : ℝ, ‖𝓕 φ ξ‖ * lpNormOn 2 (maxWindow N) (fun x => ((⨆ lam : ℝ,
          ‖modAverage N (modZ (ξ / ((N : ℕ) : ℝ)) w) f lam x‖ : ℝ) : ℂ))) = K * c₀ := by
    simp_rw [hinv]
    exact integral_mul_const _ _
  rw [hint]
  refine ⟨?_, ?_⟩
  · have hpt : ∀ x ∈ maxWindow N, ‖((⨆ lam : ℝ, ‖weightedModSum
        (fun n : ℤ => dilate ((N : ℕ) : ℝ) φ (n : ℝ) * w n) f lam x‖ : ℝ) : ℂ)‖ ≤
        ‖(K : ℂ) * ((⨆ lam : ℝ, ‖modAverage N w f lam x‖ : ℝ) : ℂ)‖ := by
      intro x _
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.iSup_nonneg fun _ =>
        norm_nonneg _), norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK0,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.iSup_nonneg fun _ =>
        norm_nonneg _)]
      exact ciSup_le fun lam => norm_weightedModSum_smooth_le N hφ hsupp w f lam x
    refine (lpNormOn_mono two_pos _ hpt).trans (le_of_eq ?_)
    have := lpNormOn_smul two_pos (K : ℂ) (maxWindow N)
      (fun x => ((⨆ lam : ℝ, ‖modAverage N w f lam x‖ : ℝ) : ℂ))
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK0] at this
    exact this
  · have := U3maxmod_L2 N w f hf
    have h0 : 0 ≤ K := hK0
    nlinarith [mul_le_mul_of_nonneg_left this h0]

/-- **The third display of `e:U3maxmod`** (Source: main paper `e:U3maxmod`, L727–L730): for
`φ ∈ C²`, `supp φ ⊆ [0, 1]`, `|φ|, |φ''| ≤ M` (the paper's `‖φ‖_{C²} ≤ 1` is `M = 1`), every
`w : ℤ → ℂ` and `f` carried by `[-N, 2N]`,
`‖sup_λ |∑_n φ_N(n) f(x-n) w(n) e(λ n)|‖_{L²([-N,2N])} ≤
160 M ‖w‖_{U³([N])} ‖f‖_{L²([-N,2N])}`. -/
theorem smooth_L2_bound (N : ℕ+) {φ : ℝ → ℂ} {M : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : Function.support φ ⊆ Set.Icc 0 1) (h0 : ∀ t, ‖φ t‖ ≤ M)
    (h2 : ∀ t, ‖deriv (deriv φ) t‖ ≤ M) (w f : ℤ → ℂ)
    (hf : ∀ y, y ∉ maxWindow N → f y = 0) :
    lpNormOn 2 (maxWindow N) (fun x => ((⨆ lam : ℝ, ‖weightedModSum
        (fun n : ℤ => dilate ((N : ℕ) : ℝ) φ (n : ℝ) * w n) f lam x‖ : ℝ) : ℂ)) ≤
      160 * M * gowersNormOn 3 (bracket N) w * lpNormOn 2 (maxWindow N) f := by
  obtain ⟨h1, h3⟩ := fourier_inversion_convexity N hφ hsupp w f hf
  have hL1 := phihat_L1_bound hφ hsupp h0 h2
  have hn1 : 0 ≤ gowersNormOn 3 (bracket N) w := gowersNormOn_nonneg _ _ _
  have hn2 : 0 ≤ lpNormOn 2 (maxWindow N) f := lpNormOn_nonneg _ _ _
  have hprod : 0 ≤ gowersNormOn 3 (bracket N) w * lpNormOn 2 (maxWindow N) f := mul_nonneg hn1 hn2
  calc _ ≤ _ := h1
    _ ≤ _ := h3
    _ ≤ 40 * (4 * M) * gowersNormOn 3 (bracket N) w * lpNormOn 2 (maxWindow N) f := by
        have : 40 * (∫ ξ : ℝ, ‖𝓕 φ ξ‖) ≤ 40 * (4 * M) := by linarith
        calc 40 * (∫ ξ : ℝ, ‖𝓕 φ ξ‖) * gowersNormOn 3 (bracket N) w * lpNormOn 2 (maxWindow N) f
            = (40 * (∫ ξ : ℝ, ‖𝓕 φ ξ‖)) * (gowersNormOn 3 (bracket N) w *
                lpNormOn 2 (maxWindow N) f) := by ring
          _ ≤ (40 * (4 * M)) * (gowersNormOn 3 (bracket N) w * lpNormOn 2 (maxWindow N) f) :=
              mul_le_mul_of_nonneg_right this hprod
          _ = _ := by ring
    _ = 160 * M * gowersNormOn 3 (bracket N) w * lpNormOn 2 (maxWindow N) f := by ring

end PrimeCarleson.Proof.Paper
