module

public import PrimeCarleson.Proof.Paper.P4a.LocalVariation
public import PrimeCarleson.Proof.Paper.P4a.EndpointHY

/-!
# The embedding bound `e:embed` for the `r`-variation of a trigonometric polynomial

Source: main paper `e:embed`, L1104–L1137 (the local variation and the endpoint term are in
`LocalVariation` and `EndpointHY`). For `N₀ ≥ 1`, `c : ℤ → ℂ` and `P(λ) = ∑_{|n| ≤ N₀} c_n e(λ n)`,

`V^r(P(λ) : λ ∈ 𝕋) ≤ C_r N₀^{1/r} (∑_{|n| ≤ N₀} |c_n|^{r'})^{1/r'}` (`embed_variation`),

for `2 ≤ r < ∞`, `1/r + 1/r' = 1`, with `C_r` depending only on `r`. The proof is the paper's:

* `rVariationOn_Ico_le_split` (the split of `e:embed`, L1110–L1115): the Jones-Seeger-Wright split
  (`Common.rVariationOn_iUnion_le_norm`) for the partition of `[0, 1)` into the intervals
  `I_j = [j/N₀, (j+1)/N₀)`, with the left endpoints `j/N₀ ∈ I_j` as reference points (so that
  no periodicity of `P` is needed);
* `local_variation_hoelder`: `(∑_j V^r(P : I_j)^r)^{1/r} ≤ N₀^{-1/r'} ‖P'‖_{L^r(𝕋)}`;
* `derivative_hausdorffYoung` (L1121–L1128): by Hausdorff-Young on `𝕋`
  applied to the coefficients `2πi n c_n`, `N₀^{-1/r'} ‖P'‖_{L^r(𝕋)} ≤ 2π C_r N₀^{1/r} ‖c‖_{ℓ^{r'}}`
  (the constant is `2π C_r`);
* `endpoint_hausdorffYoung`: `(∑_j |P(j/N₀)|^r)^{1/r} ≲_r N₀^{1/r} ‖c‖_{ℓ^{r'}}`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

/-! ### The derivative of a trigonometric polynomial -/

/-- `d/dξ e(nξ) = 2πi n e(nξ)`. -/
theorem hasDerivAt_e_mul_const (n ξ : ℝ) :
    HasDerivAt (fun ξ : ℝ => e (n * ξ)) (2 * Real.pi * Complex.I * n * e (n * ξ)) ξ := by
  have h1 : HasDerivAt (fun ξ : ℝ => ((n * ξ : ℝ) : ℂ)) (n : ℂ) ξ := by
    have := ((hasDerivAt_id ξ).const_mul n).ofReal_comp
    simpa using this
  have h2 := (h1.const_mul (2 * Real.pi * Complex.I)).cexp
  convert h2 using 1
  · ext ξ
    simp [e]
  · simp [e]
    ring

/-- The derivative of the trigonometric polynomial `ξ ↦ ∑_{n ∈ S} c_n e(nξ)` is the
trigonometric polynomial with coefficients `2πi n c_n` (L1121-L1127). -/
theorem hasDerivAt_trigSum (S : Finset ℤ) (c : ℤ → ℂ) (ξ : ℝ) :
    HasDerivAt (trigSum S c) (trigSum S (fun n => 2 * Real.pi * Complex.I * n * c n) ξ) ξ := by
  have h : ∀ n ∈ S, HasDerivAt (fun ξ : ℝ => c n * e ((n : ℝ) * ξ))
      (2 * Real.pi * Complex.I * n * c n * e ((n : ℝ) * ξ)) ξ := by
    intro n _
    have := (hasDerivAt_e_mul_const (n : ℝ) ξ).const_mul (c n)
    convert this using 1
    push_cast
    ring
  exact HasDerivAt.fun_sum h


/-! ### The splitting and the sum `e:embed` -/

/-- The intervals `I_j = [j/M, (j+1)/M)`, `0 ≤ j < M`, partition `[0, 1)`. -/
theorem iUnion_Ico_div_eq_Ico_zero_one {M : ℕ} (hM : 0 < M) :
    (⋃ j : Fin M, Ico ((j : ℝ) / M) (((j : ℝ) + 1) / M)) = Ico (0 : ℝ) 1 := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  ext x
  simp only [mem_iUnion, mem_Ico]
  constructor
  · rintro ⟨j, h1, h2⟩
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    have hj1 : (j : ℝ) + 1 ≤ M := by exact_mod_cast j.2
    exact ⟨h1.trans' (div_nonneg hj0 hMr.le), lt_of_lt_of_le h2 ((div_le_one hMr).2 hj1)⟩
  · rintro ⟨h0, h1⟩
    have hxM0 : 0 ≤ x * M := mul_nonneg h0 hMr.le
    have hxM1 : x * M < M := by nlinarith
    have hlt : ⌊x * M⌋₊ < M := by
      rw [Nat.floor_lt hxM0]
      exact_mod_cast hxM1
    refine ⟨⟨⌊x * M⌋₊, hlt⟩, ?_, ?_⟩
    · simp only
      rw [div_le_iff₀ hMr]
      exact Nat.floor_le hxM0
    · simp only
      rw [lt_div_iff₀ hMr]
      exact Nat.lt_floor_add_one _

/-- **The split of `e:embed`** (L1110–L1115): for `1 ≤ r`, `M ≥ 1` and any family `a : ℝ → ℂ`,
with `I_j = [j/M, (j+1)/M)`,
`V^r(a : [0, 1)) ≤ 3 (∑_{j<M} V^r(a : I_j)^r)^{1/r} + 2 (∑_{j<M} |a(j/M)|^r)^{1/r}`
(`e:split` with the reference points `j/M ∈ I_j`, absolute constants `3` and `2`). Source: main
paper `e:embed`, L1110–L1115. -/
theorem rVariationOn_Ico_le_split {r : ℝ} (hr : 1 ≤ r) {M : ℕ} (hM : 0 < M) (a : ℝ → ℂ) :
    rVariationOn r (Ico (0 : ℝ) 1) a ≤
      3 * (∑ j : Fin M, rVariationOn r (Ico ((j : ℝ) / M) (((j : ℝ) + 1) / M)) a ^ r) ^ (1 / r) +
        2 * (∑ j : Fin M, ‖a ((j : ℝ) / M)‖ₑ ^ r) ^ (1 / r) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have h := rVariationOn_iUnion_le_norm hr
    (fun j : Fin M => Ico ((j : ℝ) / M) (((j : ℝ) + 1) / M))
    (fun j j' hjj' x hx y hy => by
      have h1 : (j : ℝ) + 1 ≤ j' := by exact_mod_cast hjj'
      have h2 : ((j : ℝ) + 1) / M ≤ (j' : ℝ) / M := div_le_div_of_nonneg_right h1 hMr.le
      exact lt_of_lt_of_le hx.2 (h2.trans hy.1))
    (fun j => (j : ℝ) / M)
    (fun j => ⟨le_rfl, by gcongr; linarith⟩) a
  rwa [iUnion_Ico_div_eq_Ico_zero_one hM] at h

/-- **The Hausdorff–Young step for the derivative in `e:embed`** (L1121–L1128): for conjugate
exponents `2 ≤ r`, `r'` there is a constant `C` depending only on `r` such that for every `M ≥ 1`
and `c : ℤ → ℂ`, with `P'(λ) = ∑_{|n| ≤ M} 2πi n c_n e(nλ)`,
`M^{-1/r'} ‖P'‖_{L^r(𝕋)} ≤ C M^{1/r} (∑_{|n| ≤ M} |c_n|^{r'})^{1/r'}`; here `C = 2π C_r` with `C_r`
the constant of `Common.hausdorffYoung_T`. The factor
`|n| ≤ M` turns `M^{-1/r'}` into `M^{1/r}`. Source: main paper `e:embed`, L1121–L1128. -/
theorem derivative_hausdorffYoung {r r' : ℝ} (hr : 2 ≤ r) (hrr' : r.HolderConjugate r') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℕ), 0 < M → ∀ c : ℤ → ℂ,
      ENNReal.ofReal ((M : ℝ) ^ (-(1 / r'))) *
        eLpNorm (trigSum (Finset.Icc (-(M : ℤ)) M) (fun n => 2 * Real.pi * Complex.I * n * c n))
          (ENNReal.ofReal r) (volume.restrict (Ioc (0 : ℝ) 1)) ≤
      ENNReal.ofReal (C * (M : ℝ) ^ (1 / r) *
        (∑ n ∈ Finset.Icc (-(M : ℤ)) M, ‖c n‖ ^ r') ^ (1 / r')) := by
  obtain ⟨C₀, hC₀, hHY⟩ := hausdorffYoung_T hr hrr'
  have hr0 : 0 < r := by linarith
  have hr'0 : 0 < r' := hrr'.symm.pos
  refine ⟨2 * Real.pi * C₀, by positivity, fun M hM c => ?_⟩
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  set S : Finset ℤ := Finset.Icc (-(M : ℤ)) M with hS
  set b : ℤ → ℂ := fun n => 2 * Real.pi * Complex.I * n * c n with hb
  rw [eLpNorm_restrict_Ioc_eq_ofReal_integral (continuous_trigSum S b) hr0,
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 := hHY S b
  have hnb : ∀ n ∈ S, ‖b n‖ ≤ 2 * Real.pi * M * ‖c n‖ := by
    intro n hn
    have hn' : |(n : ℝ)| ≤ M := by
      have := Finset.mem_Icc.1 hn
      rw [abs_le]
      exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
    have hbn : ‖b n‖ = 2 * Real.pi * |(n : ℝ)| * ‖c n‖ := by
      simp only [hb, norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_intCast]
    rw [hbn]
    gcongr
  have h2 : (∑ n ∈ S, ‖b n‖ ^ r') ^ (1 / r') ≤
      2 * Real.pi * M * (∑ n ∈ S, ‖c n‖ ^ r') ^ (1 / r') := by
    calc (∑ n ∈ S, ‖b n‖ ^ r') ^ (1 / r')
        ≤ (∑ n ∈ S, (2 * Real.pi * M * ‖c n‖) ^ r') ^ (1 / r') := by
          gcongr with n hn
          exact hnb n hn
      _ = (∑ n ∈ S, (2 * Real.pi * M) ^ r' * ‖c n‖ ^ r') ^ (1 / r') := by
          congr 1
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Real.mul_rpow (by positivity) (norm_nonneg _)]
      _ = 2 * Real.pi * M * (∑ n ∈ S, ‖c n‖ ^ r') ^ (1 / r') := by
          rw [← Finset.mul_sum,
            Real.mul_rpow (by positivity) (Finset.sum_nonneg fun _ _ => by positivity),
            ← Real.rpow_mul (by positivity), mul_one_div_cancel hr'0.ne', Real.rpow_one]
  have hsum : (r)⁻¹ + r'⁻¹ = 1 := by simpa using hrr'.inv_add_inv_eq_inv
  have hMpow : (M : ℝ) ^ (-(1 / r')) * M = (M : ℝ) ^ (1 / r) := by
    rw [← Real.rpow_add_one hMr.ne']
    congr 1
    have : 1 / r = 1 - 1 / r' := by
      rw [one_div, one_div]; linarith
    rw [this]; ring
  calc (M : ℝ) ^ (-(1 / r')) * (∫ ξ in (0 : ℝ)..1, ‖trigSum S b ξ‖ ^ r) ^ (1 / r)
      ≤ (M : ℝ) ^ (-(1 / r')) * (C₀ * (∑ n ∈ S, ‖b n‖ ^ r') ^ (1 / r')) := by
        gcongr
        exact h1
    _ ≤ (M : ℝ) ^ (-(1 / r')) * (C₀ * (2 * Real.pi * M * (∑ n ∈ S, ‖c n‖ ^ r') ^ (1 / r'))) := by
        gcongr
    _ = 2 * Real.pi * C₀ * (M : ℝ) ^ (1 / r) * (∑ n ∈ S, ‖c n‖ ^ r') ^ (1 / r') := by
        rw [← hMpow]
        ring


/-- `(∑ ‖f i‖ₑ^r)^{1/r}` is the `ofReal` of the real `ℓ^r` norm. -/
theorem sum_enorm_rpow_rpow_eq_ofReal {ι : Type*} (s : Finset ι) (f : ι → ℂ) {r : ℝ} (hr : 0 < r) :
    (∑ i ∈ s, ‖f i‖ₑ ^ r) ^ (1 / r) = ENNReal.ofReal ((∑ i ∈ s, ‖f i‖ ^ r) ^ (1 / r)) := by
  have h : ∀ i ∈ s, ‖f i‖ₑ ^ r = ENNReal.ofReal (‖f i‖ ^ r) := fun i _ => by
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr.le]
  rw [Finset.sum_congr rfl h, ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity),
    ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity)
      (one_div_pos.2 hr).le]

/-- **`e:embed`** (L1104-L1137): for conjugate exponents `2 ≤ r`, `r'` there is a constant `C`
depending only on `r` such that for every `N₀ ≥ 1` (the paper assumes `N₀ ≥ 2`, `r > 2`) and every
`c : ℤ → ℂ`, with `P(λ) = ∑_{|n| ≤ N₀} c_n e(λ n)`,
`V^r(P(λ) : λ ∈ 𝕋) ≤ C N₀^{1/r} (∑_{|n| ≤ N₀} |c_n|^{r'})^{1/r'}` (`𝕋 = [0, 1)`, the index set of
the `rVariation`). Source: main paper `e:embed`, L1104–L1109; `C = 3 · 2π C_r + 2 · 3 C_r`
with `C_r` the Hausdorff-Young constants. -/
theorem embed_variation {r r' : ℝ} (hr : 2 ≤ r) (hrr' : r.HolderConjugate r') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N₀ : ℕ), 0 < N₀ → ∀ c : ℤ → ℂ,
      rVariationOn r (Ico (0 : ℝ) 1)
          (fun lam => ∑ n ∈ Finset.Icc (-(N₀ : ℤ)) N₀, c n * e (lam * n)) ≤
        ENNReal.ofReal (C * (N₀ : ℝ) ^ (1 / r) *
          (∑ n ∈ Finset.Icc (-(N₀ : ℤ)) N₀, ‖c n‖ ^ r') ^ (1 / r')) := by
  obtain ⟨Cd, hCd, hD⟩ := derivative_hausdorffYoung hr hrr'
  obtain ⟨Ce, hCe, hE⟩ := endpoint_hausdorffYoung hr hrr'
  have hr0 : 0 < r := by linarith
  refine ⟨3 * Cd + 2 * Ce, by positivity, fun M hM c => ?_⟩
  set S : Finset ℤ := Finset.Icc (-(M : ℤ)) M with hS
  set P : ℝ → ℂ := fun lam => ∑ n ∈ S, c n * e (lam * n) with hP
  set T : ℝ := (∑ n ∈ S, ‖c n‖ ^ r') ^ (1 / r') with hT
  have hPt : P = trigSum S c := by
    funext lam
    simp only [hP, trigSum, mul_comm lam]
  have hPd : ∀ x, HasDerivAt P (trigSum S (fun n => 2 * Real.pi * Complex.I * n * c n) x) x := by
    intro x
    rw [hPt]
    exact hasDerivAt_trigSum S c x
  have hPd' : Continuous (trigSum S (fun n => 2 * Real.pi * Complex.I * n * c n)) :=
    continuous_trigSum _ _
  have h1 := rVariationOn_Ico_le_split hrr'.lt.le hM P
  have h2 := local_variation_hoelder hrr' hM hPd hPd'
  have h3 := hD M hM c
  have h4 := hE M hM c
  have hA : (∑ j : Fin M, rVariationOn r (Ico ((j : ℝ) / M) (((j : ℝ) + 1) / M)) P ^ r) ^ (1 / r) ≤
      ENNReal.ofReal (Cd * (M : ℝ) ^ (1 / r) * T) := h2.trans h3
  have hB : (∑ j : Fin M, ‖P ((j : ℝ) / M)‖ₑ ^ r) ^ (1 / r) ≤
      ENNReal.ofReal (Ce * (M : ℝ) ^ (1 / r) * T) := by
    rw [sum_enorm_rpow_rpow_eq_ofReal _ _ hr0]
    refine ENNReal.ofReal_le_ofReal ?_
    have := Fin.sum_univ_eq_sum_range (fun j : ℕ => ‖P ((j : ℝ) / M)‖ ^ r) M
    rw [this]
    exact h4
  calc rVariationOn r (Ico (0 : ℝ) 1) P
      ≤ 3 * (∑ j : Fin M, rVariationOn r (Ico ((j : ℝ) / M) (((j : ℝ) + 1) / M)) P ^ r) ^ (1 / r) +
        2 * (∑ j : Fin M, ‖P ((j : ℝ) / M)‖ₑ ^ r) ^ (1 / r) := h1
    _ ≤ 3 * ENNReal.ofReal (Cd * (M : ℝ) ^ (1 / r) * T) +
        2 * ENNReal.ofReal (Ce * (M : ℝ) ^ (1 / r) * T) := by gcongr
    _ = ENNReal.ofReal ((3 * Cd + 2 * Ce) * (M : ℝ) ^ (1 / r) * T) := by
        rw [← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_ofNat 2,
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end PrimeCarleson.Proof.Paper
