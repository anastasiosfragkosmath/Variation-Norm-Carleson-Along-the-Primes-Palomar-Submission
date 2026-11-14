module

public import PrimeCarleson.Proof.Oplus.DensityIncrement.Basic

/-!
# The truncated density ([O+] L1937-L1940)

Source: [O+] `trunctreehaslargedensity`, L1937–L1940: "Breaking the integral up into pieces and
applying a pigeonhole
argument, it follows from (treehaslargedensity) that for each `j` there is a positive integer
`ℓ_j` such that `|I_{T_j}| ≤ C 2^{-3ℓ_j} den^{-r'} ∫_{E ∩ 2^{ℓ_j} I_{T_j}}
∑_{k : ξ_{k-1}(x) ∈ ω_{T_j}} |a_k(x)|^{r'} dx`."

The source's one-sentence argument, written out (the paper does not give it):

* `treeWeight_le_tsum`, `lintegral_weight_le_tsum`: for `x ∈ 2^m I ∖ 2^{m-1} I` the weight
  `(1 + |x - c(I)|/|I|)^{-4}` is at most `2^{4 - 4m}`; hence the density integral is at most
  `∑_{m ≥ 1} 2^{8 - 4m} ∫_{E ∩ 2^m I} ∑ |a_k|^{r'} 1_{ω_T}(ξ_{k-1})`;
* `exists_trunc_density`: if (trunctreehaslargedensity) failed for every `ℓ ≥ 1` with the constant
  `C = 2^{8 + r'}`, the series would be at most `(den/2)^{r'} |I|`, contradicting
  (treehaslargedensity).

The statement avoids negative powers: `8^ℓ den^{r'} |I_T| ≤ 2^{8 + r'} ∫_{E ∩ 2^ℓ I_T} …`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

section Trunc

variable {ρ : Idx} {r : ℝ}

/-- The weight is dominated by a geometric series of indicators of the dilates. -/
theorem treeWeight_le_tsum (𝒯 : MultitileTree ρ) (x : ℝ) :
    treeWeight 𝒯 x ≤ ∑' m : ℕ, ENNReal.ofReal (16 * (1 / 16 : ℝ) ^ m) *
      (𝒯.I.dilate ((2 : ℝ) ^ (m + 1))).indicator (fun _ => (1 : ℝ≥0∞)) x := by
  have hI := 𝒯.I.length_pos
  set u : ℝ := |x - 𝒯.I.center| / 𝒯.I.length with hu
  have hu0 : 0 ≤ u := by positivity
  have hex : ∃ m : ℕ, u < (2 : ℝ) ^ m := pow_unbounded_of_one_lt u (by norm_num)
  classical
  set m₀ := Nat.find hex with hm₀
  have hm₀spec : u < (2 : ℝ) ^ m₀ := Nat.find_spec hex
  have hmem : x ∈ 𝒯.I.dilate ((2 : ℝ) ^ (m₀ + 1)) := by
    have h1 : |x - 𝒯.I.center| < (2 : ℝ) ^ m₀ * 𝒯.I.length := by
      rwa [hu, div_lt_iff₀ hI] at hm₀spec
    rw [abs_lt] at h1
    simp only [Dyadic.dilate, mem_Ico, pow_succ]
    constructor <;> nlinarith [h1.1, h1.2]
  have hbound : (1 + u) ^ (-4 : ℤ) ≤ 16 * (1 / 16 : ℝ) ^ m₀ := by
    rcases Nat.eq_zero_or_pos m₀ with h0 | hpos
    · rw [h0]
      simp only [pow_zero, mul_one]
      have : (1 : ℝ) ≤ (1 + u) ^ 4 := one_le_pow₀ (by linarith)
      rw [zpow_neg, zpow_ofNat]
      calc ((1 + u) ^ 4)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ this
        _ ≤ 16 := by norm_num
    · obtain ⟨m, hm⟩ : ∃ m, m₀ = m + 1 := ⟨m₀ - 1, by omega⟩
      have hnot : ¬ u < (2 : ℝ) ^ m := Nat.find_min hex (by omega)
      rw [not_lt] at hnot
      rw [hm, zpow_neg, zpow_ofNat]
      have h2 : (2 : ℝ) ^ m ≤ 1 + u := by linarith
      have h3 : ((2 : ℝ) ^ m) ^ 4 ≤ (1 + u) ^ 4 := pow_le_pow_left₀ (by positivity) h2 4
      have h4 : ((1 + u) ^ 4)⁻¹ ≤ (((2 : ℝ) ^ m) ^ 4)⁻¹ :=
        inv_anti₀ (by positivity) h3
      refine h4.trans (le_of_eq ?_)
      have h16 : ((2 : ℝ) ^ m) ^ 4 = 16 ^ m := by
        rw [← pow_mul, mul_comm m 4, pow_mul]; norm_num
      rw [h16, pow_succ, one_div, inv_pow]
      field_simp
  calc treeWeight 𝒯 x ≤ ENNReal.ofReal (16 * (1 / 16 : ℝ) ^ m₀) := by
        unfold treeWeight
        exact ENNReal.ofReal_le_ofReal hbound
    _ = ENNReal.ofReal (16 * (1 / 16 : ℝ) ^ m₀) *
        (𝒯.I.dilate ((2 : ℝ) ^ (m₀ + 1))).indicator (fun _ => (1 : ℝ≥0∞)) x := by
        rw [Set.indicator_of_mem hmem, mul_one]
    _ ≤ _ := ENNReal.le_tsum (f := fun m : ℕ => ENNReal.ofReal (16 * (1 / 16 : ℝ) ^ m) *
        (𝒯.I.dilate ((2 : ℝ) ^ (m + 1))).indicator (fun _ => (1 : ℝ≥0∞)) x) m₀

/-- The tail sum over a measurable set is measurable. -/
theorem Linearization.measurable_tailSum_of_measurableSet (L : Linearization r) {Ω : Set ℝ}
    (hΩ : MeasurableSet Ω) : Measurable (L.tailSum Ω) := by
  unfold Linearization.tailSum
  refine Finset.measurable_sum _ fun k _ => ?_
  exact ((L.measurable_a k).enorm.pow_const _).mul
    ((measurable_const.indicator hΩ).comp (L.measurable_ξ _))

/-- **Breaking the integral up into pieces** (L1937): the density integral of a tree is at most
`∑_{ℓ ≥ 1} 2^{8 - 4ℓ} ∫_{E ∩ 2^ℓ I_T} ∑_{k : ξ_{k-1}(x) ∈ ω_T} |a_k(x)|^{r'} dx`. -/
theorem lintegral_weight_le_tsum (L : Linearization r) (E : Set ℝ) (C₂ : ℝ)
    (𝒯 : MultitileTree ρ) :
    ∫⁻ x in E, treeWeight 𝒯 x * L.tailSum (𝒯.ωT C₂) x ≤
      ∑' m : ℕ, ENNReal.ofReal (16 * (1 / 16 : ℝ) ^ m) *
        ∫⁻ x in E ∩ 𝒯.I.dilate ((2 : ℝ) ^ (m + 1)), L.tailSum (𝒯.ωT C₂) x := by
  have hG : Measurable (L.tailSum (𝒯.ωT C₂)) :=
    L.measurable_tailSum_of_measurableSet measurableSet_Ico
  have hD : ∀ m : ℕ, MeasurableSet (𝒯.I.dilate ((2 : ℝ) ^ (m + 1))) := fun m => measurableSet_Ico
  calc ∫⁻ x in E, treeWeight 𝒯 x * L.tailSum (𝒯.ωT C₂) x
      ≤ ∫⁻ x in E, ∑' m : ℕ, ENNReal.ofReal (16 * (1 / 16 : ℝ) ^ m) *
          (𝒯.I.dilate ((2 : ℝ) ^ (m + 1))).indicator (L.tailSum (𝒯.ωT C₂)) x := by
        refine lintegral_mono fun x => ?_
        calc treeWeight 𝒯 x * L.tailSum (𝒯.ωT C₂) x
            ≤ (∑' m : ℕ, ENNReal.ofReal (16 * (1 / 16 : ℝ) ^ m) *
              (𝒯.I.dilate ((2 : ℝ) ^ (m + 1))).indicator (fun _ => (1 : ℝ≥0∞)) x) *
                L.tailSum (𝒯.ωT C₂) x := by gcongr; exact treeWeight_le_tsum 𝒯 x
          _ = _ := by
            rw [← ENNReal.tsum_mul_right]
            refine tsum_congr fun m => ?_
            by_cases hx : x ∈ 𝒯.I.dilate ((2 : ℝ) ^ (m + 1))
            · simp [Set.indicator_of_mem hx]
            · simp [Set.indicator_of_notMem hx]
    _ = ∑' m : ℕ, ∫⁻ x in E, ENNReal.ofReal (16 * (1 / 16 : ℝ) ^ m) *
          (𝒯.I.dilate ((2 : ℝ) ^ (m + 1))).indicator (L.tailSum (𝒯.ωT C₂)) x :=
        lintegral_tsum fun m => (measurable_const.mul (hG.indicator (hD m))).aemeasurable
    _ = _ := by
        refine tsum_congr fun m => ?_
        rw [lintegral_const_mul _ (hG.indicator (hD m)), lintegral_indicator (hD m),
          Measure.restrict_restrict (hD m), Set.inter_comm]

/-- **`trunctreehaslargedensity`** ([O+] L1937-L1940): if a tree `T` satisfies
(treehaslargedensity), `(1/|I_T|) ∫_E (1 + |x - c(I_T)|/|I_T|)^{-4} ∑_{k : ξ_{k-1}(x) ∈ ω_T}
|a_k(x)|^{r'} dx > (den/2)^{r'}`, then there is an integer `ℓ ≥ 1` with
`|I_T| ≤ 2^{8 + r'} 2^{-3ℓ} den^{-r'} ∫_{E ∩ 2^ℓ I_T} ∑_{k : ξ_{k-1}(x) ∈ ω_T} |a_k(x)|^{r'} dx`
(written without negative powers). The proof is the pigeonhole argument of the source: the weight is
at most `2^{8 - 4ℓ}` on `2^ℓ I_T ∖ 2^{ℓ-1} I_T`, and `∑_ℓ 2^{8-4ℓ} 2^{3ℓ} = 2^8`. -/
theorem exists_trunc_density (hr : 1 < r) {den : ℝ} (hden : 0 < den) (L : Linearization r)
    (E : Set ℝ) (C₂ : ℝ) (𝒯 : MultitileTree ρ)
    (h : ENNReal.ofReal (den / 2) ^ Real.conjExponent r < densityExpr L E C₂ 𝒯) :
    ∃ ℓ : ℕ, 1 ≤ ℓ ∧
      ENNReal.ofReal (8 ^ ℓ * den ^ Real.conjExponent r) * ENNReal.ofReal 𝒯.I.length ≤
        ENNReal.ofReal (2 ^ (8 + Real.conjExponent r)) *
          ∫⁻ x in E ∩ 𝒯.I.dilate ((2 : ℝ) ^ ℓ), L.tailSum (𝒯.ωT C₂) x := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  set p := Real.conjExponent r with hpdef
  have hp : 0 < p := by
    rw [hpdef]; unfold Real.conjExponent
    exact div_pos (by linarith) (by linarith)
  have hI := 𝒯.I.length_pos
  set lI : ℝ≥0∞ := ENNReal.ofReal 𝒯.I.length with hlI
  have hlI0 : lI ≠ 0 := (ENNReal.ofReal_pos.2 hI).ne'
  have hlIt : lI ≠ ∞ := ENNReal.ofReal_ne_top
  set C : ℝ≥0∞ := ENNReal.ofReal (2 ^ (8 + p)) with hC
  have hC0 : C ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hCt : C ≠ ∞ := ENNReal.ofReal_ne_top
  set J : ℕ → ℝ≥0∞ := fun m => ∫⁻ x in E ∩ 𝒯.I.dilate ((2 : ℝ) ^ m), L.tailSum (𝒯.ωT C₂) x
    with hJ
  set W : ℝ≥0∞ := ∫⁻ x in E, treeWeight 𝒯 x * L.tailSum (𝒯.ωT C₂) x with hW
  have hint : W ≤ ∑' m : ℕ, ENNReal.ofReal (16 * (1 / 16 : ℝ) ^ m) * J (m + 1) :=
    lintegral_weight_le_tsum L E C₂ 𝒯
  have h1 : C * W ≤ ∑' m : ℕ, ENNReal.ofReal (16 * (1 / 16 : ℝ) ^ m) * (C * J (m + 1)) := by
    calc C * W ≤ C * ∑' m : ℕ, ENNReal.ofReal (16 * (1 / 16 : ℝ) ^ m) * J (m + 1) := by
          gcongr
      _ = ∑' m : ℕ, C * (ENNReal.ofReal (16 * (1 / 16 : ℝ) ^ m) * J (m + 1)) :=
          ENNReal.tsum_mul_left.symm
      _ = _ := tsum_congr fun m => mul_left_comm _ _ _
  have h2 : ∑' m : ℕ, ENNReal.ofReal (16 * (1 / 16 : ℝ) ^ m) * (C * J (m + 1)) ≤
      ∑' m : ℕ, ENNReal.ofReal (16 * (1 / 16 : ℝ) ^ m) *
        (ENNReal.ofReal (8 ^ (m + 1) * den ^ p) * lI) :=
    ENNReal.tsum_le_tsum fun m => mul_le_mul' le_rfl (hcon (m + 1) (by omega)).le
  have hsum : Summable fun m : ℕ => 128 * den ^ p * (1 / 2 : ℝ) ^ m :=
    summable_geometric_two.mul_left _
  have h3 : ∑' m : ℕ, ENNReal.ofReal (16 * (1 / 16 : ℝ) ^ m) *
      (ENNReal.ofReal (8 ^ (m + 1) * den ^ p) * lI) = ENNReal.ofReal (256 * den ^ p) * lI := by
    have e1 : ∀ m : ℕ, ENNReal.ofReal (16 * (1 / 16 : ℝ) ^ m) *
        (ENNReal.ofReal (8 ^ (m + 1) * den ^ p) * lI) =
          ENNReal.ofReal (128 * den ^ p * (1 / 2 : ℝ) ^ m) * lI := fun m => by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      have : (1 / 16 : ℝ) ^ m * 8 ^ m = (1 / 2) ^ m := by rw [← mul_pow]; norm_num
      calc 16 * (1 / 16 : ℝ) ^ m * (8 ^ (m + 1) * den ^ p)
          = 16 * 8 * den ^ p * ((1 / 16 : ℝ) ^ m * 8 ^ m) := by ring
        _ = _ := by rw [this]; ring
    rw [tsum_congr e1, ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg
      (fun m => by positivity) hsum, tsum_mul_left, tsum_geometric_two]
    congr 2; ring
  have h4 : lI * ENNReal.ofReal (den / 2) ^ p < W := by
    have := h
    unfold densityExpr at this
    have h5 := ENNReal.mul_lt_mul_left hlI0 hlIt this
    rwa [mul_right_comm, ENNReal.inv_mul_cancel hlI0 hlIt, one_mul, mul_comm] at h5
  have h6 : C * (lI * ENNReal.ofReal (den / 2) ^ p) = ENNReal.ofReal (256 * den ^ p) * lI := by
    rw [mul_comm lI, ← mul_assoc, ENNReal.ofReal_rpow_of_nonneg (by positivity) hp.le,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.div_rpow hden.le (by norm_num)]
    have h8 : (2 : ℝ) ^ (8 : ℝ) = 256 := by
      rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    rw [h8]
    have : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
    field_simp
  have h7 : C * (lI * ENNReal.ofReal (den / 2) ^ p) < C * W := by
    rw [mul_comm C (lI * _), mul_comm C W]
    exact ENNReal.mul_lt_mul_left hC0 hCt h4
  rw [h6] at h7
  exact absurd (h7.trans_le (h1.trans (h2.trans (h3.le)))) (lt_irrefl _)

end Trunc

end PrimeCarleson.Proof.Oplus
