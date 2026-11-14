module

public import PrimeCarleson.Proof.Oplus.Conclusion.SmallCase
public import PrimeCarleson.Proof.Oplus.Decomposition.ModelOperator

/-!
# The integral estimate `L1except` and the conclusion of the proof ([O+] Section 7, L2555-L2700)

Source: [O+] `L1except`, L2563–L2570; [O+] `mainargumentsection`, L2557–L2562.

* `L1except` ([O+] (L1except), L2563-L2570): for `r > 2`, `r' ≤ p < 2r/(r-2)`, every finite
  separated family `𝔓` of `ρ`-multitiles (`ρ` any `1`- or `2`-index with `m, n ∈ {1, …, 4}`, any
  profile choice, any linearizing data), every `F` of finite positive measure, `|f| ≤ 1_F` and
  measurable `E` with `|E| ≤ 2` there is a measurable `G` with `|G| ≤ 1/4` and
  `∫_{E ∖ G} |𝒮^ρ[f]| ≤ C |F|^{1/p}` (the integral over `ℝ ∖ G` of `1_E |𝒮^ρ[f]|`). The constant
  depends only on `r`, `p` and the admissible constants (`C₂ = 2`). The two cases `|F| > 1` and
  `|F| ≤ 1` are `l1except_large` and `l1except_small`; `|F| ≤ 1` needs `p ≥ r'` and `|F| > 1` needs
  `p < 2r/(r-2)`. The hypothesis `1 ≤ |E|` of the source is not used here (only `|E| ≤ 2`).
* `mainargumentsection` (the inequality (halfgbound) for `1 ≤ |E| ≤ 2`, L2557-L2562): by Chebyshev's
  inequality, `|{x ∈ E : |𝒮^ρ[f](x)| > C (|F|/|E|)^{1/p}}| ≤ |E|/2`.

The model operator is `modelOp ch L 𝔓 f` (Decomposition/ModelOperator.lean); `treeSum ch f L E 𝔓`
is `1_E modelOp ch L 𝔓 f`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

section Main

/-- `p < 2r/(r-2)` is `1/p > 1/2 - 1/r`. -/
theorem one_half_sub_lt_of_lt {r p : ℝ} (hr : 2 < r) (hp0 : 0 < p) (hp : p < 2 * r / (r - 2)) :
    1 / 2 - 1 / r < 1 / p := by
  have hr0 : 0 < r := by linarith
  have hr2 : 0 < r - 2 := by linarith
  have h : 1 / (2 * r / (r - 2)) < 1 / p := one_div_lt_one_div_of_lt hp0 hp
  have e : 1 / (2 * r / (r - 2)) = 1 / 2 - 1 / r := by field_simp
  rwa [e] at h

/-- **`L1except`** ([O+] (L1except), L2563-L2570). -/
theorem L1except {r p : ℝ} (hr : 2 < r) (hp1 : Real.conjExponent r ≤ p)
    (hp2 : p < 2 * r / (r - 2)) {C₁ C₂ C₃ : ℝ} (hC : AdmissibleConstants C₁ C₂ C₃)
    (hC₂ : C₂ = 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo], ρ.IsStd → ∀ (ch : ProfileChoice)
      {f : ℝ → ℂ} {F E : Set ℝ}, MeasurableSet F → volume F ≠ 0 → volume F ≠ ⊤ →
      AEStronglyMeasurable f volume → (∀ᵐ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) →
      MeasurableSet E → volume E ≤ 2 → ∀ (L : Linearization r) (𝔓 : Finset (Multitile ρ)),
      Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ)) →
      ∃ G : Set ℝ, MeasurableSet G ∧ volume G ≤ 1 / 4 ∧
        ∫⁻ x in Gᶜ, ‖treeSum ch f L E 𝔓 x‖ₑ ≤
          ENNReal.ofReal (C * (volume F).toReal ^ (1 / p)) := by
  have hr1 : 1 < r := by linarith
  have hr'1 := one_lt_conjExponent hr1
  have hp0 : 0 < p := by linarith
  obtain ⟨C₁', hC₁'0, hlarge⟩ := l1except_large hr (one_half_sub_lt_of_lt hr hp0 hp2) hC hC₂
  obtain ⟨C₂', hC₂'0, hsmall⟩ := l1except_small hr hp1 hC
  refine ⟨max C₁' C₂', lt_max_of_lt_left hC₁'0, ?_⟩
  intro ρ _ hρ ch f F E hF hF0 hFt hfm hfF hE hE2 L 𝔓 hsep
  have hFvol : volume F = ENNReal.ofReal (volume F).toReal := (ENNReal.ofReal_toReal hFt).symm
  have hFm0 : 0 < (volume F).toReal := ENNReal.toReal_pos hF0 hFt
  have hFm : 0 ≤ (volume F).toReal ^ (1 / p) := by positivity
  rcases le_or_gt (volume F).toReal 1 with h1 | h1
  · obtain ⟨G, hGm, hGv, hG⟩ := hsmall hρ ch hF hfm hfF hE hE2 L hFm0 h1 hFvol 𝔓 hsep
    exact ⟨G, hGm, hGv, hG.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hFm))⟩
  · obtain ⟨G, hGm, hGv, hG⟩ := hlarge hρ ch hfm hfF hE hE2 L h1 hFvol 𝔓 hsep
    exact ⟨G, hGm, hGv, hG.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hFm))⟩

/-- The tree sum with the indicator `1_E` agrees with the model operator on `E`. -/
theorem treeSum_eq_modelOp_of_mem {ρ : Idx} {r : ℝ} (ch : ProfileChoice) (f : ℝ → ℂ)
    (L : Linearization r) {E : Set ℝ} (S : Finset (Multitile ρ)) {x : ℝ} (hx : x ∈ E) :
    treeSum ch f L E S x = modelOp ch L S f x := by
  simp [treeSum, modelOp, hx]

/-- **`mainargumentsection`** (the inequality (halfgbound) for `1 ≤ |E| ≤ 2`, L2557-L2562
and the Chebyshev reduction of L2563-L2570). Let `r > 2` and `r' ≤ p < 2r/(r-2)`. There is `C`
(depending on `r`, `p` and the admissible constants with `C₂ = 2`) such that for every `1`- or
`2`-index `ρ` with `m, n ∈ {1, …, 4}`, profile choice, linearizing data `L`, finite separated family
`𝔓` of `ρ`-multitiles, measurable `F` with `0 < |F| < ∞`, `f` with `|f| ≤ 1_F` and measurable `E`
with `1 ≤ |E| ≤ 2`,
`|{x ∈ E : |𝒮^ρ[f](x)| > C (|F|/|E|)^{1/p}}| ≤ |E|/2`. -/
theorem mainargumentsection {r p : ℝ} (hr : 2 < r) (hp1 : Real.conjExponent r ≤ p)
    (hp2 : p < 2 * r / (r - 2)) {C₁ C₂ C₃ : ℝ} (hC : AdmissibleConstants C₁ C₂ C₃)
    (hC₂ : C₂ = 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo], ρ.IsStd → ∀ (ch : ProfileChoice)
      {f : ℝ → ℂ} {F E : Set ℝ}, MeasurableSet F → volume F ≠ 0 → volume F ≠ ⊤ →
      AEStronglyMeasurable f volume → (∀ᵐ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) →
      MeasurableSet E → 1 ≤ volume E → volume E ≤ 2 → ∀ (L : Linearization r)
      (𝔓 : Finset (Multitile ρ)), Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ)) →
      volume {x | x ∈ E ∧ C * ((volume F).toReal / (volume E).toReal) ^ (1 / p) <
        ‖modelOp ch L 𝔓 f x‖} ≤ volume E / 2 := by
  have hr1 : 1 < r := by linarith
  have hr'1 := one_lt_conjExponent hr1
  have hp0 : 0 < p := by linarith
  obtain ⟨C₀, hC₀0, hL⟩ := L1except hr hp1 hp2 hC hC₂
  refine ⟨8 * C₀, by positivity, ?_⟩
  intro ρ _ hρ ch f F E hF hF0 hFt hfm hfF hE hE1 hE2 L 𝔓 hsep
  obtain ⟨G, hGm, hGv, hG⟩ := hL hρ ch hF hF0 hFt hfm hfF hE hE2 L 𝔓 hsep
  set Fm : ℝ := (volume F).toReal with hFm
  set Em : ℝ := (volume E).toReal with hEm
  have hFm0 : 0 < Fm := ENNReal.toReal_pos hF0 hFt
  have hEt : volume E ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofNat_ne_top hE2
  have hEm1 : 1 ≤ Em := by
    have := ENNReal.toReal_mono hEt hE1
    simpa using this
  have hEm2 : Em ≤ 2 := by
    have := ENNReal.toReal_mono ENNReal.ofNat_ne_top hE2
    simpa using this
  have hEm0 : 0 < Em := by linarith
  set lam : ℝ := 8 * C₀ * (Fm / Em) ^ (1 / p) with hlam
  have hlam0 : 0 < lam := by positivity
  set S : ℝ → ℂ := treeSum ch f L E 𝔓 with hS
  have hSm : Measurable fun x => ‖S x‖ₑ :=
    (measurable_treeSum ch f L hE 𝔓).enorm
  -- the set is contained in `G` and in a superlevel set of `|S|` outside `G`
  have hsub : {x | x ∈ E ∧ lam < ‖modelOp ch L 𝔓 f x‖} ⊆
      G ∪ ({x | ENNReal.ofReal lam ≤ ‖S x‖ₑ} ∩ Gᶜ) := by
    intro x ⟨hxE, hx⟩
    by_cases hxG : x ∈ G
    · exact Or.inl hxG
    · refine Or.inr ⟨?_, hxG⟩
      change ENNReal.ofReal lam ≤ ‖S x‖ₑ
      rw [hS, treeSum_eq_modelOp_of_mem ch f L 𝔓 hxE, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hx.le
  have hmk := mul_meas_ge_le_lintegral₀ (μ := volume.restrict Gᶜ) hSm.aemeasurable
    (ENNReal.ofReal lam)
  have hlam' : ENNReal.ofReal lam ≠ 0 := (ENNReal.ofReal_pos.2 hlam0).ne'
  have hmeasset : MeasurableSet {x | ENNReal.ofReal lam ≤ ‖S x‖ₑ} :=
    measurableSet_le measurable_const hSm
  rw [Measure.restrict_apply hmeasset] at hmk
  have hbound : volume ({x | ENNReal.ofReal lam ≤ ‖S x‖ₑ} ∩ Gᶜ) ≤ 1 / 4 := by
    have h1 : volume ({x | ENNReal.ofReal lam ≤ ‖S x‖ₑ} ∩ Gᶜ) ≤
        (∫⁻ x in Gᶜ, ‖S x‖ₑ) / ENNReal.ofReal lam := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hlam') (Or.inl ENNReal.ofReal_ne_top), mul_comm]
      exact hmk
    refine h1.trans ?_
    have h2 : (∫⁻ x in Gᶜ, ‖S x‖ₑ) ≤ ENNReal.ofReal (C₀ * Fm ^ (1 / p)) := hG
    refine (ENNReal.div_le_div_right h2 _).trans ?_
    rw [← ENNReal.ofReal_div_of_pos hlam0]
    rw [show (1 / 4 : ℝ≥0∞) = ENNReal.ofReal (1 / 4) by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp]
    refine ENNReal.ofReal_le_ofReal ?_
    have hp1' : 1 / p ≤ 1 := by
      rw [div_le_one hp0]; linarith
    have e1 : Fm ^ (1 / p) = (Fm / Em) ^ (1 / p) * Em ^ (1 / p) := by
      rw [← Real.mul_rpow (by positivity) hEm0.le]; congr 1; field_simp
    have hEp : Em ^ (1 / p) ≤ 2 := by
      calc Em ^ (1 / p) ≤ Em ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hEm1 hp1'
        _ = Em := Real.rpow_one Em
        _ ≤ 2 := hEm2
    have hq : 0 < (Fm / Em) ^ (1 / p) := by positivity
    rw [div_le_iff₀ hlam0, hlam, e1]
    nlinarith [mul_le_mul_of_nonneg_left hEp (mul_nonneg hC₀0.le hq.le)]
  have hEhalf : (1 : ℝ≥0∞) / 2 ≤ volume E / 2 := by
    gcongr
  calc volume {x | x ∈ E ∧ 8 * C₀ * (Fm / Em) ^ (1 / p) < ‖modelOp ch L 𝔓 f x‖}
      ≤ volume (G ∪ ({x | ENNReal.ofReal lam ≤ ‖S x‖ₑ} ∩ Gᶜ)) := measure_mono hsub
    _ ≤ volume G + volume ({x | ENNReal.ofReal lam ≤ ‖S x‖ₑ} ∩ Gᶜ) := measure_union_le _ _
    _ ≤ 1 / 4 + 1 / 4 := add_le_add hGv hbound
    _ = 1 / 2 := by
        have q4 : (1 / 4 : ℝ≥0∞) = ENNReal.ofReal (1 / 4) := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
        have q2 : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
        rw [q4, q2, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num
    _ ≤ volume E / 2 := hEhalf

end Main

end PrimeCarleson.Proof.Oplus
