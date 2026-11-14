module

public import PrimeCarleson.Proof.Oplus.Conclusion.Holder

/-!
# The tree estimate in the form used by the Hölder splitting ([O+] L2641-L2650)

The summations of [O+] `L1except` for large and small `F`: `treeestimate` with
`q = r'` (large `F`) or `q = 1` (small `F`), restated for the regions `ℝ ∖ 2^{ℓ-1} I_T` of
`Holder.lean` (`tailSet`): for every `ℓ`,
`∫ |1_{tail_ℓ} ∑_{P ∈ T} ⟨f, φ_P⟩ φ_P a_P 1_E|^q ≤ (K w_ℓ ene den^{min(1, r'/q)})^q |I_T|` with the
weight `w_0 = 1`, `w_{n+1} = 4^{-n}` (the weight `2^{-n(N-10)}` of the tree estimate for `N = 12`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

section TreeBlock

/-- The decay weight of the tree estimate away from the top: `1` for `ℓ = 0` and `4^{-n}` for
`ℓ = n + 1` (the weight `2^{-n(N-10)}` for `N = 12`). -/
def tailWeight : ℕ → ℝ
  | 0 => 1
  | n + 1 => (1 / 4 : ℝ) ^ n

/-- The weights are positive. -/
theorem tailWeight_pos (ℓ : ℕ) : 0 < tailWeight ℓ := by
  cases ℓ with
  | zero => exact one_pos
  | succ n => exact pow_pos (by norm_num) n

/-- `w_ℓ ≤ 4 · 4^{-ℓ}`. -/
theorem tailWeight_le (ℓ : ℕ) : tailWeight ℓ ≤ 4 * (1 / 4 : ℝ) ^ ℓ := by
  cases ℓ with
  | zero => norm_num [tailWeight]
  | succ n =>
    simp only [tailWeight, pow_succ]
    nlinarith [pow_pos (show (0 : ℝ) < 1 / 4 by norm_num) n]

/-- A `q`-th power of the `L^q(s)` norm. -/
theorem lintegral_tail_rpow_le {h : ℝ → ℂ} (hm : Measurable h) {s : Set ℝ} (hs : MeasurableSet s)
    {q : ℝ} (hq : 0 < q) {a : ℝ≥0∞}
    (ha : eLpNorm h (ENNReal.ofReal q) (volume.restrict s) ≤ a) :
    ∫⁻ x, (s.indicator (fun y => ‖h y‖ₑ) x) ^ q ≤ a ^ q := by
  have h1 : ∫⁻ x, (s.indicator (fun y => ‖h y‖ₑ) x) ^ q = ∫⁻ x in s, ‖h x‖ₑ ^ q := by
    rw [← lintegral_indicator hs]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ s <;> simp [hx, ENNReal.zero_rpow_of_pos hq]
  rw [h1]
  have h2 := eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := volume.restrict s)
    (ENNReal.ofReal_pos.2 hq).ne' ENNReal.ofReal_ne_top hm.aestronglyMeasurable
  rw [ENNReal.toReal_ofReal hq.le] at h2
  calc ∫⁻ x in s, ‖h x‖ₑ ^ q = (eLpNorm h (ENNReal.ofReal q) (volume.restrict s)) ^ q := by
        rw [h2, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq.ne', ENNReal.rpow_one]
    _ ≤ a ^ q := ENNReal.rpow_le_rpow ha hq.le

/-- `r' > 1` for `r > 1`. -/
theorem one_lt_conjExponent {r : ℝ} (hr : 1 < r) : 1 < Real.conjExponent r :=
  (Real.HolderConjugate.conjExponent hr).symm.lt

/-- `r' ≤ 2` for `r ≥ 2`. -/
theorem conjExponent_le_two {r : ℝ} (hr : 2 ≤ r) : Real.conjExponent r ≤ 2 := by
  have : 0 < r - 1 := by linarith
  unfold Real.conjExponent
  rw [div_le_iff₀ this]
  linarith

/-- **The tree estimate on the regions `tailSet`** ([O+] `treeestimate` with `q ∈ [1, 2]`,
`N = 12`): the `q`-th power of the `L^q` norm of the tree sum on `ℝ ∖ 2^{ℓ-1} I_T` is at most
`(K w_ℓ ene den^{min(1, r'/q)})^q |I_T|`. -/
theorem treeestimate_tail {r q : ℝ} (hr : 2 < r) (hq1 : 1 ≤ q) (hq2 : q ≤ 2) {C₁ C₂ C₃ : ℝ}
    (hC : AdmissibleConstants C₁ C₂ C₃) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {M : ℤ}, ρ.IsStd → ∀ (ch : ProfileChoice)
      (f : ℝ → ℂ) {E : Set ℝ}, MeasurableSet E → ∀ (L : Linearization r) {S : Set (Multitile ρ)}
      {ene den : ℝ}, 0 ≤ ene → 0 ≤ den → energy C₁ C₂ M ch f S ≤ ENNReal.ofReal ene →
      density C₁ C₂ M L E S ≤ ENNReal.ofReal den → ∀ (𝒯 : MultitileTree ρ),
      𝒯.IsTree C₁ C₂ M → (∀ P ∈ 𝒯.T, P.InSquare M) → (𝒯.T : Set (Multitile ρ)) ⊆ S →
      Separated C₁ C₂ C₃ (𝒯.T : Set (Multitile ρ)) → ∀ ℓ : ℕ,
        ∫⁻ x, ((tailSet 𝒯.I ℓ).indicator (fun y => ‖treeSum ch f L E 𝒯.T y‖ₑ) x) ^ q ≤
          ENNReal.ofReal ((K * tailWeight ℓ * ene * den ^ (min 1 (Real.conjExponent r / q))) ^ q *
            𝒯.I.length) := by
  obtain ⟨K, hK0, hK⟩ := treeestimate hr hq1 hq2 12 (by norm_num) hC
  refine ⟨K, hK0, ?_⟩
  intro ρ _ M hρ ch f E hE L S ene den hene hden hen hde 𝒯 hT hsq hsub hsep ℓ
  obtain ⟨ha, hb⟩ := hK hρ ch f hE L hene hden hen hde 𝒯 hT hsq hsub hsep
  have hq0 : 0 < q := by linarith
  have hIpos := 𝒯.I.length_pos
  have hσ0 : 0 ≤ min 1 (Real.conjExponent r / q) := by
    refine le_min zero_le_one ?_
    have : 0 < Real.conjExponent r := lt_trans zero_lt_one (one_lt_conjExponent (by linarith))
    positivity
  have hm : Measurable (treeSum ch f L E 𝒯.T) := measurable_treeSum ch f L hE 𝒯.T
  set Y : ℝ := ene * den ^ (min 1 (Real.conjExponent r / q)) with hY
  have hY0 : 0 ≤ Y := by positivity
  -- the bound for the weight `tailWeight ℓ`
  have hE' : eLpNorm (treeSum ch f L E 𝒯.T) (ENNReal.ofReal q)
      (volume.restrict (tailSet 𝒯.I ℓ)) ≤
      ENNReal.ofReal (K * tailWeight ℓ * Y * 𝒯.I.length ^ (1 / q)) := by
    cases ℓ with
    | zero =>
      simp only [tailSet, Measure.restrict_univ, tailWeight]
      refine ha.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
      rw [hY]; ring
    | succ n =>
      simp only [tailSet]
      refine (hb n).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
      simp only [tailWeight, hY]
      have : ((2 : ℝ) ^ n) ^ (-(((12 : ℕ) : ℤ) - 10)) = (1 / 4 : ℝ) ^ n := by
        rw [show (-(((12 : ℕ) : ℤ) - 10)) = -(2 : ℤ) by norm_num, zpow_neg, zpow_ofNat,
          ← pow_mul, mul_comm, pow_mul]
        rw [show (2 : ℝ) ^ 2 = 4 by norm_num, one_div, inv_pow]
      rw [this]
      ring
  have hmeas := measurableSet_tailSet 𝒯.I ℓ
  have hW0 : 0 ≤ K * tailWeight ℓ * Y := by
    have := tailWeight_pos ℓ
    positivity
  refine (lintegral_tail_rpow_le hm hmeas hq0 hE').trans ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [Real.mul_rpow hW0 (by positivity), ← Real.rpow_mul hIpos.le, one_div_mul_cancel hq0.ne',
    Real.rpow_one]
  simp only [hY]
  congr 2
  ring

end TreeBlock

end PrimeCarleson.Proof.Oplus
