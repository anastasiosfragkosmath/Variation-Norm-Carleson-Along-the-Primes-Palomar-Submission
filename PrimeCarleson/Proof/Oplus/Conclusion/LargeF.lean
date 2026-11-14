module

public import PrimeCarleson.Proof.Oplus.Conclusion.Arith

/-!
# The summation for `|F| > 1` ([O+] L2611-L2650)

Source: [O+] `L1except`, the case of large `F` (L2580–L2650): the exceptional set, the Hölder step
and the summation. Given the decomposition of `𝔓` into the trees of the families `𝒯_{j,k}` (with
`∑_{T ∈ 𝒯_{j,k}} |I_T| ≲ 2^j`, the dyadic BMO bound `‖∑ 1_{2^ℓ I_T}‖_BMO ≲ 2^{2ℓ} 2^{j+k} |F|^{-1}`,
energy `≲ 2^{-(j+k)/2} |F|^{1/2}` and density `≲ 2^{-j/r'}` of the families containing the trees),
the exceptional set `G = ⋃_{j,k,ℓ} G_{j,k,ℓ}`,
`G_{j,k,ℓ} = {∑_{T ∈ 𝒯_{j,k}} 1_{2^ℓ I_T} ≥ C' |F|^{-1/q'} 2^{(1+ε)(j+k+2ℓ)}}`, has measure at most
`1/4` (`exists_measure_covering_le`, `Covering.lean`, and the geometric series) and
`∫_{ℝ ∖ G} |∑_{P} ⟨f, φ_P⟩ φ_P a_P 1_E| ≲ |F|^{1/p}` (Minkowski over `(j, k, ℓ)`, Hölder and Fubini
in `stage_bound`, the tree estimate with `q = r'`, and the real bookkeeping of `Arith.lean`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

section LargeF

/-- The sum of a finite family of `L^{q}` bounds: if `a_i ≤ W^q |I_i|` and `∑ |I_i| ≤ σ`, then
`(∑ a_i)^{1/q} ≤ W σ^{1/q}`. -/
theorem sum_rpow_le {ι : Type*} (s : Finset ι) (a : ι → ℝ≥0∞) (I : ι → ℝ)
    {W q σ : ℝ} (hW : 0 ≤ W) (hq : 0 < q) (hσ : 0 ≤ σ)
    (ha : ∀ i ∈ s, a i ≤ ENNReal.ofReal (W ^ q * I i))
    (hs : ∑ i ∈ s, ENNReal.ofReal (I i) ≤ ENNReal.ofReal σ) :
    (∑ i ∈ s, a i) ^ (1 / q) ≤ ENNReal.ofReal (W * σ ^ (1 / q)) := by
  have h1 : ∑ i ∈ s, a i ≤ ENNReal.ofReal (W ^ q * σ) := by
    calc ∑ i ∈ s, a i ≤ ∑ i ∈ s, ENNReal.ofReal (W ^ q) * ENNReal.ofReal (I i) :=
          Finset.sum_le_sum fun i hi => by
            rw [← ENNReal.ofReal_mul (by positivity)]; exact ha i hi
      _ = ENNReal.ofReal (W ^ q) * ∑ i ∈ s, ENNReal.ofReal (I i) := by rw [Finset.mul_sum]
      _ ≤ ENNReal.ofReal (W ^ q) * ENNReal.ofReal σ := mul_le_mul' le_rfl hs
      _ = ENNReal.ofReal (W ^ q * σ) := by rw [← ENNReal.ofReal_mul (by positivity)]
  refine (ENNReal.rpow_le_rpow h1 (by positivity)).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  congr 1
  rw [Real.mul_rpow (by positivity) hσ, ← Real.rpow_mul hW, mul_one_div_cancel hq.ne',
    Real.rpow_one]

/-- **The integral of one stage `𝒯_{j,k}` off the exceptional set** (L2618-L2650): for the trees of
one family, with energy and density bounds of a family containing them, the `L¹(ℝ ∖ G)` norm of
`∑_T |1_E ∑_{P ∈ R_T} ⟨f, φ_P⟩ φ_P a_P|` is at most `Γ |F|^{1/p} γ^{j+k}`, provided `G` contains
the sets `G_{j,k,ℓ}`. -/
theorem stage_integral_le {r p : ℝ} (hr : 2 < r) {q : ℕ} (hq : 1 ≤ q) {ε : ℝ} (hε : 0 < ε)
    (hεr : (1 + ε) * 2 < r) (hqp : 1 / 2 - (1 - 1 / (q : ℝ)) / r ≤ 1 / p) {C₁ C₂ C₃ : ℝ}
    (hC : AdmissibleConstants C₁ C₂ C₃) {A c C' : ℝ} (hA : 0 < A) (hc : 0 < c) (hC' : 0 < C') :
    ∃ Γ : ℝ, 0 < Γ ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {M : ℤ}, ρ.IsStd → ∀ (ch : ProfileChoice)
      (f : ℝ → ℂ) {E : Set ℝ}, MeasurableSet E → volume E ≤ 2 → ∀ (L : Linearization r)
      {Fm : ℝ}, 1 < Fm → ∀ (j k : ℕ) (𝒯 : Finset (MultitileTree ρ))
      (R : MultitileTree ρ → Finset (Multitile ρ)) (S : Set (Multitile ρ))
      (𝔓 : Finset (Multitile ρ)), Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ)) →
      (∀ P ∈ 𝔓, P.InSquare M) →
      (∀ T ∈ 𝒯, R T ⊆ T.T ∧ R T ⊆ 𝔓 ∧ T.IsTree C₁ C₂ M ∧ (T.T : Set (Multitile ρ)) ⊆ S) →
      energy C₁ C₂ M ch f S ≤ ENNReal.ofReal (A * Fm ^ (1 / 2 : ℝ) * nuE ^ (j + k)) →
      density C₁ C₂ M L E S ≤ ENNReal.ofReal (A * muD r ^ j) →
      ∑ T ∈ 𝒯, ENNReal.ofReal T.I.length ≤ ENNReal.ofReal (c * 2 ^ j) →
      ∀ {G : Set ℝ}, MeasurableSet G →
      (∀ ℓ : ℕ, {x | C' * (2 * (2 : ℝ) ^ ε) ^ (j + k + 2 * ℓ) / Fm ^ (1 - 1 / (q : ℝ)) ≤
        ∑ T ∈ 𝒯, (T.I.dilate ((2 : ℝ) ^ ℓ)).indicator (fun _ => (1 : ℝ)) x} ⊆ G) →
      ∫⁻ x in Gᶜ, ∑ T ∈ 𝒯, ‖treeSum ch f L E (R T) x‖ₑ ≤
        ENNReal.ofReal (Γ * Fm ^ (1 / p) * ((2 * (2 : ℝ) ^ ε) ^ (1 / r) * nuE) ^ (j + k)) := by
  have hr1 : 1 < r := by linarith
  have hr'1 := one_lt_conjExponent hr1
  have hr'0 : 0 < Real.conjExponent r := by linarith
  obtain ⟨K, hK0, hK⟩ := treeestimate_tail (r := r) (q := Real.conjExponent r) hr hr'1.le
    (conjExponent_le_two hr.le) hC
  set Γ₀ : ℝ := 4 * C' ^ (1 / r) * (2 : ℝ) ^ (1 / r) * K * A ^ 2 *
    c ^ (1 / Real.conjExponent r) with hΓ₀
  have hΓ₀0 : 0 ≤ Γ₀ := by positivity
  refine ⟨2 * Γ₀ + 1, by positivity, ?_⟩
  intro ρ _ M hρ ch f E hE hE2 L Fm hFm j k 𝒯 R S 𝔓 hsep hsq hR hen hde hsize G hGm hG
  have hFm0 : 0 < Fm := by linarith
  set Bq : ℕ → ℝ := fun ℓ =>
    C' * (2 * (2 : ℝ) ^ ε) ^ (j + k + 2 * ℓ) / Fm ^ (1 - 1 / (q : ℝ)) with hBq
  have hBpos : ∀ ℓ, 0 < Bq ℓ := fun ℓ => by positivity
  set g : ℕ → ℝ → ℝ := fun ℓ x =>
    ∑ T ∈ 𝒯, (T.I.dilate ((2 : ℝ) ^ ℓ)).indicator (fun _ => (1 : ℝ)) x with hg
  have hgm : ∀ ℓ, Measurable (g ℓ) := fun ℓ =>
    Finset.measurable_sum _ fun T _ => measurable_const.indicator (T.I.measurableSet_dilate _)
  have hm : ∀ T : MultitileTree ρ, Measurable (treeSum ch f L E (R T)) :=
    fun T => measurable_treeSum ch f L hE _
  have hsupp : ∀ (T : MultitileTree ρ) x, x ∉ E → treeSum ch f L E (R T) x = 0 := by
    intro T x hx
    simp [treeSum, hx]
  have h1 := stage_bound 𝒯 hr1 (fun T => T.I) (fun T => treeSum ch f L E (R T)) hm hE hsupp
    (G := G) (fun ℓ => {x | Bq ℓ ≤ g ℓ x}) hG
    (fun ℓ => measurableSet_le measurable_const (hgm ℓ)) (fun ℓ => ENNReal.ofReal (Bq ℓ))
    (by
      intro ℓ x hx
      have hx' : g ℓ x < Bq ℓ := not_le.1 hx
      have : ∑ T ∈ 𝒯, (T.I.dilate ((2 : ℝ) ^ ℓ)).indicator (fun _ => (1 : ℝ≥0∞)) x =
          ENNReal.ofReal (g ℓ x) := by
        rw [hg, ENNReal.ofReal_sum_of_nonneg
          (fun T _ => indicator_nonneg (fun _ _ => zero_le_one) x)]
        refine Finset.sum_congr rfl fun T _ => ?_
        by_cases hxT : x ∈ T.I.dilate ((2 : ℝ) ^ ℓ) <;> simp [hxT]
      rw [this]
      exact ENNReal.ofReal_le_ofReal hx'.le)
  refine h1.trans ?_
  have hν0 := nuE_pos
  have hμ0 := muD_pos r
  set ene : ℝ := A * Fm ^ (1 / 2 : ℝ) * nuE ^ (j + k) with hene
  set den : ℝ := A * muD r ^ j with hden
  have hene0 : 0 ≤ ene := by positivity
  have hden0 : 0 ≤ den := by positivity
  have hmin : min 1 (Real.conjExponent r / Real.conjExponent r) = 1 := by
    rw [div_self hr'0.ne', min_self]
  have htree : ∀ ℓ, ∀ T ∈ 𝒯, ∫⁻ x, ((tailSet T.I ℓ).indicator
      (fun y => ‖treeSum ch f L E (R T) y‖ₑ) x) ^ Real.conjExponent r ≤
      ENNReal.ofReal ((K * tailWeight ℓ * ene * den) ^ Real.conjExponent r * T.I.length) := by
    intro ℓ T hT
    obtain ⟨hRT, hR𝔓, hTT, hTS⟩ := hR T hT
    have := hK hρ ch f hE L hene0 hden0 hen hde (MultitileTree.mk (R T) T.I T.ξ)
      (hTT.of_subset (R T) hRT) (fun P hP => hsq P (hR𝔓 hP))
      ((Finset.coe_subset.2 hRT).trans hTS) (hsep.mono (Finset.coe_subset.2 hR𝔓)) ℓ
    rw [hmin, Real.rpow_one] at this
    exact this
  set γ : ℝ := (2 * (2 : ℝ) ^ ε) ^ (1 / r) * nuE with hγ
  have hterm : ∀ ℓ : ℕ, ENNReal.ofReal (Bq ℓ) ^ (1 / r) * volume E ^ (1 / r) *
      (∑ T ∈ 𝒯, ∫⁻ x, ((tailSet T.I ℓ).indicator
        (fun y => ‖treeSum ch f L E (R T) y‖ₑ) x) ^ Real.conjExponent r) ^
        (1 / Real.conjExponent r) ≤
      ENNReal.ofReal (Γ₀ * Fm ^ (1 / p) * γ ^ (j + k) * (1 / 2 : ℝ) ^ ℓ) := by
    intro ℓ
    have hW0 : 0 ≤ K * tailWeight ℓ * ene * den := by
      have := tailWeight_pos ℓ
      positivity
    have hsum := sum_rpow_le 𝒯 (fun T => ∫⁻ x, ((tailSet T.I ℓ).indicator
      (fun y => ‖treeSum ch f L E (R T) y‖ₑ) x) ^ Real.conjExponent r) (fun T => T.I.length)
      hW0 hr'0 (by positivity : 0 ≤ c * 2 ^ j) (htree ℓ) hsize
    have hE2' : volume E ^ (1 / r) ≤ ENNReal.ofReal 2 ^ (1 / r) :=
      ENNReal.rpow_le_rpow (by simpa using hE2) (by positivity)
    calc ENNReal.ofReal (Bq ℓ) ^ (1 / r) * volume E ^ (1 / r) *
        (∑ T ∈ 𝒯, ∫⁻ x, ((tailSet T.I ℓ).indicator
          (fun y => ‖treeSum ch f L E (R T) y‖ₑ) x) ^ Real.conjExponent r) ^
          (1 / Real.conjExponent r)
        ≤ ENNReal.ofReal (Bq ℓ) ^ (1 / r) * ENNReal.ofReal 2 ^ (1 / r) *
          ENNReal.ofReal (K * tailWeight ℓ * ene * den * (c * 2 ^ j) ^ (1 / Real.conjExponent r)) :=
          mul_le_mul' (mul_le_mul' le_rfl hE2') hsum
      _ = ENNReal.ofReal (Bq ℓ ^ (1 / r) * (2 : ℝ) ^ (1 / r) *
          (K * tailWeight ℓ * ene * den * (c * 2 ^ j) ^ (1 / Real.conjExponent r))) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (hBpos ℓ).le (by positivity),
            ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by positivity),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by
          have := stage_real_bound (r := r) (p := p) (q := q) hq hε hεr hqp hA hc hC' hK0 hFm
            j k ℓ (tailWeight_le ℓ)
          exact this)
  have hγ0 : 0 ≤ γ := gamma_pos.le
  set a : ℝ := Γ₀ * Fm ^ (1 / p) * γ ^ (j + k) with ha
  have ha0 : 0 ≤ a := by positivity
  calc ∑' ℓ : ℕ, ENNReal.ofReal (Bq ℓ) ^ (1 / r) * volume E ^ (1 / r) *
        (∑ T ∈ 𝒯, ∫⁻ x, ((tailSet T.I ℓ).indicator
          (fun y => ‖treeSum ch f L E (R T) y‖ₑ) x) ^ Real.conjExponent r) ^
          (1 / Real.conjExponent r)
      ≤ ∑' ℓ : ℕ, ENNReal.ofReal (a * (1 / 2 : ℝ) ^ ℓ) :=
        ENNReal.tsum_le_tsum fun ℓ => by
          have := hterm ℓ
          rw [ha]; exact this
    _ = ENNReal.ofReal (∑' ℓ : ℕ, a * (1 / 2 : ℝ) ^ ℓ) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun ℓ => by positivity)
          ((summable_geometric_two).mul_left a)).symm
    _ = ENNReal.ofReal (2 * a) := by
        rw [tsum_mul_left, tsum_geometric_two]; congr 1; ring
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hF0 : 0 ≤ Fm ^ (1 / p) := by positivity
        have hγ' : 0 ≤ γ ^ (j + k) := by positivity
        rw [ha]
        have : 0 ≤ Fm ^ (1 / p) * γ ^ (j + k) := by positivity
        nlinarith [mul_nonneg hΓ₀0 this]

/-- **The summation for `|F| > 1`** ([O+] `L1except`, with its exceptional set). Let `r > 2` and
`1/p > 1/2 - 1/r` (that is `p < 2r/(r-2)`).
Given the decomposition data of the hypotheses, there is a measurable `G` with `|G| ≤ 1/4` and
`∫_{ℝ ∖ G} |1_E ∑_{P ∈ 𝔓} ⟨f, φ_P⟩ φ_P a_P| ≤ C |F|^{1/p}`. -/
theorem large_summation {r p : ℝ} (hr : 2 < r) (hp : 1 / 2 - 1 / r < 1 / p) {C₁ C₂ C₃ : ℝ}
    (hC : AdmissibleConstants C₁ C₂ C₃) {A c : ℝ} (hA : 0 < A) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {M : ℤ}, ρ.IsStd → ∀ (ch : ProfileChoice)
      (f : ℝ → ℂ) {E : Set ℝ}, MeasurableSet E → volume E ≤ 2 → ∀ (L : Linearization r)
      {Fm : ℝ}, 1 < Fm → ∀ (𝔓 : Finset (Multitile ρ)),
      Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ)) → (∀ P ∈ 𝔓, P.InSquare M) →
      ∀ (J K : ℕ) (𝒯 : ℕ → ℕ → Finset (MultitileTree ρ))
      (R : ℕ → ℕ → MultitileTree ρ → Finset (Multitile ρ)) (S : ℕ → ℕ → Set (Multitile ρ)),
      (∀ x, treeSum ch f L E 𝔓 x = ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range K,
        ∑ T ∈ 𝒯 j k, treeSum ch f L E (R j k T) x) →
      (∀ j k, ∀ T ∈ 𝒯 j k, R j k T ⊆ T.T ∧ R j k T ⊆ 𝔓 ∧ T.IsTree C₁ C₂ M ∧
        (T.T : Set (Multitile ρ)) ⊆ S j k) →
      (∀ j k, energy C₁ C₂ M ch f (S j k) ≤
        ENNReal.ofReal (A * Fm ^ (1 / 2 : ℝ) * nuE ^ (j + k))) →
      (∀ j k, density C₁ C₂ M L E (S j k) ≤ ENNReal.ofReal (A * muD r ^ j)) →
      (∀ j k, ∑ T ∈ 𝒯 j k, ENNReal.ofReal T.I.length ≤ ENNReal.ofReal (c * 2 ^ j)) →
      (∀ j k ℓ : ℕ, dyadicBMO (fun x => ∑ T ∈ 𝒯 j k,
        (T.I.dilate ((2 : ℝ) ^ ℓ)).indicator (fun _ => (1 : ℝ)) x) ≤
        ENNReal.ofReal (c * 2 ^ (2 * ℓ) * 2 ^ (j + k) / Fm)) →
      ∃ G : Set ℝ, MeasurableSet G ∧ volume G ≤ 1 / 4 ∧
        ∫⁻ x in Gᶜ, ‖treeSum ch f L E 𝔓 x‖ₑ ≤ ENNReal.ofReal (C * Fm ^ (1 / p)) := by
  have hr0 : 0 < r := by linarith
  obtain ⟨q, ε, hq, hε, hεr, hqp⟩ := exists_large_params hr hp
  obtain ⟨Cq, hCq0, hCq⟩ := exists_measure_covering_le.{0} q hq
  set γε : ℝ := (2 : ℝ) ^ (-ε) with hγε
  have hγε0 : 0 < γε := Real.rpow_pos_of_pos (by norm_num) _
  have hγε1 : γε < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h1γ : 0 < 1 - γε := by linarith
  set C' : ℝ := max 1 (4 * Cq * c / (1 - γε) ^ 3) with hC'
  have hC'0 : 0 < C' := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hC'ge : 4 * Cq * c / (1 - γε) ^ 3 ≤ C' := le_max_right _ _
  obtain ⟨Γ, hΓ0, hΓ⟩ := stage_integral_le hr hq hε hεr hqp hC hA hc hC'0
  set γ : ℝ := (2 * (2 : ℝ) ^ ε) ^ (1 / r) * nuE with hγ
  have hγ0 : 0 < γ := gamma_pos
  have hγ1 : γ < 1 := gamma_lt_one hr hεr
  refine ⟨Γ * ((1 - γ)⁻¹) ^ 2, by positivity, ?_⟩
  intro ρ _ M hρ ch f E hE hE2 L Fm hFm 𝔓 hsep hsq J K 𝒯 R S hid hR hen hde hsize hbmo
  have hFm0 : 0 < Fm := by linarith
  set Bq : ℕ → ℕ → ℕ → ℝ := fun j k ℓ =>
    C' * (2 * (2 : ℝ) ^ ε) ^ (j + k + 2 * ℓ) / Fm ^ (1 - 1 / (q : ℝ)) with hBq
  have hBpos : ∀ j k ℓ, 0 < Bq j k ℓ := fun j k ℓ => by positivity
  set Gj : ℕ → ℕ → ℕ → Set ℝ := fun j k ℓ => {x | Bq j k ℓ ≤ ∑ T ∈ 𝒯 j k,
    (T.I.dilate ((2 : ℝ) ^ ℓ)).indicator (fun _ => (1 : ℝ)) x} with hGj
  have hGjm : ∀ j k ℓ, MeasurableSet (Gj j k ℓ) := fun j k ℓ =>
    measurableSet_le measurable_const (Finset.measurable_sum _ fun T _ =>
      measurable_const.indicator (T.I.measurableSet_dilate _))
  set G : Set ℝ := ⋃ j, ⋃ k, ⋃ ℓ, Gj j k ℓ with hG
  have hGm : MeasurableSet G := MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun k =>
    MeasurableSet.iUnion fun ℓ => hGjm j k ℓ
  refine ⟨G, hGm, ?_, ?_⟩
  · -- the measure of the exceptional set
    set cG : ℝ := (Cq * c / C') ^ q with hcG
    have hmeas : ∀ j k ℓ, volume (Gj j k ℓ) ≤
        ENNReal.ofReal (cG * γε ^ (j + k + 2 * ℓ)) := by
      intro j k ℓ
      have h := hCq (𝒯 j k) (fun T : MultitileTree ρ => T.I) ℓ (σ := c * 2 ^ j)
        (b := c * 2 ^ (2 * ℓ) * 2 ^ (j + k) / Fm) (B := Bq j k ℓ) (by positivity)
        (by positivity) (hBpos j k ℓ) (hsize j k) (hbmo j k ℓ)
      refine h.trans (ENNReal.ofReal_le_ofReal ?_)
      exact measure_real_bound hq hε hCq0 hc hC'0 hFm0 j k ℓ
    have hcG0 : 0 ≤ Cq * c / C' := by positivity
    have hcG1 : Cq * c / C' ≤ (1 - γε) ^ 3 / 4 := by
      rw [div_le_iff₀ hC'0]
      rw [div_le_iff₀ (by positivity)] at hC'ge
      nlinarith
    have hcGle : cG ≤ (1 - γε) ^ 3 / 4 := by
      refine le_trans (pow_le_of_le_one hcG0 ?_ (by omega)) hcG1
      refine hcG1.trans ?_
      have : (1 - γε) ^ 3 ≤ 1 := pow_le_one₀ h1γ.le (by linarith)
      linarith
    set a : ℝ≥0∞ := ENNReal.ofReal γε with ha
    have hterm : ∀ j k ℓ : ℕ, volume (Gj j k ℓ) ≤
        ENNReal.ofReal cG * (a ^ j * (a ^ k * a ^ ℓ)) := by
      intro j k ℓ
      refine (hmeas j k ℓ).trans ?_
      rw [ha, ← ENNReal.ofReal_pow hγε0.le, ← ENNReal.ofReal_pow hγε0.le,
        ← ENNReal.ofReal_pow hγε0.le, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hcG0' : 0 ≤ cG := by positivity
      have h2 : γε ^ (j + k + 2 * ℓ) ≤ γε ^ j * (γε ^ k * γε ^ ℓ) := by
        rw [← mul_assoc, ← pow_add, ← pow_add]
        exact pow_le_pow_of_le_one hγε0.le hγε1.le (by omega)
      exact mul_le_mul_of_nonneg_left h2 hcG0'
    calc volume G ≤ ∑' j, volume (⋃ k, ⋃ ℓ, Gj j k ℓ) := measure_iUnion_le _
      _ ≤ ∑' j, ∑' k, volume (⋃ ℓ, Gj j k ℓ) :=
          ENNReal.tsum_le_tsum fun j => measure_iUnion_le _
      _ ≤ ∑' j, ∑' k, ∑' ℓ, volume (Gj j k ℓ) :=
          ENNReal.tsum_le_tsum fun j => ENNReal.tsum_le_tsum fun k => measure_iUnion_le _
      _ ≤ ∑' j : ℕ, ∑' k : ℕ, ∑' ℓ : ℕ, ENNReal.ofReal cG * (a ^ j * (a ^ k * a ^ ℓ)) :=
          ENNReal.tsum_le_tsum fun j => ENNReal.tsum_le_tsum fun k =>
            ENNReal.tsum_le_tsum fun ℓ => hterm j k ℓ
      _ = ENNReal.ofReal cG * ((1 - a)⁻¹ * ((1 - a)⁻¹ * (1 - a)⁻¹)) := by
          have h3 : ∀ j k : ℕ, ∑' ℓ : ℕ, ENNReal.ofReal cG * (a ^ j * (a ^ k * a ^ ℓ)) =
              ENNReal.ofReal cG * (a ^ j * (a ^ k * (1 - a)⁻¹)) := fun j k => by
            rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
              ENNReal.tsum_geometric]
          have h2 : ∀ j : ℕ, ∑' k : ℕ, ENNReal.ofReal cG * (a ^ j * (a ^ k * (1 - a)⁻¹)) =
              ENNReal.ofReal cG * (a ^ j * ((1 - a)⁻¹ * (1 - a)⁻¹)) := fun j => by
            rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right,
              ENNReal.tsum_geometric]
          simp_rw [h3, h2]
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
      _ = ENNReal.ofReal (cG * (((1 - γε)⁻¹) * (((1 - γε)⁻¹) * ((1 - γε)⁻¹)))) := by
          have h1a : 1 - a = ENNReal.ofReal (1 - γε) := by
            rw [ENNReal.ofReal_sub 1 hγε0.le, ENNReal.ofReal_one]
          rw [h1a, ← ENNReal.ofReal_inv_of_pos h1γ, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ 1 / 4 := by
          rw [show (1 / 4 : ℝ≥0∞) = ENNReal.ofReal (1 / 4) by
            rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp]
          refine ENNReal.ofReal_le_ofReal ?_
          calc cG * ((1 - γε)⁻¹ * ((1 - γε)⁻¹ * (1 - γε)⁻¹))
              ≤ (1 - γε) ^ 3 / 4 * ((1 - γε)⁻¹ * ((1 - γε)⁻¹ * (1 - γε)⁻¹)) :=
                mul_le_mul_of_nonneg_right hcGle (by positivity)
            _ = 1 / 4 := by field_simp
  · -- the integral outside the exceptional set
    have hm : ∀ j k (T : MultitileTree ρ), Measurable fun x => ‖treeSum ch f L E (R j k T) x‖ₑ :=
      fun j k T => (measurable_treeSum ch f L hE _).enorm
    have hgeo : ∀ N : ℕ, ∑ i ∈ Finset.range N, γ ^ i ≤ (1 - γ)⁻¹ := fun N => by
      rw [← tsum_geometric_of_lt_one hγ0.le hγ1]
      exact (summable_geometric_of_lt_one hγ0.le hγ1).sum_le_tsum _ fun i _ => pow_nonneg hγ0.le i
    calc ∫⁻ x in Gᶜ, ‖treeSum ch f L E 𝔓 x‖ₑ
        ≤ ∫⁻ x in Gᶜ, ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range K, ∑ T ∈ 𝒯 j k,
            ‖treeSum ch f L E (R j k T) x‖ₑ := by
          refine lintegral_mono fun x => ?_
          rw [hid x]
          exact (enorm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
            (enorm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => enorm_sum_le _ _))
      _ = ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range K, ∫⁻ x in Gᶜ, ∑ T ∈ 𝒯 j k,
            ‖treeSum ch f L E (R j k T) x‖ₑ := by
          rw [lintegral_finsetSum _ fun j _ => Finset.measurable_sum _ fun k _ =>
            Finset.measurable_sum _ fun T _ => hm j k T]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [lintegral_finsetSum _ fun k _ => Finset.measurable_sum _ fun T _ => hm j k T]
      _ ≤ ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range K,
            ENNReal.ofReal (Γ * Fm ^ (1 / p) * γ ^ (j + k)) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ =>
            hΓ hρ ch f hE hE2 L hFm j k (𝒯 j k) (R j k) (S j k) 𝔓 hsep hsq (hR j k) (hen j k)
              (hde j k) (hsize j k) hGm fun ℓ x hx =>
                mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨k, mem_iUnion.2 ⟨ℓ, hx⟩⟩⟩
      _ = ENNReal.ofReal (∑ j ∈ Finset.range J, ∑ k ∈ Finset.range K,
            Γ * Fm ^ (1 / p) * γ ^ (j + k)) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun j _ => Finset.sum_nonneg fun k _ => by positivity]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [ENNReal.ofReal_sum_of_nonneg fun k _ => by positivity]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hF0 : 0 ≤ Fm ^ (1 / p) := by positivity
          have e1 : ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range K, Γ * Fm ^ (1 / p) * γ ^ (j + k) =
              Γ * Fm ^ (1 / p) * ((∑ j ∈ Finset.range J, γ ^ j) * ∑ k ∈ Finset.range K, γ ^ k) := by
            rw [Finset.sum_mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [pow_add]
          rw [e1]
          have h1γ' : 0 ≤ (1 - γ)⁻¹ := inv_nonneg.2 (by linarith)
          calc Γ * Fm ^ (1 / p) * ((∑ j ∈ Finset.range J, γ ^ j) * ∑ k ∈ Finset.range K, γ ^ k)
              ≤ Γ * Fm ^ (1 / p) * ((1 - γ)⁻¹ * (1 - γ)⁻¹) := by
                gcongr
                · exact hgeo J
                · exact hgeo K
            _ = Γ * ((1 - γ)⁻¹) ^ 2 * Fm ^ (1 / p) := by ring

end LargeF

end PrimeCarleson.Proof.Oplus
