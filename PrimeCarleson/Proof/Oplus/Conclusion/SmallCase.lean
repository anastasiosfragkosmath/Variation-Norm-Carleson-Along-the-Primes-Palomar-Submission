module

public import PrimeCarleson.Proof.Oplus.Conclusion.LargeCase

/-!
# The case `|F| ≤ 1` of `L1except` ([O+] L2652-L2685)

Source: [O+] `L1except`, the case of small `F` (L2652–L2685): the exceptional set, the reduction
to large values of the maximal function, the energy bound, the decomposition and the tree sum.
With `G = {M[1_F] > 16 |F|}` (`|G| ≤ 1/4` by the weak type `(1,1)` bound, so
`C'' = 16`), the multitiles whose time interval lies in `G` are handled by `tileslargemaxprop`
(`≲ |F| (16 |F|)^{-1/r} ≲ |F|^{1/r'} ≤ |F|^{1/p}`), and the others, `𝔓'`, have energy
`≲ |F|` (`exists_energy_le_of_not_subset`, the Hardy-Littlewood form of the tile energy bound which
replaces the false dyadic `tilessmallmaxprop`). The energy-density decomposition
of `𝔓'` (`exists_energy_density_stages`) and the tree estimate with `q = 1` give
`∑_j ∑_{T ∈ 𝒯_j} K min(2^{-j/2}|F|^{1/2}, |F|) 2^{-j/r'} |I_T| ≲ ∑_j 2^{j/r}
min(2^{-j/2}|F|^{1/2}, |F|) ≲ |F|^{1/r'}` (`small_sum_le`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson.Proof.Common

section SmallCase

/-- **The summation for `|F| ≤ 1`** (the tree sum of [O+] `L1except`, L2677-L2685): given the
decomposition of `𝔓'` into the trees of the stages `𝒯_j` in families `S_j` of energy
`≤ min(a |F|^{1/2} ν^j, a |F|)` and density `≤ a μ^j`, with `∑_{T ∈ 𝒯_j} |I_T| ≤ c 2^j`,
`∫ |1_E ∑_{P ∈ 𝔓'} ⟨f, φ_P⟩ φ_P a_P| ≤ C |F|^{1 - 1/r}`. -/
theorem small_summation {r : ℝ} (hr : 2 < r) {C₁ C₂ C₃ : ℝ}
    (hC : AdmissibleConstants C₁ C₂ C₃) {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {M : ℤ}, ρ.IsStd → ∀ (ch : ProfileChoice)
      (f : ℝ → ℂ) {E : Set ℝ}, MeasurableSet E → ∀ (L : Linearization r) {Fm : ℝ}, 0 < Fm →
      Fm ≤ 1 → ∀ (𝔓 : Finset (Multitile ρ)), Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ)) →
      (∀ P ∈ 𝔓, P.InSquare M) → ∀ (J : ℕ) (𝒯 : ℕ → Finset (MultitileTree ρ))
      (R : ℕ → MultitileTree ρ → Finset (Multitile ρ)) (S : ℕ → Set (Multitile ρ)),
      (∀ x, treeSum ch f L E 𝔓 x = ∑ j ∈ Finset.range J, ∑ T ∈ 𝒯 j,
        treeSum ch f L E (R j T) x) →
      (∀ j, ∀ T ∈ 𝒯 j, R j T ⊆ T.T ∧ R j T ⊆ 𝔓 ∧ T.IsTree C₁ C₂ M ∧
        (T.T : Set (Multitile ρ)) ⊆ S j) →
      (∀ j, energy C₁ C₂ M ch f (S j) ≤
        ENNReal.ofReal (min (a * Fm ^ (1 / 2 : ℝ) * nuE ^ j) (a * Fm))) →
      (∀ j, density C₁ C₂ M L E (S j) ≤ ENNReal.ofReal (a * muD r ^ j)) →
      (∀ j, ∑ T ∈ 𝒯 j, ENNReal.ofReal T.I.length ≤ ENNReal.ofReal (c * 2 ^ j)) →
      ∫⁻ x, ‖treeSum ch f L E 𝔓 x‖ₑ ≤ ENNReal.ofReal (C * Fm ^ (1 - 1 / r)) := by
  have hr1 : 1 < r := by linarith
  have hr'1 := one_lt_conjExponent hr1
  obtain ⟨K, hK0, hK⟩ := treeestimate_tail (r := r) (q := 1) hr le_rfl (by norm_num) hC
  obtain ⟨Cs, hCs0, hCs⟩ := small_sum_le hr
  refine ⟨K * a ^ 2 * c * Cs + 1, by positivity, ?_⟩
  intro ρ _ M hρ ch f E hE L Fm hFm0 hFm1 𝔓 hsep hsq J 𝒯 R S hid hR hen hde hsize
  have hm : ∀ j (T : MultitileTree ρ), Measurable fun x => ‖treeSum ch f L E (R j T) x‖ₑ :=
    fun j T => (measurable_treeSum ch f L hE _).enorm
  have hmin : min 1 (Real.conjExponent r / 1) = 1 := by
    rw [div_one]; exact min_eq_left hr'1.le
  set ene : ℕ → ℝ := fun j => min (a * Fm ^ (1 / 2 : ℝ) * nuE ^ j) (a * Fm) with hene
  set den : ℕ → ℝ := fun j => a * muD r ^ j with hden
  have hene0 : ∀ j, 0 ≤ ene j := fun j => le_min
    (mul_nonneg (mul_nonneg ha.le (Real.rpow_nonneg hFm0.le _)) (pow_nonneg nuE_pos.le j))
    (mul_nonneg ha.le hFm0.le)
  have hden0 : ∀ j, 0 ≤ den j := fun j => mul_nonneg ha.le (pow_nonneg (muD_pos r).le j)
  have htree : ∀ j, ∀ T ∈ 𝒯 j, ∫⁻ x, ‖treeSum ch f L E (R j T) x‖ₑ ≤
      ENNReal.ofReal (K * ene j * den j * T.I.length) := by
    intro j T hT
    obtain ⟨hRT, hR𝔓, hTT, hTS⟩ := hR j T hT
    have := hK hρ ch f hE L (hene0 j) (hden0 j) (hen j) (hde j) (MultitileTree.mk (R j T) T.I T.ξ)
      (hTT.of_subset (R j T) hRT) (fun P hP => hsq P (hR𝔓 hP))
      ((Finset.coe_subset.2 hRT).trans hTS) (hsep.mono (Finset.coe_subset.2 hR𝔓)) 0
    simp only [tailSet, Set.indicator_univ, ENNReal.rpow_one, hmin, Real.rpow_one,
      tailWeight, mul_one] at this
    exact this
  have hstage : ∀ j, ∑ T ∈ 𝒯 j, ∫⁻ x, ‖treeSum ch f L E (R j T) x‖ₑ ≤
      ENNReal.ofReal (K * ene j * den j * (c * 2 ^ j)) := by
    intro j
    calc ∑ T ∈ 𝒯 j, ∫⁻ x, ‖treeSum ch f L E (R j T) x‖ₑ
        ≤ ∑ T ∈ 𝒯 j, ENNReal.ofReal (K * ene j * den j) * ENNReal.ofReal T.I.length :=
          Finset.sum_le_sum fun T hT => (htree j T hT).trans (by
            rw [← ENNReal.ofReal_mul (by have := hene0 j; have := hden0 j; positivity)])
      _ = ENNReal.ofReal (K * ene j * den j) * ∑ T ∈ 𝒯 j, ENNReal.ofReal T.I.length := by
          rw [Finset.mul_sum]
      _ ≤ ENNReal.ofReal (K * ene j * den j) * ENNReal.ofReal (c * 2 ^ j) :=
          mul_le_mul' le_rfl (hsize j)
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by have := hene0 j; have := hden0 j; positivity)]
  calc ∫⁻ x, ‖treeSum ch f L E 𝔓 x‖ₑ
      ≤ ∫⁻ x, ∑ j ∈ Finset.range J, ∑ T ∈ 𝒯 j, ‖treeSum ch f L E (R j T) x‖ₑ := by
        refine lintegral_mono fun x => ?_
        rw [hid x]
        exact (enorm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => enorm_sum_le _ _)
    _ = ∑ j ∈ Finset.range J, ∑ T ∈ 𝒯 j, ∫⁻ x, ‖treeSum ch f L E (R j T) x‖ₑ := by
        rw [lintegral_finsetSum _ fun j _ => Finset.measurable_sum _ fun T _ => hm j T]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [lintegral_finsetSum _ fun T _ => hm j T]
    _ ≤ ∑ j ∈ Finset.range J, ENNReal.ofReal (K * ene j * den j * (c * 2 ^ j)) :=
        Finset.sum_le_sum fun j _ => hstage j
    _ = ENNReal.ofReal (∑ j ∈ Finset.range J, K * ene j * den j * (c * 2 ^ j)) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun j _ => by
          have := hene0 j; have := hden0 j; positivity]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hϑ : ∀ j : ℕ, K * ene j * den j * (c * 2 ^ j) =
            K * a ^ 2 * c * (((2 : ℝ) ^ (1 / r)) ^ j * min (Fm ^ (1 / 2 : ℝ) * nuE ^ j) Fm) := by
          intro j
          have h1 : ene j = a * min (Fm ^ (1 / 2 : ℝ) * nuE ^ j) Fm := by
            simp only [hene]
            rw [mul_assoc, ← mul_min_of_nonneg _ _ ha.le]
          have h2 : ((2 : ℝ) ^ (1 / r)) ^ j = muD r ^ j * 2 ^ j := by
            rw [← muD_mul_two hr1, mul_pow]
          rw [h1, h2]
          simp only [hden]
          ring
        simp_rw [hϑ]
        rw [← Finset.mul_sum]
        have := hCs hFm0 hFm1 J
        have hKac : 0 ≤ K * a ^ 2 * c := by positivity
        calc K * a ^ 2 * c * ∑ j ∈ Finset.range J, ((2 : ℝ) ^ (1 / r)) ^ j *
              min (Fm ^ (1 / 2 : ℝ) * nuE ^ j) Fm
            ≤ K * a ^ 2 * c * (Cs * Fm ^ (1 - 1 / r)) := mul_le_mul_of_nonneg_left this hKac
          _ ≤ (K * a ^ 2 * c * Cs + 1) * Fm ^ (1 - 1 / r) := by
              have : 0 ≤ Fm ^ (1 - 1 / r) := by positivity
              nlinarith

/-- **The decomposition for `|F| ≤ 1`** ([O+] `L1except`, case of small `F`): a finite separated
family `𝔓` (this is `𝔓'` of the source) of energy at most `κ |F|` is, up to the multitiles with zero
coefficient, the disjoint union of the sets `R_{j,T} ⊆ T`, `T ∈ 𝒯_j`, where the trees of stage `j`
lie in a family `S_j` of energy `≤ min(a |F|^{1/2} 2^{-j/2}, a |F|)` and density
`≤ a 2^{-j/r'}`, with `∑_{T ∈ 𝒯_j} |I_T| ≤ c 2^j`. -/
theorem exists_small_decomposition {r : ℝ} (hr : 2 < r) {C₁ C₂ C₃ : ℝ}
    (hC : AdmissibleConstants C₁ C₂ C₃) {κ : ℝ} (hκ : 0 < κ) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {M : ℤ}, ρ.IsStd →
      ∀ (ch : ProfileChoice) {f : ℝ → ℂ} {F E : Set ℝ}, AEStronglyMeasurable f volume →
      (∀ᵐ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) → volume E ≤ 2 →
      ∀ (L : Linearization r) {Fm : ℝ}, 0 < Fm → Fm ≤ 1 → volume F = ENNReal.ofReal Fm →
      ∀ (𝔓 : Finset (Multitile ρ)), Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ)) →
      (∀ P ∈ 𝔓, P.InSquare M) →
      energy C₁ C₂ M ch f (𝔓 : Set (Multitile ρ)) ≤ ENNReal.ofReal (κ * Fm) →
      ∃ (J : ℕ) (𝒯 : ℕ → Finset (MultitileTree ρ))
        (R : ℕ → MultitileTree ρ → Finset (Multitile ρ)) (S : ℕ → Set (Multitile ρ)),
      (∀ x, treeSum ch f L E 𝔓 x = ∑ j ∈ Finset.range J, ∑ T ∈ 𝒯 j,
        treeSum ch f L E (R j T) x) ∧
      (∀ j, ∀ T ∈ 𝒯 j, R j T ⊆ T.T ∧ R j T ⊆ 𝔓 ∧ T.IsTree C₁ C₂ M ∧
        (T.T : Set (Multitile ρ)) ⊆ S j) ∧
      (∀ j, energy C₁ C₂ M ch f (S j) ≤
        ENNReal.ofReal (min (a * Fm ^ (1 / 2 : ℝ) * nuE ^ j) (a * Fm))) ∧
      (∀ j, density C₁ C₂ M L E (S j) ≤ ENNReal.ofReal (a * muD r ^ j)) ∧
      (∀ j, ∑ T ∈ 𝒯 j, ENNReal.ofReal T.I.length ≤ ENNReal.ofReal (c * 2 ^ j)) := by
  classical
  have hr1 : 1 < r := by linarith
  obtain ⟨K₀, hK₀0, hK₀⟩ := exists_univ_den_ene_bound
  obtain ⟨KS, hKS0, hKS⟩ := exists_energy_density_stages hr1
  set a : ℝ := K₀ + κ + 1 with hadef
  have ha : 0 < a := by positivity
  set c : ℝ := KS / a ^ 2 + 2 * KS / a ^ Real.conjExponent r with hcdef
  have hc : 0 < c := by positivity
  refine ⟨a, c, ha, hc, ?_⟩
  intro ρ _ M hρ ch f F E hfm hfF hE2 L Fm hFm0 hFm1 hFvol 𝔓 hsep hsq hen𝔓
  have hf1 : ∀ᵐ x, ‖f x‖ ≤ 1 := hfF.mono fun x hx =>
    hx.trans (by by_cases h : x ∈ F <;> simp [h])
  obtain ⟨hde𝔓, -⟩ := hK₀ (M := M) hC hρ ch hfm hf1 hr1 L E (𝔓 : Set (Multitile ρ)) hsep
  set e₀ : ℝ := a * Fm ^ (1 / 2 : ℝ) with he₀def
  have hFle : Fm ≤ Fm ^ (1 / 2 : ℝ) := by
    calc Fm = Fm ^ (1 : ℝ) := (Real.rpow_one Fm).symm
      _ ≤ Fm ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hFm0 hFm1 (by norm_num)
  have he₀ : 0 < e₀ := by positivity
  have hκa : κ ≤ a := by linarith
  have hen' : energy C₁ C₂ M ch f (𝔓 : Set (Multitile ρ)) ≤ ENNReal.ofReal e₀ :=
    hen𝔓.trans (ENNReal.ofReal_le_ofReal (by nlinarith))
  have hde' : density C₁ C₂ M L E (𝔓 : Set (Multitile ρ)) ≤ ENNReal.ofReal a :=
    hde𝔓.trans (ENNReal.ofReal_le_ofReal (by linarith))
  obtain ⟨J, 𝒯₁, Q₁, hI1, hcov₁⟩ := hKS hC hρ ch hfm hfF L E hsep hsq he₀ ha one_half_le_nuE
    nuE_lt_one (one_half_le_muD hr1) (muD_lt_one hr1) hen' hde'
  have : Nonempty (Σ _ : ℕ, MultitileTree ρ) := ⟨⟨0, MultitileTree.mk ∅ ⟨0, 0⟩ 0⟩⟩
  set s : Finset (Σ _ : ℕ, MultitileTree ρ) := (Finset.range J).sigma 𝒯₁ with hs
  set Q : Finset (Multitile ρ) := 𝔓.filter fun P => P.coeff ch f ≠ 0 with hQ
  have hcov : ∀ P ∈ Q, ∃ i ∈ s, P ∈ (fun i : (Σ _ : ℕ, MultitileTree ρ) => i.2.T) i := by
    intro P hP
    obtain ⟨hP𝔓, hPc⟩ := Finset.mem_filter.1 hP
    rcases hcov₁ P hP𝔓 with h | ⟨j, hj, T, hT, hPT⟩
    · exact absurd h hPc
    · exact ⟨⟨j, T⟩, Finset.mem_sigma.2 ⟨Finset.mem_range.2 hj, hT⟩, hPT⟩
  obtain ⟨R, hRV, hRQ, hRsum⟩ := exists_assignment.{_, _, 0} s (fun i => i.2.T) Q hcov
  refine ⟨J, 𝒯₁, fun j T => R ⟨j, T⟩, fun j => (Q₁ j : Set (Multitile ρ)), ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    have h1 : treeSum ch f L E 𝔓 x = ∑ P ∈ Q, P.coeff ch f * P.wavePacket ch x * P.aP L x *
        E.indicator (fun _ => (1 : ℂ)) x := by
      rw [hQ, Finset.sum_filter_of_ne]
      · rfl
      · intro P _ hP hc
        exact hP (by simp [hc])
    rw [h1, hRsum (fun P => P.coeff ch f * P.wavePacket ch x * P.aP L x *
      E.indicator (fun _ => (1 : ℂ)) x), hs, Finset.sum_sigma]
    rfl
  · intro j T hT
    have hT' := (hI1 j).2.2.2.1 T hT
    exact ⟨hRV ⟨j, T⟩, (hRQ ⟨j, T⟩).trans (Finset.filter_subset _ _), hT'.1, hT'.2⟩
  · intro j
    obtain ⟨hQ𝔓, hQen, hQde, hT, hcost⟩ := hI1 j
    have hmono : energy C₁ C₂ M ch f (Q₁ j : Set (Multitile ρ)) ≤
        energy C₁ C₂ M ch f (𝔓 : Set (Multitile ρ)) :=
      energyOf_mono C₁ C₂ M _ (by exact_mod_cast hQ𝔓)
    have h2 : energy C₁ C₂ M ch f (Q₁ j : Set (Multitile ρ)) ≤ ENNReal.ofReal (a * Fm) :=
      hmono.trans (hen𝔓.trans (ENNReal.ofReal_le_ofReal (by nlinarith)))
    rcases le_total (a * Fm ^ (1 / 2 : ℝ) * nuE ^ j) (a * Fm) with h | h
    · rw [min_eq_left h]; exact hQen
    · rw [min_eq_right h]; exact h2
  · intro j
    exact (hI1 j).2.2.1
  · intro j
    refine ((hI1 j).2.2.2.2).trans ?_
    rw [hFvol]
    exact stage_cost_le hr1 hKS0.le ha hFm0 hE2 j

/-- **The case `0 < |F| ≤ 1` of `L1except`** ([O+] L2652-L2685): for `r > 2` and `p ≥ r'` there
is an absolute `C` such that for every finite separated family `𝔓` of multitiles there is a
measurable `G = {M[1_F] > 16 |F|}` with `|G| ≤ 1/4` and
`∫_{ℝ ∖ G} |1_E ∑_{P ∈ 𝔓} ⟨f, φ_P⟩ φ_P a_P| ≤ C |F|^{1/p}` (for `|E| ≤ 2`, `|f| ≤ 1_F`). -/
theorem l1except_small {r p : ℝ} (hr : 2 < r) (hp : Real.conjExponent r ≤ p) {C₁ C₂ C₃ : ℝ}
    (hC : AdmissibleConstants C₁ C₂ C₃) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo], ρ.IsStd → ∀ (ch : ProfileChoice)
      {f : ℝ → ℂ} {F E : Set ℝ}, MeasurableSet F → AEStronglyMeasurable f volume →
      (∀ᵐ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) → MeasurableSet E → volume E ≤ 2 →
      ∀ (L : Linearization r) {Fm : ℝ}, 0 < Fm → Fm ≤ 1 → volume F = ENNReal.ofReal Fm →
      ∀ (𝔓 : Finset (Multitile ρ)), Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ)) →
      ∃ G : Set ℝ, MeasurableSet G ∧ volume G ≤ 1 / 4 ∧
        ∫⁻ x in Gᶜ, ‖treeSum ch f L E 𝔓 x‖ₑ ≤ ENNReal.ofReal (C * Fm ^ (1 / p)) := by
  classical
  have hr1 : 1 < r := by linarith
  have hr'1 := one_lt_conjExponent hr1
  have hC1 : 0 < C₁ := by linarith [hC.one_le, hC.lt₁, hC.lt₂]
  obtain ⟨Kτ, hKτ0, hKτ⟩ := exists_energy_le_of_not_subset
  obtain ⟨K₁, hK₁0, hK₁⟩ := tileslargemaxprop_treeSum 4 (by norm_num)
  set κ : ℝ := Kτ * (1 + C₁) * 16 + 1 with hκdef
  have hκ : 0 < κ := by positivity
  obtain ⟨a, c, ha, hc, hdec⟩ := exists_small_decomposition hr hC hκ
  obtain ⟨Cs, hCs0, hCs⟩ := small_summation hr hC ha hc
  refine ⟨K₁ + Cs, by positivity, ?_⟩
  intro ρ _ hρ ch f F E hF hfm hfF hE hE2 L Fm hFm0 hFm1 hFvol 𝔓 hsep
  obtain ⟨M, hsq⟩ := exists_inSquare_finset 𝔓
  have hFt : volume F ≠ ⊤ := by rw [hFvol]; exact ENNReal.ofReal_ne_top
  have hF0 : volume F ≠ 0 := by rw [hFvol]; exact (ENNReal.ofReal_pos.2 hFm0).ne'
  have hlam : 0 < 16 * Fm := by positivity
  -- the exponent comparison `Fm^{1 - 1/r} ≤ Fm^{1/p}`
  have hp0 : 0 < p := by linarith
  have h1p : 1 / p ≤ 1 - 1 / r := by
    rw [← one_div_conjExponent_eq hr1]
    exact one_div_le_one_div_of_le (by linarith) hp
  have hpow : Fm ^ (1 - 1 / r) ≤ Fm ^ (1 / p) := Real.rpow_le_rpow_of_exponent_ge hFm0 hFm1 h1p
  set G : Set ℝ := maxSuperlevel F (16 * Fm) with hG
  have hGm : MeasurableSet G := measurableSet_maxSuperlevel F _
  have hGvol : volume G ≤ 1 / 4 := by
    have h := volume_maximalHLR_indicator_gt_sixteen_le hF hF0 hFt
    refine le_trans (le_of_eq ?_) h
    simp only [hG, maxSuperlevel]
    congr 2
    ext x
    rw [ENNReal.ofReal_mul (by norm_num), hFvol]
    simp
  refine ⟨G, hGm, hGvol, ?_⟩
  set 𝔓in : Finset (Multitile ρ) := 𝔓.filter fun P => P.I.toSet ⊆ G with h𝔓in
  set 𝔓' : Finset (Multitile ρ) := 𝔓.filter fun P => ¬ P.I.toSet ⊆ G with h𝔓'
  have hsplit : ∀ x, treeSum ch f L E 𝔓 x = treeSum ch f L E 𝔓in x + treeSum ch f L E 𝔓' x := by
    intro x
    simp only [treeSum, h𝔓in, h𝔓']
    rw [Finset.sum_filter_add_sum_filter_not]
  have hmeas : ∀ T : Finset (Multitile ρ), Measurable fun x => ‖treeSum ch f L E T x‖ₑ :=
    fun T => (measurable_treeSum ch f L hE T).enorm
  calc ∫⁻ x in Gᶜ, ‖treeSum ch f L E 𝔓 x‖ₑ
      ≤ ∫⁻ x in Gᶜ, (‖treeSum ch f L E 𝔓in x‖ₑ + ‖treeSum ch f L E 𝔓' x‖ₑ) := by
        refine lintegral_mono fun x => ?_
        rw [hsplit x]
        exact enorm_add_le _ _
    _ = (∫⁻ x in Gᶜ, ‖treeSum ch f L E 𝔓in x‖ₑ) + ∫⁻ x in Gᶜ, ‖treeSum ch f L E 𝔓' x‖ₑ :=
        lintegral_add_left (μ := volume.restrict Gᶜ) (hmeas 𝔓in)
          (fun x => ‖treeSum ch f L E 𝔓' x‖ₑ)
    _ ≤ ENNReal.ofReal (K₁ * Fm ^ (1 / p)) + ENNReal.ofReal (Cs * Fm ^ (1 / p)) := by
        refine add_le_add ?_ ?_
        · -- the multitiles with `I ⊂ G`
          have h := hK₁ (Fact.out : ρ.IsOneOrTwo) hr.le ch L hE 𝔓in hF hfm hfF hlam
            (fun P hP => (Finset.mem_filter.1 hP).2)
          rw [← eLpNorm_one_eq_lintegral_enorm
            (measurable_treeSum ch f L hE 𝔓in).aestronglyMeasurable]
          refine h.trans ?_
          rw [hFvol, ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h16 : (16 : ℝ) ^ (-(1 / r)) ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by
              have : 0 < 1 / r := by positivity
              linarith)
          have e1 : (16 * Fm) ^ (-(1 / r)) * Fm = 16 ^ (-(1 / r)) * Fm ^ (1 - 1 / r) := by
            rw [Real.mul_rpow (by norm_num) hFm0.le, mul_assoc, sub_eq_add_neg,
              Real.rpow_add hFm0, Real.rpow_one, mul_comm Fm]
          have hF1 : 0 ≤ Fm ^ (1 - 1 / r) := by positivity
          calc K₁ * (16 * Fm) ^ (-(1 / r)) * Fm = K₁ * (16 ^ (-(1 / r)) * Fm ^ (1 - 1 / r)) := by
                rw [mul_assoc, e1]
            _ ≤ K₁ * (1 * Fm ^ (1 / p)) := by
                refine mul_le_mul_of_nonneg_left ?_ hK₁0.le
                exact mul_le_mul h16 hpow hF1 zero_le_one
            _ = K₁ * Fm ^ (1 / p) := by ring
        · -- the remaining multitiles `𝔓'`
          have hsep' : Separated C₁ C₂ C₃ (𝔓' : Set (Multitile ρ)) :=
            hsep.mono (by exact_mod_cast Finset.filter_subset _ _)
          have hsq' : ∀ P ∈ 𝔓', P.InSquare M := fun P hP =>
            hsq P (Finset.mem_filter.1 hP).1
          have hen' : energy C₁ C₂ M ch f (𝔓' : Set (Multitile ρ)) ≤ ENNReal.ofReal (κ * Fm) := by
            refine (hKτ (M := M) hC hρ ch hF hfm hfF hlam (𝔓' : Set (Multitile ρ)) hsep'
              (fun P hP => (Finset.mem_filter.1 hP).2)).trans (ENNReal.ofReal_le_ofReal ?_)
            rw [hκdef]
            nlinarith
          obtain ⟨J, 𝒯, R, S, h1, h2, h3, h4, h5⟩ :=
            hdec (M := M) hρ ch hfm hfF hE2 L hFm0 hFm1 hFvol 𝔓' hsep' hsq' hen'
          refine (setLIntegral_le_lintegral _ _).trans ?_
          refine (hCs hρ ch f hE L hFm0 hFm1 𝔓' hsep' hsq' J 𝒯 R S h1 h2 h3 h4 h5).trans ?_
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpow hCs0.le)
    _ = ENNReal.ofReal ((K₁ + Cs) * Fm ^ (1 / p)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

end SmallCase

end PrimeCarleson.Proof.Oplus
