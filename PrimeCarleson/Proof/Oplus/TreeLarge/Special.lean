module

public import PrimeCarleson.Proof.Oplus.TreeLarge.LargeIntervals

/-!
# The tree estimate for special trees ([O+] L2137-L2150)

Source: [O+] `treeestimate`, L2137–L2150 for one special tree (`l`-lacunary, or `l`-overlapping
with (jconsolidation) and `l^±`; L2137-L2150):
"(Lqfortree)
for `T` follows from the small-interval estimate on each `J ∈ 𝒥`, the large-interval estimate for
`J ∈ 𝒥` meeting `16 I_T` and (treeestimateaway) for `ℓ = 4`". On `J`, the tree sum is the sum of the
part with `|I| < C''|J|` and the part with `|I| ≥ C''|J|`; `ℝ = 16 I_T ∪ (ℝ ∖ 16 I_T)`, the
intervals
`J ∈ 𝒥` meeting `16 I_T` cover `16 I_T`, and the sums over finite subfamilies are bounded by
`treeestimate_small_intervals_sum`, `treeestimate_large_intervals_sum` (the supremum over finite
subfamilies is the `tsum`). The result is in the `q`-th power form
`∫ |∑_P ⟨f, φ_P⟩ φ_P a_P 1_E|^q ≤ (K ene den^{min(1, r'/q)})^q |I_T|`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson PrimeCarleson.Proof.Common

section Special

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ}

omit [Fact ρ.IsOneOrTwo] in
/-- The tree sum splits according to the size of `|I|`. -/
theorem treeSum_filter_split {r : ℝ} (ch : ProfileChoice) (f : ℝ → ℂ) (L : Linearization r)
    (E : Set ℝ) (T : Finset (Multitile ρ)) (c : ℝ) (x : ℝ) :
    treeSum ch f L E T x = treeSum ch f L E (T.filter fun P => P.I.length < c) x +
      treeSum ch f L E (T.filter fun P => c ≤ P.I.length) x := by
  classical
  unfold treeSum
  rw [← Finset.sum_filter_add_sum_filter_not T (fun P => P.I.length < c)]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext P
  simp [not_lt]

/-- **The assembly of `treeestimate` for a special tree**, `q`-th power form: for `r > 2`,
`1 ≤ q ≤ 2`, `N ≥ 11` there is `K` such that for every tree `T ⊂ S` of multitiles in the square
`[-2^M, 2^M]²` which is `l`-lacunary or `l`-overlapping with (jconsolidation) and `l^±`, satisfying
the separation assumptions, with `energy(S) ≤ ene`, `density(S) ≤ den`,
`∫ |∑_{P ∈ T} ⟨f, φ_P⟩ φ_P a_P 1_E|^q ≤ (K ene den^{min(1, r'/q)})^q |I_T|`. -/
theorem treeestimate_special_pow {r q : ℝ} (hr : 2 < r) (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (N : ℕ)
    (hN : 11 ≤ N) (hC : AdmissibleConstants C₁ C₂ C₃) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {M : ℤ}, ρ.IsStd → ∀ (ch : ProfileChoice)
      (f : ℝ → ℂ) {E : Set ℝ}, MeasurableSet E → ∀ (L : Linearization r) {S : Set (Multitile ρ)}
      {ene den : ℝ}, 0 ≤ ene → 0 ≤ den → energy C₁ C₂ M ch f S ≤ ENNReal.ofReal ene →
      density C₁ C₂ M L E S ≤ ENNReal.ofReal den → ∀ (𝒯 : MultitileTree ρ),
      𝒯.IsTree C₁ C₂ M → (∀ P ∈ 𝒯.T, P.InSquare M) → (𝒯.T : Set (Multitile ρ)) ⊆ S →
      Separated C₁ C₂ C₃ (𝒯.T : Set (Multitile ρ)) → 𝒯.IsSpecialJ C₂ →
        ∫⁻ x, ‖treeSum ch f L E 𝒯.T x‖ₑ ^ q ≤
          ENNReal.ofReal ((K * ene * den ^ (min 1 (Real.conjExponent r / q))) ^ q *
            𝒯.I.length) := by
  classical
  have hr1 : 1 < r := by linarith
  have hq0 : 0 < q := by linarith
  obtain ⟨Ksm, hKsm0, hKsm⟩ := treeestimate_small_intervals_sum hr.le hq1 hq2 7 (by norm_num) hC
  obtain ⟨Kaw, hKaw0, hKaw⟩ := treeestimate_away_from_top hr.le hq1 hq2 N hN hC
  obtain ⟨Klg, hKlg0, hKlg⟩ := treeestimate_large_intervals_sum hr hq1 hq2 hC
  set κaw : ℝ := Kaw * ((2 : ℝ) ^ 4) ^ (-((N : ℤ) - 10)) with hκaw
  have hκaw0 : 0 ≤ κaw := by positivity
  set c : ℝ := 2 ^ (q - 1) * (Ksm ^ q * 48 + Klg ^ q * 48) + κaw ^ q with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨c ^ (1 / q), by positivity, ?_⟩
  intro ρ _ M hρ ch f E hE L S ene den hene hden hen hde 𝒯 hT hsq hsub hsep hspec
  set σ := min 1 (Real.conjExponent r / q) with hσ
  have hσ0 : 0 ≤ σ := by
    refine le_min zero_le_one ?_
    have : 0 < Real.conjExponent r := by
      unfold Real.conjExponent
      exact div_pos (by linarith) (by linarith)
    positivity
  set B : ℝ := ene * den ^ σ with hB
  have hB0 : 0 ≤ B := by positivity
  have hIpos := 𝒯.I.length_pos
  have hfin : (c ^ (1 / q) * ene * den ^ σ) ^ q * 𝒯.I.length = c * B ^ q * 𝒯.I.length := by
    rw [mul_assoc, ← hB, Real.mul_rpow (by positivity) hB0, ← Real.rpow_mul hc0,
      one_div_mul_cancel hq0.ne', Real.rpow_one]
  rw [hfin]
  by_cases hne : 𝒯.T.Nonempty
  swap
  · have : treeSum ch f L E 𝒯.T = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty.1 hne]
      funext x
      simp [treeSum]
    rw [this]
    simp only [Pi.zero_apply, enorm_zero, ENNReal.zero_rpow_of_pos hq0, lintegral_const,
      zero_mul]
    exact zero_le
  set F := treeSum ch f L E 𝒯.T with hF
  have hFm : Measurable F := measurable_treeSum ch f L hE _
  set U : Set ℝ := 𝒯.I.dilate 16 with hU
  have hUm : MeasurableSet U := measurableSet_Ico
  -- the far region
  have hfar : ∫⁻ x in Uᶜ, ‖F x‖ₑ ^ q ≤ ENNReal.ofReal (κaw ^ q * B ^ q * 𝒯.I.length) := by
    have h := hKaw hρ ch f hE L hene hden hen hde 𝒯 hT hsq hsub hsep (ℓ := 4) le_rfl
    have hUe : 𝒯.I.dilate ((2 : ℝ) ^ (4 : ℕ)) = U := by
      rw [hU]; norm_num
    rw [hUe] at h
    have hmeas : AEStronglyMeasurable F (volume.restrict Uᶜ) := hFm.aestronglyMeasurable
    have heq : ∫⁻ x in Uᶜ, ‖F x‖ₑ ^ q =
        (eLpNorm F (ENNReal.ofReal q) (volume.restrict Uᶜ)) ^ q := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hq0).ne'
        ENNReal.ofReal_ne_top hmeas, ENNReal.toReal_ofReal hq0.le, ← ENNReal.rpow_mul,
        one_div_mul_cancel hq0.ne', ENNReal.rpow_one]
    rw [heq]
    refine (ENNReal.rpow_le_rpow h hq0.le).trans ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have e1 : (Kaw * ((2 : ℝ) ^ 4) ^ (-((N : ℤ) - 10)) * ene * den ^ σ *
        𝒯.I.length ^ (1 / q)) = (κaw * B) * 𝒯.I.length ^ (1 / q) := by
      rw [hκaw, hB]; ring
    rw [e1, Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity)
      (by positivity), ← Real.rpow_mul hIpos.le, one_div_mul_cancel hq0.ne', Real.rpow_one]
  -- the near region
  set sm : Dyadic → ℝ → ℂ := fun J => treeSum ch f L E
    (𝒯.T.filter fun P => P.I.length < Cpp C₁ C₂ * J.length) with hsm
  set lg : Dyadic → ℝ → ℂ := fun J => treeSum ch f L E
    (𝒯.T.filter fun P => Cpp C₁ C₂ * J.length ≤ P.I.length) with hlg
  have hsmm : ∀ J, Measurable (sm J) := fun J => measurable_treeSum ch f L hE _
  have hlgm : ∀ J, Measurable (lg J) := fun J => measurable_treeSum ch f L hE _
  have hFsplit : ∀ J : Dyadic, ∀ x, F x = sm J x + lg J x := fun J x =>
    treeSum_filter_split ch f L E 𝒯.T (Cpp C₁ C₂ * J.length) x
  have h2 : (2 : ℝ≥0∞) ^ (q - 1) = ENNReal.ofReal (2 ^ (q - 1)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by linarith)]
    simp
  set I1 : Dyadic → ℝ≥0∞ := fun J => ∫⁻ x in J.toSet, ‖sm J x‖ₑ ^ q with hI1
  set I2 : Dyadic → ℝ≥0∞ := fun J => ∫⁻ x in J.toSet, ‖lg J x‖ₑ ^ q with hI2
  have hperJ : ∀ J : Dyadic, ∫⁻ x in J.toSet, ‖F x‖ₑ ^ q ≤
      (2 : ℝ≥0∞) ^ (q - 1) * (I1 J + I2 J) := by
    intro J
    calc ∫⁻ x in J.toSet, ‖F x‖ₑ ^ q
        ≤ ∫⁻ x in J.toSet, (2 : ℝ≥0∞) ^ (q - 1) * (‖sm J x‖ₑ ^ q + ‖lg J x‖ₑ ^ q) :=
          lintegral_mono fun x => by
            rw [hFsplit J x]
            exact (ENNReal.rpow_le_rpow (enorm_add_le _ _) hq0.le).trans
              (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hq1)
      _ = (2 : ℝ≥0∞) ^ (q - 1) * ∫⁻ x in J.toSet, (‖sm J x‖ₑ ^ q + ‖lg J x‖ₑ ^ q) :=
          lintegral_const_mul' _ _ (by
            rw [h2]; exact ENNReal.ofReal_ne_top)
      _ = (2 : ℝ≥0∞) ^ (q - 1) * (I1 J + I2 J) := by
          rw [lintegral_add_left ((hsmm J).enorm.pow_const q)]
  set X𝒥 : Set Dyadic := {J | 𝒯.IsMaxAvoiding J ∧ (J.toSet ∩ U).Nonempty} with hX
  have hcountable : Countable X𝒥 := (Set.to_countable _).to_subtype
  have hcover : U ⊆ ⋃ J : X𝒥, J.1.toSet := by
    intro x hx
    obtain ⟨J, hJ, hxJ⟩ := MultitileTree.exists_isMaxAvoiding_mem hne x
    exact Set.mem_iUnion.2 ⟨⟨J, hJ, ⟨x, hxJ, hx⟩⟩, hxJ⟩
  have hnear : ∫⁻ x in U, ‖F x‖ₑ ^ q ≤ ENNReal.ofReal (2 ^ (q - 1) *
      (((Ksm * B) ^ q + (Klg * B) ^ q) * (48 * 𝒯.I.length))) := by
    calc ∫⁻ x in U, ‖F x‖ₑ ^ q ≤ ∫⁻ x in ⋃ J : X𝒥, J.1.toSet, ‖F x‖ₑ ^ q :=
          lintegral_mono_set hcover
      _ ≤ ∑' J : X𝒥, ∫⁻ x in J.1.toSet, ‖F x‖ₑ ^ q := lintegral_iUnion_le _ _
      _ ≤ _ := by
          rw [ENNReal.tsum_eq_iSup_sum]
          refine iSup_le fun s => ?_
          have h𝒥 : ∀ J ∈ s.image Subtype.val,
              𝒯.IsMaxAvoiding J ∧ (J.toSet ∩ 𝒯.I.dilate 16).Nonempty := by
            intro J hJ
            obtain ⟨J', -, rfl⟩ := Finset.mem_image.1 hJ
            exact J'.2
          have hinj : Set.InjOn (Subtype.val : X𝒥 → Dyadic) (s : Set X𝒥) :=
            fun a _ b _ h => Subtype.ext h
          have hs1 := hKsm hρ ch f hE L hene hden hen hde 𝒯 hT hsq hsub hsep hne
            (s.image Subtype.val) h𝒥
          have hs2 := hKlg hρ ch f hE L hene hden hen hde 𝒯 hT hsq hsub hsep hspec hne
            (s.image Subtype.val) h𝒥
          rw [Finset.sum_image hinj] at hs1 hs2
          have hKB : ∀ K : ℝ, K * ene * den ^ σ = K * B := fun K => by rw [hB]; ring
          rw [hKB] at hs1 hs2
          calc ∑ J ∈ s, ∫⁻ x in J.1.toSet, ‖F x‖ₑ ^ q
              ≤ ∑ J ∈ s, (2 : ℝ≥0∞) ^ (q - 1) * (I1 J.1 + I2 J.1) :=
                Finset.sum_le_sum fun J _ => hperJ J.1
            _ = (2 : ℝ≥0∞) ^ (q - 1) * (∑ J ∈ s, I1 J.1 + ∑ J ∈ s, I2 J.1) := by
                rw [← Finset.mul_sum, Finset.sum_add_distrib]
            _ ≤ ENNReal.ofReal (2 ^ (q - 1)) * (ENNReal.ofReal ((Ksm * B) ^ q *
                  (48 * 𝒯.I.length)) + ENNReal.ofReal ((Klg * B) ^ q *
                  (48 * 𝒯.I.length))) := by
                rw [h2]
                gcongr
            _ = _ := by
                rw [← ENNReal.ofReal_add (by positivity) (by positivity),
                  ← ENNReal.ofReal_mul (by positivity)]
                congr 1
                ring
  have htot := (lintegral_add_compl (μ := volume) (fun x => ‖F x‖ₑ ^ q) hUm).symm
  rw [htot]
  calc (∫⁻ x in U, ‖F x‖ₑ ^ q) + ∫⁻ x in Uᶜ, ‖F x‖ₑ ^ q
      ≤ ENNReal.ofReal (2 ^ (q - 1) * (((Ksm * B) ^ q + (Klg * B) ^ q) * (48 * 𝒯.I.length))) +
        ENNReal.ofReal (κaw ^ q * B ^ q * 𝒯.I.length) := add_le_add hnear hfar
    _ = ENNReal.ofReal (2 ^ (q - 1) * (((Ksm * B) ^ q + (Klg * B) ^ q) * (48 * 𝒯.I.length)) +
        κaw ^ q * B ^ q * 𝒯.I.length) := (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ = ENNReal.ofReal (c * B ^ q * 𝒯.I.length) := by
        congr 1
        rw [Real.mul_rpow hKsm0 hB0, Real.mul_rpow hKlg0 hB0, hc]
        ring

end Special

end PrimeCarleson.Proof.Oplus
