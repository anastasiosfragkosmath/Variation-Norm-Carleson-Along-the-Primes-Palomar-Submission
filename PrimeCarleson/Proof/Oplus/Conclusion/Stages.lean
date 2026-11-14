module

public import PrimeCarleson.Proof.Oplus.Conclusion.Iteration

/-!
# The energy-density decomposition ([O+] L2582-L2602 and L2666-L2676)

Source: [O+] `L1except`, L2582–L2602 (first half) and the small-`F` decomposition (L2666–L2676):
a finite separated family `𝔓` of multitiles with energy at
most `e₀` and density at most `d₀` is covered by the trees of the stages `𝒯_j`, `j < J`, where the
trees of stage `j` lie in a family `Q_j` of energy at most `e₀ ν^j` and density at most
`d₀ μ^j`, with `∑_{T ∈ 𝒯_j} |I_T| ≲ (e₀ ν^j)^{-2} |F| + (d₀ μ^j)^{-r'} |E|`; with `ν² = 1/2` and
`μ^{r'} = 1/2` this is `≲ 2^j`. The source writes the interleaved halvings (the energy at rate
`2^{-1/2}` and the density at rate `2^{-1/r'}` per index) without proof; the proof
here is that both propositions *halve* their parameter, which is stronger than the rate
`ν, μ ≥ 1/2` required, so stage `j` applies the energy increment with `e = e₀ ν^j` followed by
the density increment with `den = d₀ μ^j` to the family left by stage `j - 1`. The multitiles with
zero coefficient may never be selected; the covering statement is for the multitiles with nonzero
coefficient (`exists_J_coeff_zero`), which are the only ones that contribute to `S^ρ[f]`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

section Stages

/-- **The energy-density decomposition** ([O+] `L1except`: the decomposition for large `F`, first
half, and for small `F`). For `r > 1` there is `K > 0` such that for every `1`- or
`2`-index `ρ` with `m, n ∈ {1, …, 4}`, every profile choice, `f` with `|f| ≤ 1_F`, linearizing data
`L`, set `E`, finite separated family `𝔓` in the square `[-2^M, 2^M]²`, and `ν, μ ∈ [1/2, 1)`,
if `energy(𝔓) ≤ e₀` and `density(𝔓) ≤ d₀` there are `J`, trees `𝒯_j` and families `Q_j ⊆ 𝔓` with
the properties listed in the conclusion. -/
theorem exists_energy_density_stages {r : ℝ} (hr : 1 < r) :
    ∃ K : ℝ, 0 < K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ},
      AdmissibleConstants C₁ C₂ C₃ → ρ.IsStd → ∀ (ch : ProfileChoice) {f : ℝ → ℂ} {F : Set ℝ},
      AEStronglyMeasurable f volume → (∀ᵐ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) →
      ∀ (L : Linearization r) (E : Set ℝ) {𝔓 : Finset (Multitile ρ)},
      Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ)) → (∀ P ∈ 𝔓, P.InSquare M) →
      ∀ {e₀ d₀ ν μ : ℝ}, 0 < e₀ → 0 < d₀ → 1 / 2 ≤ ν → ν < 1 → 1 / 2 ≤ μ → μ < 1 →
      energy C₁ C₂ M ch f (𝔓 : Set (Multitile ρ)) ≤ ENNReal.ofReal e₀ →
      density C₁ C₂ M L E (𝔓 : Set (Multitile ρ)) ≤ ENNReal.ofReal d₀ →
      ∃ (J : ℕ) (𝒯 : ℕ → Finset (MultitileTree ρ)) (Q : ℕ → Finset (Multitile ρ)),
        (∀ j, Q j ⊆ 𝔓 ∧
          energy C₁ C₂ M ch f (Q j : Set (Multitile ρ)) ≤ ENNReal.ofReal (e₀ * ν ^ j) ∧
          density C₁ C₂ M L E (Q j : Set (Multitile ρ)) ≤ ENNReal.ofReal (d₀ * μ ^ j) ∧
          (∀ T ∈ 𝒯 j, T.IsTree C₁ C₂ M ∧ (T.T : Set (Multitile ρ)) ⊆ (Q j : Set (Multitile ρ))) ∧
          ∑ T ∈ 𝒯 j, ENNReal.ofReal T.I.length ≤
            ENNReal.ofReal (K / (e₀ * ν ^ j) ^ 2) * volume F +
              ENNReal.ofReal (K / (d₀ * μ ^ j) ^ Real.conjExponent r) * volume E) ∧
        ∀ P ∈ 𝔓, P.coeff ch f = 0 ∨ ∃ j < J, ∃ T ∈ 𝒯 j, P ∈ T.T := by
  classical
  obtain ⟨KE, hKE0, hKE⟩ := energy_increment
  obtain ⟨KD, hKD0, hKD⟩ := density_increment hr
  refine ⟨max KE KD, lt_max_of_lt_left hKE0, ?_⟩
  intro ρ _ C₁ C₂ C₃ M hC hρ ch f F hfm hfF L E 𝔓 hsep hsq e₀ d₀ ν μ he₀ hd₀ hν hν1 hμ hμ1 hen hde
  have hν0 : 0 < ν := by linarith
  have hμ0 : 0 < μ := by linarith
  set Inv : ℕ → Finset (Multitile ρ) → Prop := fun j Q => Q ⊆ 𝔓 ∧
    energy C₁ C₂ M ch f (Q : Set (Multitile ρ)) ≤ ENNReal.ofReal (e₀ * ν ^ j) ∧
    density C₁ C₂ M L E (Q : Set (Multitile ρ)) ≤ ENNReal.ofReal (d₀ * μ ^ j) with hInv
  set Out : ℕ → Finset (Multitile ρ) → Finset (MultitileTree ρ) → Prop := fun j Q 𝒯 =>
    (∀ T ∈ 𝒯, T.IsTree C₁ C₂ M ∧ (T.T : Set (Multitile ρ)) ⊆ (Q : Set (Multitile ρ))) ∧
    ∑ T ∈ 𝒯, ENNReal.ofReal T.I.length ≤
      ENNReal.ofReal (max KE KD / (e₀ * ν ^ j) ^ 2) * volume F +
        ENNReal.ofReal (max KE KD / (d₀ * μ ^ j) ^ Real.conjExponent r) * volume E with hOut
  have hstep : ∀ j (Q : Finset (Multitile ρ)), Inv j Q → ∃ 𝒯 : Finset (MultitileTree ρ),
      Out j Q 𝒯 ∧ (∀ T ∈ 𝒯, T.T ⊆ Q) ∧ Inv (j + 1) (Q \ 𝒯.biUnion fun T => T.T) := by
    intro j Q ⟨hQ𝔓, hQen, hQde⟩
    have hej : 0 < e₀ * ν ^ j := by positivity
    have hdj : 0 < d₀ * μ ^ j := by positivity
    have hsepQ : Separated C₁ C₂ C₃ (Q : Set (Multitile ρ)) := hsep.mono (by exact_mod_cast hQ𝔓)
    have hsqQ : ∀ P ∈ Q, P.InSquare M := fun P hP => hsq P (hQ𝔓 hP)
    obtain ⟨𝒯E, hE1, hE2, hE3, -, -⟩ := hKE hC hρ ch hfm hfF hej hsepQ hsqQ hQen
    set Q₁ : Finset (Multitile ρ) := Q \ 𝒯E.biUnion fun T => T.T with hQ₁
    have hQ₁c : (Q₁ : Set (Multitile ρ)) =
        (Q : Set (Multitile ρ)) \ ⋃ T ∈ 𝒯E, (T.T : Set (Multitile ρ)) := by
      rw [hQ₁]
      ext P
      simp
    have hsqQ₁ : ∀ P ∈ Q₁, P.InSquare M := fun P hP => hsqQ P (Finset.sdiff_subset hP)
    obtain ⟨𝒯D, hD1, hD2, hD3, -⟩ := hKD hC hρ L E hdj hsqQ₁
    refine ⟨𝒯E ∪ 𝒯D, ⟨?_, ?_⟩, ?_, ?_⟩
    · intro T hT
      rcases Finset.mem_union.1 hT with h | h
      · exact ⟨(hE1 T h).1, (hE1 T h).2.1⟩
      · refine ⟨(hD1 T h).1, (hD1 T h).2.1.trans ?_⟩
        rw [hQ₁c]; exact sdiff_subset
    · refine (sum_union_le_add_ennreal 𝒯E 𝒯D _).trans ?_
      refine add_le_add ?_ ?_
      · refine hE2.trans ?_
        gcongr
        exact le_max_left _ _
      · refine hD2.trans ?_
        gcongr
        exact le_max_right _ _
    · intro T hT P hP
      rcases Finset.mem_union.1 hT with h | h
      · exact (Finset.mem_coe.1 ((hE1 T h).2.1 hP))
      · have := (hD1 T h).2.1 hP
        rw [hQ₁c] at this
        exact Finset.mem_coe.1 this.1
    · have hQ₂c : (((Q \ (𝒯E ∪ 𝒯D).biUnion fun T => T.T : Finset (Multitile ρ)) :
          Set (Multitile ρ)) = (Q₁ : Set (Multitile ρ)) \ ⋃ T ∈ 𝒯D, (T.T : Set (Multitile ρ))) := by
        rw [hQ₁]
        ext P
        simp only [Finset.coe_sdiff, Finset.coe_biUnion, Finset.mem_union, mem_sdiff,
          Finset.mem_coe, mem_iUnion, exists_prop, not_exists, not_and]
        constructor
        · rintro ⟨hP, h⟩
          exact ⟨⟨hP, fun T hT => h T (Or.inl hT)⟩, fun T hT => h T (Or.inr hT)⟩
        · rintro ⟨⟨hP, h1⟩, h2⟩
          exact ⟨hP, fun T hT => hT.elim (h1 T) (h2 T)⟩
      have hQ₂sub : (((Q \ (𝒯E ∪ 𝒯D).biUnion fun T => T.T : Finset (Multitile ρ)) :
          Set (Multitile ρ))) ⊆ (Q₁ : Set (Multitile ρ)) := by
        rw [hQ₂c]; exact sdiff_subset
      refine ⟨Finset.sdiff_subset.trans hQ𝔓, ?_, ?_⟩
      · refine (energyOf_mono C₁ C₂ M _ hQ₂sub).trans ?_
        have h1 : energy C₁ C₂ M ch f (Q₁ : Set (Multitile ρ)) ≤
            ENNReal.ofReal (e₀ * ν ^ j / 2) := by
          rw [hQ₁c]; exact hE3
        refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
        rw [pow_succ]
        have : 0 < e₀ * ν ^ j := hej
        nlinarith
      · rw [hQ₂c]
        refine hD3.trans (ENNReal.ofReal_le_ofReal ?_)
        rw [pow_succ]
        have : 0 < d₀ * μ ^ j := hdj
        nlinarith
  obtain ⟨J, hJ⟩ := exists_J_coeff_zero (C₁ := C₁) (C₂ := C₂) (C₃ := C₃) (M := M) hC hρ ch f 𝔓 hsq
    he₀ hν0 hν1
  obtain ⟨𝒯, Q, hQ0, hall, hcover⟩ := exists_iteration (fun T : MultitileTree ρ => T.T) Inv Out
    hstep 𝔓 ⟨subset_rfl, by simpa using hen, by simpa using hde⟩ {P | P.coeff ch f = 0} J
    (fun Q hQ hInv P hP => hJ Q hQ hInv.2.1 P hP)
  refine ⟨J, 𝒯, Q, fun j => ?_, hcover⟩
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, -, -⟩ := hall j
  exact ⟨h1, h2, h3, h4, h5⟩

end Stages

section BmoStages

/-- **The energy decomposition with the BMO bound** ([O+] `L1except`: the decomposition for large
`F`, second half; L2589-L2602). If `𝔔` is covered by the trees of `𝒯'` and has energy at most `e₀`,
then (for
`C₂ = 2`, as in L1875) there are stages `𝒯_k` of trees in families `Q_k ⊆ 𝔔` of energy at most
`e₀ ν^k`, with the dyadic BMO bound `‖∑_{T ∈ 𝒯_k} 1_{2^ℓ I_T}‖_BMO ≲ 2^{2ℓ} (e₀ ν^k)^{-2}` for every
`ℓ` and the covering bound `∑_{T ∈ 𝒯_k} |I_T| ≲ ∑_{T' ∈ 𝒯'} |I_{T'}|` of (pisatree), which lets the
tree lengths stay at the scale `2^j` of the first decomposition. The covering `𝔔 ⊆ ⋃ 𝒯'` is used
through the restricted trees of the remaining families (restrictions of trees are trees with the
same top interval). -/
theorem exists_energy_bmo_stages :
    ∃ K : ℝ, 0 < K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ},
      AdmissibleConstants C₁ C₂ C₃ → C₂ = 2 → ρ.IsStd → ∀ (ch : ProfileChoice) {f : ℝ → ℂ}
      {F : Set ℝ}, AEStronglyMeasurable f volume →
      (∀ᵐ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) →
      ∀ {𝔔 : Finset (Multitile ρ)}, Separated C₁ C₂ C₃ (𝔔 : Set (Multitile ρ)) →
      (∀ P ∈ 𝔔, P.InSquare M) → ∀ (𝒯' : Finset (MultitileTree ρ)),
      (∀ T ∈ 𝒯', T.IsTree C₁ C₂ M) →
      (𝔔 : Set (Multitile ρ)) ⊆ ⋃ T ∈ 𝒯', (T.T : Set (Multitile ρ)) →
      ∀ {e₀ ν : ℝ}, 0 < e₀ → 1 / 2 ≤ ν → ν < 1 →
      energy C₁ C₂ M ch f (𝔔 : Set (Multitile ρ)) ≤ ENNReal.ofReal e₀ →
      ∃ (J : ℕ) (𝒯 : ℕ → Finset (MultitileTree ρ)) (Q : ℕ → Finset (Multitile ρ)),
        (∀ k, Q k ⊆ 𝔔 ∧
          energy C₁ C₂ M ch f (Q k : Set (Multitile ρ)) ≤ ENNReal.ofReal (e₀ * ν ^ k) ∧
          (∀ T ∈ 𝒯 k, T.IsTree C₁ C₂ M ∧ (T.T : Set (Multitile ρ)) ⊆ (Q k : Set (Multitile ρ))) ∧
          (∀ ℓ : ℕ, dyadicBMO (fun x => ∑ T ∈ 𝒯 k, (T.I.dilate (2 ^ ℓ)).indicator
            (fun _ => (1 : ℝ)) x) ≤ ENNReal.ofReal (K * 2 ^ (2 * ℓ) / (e₀ * ν ^ k) ^ 2)) ∧
          ∑ T ∈ 𝒯 k, ENNReal.ofReal T.I.length ≤
            ENNReal.ofReal K * ∑ T' ∈ 𝒯', ENNReal.ofReal T'.I.length) ∧
        ∀ P ∈ 𝔔, P.coeff ch f = 0 ∨ ∃ k < J, ∃ T ∈ 𝒯 k, P ∈ T.T := by
  classical
  obtain ⟨KE, hKE0, hKE⟩ := energy_increment
  refine ⟨KE, hKE0, ?_⟩
  intro ρ _ C₁ C₂ C₃ M hC hC₂ hρ ch f F hfm hfF 𝔔 hsep hsq 𝒯' h𝒯' hcov e₀ ν he₀ hν hν1 hen
  have hν0 : 0 < ν := by linarith
  set Inv : ℕ → Finset (Multitile ρ) → Prop := fun k Q => Q ⊆ 𝔔 ∧
    energy C₁ C₂ M ch f (Q : Set (Multitile ρ)) ≤ ENNReal.ofReal (e₀ * ν ^ k) with hInv
  set Out : ℕ → Finset (Multitile ρ) → Finset (MultitileTree ρ) → Prop := fun k Q 𝒯 =>
    (∀ T ∈ 𝒯, T.IsTree C₁ C₂ M ∧ (T.T : Set (Multitile ρ)) ⊆ (Q : Set (Multitile ρ))) ∧
    (∀ ℓ : ℕ, dyadicBMO (fun x => ∑ T ∈ 𝒯, (T.I.dilate (2 ^ ℓ)).indicator
      (fun _ => (1 : ℝ)) x) ≤ ENNReal.ofReal (KE * 2 ^ (2 * ℓ) / (e₀ * ν ^ k) ^ 2)) ∧
    ∑ T ∈ 𝒯, ENNReal.ofReal T.I.length ≤
      ENNReal.ofReal KE * ∑ T' ∈ 𝒯', ENNReal.ofReal T'.I.length with hOut
  have hstep : ∀ k (Q : Finset (Multitile ρ)), Inv k Q → ∃ 𝒯 : Finset (MultitileTree ρ),
      Out k Q 𝒯 ∧ (∀ T ∈ 𝒯, T.T ⊆ Q) ∧ Inv (k + 1) (Q \ 𝒯.biUnion fun T => T.T) := by
    intro k Q ⟨hQ𝔔, hQen⟩
    have hek : 0 < e₀ * ν ^ k := by positivity
    have hsepQ : Separated C₁ C₂ C₃ (Q : Set (Multitile ρ)) := hsep.mono (by exact_mod_cast hQ𝔔)
    have hsqQ : ∀ P ∈ Q, P.InSquare M := fun P hP => hsq P (hQ𝔔 hP)
    obtain ⟨𝒯E, hE1, -, hE3, hE4, hE5⟩ := hKE hC hρ ch hfm hfF hek hsepQ hsqQ hQen
    set res : MultitileTree ρ → MultitileTree ρ := fun T' => ⟨T'.T.filter (· ∈ Q), T'.I, T'.ξ⟩
      with hres
    have hQc : (Q : Set (Multitile ρ)) = ⋃ T ∈ 𝒯'.image res, (T.T : Set (Multitile ρ)) := by
      ext P
      simp only [Finset.mem_coe, mem_iUnion, Finset.mem_image, exists_prop]
      constructor
      · intro hP
        obtain ⟨T', hT', hPT'⟩ := mem_iUnion₂.1 (hcov (hQ𝔔 hP))
        exact ⟨res T', ⟨T', hT', rfl⟩, Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hPT', hP⟩)⟩
      · rintro ⟨_, ⟨T', hT', rfl⟩, hP⟩
        exact (Finset.mem_filter.1 hP).2
    have hpisa := hE5 hC₂ (𝒯'.image res) (by
      intro T hT
      obtain ⟨T', hT', rfl⟩ := Finset.mem_image.1 hT
      exact (h𝒯' T' hT').of_subset _ (Finset.filter_subset _ _)) hQc
    refine ⟨𝒯E, ⟨fun T hT => ⟨(hE1 T hT).1, (hE1 T hT).2.1⟩, hE4, ?_⟩, fun T hT => ?_, ?_⟩
    · refine hpisa.trans ?_
      exact mul_le_mul' le_rfl (sum_image_le_sum_comp_ennreal 𝒯' res
        (fun T : MultitileTree ρ => ENNReal.ofReal T.I.length))
    · intro P hP
      exact Finset.mem_coe.1 ((hE1 T hT).2.1 hP)
    · have hc : (((Q \ 𝒯E.biUnion fun T => T.T : Finset (Multitile ρ)) : Set (Multitile ρ))) =
          (Q : Set (Multitile ρ)) \ ⋃ T ∈ 𝒯E, (T.T : Set (Multitile ρ)) := by
        ext P; simp
      refine ⟨Finset.sdiff_subset.trans hQ𝔔, ?_⟩
      rw [hc]
      refine hE3.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [pow_succ]
      nlinarith
  obtain ⟨J, hJ⟩ := exists_J_coeff_zero (C₁ := C₁) (C₂ := C₂) (C₃ := C₃) (M := M) hC hρ ch f 𝔔 hsq
    he₀ hν0 hν1
  obtain ⟨𝒯, Q, hQ0, hall, hcover⟩ := exists_iteration (fun T : MultitileTree ρ => T.T) Inv Out
    hstep 𝔔 ⟨subset_rfl, by simpa using hen⟩ {P | P.coeff ch f = 0} J
    (fun Q hQ hInv P hP => hJ Q hQ hInv.2 P hP)
  refine ⟨J, 𝒯, Q, fun k => ?_, hcover⟩
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4, h5⟩, -, -⟩ := hall k
  exact ⟨h1, h2, h3, h4, h5⟩

end BmoStages

end PrimeCarleson.Proof.Oplus
