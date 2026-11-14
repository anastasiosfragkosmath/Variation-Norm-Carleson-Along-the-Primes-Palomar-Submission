module

public import PrimeCarleson.Proof.Oplus.Conclusion.LargeF

/-!
# The case `|F| > 1` of `L1except` ([O+] L2580-L2650)

Source: [O+] `L1except`, the case of large `F` (L2580–L2650): the decomposition, the choice of
the parameters, the exceptional set, the Hölder step and the summation.

`exists_large_decomposition`: the finite separated family `𝔓` is, up to the multitiles with zero
coefficient, the disjoint union of the sets `R_{j,k,T} ⊆ T`, `T ∈ 𝒯_{j,k}`, where `𝒯_{j,k}`
consists of trees in a family `S_{j,k}` of energy `≤ A |F|^{1/2} 2^{-(j+k)/2}` and density
`≤ A 2^{-j/r'}`, with `∑_{T ∈ 𝒯_{j,k}} |I_T| ≤ c 2^j` and
`‖∑_{T ∈ 𝒯_{j,k}} 1_{2^ℓ I_T}‖_BMO ≤ c 2^{2ℓ} 2^{j+k}/|F|`. The first index comes from the
energy-density decomposition (`exists_energy_density_stages`) with
`e₀ = A |F|^{1/2}` and `d₀ = A` (the universal bounds on density and energy, [O+] L1357-L1363, are
at most `A`, and `|F| > 1`); the second from the energy decomposition with the BMO bound
(`exists_energy_bmo_stages`) applied to the union `𝔔_j` of the trees of stage `j`, which is covered
by the trees of `𝒯_j` (this is where (pisatree) keeps the lengths at the scale `2^j`).

`l1except_large` combines it with `large_summation`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

section LargeCase

/-- A finite family of multitiles lies in some square `[-2^M, 2^M]²`. -/
theorem exists_inSquare_finset {ρ : Idx} (𝔓 : Finset (Multitile ρ)) :
    ∃ M : ℤ, ∀ P ∈ 𝔓, P.InSquare M := by
  choose f hf using fun P : Multitile ρ => P.exists_inSquare
  obtain ⟨M, hM⟩ := (𝔓.finite_toSet.image f).bddAbove
  exact ⟨M, fun P hP => (hf P).mono (hM ⟨P, hP, rfl⟩)⟩

/-- **The decomposition for `|F| > 1`** ([O+] `L1except`, case of large `F`). -/
theorem exists_large_decomposition {r : ℝ} (hr : 2 < r) {C₁ C₂ C₃ : ℝ}
    (hC : AdmissibleConstants C₁ C₂ C₃) (hC₂ : C₂ = 2) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {M : ℤ}, ρ.IsStd →
      ∀ (ch : ProfileChoice) {f : ℝ → ℂ} {F E : Set ℝ}, AEStronglyMeasurable f volume →
      (∀ᵐ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) → volume E ≤ 2 →
      ∀ (L : Linearization r) {Fm : ℝ}, 1 < Fm → volume F = ENNReal.ofReal Fm →
      ∀ (𝔓 : Finset (Multitile ρ)), Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ)) →
      (∀ P ∈ 𝔓, P.InSquare M) →
      ∃ (J K : ℕ) (𝒯 : ℕ → ℕ → Finset (MultitileTree ρ))
        (R : ℕ → ℕ → MultitileTree ρ → Finset (Multitile ρ)) (S : ℕ → ℕ → Set (Multitile ρ)),
      (∀ x, treeSum ch f L E 𝔓 x = ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range K,
        ∑ T ∈ 𝒯 j k, treeSum ch f L E (R j k T) x) ∧
      (∀ j k, ∀ T ∈ 𝒯 j k, R j k T ⊆ T.T ∧ R j k T ⊆ 𝔓 ∧ T.IsTree C₁ C₂ M ∧
        (T.T : Set (Multitile ρ)) ⊆ S j k) ∧
      (∀ j k, energy C₁ C₂ M ch f (S j k) ≤
        ENNReal.ofReal (A * Fm ^ (1 / 2 : ℝ) * nuE ^ (j + k))) ∧
      (∀ j k, density C₁ C₂ M L E (S j k) ≤ ENNReal.ofReal (A * muD r ^ j)) ∧
      (∀ j k, ∑ T ∈ 𝒯 j k, ENNReal.ofReal T.I.length ≤ ENNReal.ofReal (c * 2 ^ j)) ∧
      (∀ j k ℓ : ℕ, dyadicBMO (fun x => ∑ T ∈ 𝒯 j k,
        (T.I.dilate ((2 : ℝ) ^ ℓ)).indicator (fun _ => (1 : ℝ)) x) ≤
        ENNReal.ofReal (c * 2 ^ (2 * ℓ) * 2 ^ (j + k) / Fm)) := by
  classical
  have hr1 : 1 < r := by linarith
  obtain ⟨K₀, hK₀0, hK₀⟩ := exists_univ_den_ene_bound
  obtain ⟨KS, hKS0, hKS⟩ := exists_energy_density_stages hr1
  obtain ⟨KB, hKB0, hKB⟩ := exists_energy_bmo_stages
  set A : ℝ := K₀ + 1 with hAdef
  have hA : 0 < A := by positivity
  set c₁ : ℝ := KS / A ^ 2 + 2 * KS / A ^ Real.conjExponent r with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  set c : ℝ := KB / A ^ 2 + KB * c₁ with hcdef
  have hc : 0 < c := by positivity
  refine ⟨A, c, hA, hc, ?_⟩
  intro ρ _ M hρ ch f F E hfm hfF hE2 L Fm hFm hFvol 𝔓 hsep hsq
  have hFm0 : 0 < Fm := by linarith
  have hf1 : ∀ᵐ x, ‖f x‖ ≤ 1 := hfF.mono fun x hx =>
    hx.trans (by by_cases h : x ∈ F <;> simp [h])
  obtain ⟨hde𝔓, hen𝔓⟩ := hK₀ (M := M) hC hρ ch hfm hf1 hr1 L E (𝔓 : Set (Multitile ρ)) hsep
  set e₀ : ℝ := A * Fm ^ (1 / 2 : ℝ) with he₀def
  have hsqrt1 : 1 ≤ Fm ^ (1 / 2 : ℝ) := Real.one_le_rpow hFm.le (by norm_num)
  have he₀ : 0 < e₀ := by positivity
  have hK₀A : K₀ ≤ A := by linarith
  have hen' : energy C₁ C₂ M ch f (𝔓 : Set (Multitile ρ)) ≤ ENNReal.ofReal e₀ :=
    hen𝔓.trans (ENNReal.ofReal_le_ofReal (by nlinarith))
  have hde' : density C₁ C₂ M L E (𝔓 : Set (Multitile ρ)) ≤ ENNReal.ofReal A :=
    hde𝔓.trans (ENNReal.ofReal_le_ofReal hK₀A)
  obtain ⟨J, 𝒯₁, Q₁, hI1, hcov₁⟩ := hKS hC hρ ch hfm hfF L E hsep hsq he₀ hA one_half_le_nuE
    nuE_lt_one (one_half_le_muD hr1) (muD_lt_one hr1) hen' hde'
  have hI2 : ∀ j, ∃ (Jk : ℕ) (𝒯₂ : ℕ → Finset (MultitileTree ρ))
      (Q₂ : ℕ → Finset (Multitile ρ)),
      (∀ k, Q₂ k ⊆ (𝒯₁ j).biUnion (fun T => T.T) ∧
        energy C₁ C₂ M ch f (Q₂ k : Set (Multitile ρ)) ≤ ENNReal.ofReal (e₀ * nuE ^ j * nuE ^ k) ∧
        (∀ T ∈ 𝒯₂ k, T.IsTree C₁ C₂ M ∧ (T.T : Set (Multitile ρ)) ⊆ (Q₂ k : Set (Multitile ρ))) ∧
        (∀ ℓ : ℕ, dyadicBMO (fun x => ∑ T ∈ 𝒯₂ k, (T.I.dilate (2 ^ ℓ)).indicator
          (fun _ => (1 : ℝ)) x) ≤
            ENNReal.ofReal (KB * 2 ^ (2 * ℓ) / (e₀ * nuE ^ j * nuE ^ k) ^ 2)) ∧
        ∑ T ∈ 𝒯₂ k, ENNReal.ofReal T.I.length ≤
          ENNReal.ofReal KB * ∑ T' ∈ 𝒯₁ j, ENNReal.ofReal T'.I.length) ∧
      ∀ P ∈ (𝒯₁ j).biUnion (fun T => T.T), P.coeff ch f = 0 ∨ ∃ k < Jk, ∃ T ∈ 𝒯₂ k, P ∈ T.T := by
    intro j
    obtain ⟨hQ𝔓, hQen, hQde, hT, hcost⟩ := hI1 j
    set 𝔔 : Finset (Multitile ρ) := (𝒯₁ j).biUnion fun T => T.T with h𝔔
    have h𝔔Q : 𝔔 ⊆ Q₁ j := fun P hP => by
      obtain ⟨T, hT', hPT⟩ := Finset.mem_biUnion.1 hP
      exact Finset.mem_coe.1 ((hT T hT').2 hPT)
    have h𝔔𝔓 : 𝔔 ⊆ 𝔓 := h𝔔Q.trans hQ𝔓
    obtain ⟨J₂, 𝒯₂, Q₂, h2, hcov⟩ := hKB (M := M) hC hC₂ hρ ch hfm hfF (𝔔 := 𝔔)
      (hsep.mono (by exact_mod_cast h𝔔𝔓)) (fun P hP => hsq P (h𝔔𝔓 hP)) (𝒯₁ j)
      (fun T hT' => (hT T hT').1)
      (fun P hP => mem_iUnion₂.2 (by
        obtain ⟨T, hT', hPT⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hP)
        exact ⟨T, hT', Finset.mem_coe.2 hPT⟩))
      (e₀ := e₀ * nuE ^ j) (ν := nuE) (mul_pos he₀ (pow_pos nuE_pos j)) one_half_le_nuE
      nuE_lt_one
      ((energyOf_mono C₁ C₂ M _ (by exact_mod_cast h𝔔Q)).trans hQen)
    exact ⟨J₂, 𝒯₂, Q₂, h2, hcov⟩
  choose Jk 𝒯₂ Q₂ hI2' using hI2
  set Kmax : ℕ := (Finset.range J).sup Jk with hKmax
  have : Nonempty (Σ _ : ℕ × ℕ, MultitileTree ρ) :=
    ⟨⟨(0, 0), MultitileTree.mk ∅ ⟨0, 0⟩ 0⟩⟩
  set s : Finset (Σ _ : ℕ × ℕ, MultitileTree ρ) :=
    (Finset.range J ×ˢ Finset.range Kmax).sigma fun jk => 𝒯₂ jk.1 jk.2 with hs
  set Q : Finset (Multitile ρ) := 𝔓.filter fun P => P.coeff ch f ≠ 0 with hQ
  have hcov : ∀ P ∈ Q, ∃ i ∈ s, P ∈ (fun i : (Σ _ : ℕ × ℕ, MultitileTree ρ) => i.2.T) i := by
    intro P hP
    obtain ⟨hP𝔓, hPc⟩ := Finset.mem_filter.1 hP
    rcases hcov₁ P hP𝔓 with h | ⟨j, hj, T, hT, hPT⟩
    · exact absurd h hPc
    · have hPQ : P ∈ (𝒯₁ j).biUnion fun T => T.T := Finset.mem_biUnion.2 ⟨T, hT, hPT⟩
      rcases (hI2' j).2 P hPQ with h | ⟨k, hk, T', hT', hPT'⟩
      · exact absurd h hPc
      · refine ⟨⟨(j, k), T'⟩, ?_, hPT'⟩
        simp only [hs, Finset.mem_sigma, Finset.mem_product, Finset.mem_range]
        exact ⟨⟨hj, lt_of_lt_of_le hk (Finset.le_sup (f := Jk) (Finset.mem_range.2 hj))⟩, hT'⟩
  obtain ⟨R, hRV, hRQ, hRsum⟩ := exists_assignment.{_, _, 0} s (fun i => i.2.T) Q hcov
  refine ⟨J, Kmax, 𝒯₂, fun j k T => R ⟨(j, k), T⟩, fun j k => (Q₂ j k : Set (Multitile ρ)),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    have h1 : treeSum ch f L E 𝔓 x = ∑ P ∈ Q, P.coeff ch f * P.wavePacket ch x * P.aP L x *
        E.indicator (fun _ => (1 : ℂ)) x := by
      rw [hQ, Finset.sum_filter_of_ne]
      · rfl
      · intro P _ hP hc
        exact hP (by simp [hc])
    rw [h1, hRsum (fun P => P.coeff ch f * P.wavePacket ch x * P.aP L x *
      E.indicator (fun _ => (1 : ℂ)) x), hs, Finset.sum_sigma, Finset.sum_product]
    rfl
  · intro j k T hT
    have hT' := ((hI2' j).1 k).2.2.1 T hT
    exact ⟨hRV ⟨(j, k), T⟩, (hRQ ⟨(j, k), T⟩).trans (Finset.filter_subset _ _), hT'.1, hT'.2⟩
  · intro j k
    refine (((hI2' j).1 k).2.1).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [he₀def, pow_add]; ring
  · intro j k
    have hsub : (Q₂ j k : Set (Multitile ρ)) ⊆ (Q₁ j : Set (Multitile ρ)) := by
      exact_mod_cast (((hI2' j).1 k).1).trans (by
        intro P hP
        obtain ⟨T, hT', hPT⟩ := Finset.mem_biUnion.1 hP
        exact Finset.mem_coe.1 (((hI1 j).2.2.2.1 T hT').2 hPT))
    exact (density_mono C₁ C₂ M L E hsub).trans ((hI1 j).2.2.1)
  · intro j k
    refine (((hI2' j).1 k).2.2.2.2).trans ?_
    have h1 : ∑ T' ∈ 𝒯₁ j, ENNReal.ofReal T'.I.length ≤ ENNReal.ofReal (c₁ * 2 ^ j) := by
      refine ((hI1 j).2.2.2.2).trans ?_
      rw [hFvol]
      exact stage_cost_le hr1 hKS0.le hA hFm0 hE2 j
    refine (mul_le_mul' le_rfl h1).trans ?_
    rw [← ENNReal.ofReal_mul hKB0.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have : 0 ≤ KB / A ^ 2 := by positivity
    have h2 : (0 : ℝ) < 2 ^ j := by positivity
    rw [hcdef]
    nlinarith
  · intro j k ℓ
    refine (((hI2' j).1 k).2.2.2.1 ℓ).trans (ENNReal.ofReal_le_ofReal ?_)
    have hν := nuE_pos
    have e1 : (e₀ * nuE ^ j * nuE ^ k) ^ 2 = A ^ 2 * Fm * ((2 : ℝ) ^ (j + k))⁻¹ := by
      have hF2 : (Fm ^ (1 / 2 : ℝ)) ^ 2 = Fm := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hFm0.le]; norm_num
      have h3 : e₀ * nuE ^ j * nuE ^ k = A * Fm ^ (1 / 2 : ℝ) * nuE ^ (j + k) := by
        rw [he₀def, pow_add]; ring
      rw [h3, mul_pow, mul_pow, hF2, ← pow_mul, mul_comm (j + k) 2, pow_mul, nuE_sq, one_div,
        inv_pow]
    rw [e1]
    have e2 : KB * 2 ^ (2 * ℓ) / (A ^ 2 * Fm * ((2 : ℝ) ^ (j + k))⁻¹) =
        KB / A ^ 2 * 2 ^ (2 * ℓ) * 2 ^ (j + k) / Fm := by
      field_simp
    rw [e2]
    have h2 : 0 ≤ (2 : ℝ) ^ (2 * ℓ) * 2 ^ (j + k) / Fm := by positivity
    have e3 : KB / A ^ 2 * 2 ^ (2 * ℓ) * 2 ^ (j + k) / Fm =
        KB / A ^ 2 * (2 ^ (2 * ℓ) * 2 ^ (j + k) / Fm) := by ring
    have e4 : c * 2 ^ (2 * ℓ) * 2 ^ (j + k) / Fm = c * (2 ^ (2 * ℓ) * 2 ^ (j + k) / Fm) := by ring
    rw [e3, e4]
    refine mul_le_mul_of_nonneg_right ?_ h2
    rw [hcdef]
    have : 0 ≤ KB * c₁ := by positivity
    linarith

/-- **The case `|F| > 1` of `L1except`** ([O+] L2580-L2650): for `r > 2`, `1/p > 1/2 - 1/r` and
`C₂ = 2` there are an absolute `C` and, for every finite separated family `𝔓` of multitiles, a
measurable set `G` with `|G| ≤ 1/4` and `∫_{ℝ ∖ G} |1_E ∑_{P ∈ 𝔓} ⟨f, φ_P⟩ φ_P a_P| ≤ C |F|^{1/p}`
(for `|E| ≤ 2`, `|f| ≤ 1_F`). -/
theorem l1except_large {r p : ℝ} (hr : 2 < r) (hp : 1 / 2 - 1 / r < 1 / p) {C₁ C₂ C₃ : ℝ}
    (hC : AdmissibleConstants C₁ C₂ C₃) (hC₂ : C₂ = 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo], ρ.IsStd → ∀ (ch : ProfileChoice)
      {f : ℝ → ℂ} {F E : Set ℝ}, AEStronglyMeasurable f volume →
      (∀ᵐ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) → MeasurableSet E → volume E ≤ 2 →
      ∀ (L : Linearization r) {Fm : ℝ}, 1 < Fm → volume F = ENNReal.ofReal Fm →
      ∀ (𝔓 : Finset (Multitile ρ)), Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ)) →
      ∃ G : Set ℝ, MeasurableSet G ∧ volume G ≤ 1 / 4 ∧
        ∫⁻ x in Gᶜ, ‖treeSum ch f L E 𝔓 x‖ₑ ≤ ENNReal.ofReal (C * Fm ^ (1 / p)) := by
  obtain ⟨A, c, hA, hc, hdec⟩ := exists_large_decomposition hr hC hC₂
  obtain ⟨C, hC0, hsum⟩ := large_summation hr hp hC hA hc
  refine ⟨C, hC0, ?_⟩
  intro ρ _ hρ ch f F E hfm hfF hE hE2 L Fm hFm hFvol 𝔓 hsep
  obtain ⟨M, hsq⟩ := exists_inSquare_finset 𝔓
  obtain ⟨J, K, 𝒯, R, S, h1, h2, h3, h4, h5, h6⟩ :=
    hdec (M := M) hρ ch hfm hfF hE2 L hFm hFvol 𝔓 hsep hsq
  exact hsum hρ ch f hE hE2 L hFm 𝔓 hsep hsq J K 𝒯 R S h1 h2 h3 h4 h5 h6

end LargeCase

end PrimeCarleson.Proof.Oplus
