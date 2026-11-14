module

public import PrimeCarleson.Proof.Oplus.EnergyIncrement.BmoMain
public import PrimeCarleson.Proof.Oplus.EnergyIncrement.FarBessel

/-!
# The error terms of `bmosummeasures` ([O+] L1740-L1795)

Source: [O+], L1741–L1743; [O+], L1779–L1785 (L1740-L1795): "For each `T ∈ 𝒯^j` and `P ∈ S(T)` we
have `|I| ≤ 2^{-j}|I_T| ≤ 2^{-j}|J|`. Thus
`∑_{T ∈ 𝒯^j} |I_T| ≲ ∑_{T ∈ 𝒯^j} 2^j e^{-2} ∑_{P ∈ S(T) : |I| ≤ 2^{-j}|J|} |⟨f'', φ_P⟩|²`. Since the
`S` are pairwise disjoint, the right hand side is
`≲ 2^j e^{-2} ∑_{k ≥ j} ∑_{P : |I| = 2^{-k}|J|, I ⊂ 2^{ℓ+1}J} |⟨f'', φ_P⟩|²`" and the bound of the
last sums by `sumafterorth` (`FarBessel.lean`: `sumafterorth_aux` is the printed (sumafterorth),
`exists_sum_norm_sq_coeff_le_far` its consequence for `|f''| ≤ 1`).

`𝒯^d` is `HasLargeSubtree` at `d` (`BmoSetup.lean`); the subtree `S'` realizing it has
`|I_{S'}| = 2^{-d}|I_T|` and `(e²/16)|I_{S'}| ≤ ∑_{P ∈ S'} |⟨f'', φ_P⟩|²`, so
`|I_T| = 2^d |I_{S'}| ≤
(16/e²) 2^d ∑_{P ∈ S'} |⟨f'', φ_P⟩|²` with `S' ⊂ S(T)`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- A geometric tail: for a finite set `t` of exponents `≥ d`, `∑_{k ∈ t} (1/8)^k ≤ 2 (1/8)^d`. -/
theorem sum_one_eighth_pow_le (t : Finset ℕ) {d : ℕ} (ht : ∀ k ∈ t, d ≤ k) :
    ∑ k ∈ t, (1 / 8 : ℝ) ^ k ≤ 2 * (1 / 8 : ℝ) ^ d := by
  set N : ℕ := t.sup id + 1 with hN
  have hsub : t ⊆ Finset.Ico d N := by
    intro k hk
    rw [Finset.mem_Ico]
    exact ⟨ht k hk, Nat.lt_succ_of_le (Finset.le_sup (f := id) hk)⟩
  calc ∑ k ∈ t, (1 / 8 : ℝ) ^ k ≤ ∑ k ∈ Finset.Ico d N, (1 / 8 : ℝ) ^ k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => by positivity
    _ = ∑ i ∈ Finset.range (N - d), (1 / 8 : ℝ) ^ (d + i) := Finset.sum_Ico_eq_sum_range _ _ _
    _ = (1 / 8 : ℝ) ^ d * ∑ i ∈ Finset.range (N - d), (1 / 8 : ℝ) ^ i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [pow_add]
    _ ≤ (1 / 8 : ℝ) ^ d * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine le_trans (Finset.sum_le_sum fun i _ => ?_) (sum_geometric_two_le (N - d))
        exact pow_le_pow_left₀ (by positivity) (by norm_num : (1 / 8 : ℝ) ≤ 1 / 2) i
    _ = 2 * (1 / 8 : ℝ) ^ d := by ring


/-- `|J|/2^d = 2^{k_J - d}`. -/
theorem Dyadic.length_div_pow (J : Dyadic) (d : ℕ) :
    J.length / 2 ^ d = (2 : ℝ) ^ (J.k - d) := by
  unfold Dyadic.length
  rw [zpow_sub₀ (by norm_num), zpow_natCast]

open Classical in
/-- **The tail of the far sums**: if every `k`-fiber of multitiles `P` with `|I| = |J|/2^k`,
`I ⊂ 2^{ℓ+1}J` satisfies `∑_P |c_P|² ≤ K_f (|J|/2^k) 4^{-(k+ℓ)}`, then
`∑_{P ∈ 𝔓 : I ⊂ 2^{ℓ+1}J, |I| ≤ |J|/2^d} |c_P|² ≤ 2 K_f |J| 4^{-ℓ} 8^{-d}`. -/
theorem sum_norm_sq_le_tail {ρ : Idx} {ch : ProfileChoice} {g : ℝ → ℂ} {J : Dyadic} {ℓ : ℕ}
    {Kf : ℝ} (hKf0 : 0 ≤ Kf)
    (hKf : ∀ (k : ℕ) (Q : Finset (Multitile ρ)),
      (∀ P ∈ Q, P.I.length = J.length / 2 ^ k ∧ P.I.toSet ⊆ J.dilate (2 ^ (ℓ + 1))) →
      ∑ P ∈ Q, ‖P.coeff ch g‖ ^ 2 ≤ Kf * (J.length / 2 ^ k) * (1 / 4) ^ (k + ℓ))
    (𝔓 : Finset (Multitile ρ)) (d : ℕ) :
    ∑ P ∈ 𝔓.filter (fun P => P.I.toSet ⊆ J.dilate (2 ^ (ℓ + 1)) ∧
        P.I.length ≤ J.length / 2 ^ d), ‖P.coeff ch g‖ ^ 2 ≤
      2 * Kf * J.length * (1 / 4) ^ ℓ * (1 / 8) ^ d := by
  set V := 𝔓.filter (fun P => P.I.toSet ⊆ J.dilate (2 ^ (ℓ + 1)) ∧
    P.I.length ≤ J.length / 2 ^ d) with hV
  set kf : Multitile ρ → ℕ := fun P => (J.k - P.I.k).toNat with hkf
  have hfacts : ∀ P ∈ V, d ≤ kf P ∧ P.I.k = J.k - kf P := by
    intro P hP
    have h := (Finset.mem_filter.1 hP).2.2
    rw [Dyadic.length_div_pow] at h
    have h2 : P.I.k ≤ J.k - d := by
      have : (2 : ℝ) ^ P.I.k ≤ (2 : ℝ) ^ (J.k - d) := h
      exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 this
    refine ⟨by simp only [hkf]; omega, by simp only [hkf]; omega⟩
  have hfiber : ∀ k ∈ V.image kf, ∑ P ∈ V.filter (fun P => kf P = k), ‖P.coeff ch g‖ ^ 2 ≤
      Kf * J.length * (1 / 4) ^ ℓ * (1 / 8) ^ k := by
    intro k hk
    obtain ⟨P₀, hP₀, rfl⟩ := Finset.mem_image.1 hk
    refine (hKf (kf P₀) (V.filter (fun P => kf P = kf P₀)) fun P hP => ?_).trans ?_
    · have h1 := Finset.mem_filter.1 hP
      obtain ⟨-, hk'⟩ := hfacts P h1.1
      refine ⟨?_, (Finset.mem_filter.1 h1.1).2.1⟩
      rw [Dyadic.length_div_pow, ← h1.2]
      unfold Dyadic.length; rw [hk']
    · have : Kf * (J.length / 2 ^ kf P₀) * (1 / 4 : ℝ) ^ (kf P₀ + ℓ) =
          Kf * J.length * (1 / 4) ^ ℓ * (1 / 8) ^ kf P₀ := by
        have e8 : (1 / 8 : ℝ) ^ kf P₀ = (1 / 2) ^ kf P₀ * (1 / 4) ^ kf P₀ := by
          rw [← mul_pow]; norm_num
        have h2 : J.length / 2 ^ kf P₀ = J.length * (1 / 2) ^ kf P₀ := by
          rw [one_div, inv_pow, div_eq_mul_inv]
        rw [h2, e8, pow_add]; ring
      rw [this]
  have hmaps : ∀ P ∈ V, kf P ∈ V.image kf := fun P hP => Finset.mem_image_of_mem _ hP
  calc ∑ P ∈ V, ‖P.coeff ch g‖ ^ 2
      = ∑ k ∈ V.image kf, ∑ P ∈ V.filter (fun P => kf P = k), ‖P.coeff ch g‖ ^ 2 :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ k ∈ V.image kf, Kf * J.length * (1 / 4) ^ ℓ * (1 / 8) ^ k := Finset.sum_le_sum hfiber
    _ = Kf * J.length * (1 / 4) ^ ℓ * ∑ k ∈ V.image kf, (1 / 8 : ℝ) ^ k := by
        rw [Finset.mul_sum]
    _ ≤ Kf * J.length * (1 / 4) ^ ℓ * (2 * (1 / 8) ^ d) := by
        refine mul_le_mul_of_nonneg_left (sum_one_eighth_pow_le _ fun k hk => ?_) (by
          have := J.length_pos; positivity)
        obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hk
        exact (hfacts P hP).1
    _ = 2 * Kf * J.length * (1 / 4) ^ ℓ * (1 / 8) ^ d := by ring

section Error

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ : ℝ} {M : ℤ} {ch : ProfileChoice} {f : ℝ → ℂ}
  {e : ℝ} {𝔓 : Finset (Multitile ρ)} {n : ℕ} {S T : ℕ → MultitileTree ρ}

open Classical in
/-- **`sumTj`** ([O+] L1741-L1795): for every `d ≥ 0`,
`∑_{T ∈ 𝒯^d} |I_T| ≤ K e^{-2} 2^{-ℓ-d} |J|` (`𝒯^d`: the `j` with `T_j ∈ 𝒯̃` such that `S_j` has an
`l`-overlapping subtree `S'`, `|I_{S'}| = 2^{-d}|I_{S_j}|`, with `(1/|I_{S'}|) ∑_{P ∈ S'}
|⟨f'', φ_P⟩|² ≥ e²/16`, `f'' = 1_{ℝ ∖ 2^{ℓ+5}J} f`). -/
theorem sumTj : ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ : ℝ} {M : ℤ}
    (ch : ProfileChoice) {f : ℝ → ℂ}, AEStronglyMeasurable f volume → (∀ᵐ x, ‖f x‖ ≤ 1) →
    ∀ {e : ℝ}, 0 < e → ∀ {𝔓 : Finset (Multitile ρ)} {n : ℕ} {S T : ℕ → MultitileTree ρ},
    IsSelection C₁ C₂ M ch f e 𝔓 n S T → ∀ (J : Dyadic) (ℓ d : ℕ),
      ∑ j ∈ (Finset.range n).filter (fun j => InTilde S J ℓ j ∧
          HasLargeSubtree C₁ C₂ M ch ((J.dilate (2 ^ (ℓ + 5)))ᶜ.indicator f) (e ^ 2 / 16) (S j) d),
        (S j).I.length ≤ K / e ^ 2 * ((1 / 2) ^ (ℓ + d) * J.length) := by
  obtain ⟨Kf, hKf0, hKf⟩ := exists_sum_norm_sq_coeff_le_far
  refine ⟨32 * Kf, by positivity, fun {ρ} _ {C₁ C₂} {M} ch {f} hfm hf1 {e} he {𝔓} {n} {S} {T} sel
    J ℓ d => ?_⟩
  set D : Set ℝ := J.dilate (2 ^ (ℓ + 5)) with hDdef
  have hD : MeasurableSet D := J.measurableSet_dilate _
  set g'' : ℝ → ℂ := Dᶜ.indicator f with hg''
  have hg''m : AEStronglyMeasurable g'' volume := hfm.indicator hD.compl
  have hg''b : ∀ᵐ x, ‖g'' x‖ ≤ 1 := by
    filter_upwards [hf1] with x hx
    by_cases h : x ∈ D
    · simp [hg'', h]
    · simpa [hg'', h] using hx
  have hg''0 : ∀ x ∈ D, g'' x = 0 := fun x hx => by simp [hg'', hx]
  set TD := (Finset.range n).filter (fun j => InTilde S J ℓ j ∧
      HasLargeSubtree C₁ C₂ M ch g'' (e ^ 2 / 16) (S j) d) with hTD
  have : Nonempty (MultitileTree ρ) := ⟨⟨∅, ⟨0, 0⟩, 0⟩⟩
  have hex : ∀ j ∈ TD, ∃ S' : MultitileTree ρ, S'.IsTree C₁ C₂ M ∧ S'.IsOverlapping C₂ ∧
      (S'.T : Set (Multitile ρ)) ⊆ (S j).T ∧ S'.I.length = (S j).I.length / 2 ^ d ∧
      e ^ 2 / 16 * S'.I.length ≤ ∑ P ∈ S'.T, ‖P.coeff ch g''‖ ^ 2 :=
    fun j hj => (Finset.mem_filter.1 hj).2.2
  choose! S' hS'tree hS'ov hS'sub hS'len hS'large using hex
  have he2 : 0 < e ^ 2 := by positivity
  -- the bound for one tree
  have hper : ∀ j ∈ TD, (S j).I.length ≤
      16 / e ^ 2 * 2 ^ d * ∑ P ∈ (S' j).T, ‖P.coeff ch g''‖ ^ 2 := by
    intro j hj
    have h1 := hS'large j hj
    have h2 := hS'len j hj
    have h3 : (S j).I.length = 2 ^ d * (S' j).I.length := by
      rw [h2]; field_simp
    rw [h3]
    have : (S' j).I.length ≤ 16 / e ^ 2 * ∑ P ∈ (S' j).T, ‖P.coeff ch g''‖ ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ he2]; nlinarith
    calc 2 ^ d * (S' j).I.length ≤ 2 ^ d * (16 / e ^ 2 * ∑ P ∈ (S' j).T, ‖P.coeff ch g''‖ ^ 2) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  -- the multitiles of the trees `S'_j` lie in `V`
  set V := 𝔓.filter (fun P => P.I.toSet ⊆ J.dilate (2 ^ (ℓ + 1)) ∧
    P.I.length ≤ J.length / 2 ^ d) with hV
  have hdisj : (↑TD : Set ℕ).PairwiseDisjoint (fun j => (S' j).T) := by
    intro j hj k hk hne
    have hjTD : j ∈ TD := Finset.mem_coe.1 hj
    have hkTD : k ∈ TD := Finset.mem_coe.1 hk
    have hjn : j < n := Finset.mem_range.1 (Finset.mem_filter.1 hjTD).1
    have hkn : k < n := Finset.mem_range.1 (Finset.mem_filter.1 hkTD).1
    refine Finset.disjoint_left.2 fun P hPj hPk => ?_
    exact Finset.disjoint_left.1 (sel.disjoint_S_S hjn hkn hne)
      (Finset.mem_coe.1 (hS'sub j hjTD (Finset.mem_coe.2 hPj)))
      (Finset.mem_coe.1 (hS'sub k hkTD (Finset.mem_coe.2 hPk)))
  have hsubV : TD.biUnion (fun j => (S' j).T) ⊆ V := by
    intro P hP
    obtain ⟨j, hjTD, hPj⟩ := Finset.mem_biUnion.1 hP
    have hjn : j < n := Finset.mem_range.1 (Finset.mem_filter.1 hjTD).1
    have hjT : InTilde S J ℓ j := (Finset.mem_filter.1 hjTD).2.1
    have hPS : P ∈ (S j).T := Finset.mem_coe.1 (hS'sub j hjTD (Finset.mem_coe.2 hPj))
    refine Finset.mem_filter.2 ⟨sel.mem_of_mem_S hjn hPS, ?_, ?_⟩
    · exact ((sel.S_isTree hjn).time P hPS).trans hjT.1
    · have h1 : P.I.toSet ⊆ (S' j).I.toSet := (hS'tree j hjTD).time P hPj
      have h2 : P.I.length ≤ (S' j).I.length :=
        Dyadic.length_le_iff.2 (Dyadic.k_le_of_toSet_subset h1)
      rw [hS'len j hjTD] at h2
      exact h2.trans (div_le_div_of_nonneg_right hjT.2 (by positivity))
  have hJ0 := J.length_pos
  calc ∑ j ∈ TD, (S j).I.length
      ≤ ∑ j ∈ TD, 16 / e ^ 2 * 2 ^ d * ∑ P ∈ (S' j).T, ‖P.coeff ch g''‖ ^ 2 :=
        Finset.sum_le_sum hper
    _ = 16 / e ^ 2 * 2 ^ d * ∑ P ∈ TD.biUnion (fun j => (S' j).T), ‖P.coeff ch g''‖ ^ 2 := by
        rw [Finset.sum_biUnion hdisj, Finset.mul_sum]
    _ ≤ 16 / e ^ 2 * 2 ^ d * ∑ P ∈ V, ‖P.coeff ch g''‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsubV fun _ _ _ => by
          positivity) (by positivity)
    _ ≤ 16 / e ^ 2 * 2 ^ d * (2 * Kf * J.length * (1 / 4) ^ ℓ * (1 / 8) ^ d) :=
        mul_le_mul_of_nonneg_left (sum_norm_sq_le_tail hKf0
          (fun k Q hQ => hKf ch J ℓ k Q hQ hg''m hg''b hg''0) 𝔓 d) (by positivity)
    _ = 32 * Kf / e ^ 2 * (J.length * (1 / 4) ^ (ℓ + d)) := by
        have e1 : (2 : ℝ) ^ d * (1 / 8) ^ d = (1 / 4) ^ d := by
          rw [← mul_pow]; norm_num
        rw [pow_add]
        field_simp
        rw [← e1]; ring
    _ ≤ 32 * Kf / e ^ 2 * ((1 / 2) ^ (ℓ + d) * J.length) := by
        have : (1 / 4 : ℝ) ^ (ℓ + d) ≤ (1 / 2) ^ (ℓ + d) :=
          pow_le_pow_left₀ (by norm_num) (by norm_num) _
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc J.length * (1 / 4 : ℝ) ^ (ℓ + d) ≤ J.length * (1 / 2) ^ (ℓ + d) :=
              mul_le_mul_of_nonneg_left this hJ0.le
          _ = (1 / 2) ^ (ℓ + d) * J.length := mul_comm _ _

open Classical in
/-- **`bmosummeasures`** ([O+] L1657-L1795): for every dyadic `J` and `ℓ ≥ 0`,
`∑_{T ∈ 𝒯 : J ∩ 2^ℓ I_T ≠ ∅, J ⊄ 2^ℓ I_T} |I_T| ≤ K e^{-2} 2^ℓ |J|`. -/
theorem bmosummeasures : ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ},
    AdmissibleConstants C₁ C₂ C₃ → ρ.IsStd → ∀ (ch : ProfileChoice) {f : ℝ → ℂ} {F : Set ℝ},
    AEStronglyMeasurable f volume → (∀ᵐ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) →
    ∀ {e : ℝ}, 0 < e → ∀ {𝔓 : Finset (Multitile ρ)},
    Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ)) → (∀ P ∈ 𝔓, P.InSquare M) →
    energy C₁ C₂ M ch f (𝔓 : Set (Multitile ρ)) ≤ ENNReal.ofReal e →
    ∀ {n : ℕ} {S T : ℕ → MultitileTree ρ}, IsSelection C₁ C₂ M ch f e 𝔓 n S T →
    ∀ (J : Dyadic) (ℓ : ℕ),
      ∑ j ∈ (Finset.range n).filter (fun j => ((T j).I.dilate (2 ^ ℓ) ∩ J.toSet).Nonempty ∧
          ¬ J.toSet ⊆ (T j).I.dilate (2 ^ ℓ)), (T j).I.length ≤ K / e ^ 2 * (2 ^ ℓ * J.length) := by
  obtain ⟨Km, hKm0, hKm⟩ := sumITinTprime
  obtain ⟨Kj, hKj0, hKj⟩ := sumTj
  refine ⟨Km + 2 * Kj, by positivity, fun {ρ} _ {C₁ C₂ C₃} {M} hC hρ ch {f} {F} hfm hfF {e} he {𝔓}
    hsep hsq hen {n} {S} {T} sel J ℓ => ?_⟩
  have hf1 : ∀ᵐ x, ‖f x‖ ≤ 1 := by
    filter_upwards [hfF] with x hx
    exact hx.trans (Set.indicator_le_self' (fun _ _ => zero_le_one) x |>.trans le_rfl)
  have he2 : 0 < e ^ 2 := by positivity
  have hJ0 := J.length_pos
  set g'' : ℝ → ℂ := (J.dilate (2 ^ (ℓ + 5)))ᶜ.indicator f with hg''
  set Pm : ℕ → Prop := fun j => ∀ d : ℕ,
    ¬ HasLargeSubtree C₁ C₂ M ch g'' (e ^ 2 / 16) (S j) d with hPm
  set Tt := (Finset.range n).filter (InTilde S J ℓ) with hTt
  -- (1) the trees of the sum lie in `𝒯̃`
  have hsub : (Finset.range n).filter (fun j => ((T j).I.dilate (2 ^ ℓ) ∩ J.toSet).Nonempty ∧
      ¬ J.toSet ⊆ (T j).I.dilate (2 ^ ℓ)) ⊆ Tt := by
    intro j hj
    obtain ⟨hjn, h1, h2⟩ := Finset.mem_filter.1 hj
    have hTI := sel.T_I (Finset.mem_range.1 hjn)
    rw [hTI] at h1 h2
    obtain ⟨hl, hs⟩ := Dyadic.length_le_and_subset_dilate (S j).I J ℓ h1 h2
    exact Finset.mem_filter.2 ⟨hjn, hs, hl⟩
  have hTS : ∀ j ∈ Finset.range n, (T j).I.length = (S j).I.length := fun j hj => by
    rw [sel.T_I (Finset.mem_range.1 hj)]
  have hx0 : ∀ j ∈ Tt, 0 ≤ (S j).I.length := fun j _ => (S j).I.length_pos.le
  have hstep1 : ∑ j ∈ (Finset.range n).filter (fun j =>
        ((T j).I.dilate (2 ^ ℓ) ∩ J.toSet).Nonempty ∧ ¬ J.toSet ⊆ (T j).I.dilate (2 ^ ℓ)),
      (T j).I.length ≤ ∑ j ∈ Tt, (S j).I.length := by
    calc _ = ∑ j ∈ (Finset.range n).filter (fun j =>
            ((T j).I.dilate (2 ^ ℓ) ∩ J.toSet).Nonempty ∧ ¬ J.toSet ⊆ (T j).I.dilate (2 ^ ℓ)),
          (S j).I.length :=
          Finset.sum_congr rfl fun j hj => hTS j (Finset.mem_filter.1 hj).1
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun j hj _ => (S j).I.length_pos.le
  -- (2) the main term and the error terms
  have hmain := hKm hC hρ ch hfm hfF he hsep hsq hen sel J ℓ
  have hsplit : ∑ j ∈ Tt, (S j).I.length = ∑ j ∈ Tt.filter Pm, (S j).I.length +
      ∑ j ∈ Tt.filter (fun j => ¬ Pm j), (S j).I.length :=
    (Finset.sum_filter_add_sum_filter_not Tt Pm _).symm
  have hmain' : ∑ j ∈ Tt.filter Pm, (S j).I.length ≤ Km / e ^ 2 * (2 ^ ℓ * J.length) := by
    have : Tt.filter Pm = (Finset.range n).filter (fun j => InTilde S J ℓ j ∧ ∀ d : ℕ,
        ¬ HasLargeSubtree C₁ C₂ M ch ((J.dilate (2 ^ (ℓ + 5)))ᶜ.indicator f) (e ^ 2 / 16)
          (S j) d) := by
      rw [hTt, Finset.filter_filter]
    rw [this]; exact hmain
  -- the range of `d`
  set Dmax : ℕ := 𝔓.sup (fun P => (J.k - P.I.k).toNat) + 1 with hDmax
  have hdlt : ∀ j ∈ Tt.filter (fun j => ¬ Pm j), ∃ d < Dmax,
      HasLargeSubtree C₁ C₂ M ch g'' (e ^ 2 / 16) (S j) d := by
    intro j hj
    obtain ⟨hjTt, hnP⟩ := Finset.mem_filter.1 hj
    have hjn : j < n := Finset.mem_range.1 (Finset.mem_filter.1 hjTt).1
    have hjT : InTilde S J ℓ j := (Finset.mem_filter.1 hjTt).2
    rw [hPm] at hnP
    simp only [not_forall, not_not] at hnP
    obtain ⟨d, S', hS'tree, hS'ov, hS'sub, hS'len, hS'large⟩ := hnP
    refine ⟨d, ?_, ⟨S', hS'tree, hS'ov, hS'sub, hS'len, hS'large⟩⟩
    have hne : S'.T.Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      rw [hcon, Finset.sum_empty] at hS'large
      have := S'.I.length_pos
      nlinarith [mul_pos (by positivity : 0 < e ^ 2 / 16) this]
    obtain ⟨P, hP⟩ := hne
    have hPS : P ∈ (S j).T := Finset.mem_coe.1 (hS'sub (Finset.mem_coe.2 hP))
    have h1 : P.I.toSet ⊆ S'.I.toSet := hS'tree.time P hP
    have h2 : P.I.length ≤ S'.I.length := Dyadic.length_le_iff.2 (Dyadic.k_le_of_toSet_subset h1)
    rw [hS'len] at h2
    have h3 : P.I.length ≤ J.length / 2 ^ d :=
      h2.trans (div_le_div_of_nonneg_right hjT.2 (by positivity))
    rw [Dyadic.length_div_pow] at h3
    have h4 : P.I.k ≤ J.k - d := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 h3
    have h5 : (J.k - P.I.k).toNat ≤ 𝔓.sup (fun P => (J.k - P.I.k).toNat) :=
      Finset.le_sup (f := fun P => (J.k - P.I.k).toNat) (sel.mem_of_mem_S hjn hPS)
    omega
  -- (3) the sum over the error trees
  set TD : ℕ → Finset ℕ := fun d => (Finset.range n).filter (fun j => InTilde S J ℓ j ∧
    HasLargeSubtree C₁ C₂ M ch g'' (e ^ 2 / 16) (S j) d) with hTD
  have herr : ∑ j ∈ Tt.filter (fun j => ¬ Pm j), (S j).I.length ≤
      ∑ d ∈ Finset.range Dmax, ∑ j ∈ TD d, (S j).I.length := by
    set E := Tt.filter (fun j => ¬ Pm j) with hE
    have h1 : ∑ j ∈ E, (S j).I.length ≤ ∑ d ∈ Finset.range Dmax, ∑ j ∈ E.filter
        (fun j => HasLargeSubtree C₁ C₂ M ch g'' (e ^ 2 / 16) (S j) d), (S j).I.length := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum fun j hj => ?_
      obtain ⟨d, hd, hdj⟩ := hdlt j hj
      have := Finset.single_le_sum (f := fun d => if HasLargeSubtree C₁ C₂ M ch g'' (e ^ 2 / 16)
        (S j) d then (S j).I.length else 0) (s := Finset.range Dmax)
        (fun d _ => by split_ifs <;> simp [(S j).I.length_pos.le]) (Finset.mem_range.2 hd)
      simpa [hdj] using this
    refine h1.trans (Finset.sum_le_sum fun d _ => ?_)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun j _ _ => (S j).I.length_pos.le
    intro j hj
    obtain ⟨hjE, hdj⟩ := Finset.mem_filter.1 hj
    obtain ⟨hjTt, -⟩ := Finset.mem_filter.1 hjE
    obtain ⟨hjn, hjT⟩ := Finset.mem_filter.1 hjTt
    exact Finset.mem_filter.2 ⟨hjn, hjT, hdj⟩
  have herr2 : ∑ d ∈ Finset.range Dmax, ∑ j ∈ TD d, (S j).I.length ≤
      2 * Kj / e ^ 2 * ((1 / 2) ^ ℓ * J.length) := by
    calc ∑ d ∈ Finset.range Dmax, ∑ j ∈ TD d, (S j).I.length
        ≤ ∑ d ∈ Finset.range Dmax, Kj / e ^ 2 * ((1 / 2) ^ (ℓ + d) * J.length) :=
          Finset.sum_le_sum fun d _ => hKj ch hfm hf1 he sel J ℓ d
      _ = Kj / e ^ 2 * ((1 / 2) ^ ℓ * J.length) *
            ∑ d ∈ Finset.range Dmax, (1 / 2 : ℝ) ^ d := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [pow_add]; ring
      _ ≤ Kj / e ^ 2 * ((1 / 2) ^ ℓ * J.length) * 2 :=
          mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (by positivity)
      _ = 2 * Kj / e ^ 2 * ((1 / 2) ^ ℓ * J.length) := by ring
  -- (4) conclusion
  have hpow : (1 / 2 : ℝ) ^ ℓ ≤ 2 ^ ℓ := by
    calc (1 / 2 : ℝ) ^ ℓ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      _ ≤ 2 ^ ℓ := one_le_pow₀ (by norm_num)
  calc _ ≤ ∑ j ∈ Tt, (S j).I.length := hstep1
    _ ≤ Km / e ^ 2 * (2 ^ ℓ * J.length) + 2 * Kj / e ^ 2 * ((1 / 2) ^ ℓ * J.length) := by
        rw [hsplit]; exact add_le_add hmain' (herr.trans herr2)
    _ ≤ Km / e ^ 2 * (2 ^ ℓ * J.length) + 2 * Kj / e ^ 2 * (2 ^ ℓ * J.length) := by
        gcongr
    _ = (Km + 2 * Kj) / e ^ 2 * (2 ^ ℓ * J.length) := by ring

open Classical in
/-- **`etreebmobound`** ([O+] L1435-L1437, L1648-L1661): for every `ℓ ≥ 0`,
`‖∑_{j < n} 1_{2^ℓ I_{T_j}}‖_{BMO} ≤ K 2^{2ℓ} e^{-2}` (the dyadic BMO norm, `dyadicBMO`). -/
theorem etreebmobound : ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ},
    AdmissibleConstants C₁ C₂ C₃ → ρ.IsStd → ∀ (ch : ProfileChoice) {f : ℝ → ℂ} {F : Set ℝ},
    AEStronglyMeasurable f volume → (∀ᵐ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) →
    ∀ {e : ℝ}, 0 < e → ∀ {𝔓 : Finset (Multitile ρ)},
    Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ)) → (∀ P ∈ 𝔓, P.InSquare M) →
    energy C₁ C₂ M ch f (𝔓 : Set (Multitile ρ)) ≤ ENNReal.ofReal e →
    ∀ {n : ℕ} {S T : ℕ → MultitileTree ρ}, IsSelection C₁ C₂ M ch f e 𝔓 n S T → ∀ (ℓ : ℕ),
      dyadicBMO (fun x => ∑ j ∈ Finset.range n,
        ((T j).I.dilate (2 ^ ℓ)).indicator (fun _ => (1 : ℝ)) x) ≤
        ENNReal.ofReal (K * 2 ^ (2 * ℓ) / e ^ 2) := by
  obtain ⟨K, hK0, hK⟩ := bmosummeasures
  refine ⟨2 * K, by positivity, fun {ρ} _ {C₁ C₂ C₃} {M} hC hρ ch {f} {F} hfm hfF {e} he {𝔓}
    hsep hsq hen {n} {S} {T} sel ℓ => ?_⟩
  have h := dyadicBMO_sum_dilate_indicator_le (Finset.range n) (fun j => (T j).I) ℓ
    (A := K / e ^ 2 * 2 ^ ℓ) (fun J => by
      have := hK hC hρ ch hfm hfF he hsep hsq hen sel J ℓ
      calc _ ≤ K / e ^ 2 * (2 ^ ℓ * J.length) := this
        _ = K / e ^ 2 * 2 ^ ℓ * J.length := by ring)
  refine h.trans (le_of_eq ?_)
  congr 1
  rw [show 2 * ℓ = ℓ + ℓ by ring, pow_add]
  ring

end Error


end PrimeCarleson.Proof.Oplus
