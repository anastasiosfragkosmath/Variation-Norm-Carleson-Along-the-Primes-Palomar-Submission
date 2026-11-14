module

public import PrimeCarleson.Proof.Oplus.External.TileEnergyPackets
public import PrimeCarleson.Proof.Oplus.Estimates.All
public import PrimeCarleson.Proof.Oplus.EnergyIncrement.Basic

/-!
# The tile-energy bound outside the Hardy–Littlewood superlevel set

[O+] L2456-L2465 (`tilessmallmaxprop`), consumed at L2653-L2665 (the energy bound in the small-`F`
case of `L1except`); proof: Grafakos–Tao–Terwilleger, Lemma 1 (arXiv math/0212164v1), with its
argument supplemented here.

**The printed proposition is false** for the dyadic maximal function `M_D`: for a single multitile
`P` with `I = I_T = [0,1)`, `F = [-1,0)` and `f = 1_F φ_P/|φ_P|`, `M_D[1_F] = 0` on `[0, ∞)`. The
form proved here is the one consumed, with the Hardy–Littlewood maximal function (`maxSuperlevel`).

* `exists_tile_energy_le_of_subset`: for every `l`-overlapping tree `T` of `ρ`-multitiles (any `1`-
  or `2`-index with `m, n ∈ {1, …, 4}`, any admissible constants, any profile choice), every
  subfamily `Q ⊆ T` none of whose time intervals lies in `Ω_λ = {M[1_F] > λ}`, every `λ > 0`,
  measurable `F` and `f` with `|f| ≤ 1_F`,
  `(1/|I_T|) ∑_{P ∈ Q} |⟨f, φ_P⟩|² ≤ K (1 + C₁)² λ²`;
* `exists_energy_le_of_not_subset`: the energy form: for a separated family `S` all of whose
  multitiles have `I ⊄ Ω_λ`, `energy(S) ≤ K (1 + C₁) λ` (threshold `λ ∈ ℝ`).

The constant depends on `C₁` only through the factor `(1 + C₁)` (the modulation of the packets by
`ξ_T` costs `|ξ_T - c(ω_u)| ≤ C₁/(4|I|)` in the derivative bound).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal ComplexConjugate
open PrimeCarleson.Proof.Common (maximalHLR)

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson PrimeCarleson.Proof.Goal0

section Tree

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ}

/-- For `P` in an `l`-overlapping tree, `|ξ_T - c(ω_u)| ≤ C₁/(4|I|)`
(`C₂ ω_l ⊂ C₁ ω_u` and `|ω_u| = 1/(2|I|)`). -/
theorem abs_xi_sub_center_le (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    (𝒯 : MultitileTree ρ) (hov : 𝒯.IsOverlapping C₂) {P : Multitile ρ} (hP : P ∈ 𝒯.T) :
    |𝒯.ξ - P.ωu.center| ≤ C₁ / (4 * P.I.length) := by
  have hmem : 𝒯.ξ ∈ (ρ.ωlDyadic P.ωu).dilate C₂ := hov P hP
  have hsub := (hC.geometry ρ hρ Fact.out P.ωu).2.2.1 hmem
  obtain ⟨h1, h2⟩ := hsub
  have hL := P.I.length_pos
  have harea := P.length_I_mul_length_ωu
  have hu : P.ωu.length = 1 / (2 * P.I.length) := by
    field_simp; linarith
  rw [abs_le]
  have hC1 : 0 < C₁ := by linarith [hC.one_le, hC.lt₁, hC.lt₂]
  have : C₁ * P.ωu.length / 2 = C₁ / (4 * P.I.length) := by
    rw [hu]; field_simp; ring
  constructor <;> linarith

/-- Distinct multitiles of a tree have distinct time intervals. -/
theorem injOn_I_of_isTree (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    (𝒯 : MultitileTree ρ) (hT : 𝒯.IsTree C₁ C₂ M)
    (hsep : SeparationProp2 C₁ (𝒯.T : Set (Multitile ρ)))
    (S : Finset (Multitile ρ)) (hS : S ⊆ 𝒯.T) :
    Set.InjOn (fun P : Multitile ρ => P.I) (S : Set (Multitile ρ)) := by
  intro P hP P' hP' hPP'
  by_contra hne
  have hlen : P.ωu.length = P'.ωu.length := by
    rw [Dyadic.length_eq_iff]
    have e1 := P.area
    have e2 := P'.area
    simp only at hPP'
    rw [hPP'] at e1
    omega
  have hd := treeobs_disjoint_time hC hρ 𝒯 hT hsep (hS hP) (hS hP') hne hlen
  simp only at hPP'
  rw [hPP'] at hd
  exact Set.disjoint_left.1 hd P'.I.left_mem_toSet P'.I.left_mem_toSet

end Tree

/-- **The tile-energy bound outside the Hardy–Littlewood superlevel set** (Source: [O+]
`tilessmallmaxprop`, L2456–L2465; Grafakos–Tao–Terwilleger, Lemma 1; the repaired form of
`tilessmallmaxprop`), for a subfamily: there is an absolute constant `K` such that for every `1`- or
`2`-index `ρ` with `m, n ∈ {1, …, 4}`, admissible `C₁ > C₂ > C₃ ≥ 1`, profile choice,
`l`-overlapping tree `𝒯` of `ρ`-multitiles satisfying the separation assumptions, every subfamily
`Q ⊆ 𝒯` none of whose time intervals lies in `Ω_λ = {M[1_F] > λ}`, every `λ > 0`, measurable `F` and
`f` with `|f| ≤ 1_F`, `∑_{P ∈ Q} |⟨f, φ_P⟩|² ≤ K (1 + C₁)² λ² |I_𝒯|`. -/
theorem exists_tile_energy_le_of_subset :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ},
      AdmissibleConstants C₁ C₂ C₃ → ρ.IsStd → ∀ (ch : ProfileChoice) (𝒯 : MultitileTree ρ),
      𝒯.IsTree C₁ C₂ M → 𝒯.IsOverlapping C₂ →
      Separated C₁ C₂ C₃ (𝒯.T : Set (Multitile ρ)) → ∀ {F : Set ℝ} {f : ℝ → ℂ},
      MeasurableSet F → AEStronglyMeasurable f volume →
      (∀ᵐ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) → ∀ {lam : ℝ}, 0 < lam →
      ∀ (Q : Finset (Multitile ρ)), Q ⊆ 𝒯.T → (∀ P ∈ Q, ¬ P.I.toSet ⊆ maxSuperlevel F lam) →
        ∑ P ∈ Q, ‖P.coeff ch f‖ ^ 2 ≤ K * (1 + C₁) ^ 2 * lam ^ 2 * 𝒯.I.length := by
  obtain ⟨A₀, hA₀, hpbm⟩ := exists_packetBounds_modulated
  obtain ⟨K₀, hK₀, horth⟩ := exists_tree_orthogonality
  refine ⟨15000000 * (A₀ ^ 2 + K₀ + 1), by positivity, ?_⟩
  intro ρ _ C₁ C₂ C₃ M hC hρ ch 𝒯 hT hov hsep F f hF hfm hfae lam hlam Q hQsub hnot
  have hC1 : 0 < C₁ := by linarith [hC.one_le, hC.lt₁, hC.lt₂]
  -- replace `f` by a function with the pointwise bound
  set f' : ℝ → ℂ := fun x => if ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x then f x else 0 with hf'
  have hf'ae : f' =ᵐ[volume] f := by
    filter_upwards [hfae] with x hx
    simp only [hf', hx, ↓reduceIte]
  have hf'm : AEStronglyMeasurable f' volume := hfm.congr hf'ae.symm
  have hf'b : ∀ x, ‖f' x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x := by
    intro x
    simp only [hf']
    by_cases hx : ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x
    · simp [hx]
    · simp only [hx, ↓reduceIte, norm_zero]
      exact indicator_nonneg (fun _ _ => zero_le_one) x
  have hcoeff : ∀ P : Multitile ρ, P.coeff ch f = P.coeff ch f' := by
    intro P
    unfold Multitile.coeff pairing
    refine integral_congr_ae ?_
    filter_upwards [hf'ae] with x hx
    rw [hx]
  simp_rw [hcoeff]
  clear_value f'
  classical
  set ξ := 𝒯.ξ with hξ
  set ft : ℝ → ℂ := fun y => e (-(ξ * y)) * f' y with hft
  set ψ : Multitile ρ → ℝ → ℂ := fun P y => e (-(ξ * y)) * P.wavePacket ch y with hψ
  have hecont : ∀ a : ℝ, Continuous (fun y : ℝ => e (-(a * y))) := fun a =>
    (show Differentiable ℝ (fun y : ℝ => e (-(a * y))) from fun y =>
      (hasDerivAt_e_neg_mul a y).differentiableAt).continuous
  have hftm : AEStronglyMeasurable ft volume := (hecont ξ).aestronglyMeasurable.mul hf'm
  have hftb : ∀ x, ‖ft x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x := fun x => by
    simp only [hft]; rw [norm_mul, norm_e, one_mul]; exact hf'b x
  have hpb : ∀ P ∈ Q, PacketBounds (A₀ * (1 + C₁)) P.I (ψ P) := fun P hP =>
    hpbm ρ ch P ξ C₁ hC1.le (abs_xi_sub_center_le hC hρ 𝒯 hov (hQsub hP))
  have hinj := injOn_I_of_isTree hC hρ 𝒯 hT hsep.prop2 Q hQsub
  have hsub : ∀ P ∈ Q, P.I.toSet ⊆ 𝒯.I.toSet := fun P hP => hT.time P (hQsub hP)
  have hbes : ∀ g : ℝ → ℂ, MemLp g 2 volume →
      ∑ P ∈ Q, ‖pairing g (ψ P)‖ ^ 2 ≤ (K₀ + 1) * ∫ x, ‖g x‖ ^ 2 := by
    intro g hg
    set g' : ℝ → ℂ := fun y => e (ξ * y) * g y with hg'
    have hecont' : Continuous (fun y : ℝ => e (ξ * y)) := by
      have := hecont (-ξ)
      simpa using this
    have hg'm : AEStronglyMeasurable g' volume :=
      hecont'.aestronglyMeasurable.mul hg.aestronglyMeasurable
    have hnorm' : ∀ y, ‖g' y‖ = ‖g y‖ := fun y => by
      simp only [hg']; rw [norm_mul, norm_e, one_mul]
    have hg'2 : MemLp g' 2 volume :=
      hg.congr_norm hg'm (Filter.Eventually.of_forall fun y => (hnorm' y).symm)
    have hnorm : ∫ x, ‖g' x‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 := by
      congr 1; funext x; rw [hnorm']
    set 𝒯Q : MultitileTree ρ := ⟨Q, 𝒯.I, 𝒯.ξ⟩ with h𝒯Q
    have hTQ : 𝒯Q.IsTree C₁ C₂ M :=
      ⟨hT.top_subset, hT.ξ_mem, fun P hP => hT.time P (hQsub hP),
        fun P hP => hT.freq P (hQsub hP)⟩
    have hovQ : 𝒯Q.IsOverlapping C₂ := fun P hP => hov P (hQsub hP)
    have hsepQ : Separated C₁ C₂ C₃ (𝒯Q.T : Set (Multitile ρ)) :=
      hsep.mono (fun P hP => hQsub hP)
    have horthQ : ∀ c : Multitile ρ → ℂ, ∫ x, ‖∑ P ∈ Q, c P * P.wavePacket ch x‖ ^ 2 ≤
        (K₀ + 1) * ∑ P ∈ Q, ‖c P‖ ^ 2 := by
      intro c
      have := horth hC hρ ch 𝒯Q hTQ hovQ hsepQ c
      simp only [smul_eq_mul] at this
      refine this.trans ?_
      have : 0 ≤ ∑ P ∈ Q, ‖c P‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
      nlinarith
    have h1 := sum_norm_sq_pairing_le_of_orthogonality Q (fun P => P.wavePacket ch)
      (fun P => ch.isProfile.memLp_wavePacketOf P.I P.ωu) (K := K₀ + 1) (by positivity) horthQ hg'2
    calc ∑ P ∈ Q, ‖pairing g (ψ P)‖ ^ 2 = ∑ P ∈ Q, ‖pairing g' (P.wavePacket ch)‖ ^ 2 := by
          refine Finset.sum_congr rfl fun P _ => ?_
          rw [hψ]
          simp only
          rw [pairing_mul_e_eq]
      _ ≤ (K₀ + 1) * ∫ x, ‖g' x‖ ^ 2 := h1
      _ = (K₀ + 1) * ∫ x, ‖g x‖ ^ 2 := by rw [hnorm]
  have key := tile_energy_abstract (IT := 𝒯.I) hF hlam hftm hftb Q (fun P => P.I) ψ
    (A := A₀ * (1 + C₁)) (B := K₀ + 1) (by positivity) (by positivity) hinj hsub hpb hnot hbes
  calc ∑ P ∈ Q, ‖P.coeff ch f'‖ ^ 2 = ∑ P ∈ Q, ‖pairing ft (ψ P)‖ ^ 2 := by
        refine Finset.sum_congr rfl fun P _ => ?_
        have := pairing_modulate f' (P.wavePacket ch) ξ
        rw [hψ, hft]
        simp only
        rw [this]
        rfl
    _ ≤ 15000000 * ((A₀ * (1 + C₁)) ^ 2 + (K₀ + 1)) * lam ^ 2 * 𝒯.I.length := key
    _ ≤ 15000000 * (A₀ ^ 2 + K₀ + 1) * (1 + C₁) ^ 2 * lam ^ 2 * 𝒯.I.length := by
        have hL := 𝒯.I.length_pos
        have h1 : (1 : ℝ) ≤ (1 + C₁) ^ 2 := by nlinarith
        have h2 : 0 ≤ lam ^ 2 * 𝒯.I.length := by positivity
        have h3 : (A₀ * (1 + C₁)) ^ 2 + (K₀ + 1) ≤ (A₀ ^ 2 + K₀ + 1) * (1 + C₁) ^ 2 := by
          nlinarith [sq_nonneg A₀]
        calc 15000000 * ((A₀ * (1 + C₁)) ^ 2 + (K₀ + 1)) * lam ^ 2 * 𝒯.I.length
            = 15000000 * (((A₀ * (1 + C₁)) ^ 2 + (K₀ + 1)) * (lam ^ 2 * 𝒯.I.length)) := by ring
          _ ≤ 15000000 * ((A₀ ^ 2 + K₀ + 1) * (1 + C₁) ^ 2 * (lam ^ 2 * 𝒯.I.length)) := by
              gcongr
          _ = _ := by ring

/-- **The energy form of the tile-energy bound** (the form consumed at L2653-L2665 of [O+], in the
small-`F` case of `L1except`): there is an absolute constant `K` such that for every
separated family `S` of `ρ`-multitiles none of whose time intervals lies inside
`Ω_λ = {M[1_F] > λ}`, `energy(S) ≤ K (1 + C₁) λ`. With `λ = 16 |F|` (so that `|Ω_λ| ≤ 1/4`,
`volume_maximalHLR_indicator_gt_sixteen_le`) this is `energy(𝔓') ≲ |F|` for
`𝔓' = {P : I ⊄ G}`. -/
theorem exists_energy_le_of_not_subset :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ},
      AdmissibleConstants C₁ C₂ C₃ → ρ.IsStd → ∀ (ch : ProfileChoice) {F : Set ℝ} {f : ℝ → ℂ},
      MeasurableSet F → AEStronglyMeasurable f volume →
      (∀ᵐ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) → ∀ {lam : ℝ}, 0 < lam →
      ∀ (S : Set (Multitile ρ)), Separated C₁ C₂ C₃ S →
        (∀ P ∈ S, ¬ P.I.toSet ⊆ maxSuperlevel F lam) →
        energy C₁ C₂ M ch f S ≤ ENNReal.ofReal (K * (1 + C₁) * lam) := by
  obtain ⟨K, hK0, hK⟩ := exists_tile_energy_le_of_subset
  refine ⟨√K, Real.sqrt_nonneg _, ?_⟩
  intro ρ _ C₁ C₂ C₃ M hC hρ ch F f hF hfm hf lam hlam S hS hnot
  have hC1 : 0 < C₁ := by linarith [hC.one_le, hC.lt₁, hC.lt₂]
  unfold energy energyOf
  refine iSup_le fun 𝒯 => iSup_le fun hT => iSup_le fun hov => iSup_le fun hsub => ?_
  classical
  have hsep : Separated C₁ C₂ C₃ (𝒯.T : Set (Multitile ρ)) := hS.mono hsub
  have hsum := hK (M := M) hC hρ ch 𝒯 hT hov hsep hF hfm hf hlam 𝒯.T (subset_refl _)
    fun P hP => hnot P (hsub hP)
  have hIT := 𝒯.I.length_pos
  have h1 : ∑ P ∈ 𝒯.T, ‖P.coeff ch f‖ₑ ^ 2 ≤
      ENNReal.ofReal (K * (1 + C₁) ^ 2 * lam ^ 2 * 𝒯.I.length) := by
    have : ∑ P ∈ 𝒯.T, ‖P.coeff ch f‖ₑ ^ 2 = ENNReal.ofReal (∑ P ∈ 𝒯.T, ‖P.coeff ch f‖ ^ 2) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun P _ => by positivity)]
      refine Finset.sum_congr rfl fun P _ => ?_
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    rw [this]
    exact ENNReal.ofReal_le_ofReal hsum
  calc ((ENNReal.ofReal 𝒯.I.length)⁻¹ * ∑ P ∈ 𝒯.T, ‖P.coeff ch f‖ₑ ^ 2) ^ (1 / 2 : ℝ)
      ≤ ((ENNReal.ofReal 𝒯.I.length)⁻¹ *
          ENNReal.ofReal (K * (1 + C₁) ^ 2 * lam ^ 2 * 𝒯.I.length)) ^ (1 / 2 : ℝ) := by
        gcongr
    _ = ENNReal.ofReal (√K * (1 + C₁) * lam) := by
        rw [← ENNReal.ofReal_inv_of_pos hIT, ← ENNReal.ofReal_mul (inv_pos.2 hIT).le]
        have : (𝒯.I.length)⁻¹ * (K * (1 + C₁) ^ 2 * lam ^ 2 * 𝒯.I.length) =
            K * (1 + C₁) ^ 2 * lam ^ 2 := by field_simp
        rw [this, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          ← Real.sqrt_eq_rpow]
        congr 1
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
          Real.sqrt_sq (by linarith), Real.sqrt_sq hlam.le]

end PrimeCarleson.Proof.Oplus
