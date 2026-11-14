module

public import PrimeCarleson.Proof.Oplus.Estimates.TreeObs
public import PrimeCarleson.Proof.Oplus.Estimates.SchwartzEstimate
public import PrimeCarleson.Proof.Oplus.Estimates.SameInterval

/-!
# Orthogonality in a tree and the universal energy and density bounds ([O+] L1357-L1400)

Source: [O+] `univ-den-ene-bound`, L1357–L1363; [O+] `univ-den-ene-bound`, L1377–L1380; [O+]
`univ-den-ene-bound`, L1387–L1394 (L1357-L1400).

* `exists_tree_orthogonality` (tree orthogonality, [O+] L1373-L1380) and
  `exists_tree_orthogonality_coeff`: there is `K` such that for every `l`-overlapping tree `T` of
  `ρ`-multitiles with the separation assumptions (`ρ` any `1`- or `2`-index with
  `m, n ∈ {1, …, 4}`, any admissible `C₁ > C₂ > C₃ ≥ 1`, any profile choice) and every
  coefficients `c`, `∫ |∑_{P ∈ T} c_P φ_P|² ≤ K ∑_{P ∈ T} |c_P|²`. For `c_P = ⟨f', φ_P⟩` this is the
  printed `‖∑ ⟨f',φ_P⟩ φ_P‖_{L²} ≲ (∑ |⟨f',φ_P⟩|²)^{1/2}`. Proof: the Gram matrix `⟨φ_P, φ_{P'}⟩`
  of the tree vanishes for `|ω_u| ≠ |ω_u'|` (Plancherel, the supports `C₃ ω_u` are disjoint by
  `treeobs_disjoint_dilate`), and for `|ω_u| = |ω_u'|` is bounded by `∫_{I'} w_I` with disjoint
  `I'` (`treeobs_disjoint_time`, `schwartzestimate`): Schur's test
  (`norm_sum_sum_le_of_row_sum_le`, `sum_norm_pairing_le`).
* `sum_norm_sq_pairing_le_of_orthogonality`: duality, a Riesz upper bound gives
  `∑ |⟨g, φ_P⟩|² ≤ K ∫ |g|²`.
* `exists_far_field_tail` (the far-field tail, [O+] L1387-L1394): for `|f''| ≤ 1_{ℝ ∖ 3 I_T}`,
  `|⟨f'', φ_P⟩| ≤ K |I|^{1/2} (|I|/|I_T|)^N` and `∑_{P ∈ T} |⟨f'', φ_P⟩|² ≤ K |I_T|`
  (`Multitile.exists_norm_coeff_le_far`, `sum_length_mul_ratio_pow_le`: counting by scales).
* `exists_sum_norm_sq_coeff_le`, `exists_energy_le`, `density_le_one`, `exists_univ_den_ene_bound`
  (`univ-den-ene-bound`, [O+] L1365-L1400): `∑_{P ∈ T} |⟨f, φ_P⟩|² ≤ K |I_T|` for every
  `l`-overlapping tree and `|f| ≤ 1`, hence `energy ≤ √K`; `density ≤ (2/3)^{1/r'} ≤ 1` (`r > 1`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped FourierTransform SchwartzMap ContDiff ComplexConjugate ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

/-! ### Schur's test for a Gram matrix -/

/-- **Schur's test**: `|∑_{P,P'} c_P conj(c_{P'}) G(P,P')| ≤ K ∑ |c_P|²` if
`|G(P',P)| = |G(P,P')|` and the absolute row sums are at most `K`. -/
theorem norm_sum_sum_le_of_row_sum_le {ι : Type*} (T : Finset ι) (c : ι → ℂ) (G : ι → ι → ℂ)
    {K : ℝ} (hsymm : ∀ P P', ‖G P' P‖ = ‖G P P'‖) (hrow : ∀ P ∈ T, ∑ P' ∈ T, ‖G P P'‖ ≤ K) :
    ‖∑ P ∈ T, ∑ P' ∈ T, c P * (starRingEnd ℂ) (c P') * G P P'‖ ≤ K * ∑ P ∈ T, ‖c P‖ ^ 2 := by
  have h1 : ‖∑ P ∈ T, ∑ P' ∈ T, c P * (starRingEnd ℂ) (c P') * G P P'‖ ≤
      ∑ P ∈ T, ∑ P' ∈ T, ‖c P‖ * ‖c P'‖ * ‖G P P'‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun P _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun P' _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_conj]
  refine h1.trans ?_
  have h2 : ∀ P P' : ι, ‖c P‖ * ‖c P'‖ * ‖G P P'‖ ≤
      (‖c P‖ ^ 2 * ‖G P P'‖ + ‖c P'‖ ^ 2 * ‖G P' P‖) / 2 := by
    intro P P'
    rw [hsymm P P']
    nlinarith [sq_nonneg (‖c P‖ - ‖c P'‖), norm_nonneg (G P P')]
  calc ∑ P ∈ T, ∑ P' ∈ T, ‖c P‖ * ‖c P'‖ * ‖G P P'‖
      ≤ ∑ P ∈ T, ∑ P' ∈ T, (‖c P‖ ^ 2 * ‖G P P'‖ + ‖c P'‖ ^ 2 * ‖G P' P‖) / 2 :=
        Finset.sum_le_sum fun P _ => Finset.sum_le_sum fun P' _ => h2 P P'
    _ = (∑ P ∈ T, ‖c P‖ ^ 2 * ∑ P' ∈ T, ‖G P P'‖ +
          ∑ P ∈ T, ∑ P' ∈ T, ‖c P'‖ ^ 2 * ‖G P' P‖) / 2 := by
        simp_rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = ∑ P ∈ T, ‖c P‖ ^ 2 * ∑ P' ∈ T, ‖G P P'‖ := by
        have : ∑ P ∈ T, ∑ P' ∈ T, ‖c P'‖ ^ 2 * ‖G P' P‖ =
            ∑ P ∈ T, ‖c P‖ ^ 2 * ∑ P' ∈ T, ‖G P P'‖ := by
          rw [Finset.sum_comm]
          simp_rw [Finset.mul_sum]
        rw [this]; ring
    _ ≤ ∑ P ∈ T, ‖c P‖ ^ 2 * K :=
        Finset.sum_le_sum fun P hP => mul_le_mul_of_nonneg_left (hrow P hP) (by positivity)
    _ = K * ∑ P ∈ T, ‖c P‖ ^ 2 := by rw [Finset.mul_sum]; simp_rw [mul_comm]

/-! ### Expansion of the square of a finite sum of `L²` functions -/

/-- `∫ |∑ c_i φ_i|² = ∑_{i,j} c_i conj(c_j) ⟨φ_i, φ_j⟩` (as a complex number) for finitely many
`L²` functions. -/
theorem integral_norm_sq_sum_eq {ι : Type*} (T : Finset ι) (φ : ι → ℝ → ℂ) (c : ι → ℂ)
    (hφ : ∀ i, MemLp (φ i) 2 volume) :
    (((∫ x, ‖∑ i ∈ T, c i * φ i x‖ ^ 2 : ℝ)) : ℂ) =
      ∑ i ∈ T, ∑ j ∈ T, c i * (starRingEnd ℂ) (c j) * pairing (φ i) (φ j) := by
  rw [← integral_complex_ofReal]
  have h1 : ∀ x : ℝ, (((‖∑ i ∈ T, c i * φ i x‖ ^ 2 : ℝ)) : ℂ) =
      ∑ i ∈ T, ∑ j ∈ T, c i * (starRingEnd ℂ) (c j) * (φ i x * (starRingEnd ℂ) (φ j x)) := by
    intro x
    rw [Complex.sq_norm, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]; ring
  simp_rw [h1]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul]; rfl
    · intro j _
      exact ((hφ i).integrable_mul (hφ j).star).const_mul _
  · intro i _
    exact integrable_finsetSum _ fun j _ => ((hφ i).integrable_mul (hφ j).star).const_mul _

/-! ### The Gram matrix of a tree -/

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ}

/-- The Gram matrix of a tree vanishes between packets of different scales (the supports
`C₃ ω_u` and `C₃ ω_u'` are disjoint, `treeobs_disjoint_dilate`). -/
theorem pairing_eq_zero_of_length_ne (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    (ch ch' : ProfileChoice) (𝒯 : MultitileTree ρ) (hov : 𝒯.IsOverlapping C₂)
    (hsc : SeparationOfScales C₁ C₂ C₃ (𝒯.T : Set (Multitile ρ))) {P P' : Multitile ρ}
    (hP : P ∈ 𝒯.T) (hP' : P' ∈ 𝒯.T) (hne : P.ωu.length ≠ P'.ωu.length) :
    pairing (P.wavePacket ch) (P'.wavePacket ch') = 0 := by
  have hd := treeobs_disjoint_dilate hC hρ 𝒯 hov hsc hP hP' hne
  exact pairing_wavePacketOf_eq_zero_of_support ch.isProfile ch'.isProfile P.I P.ωu P'.I P'.ωu
    (S := P.ωu.dilate C₃) (S' := P'.ωu.dilate C₃)
    ((subset_tsupport _).trans (hC.packet_support ch P.I P.ωu))
    ((subset_tsupport _).trans (hC.packet_support ch' P'.I P'.ωu)) hd

/-- **The row sums of the Gram matrix of a tree are bounded**: if `K₀` is the constant of
`schwartzestimate` for `N = 2`, then for every `P ∈ T`,
`∑_{P' ∈ T} |⟨φ_P, φ_{P'}⟩| ≤ 2 K₀`. -/
theorem sum_norm_pairing_le (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    (ch : ProfileChoice) (𝒯 : MultitileTree ρ) (hT : 𝒯.IsTree C₁ C₂ M)
    (hov : 𝒯.IsOverlapping C₂) (hsep : Separated C₁ C₂ C₃ (𝒯.T : Set (Multitile ρ))) {K₀ : ℝ}
    (hK₀ : ∀ (ρ ρ' : Idx) (ch ch' : ProfileChoice) (P : Multitile ρ) (P' : Multitile ρ'),
      P'.I.length ≤ P.I.length →
      ‖pairing (P.wavePacket ch) (P'.wavePacket ch')‖ ≤
        K₀ * √(P.I.length / P'.I.length) * ∫ x in P'.I.toSet, P.I.weight 2 x)
    (hK₀0 : 0 ≤ K₀) {P : Multitile ρ} (hP : P ∈ 𝒯.T) :
    ∑ P' ∈ 𝒯.T, ‖pairing (P.wavePacket ch) (P'.wavePacket ch)‖ ≤ 2 * K₀ := by
  classical
  set F : Finset (Multitile ρ) := 𝒯.T.filter fun P' => P'.ωu.length = P.ωu.length with hF
  have hzero : ∀ P' ∈ 𝒯.T, P' ∉ F → ‖pairing (P.wavePacket ch) (P'.wavePacket ch)‖ = 0 := by
    intro P' hP' hnF
    have : P'.ωu.length ≠ P.ωu.length := fun h => hnF (Finset.mem_filter.2 ⟨hP', h⟩)
    rw [pairing_eq_zero_of_length_ne hC hρ ch ch 𝒯 hov hsep.scales hP hP' this.symm, norm_zero]
  rw [← Finset.sum_subset (Finset.filter_subset _ _) fun P' hP' hnF => hzero P' hP' hnF]
  have hlen : ∀ P' ∈ F, P'.I.length = P.I.length := by
    intro P' hP'
    have h1 := (Finset.mem_filter.1 hP').2
    have h2 : P'.ωu.k = P.ωu.k := Dyadic.length_eq_iff.1 h1
    rw [Dyadic.length_eq_iff]
    have := P.area
    have := P'.area
    omega
  have hterm : ∀ P' ∈ F, ‖pairing (P.wavePacket ch) (P'.wavePacket ch)‖ ≤
      K₀ * ∫ x in P'.I.toSet, P.I.weight 2 x := by
    intro P' hP'
    have := hK₀ ρ ρ ch ch P P' (le_of_eq (hlen P' hP'))
    rw [hlen P' hP', div_self P.I.length_ne_zero, Real.sqrt_one, mul_one] at this
    exact this
  have hdisj : Set.Pairwise (F : Set (Multitile ρ))
      (Function.onFun Disjoint fun P' => P'.I.toSet) := by
    intro P' hP' P'' hP'' hne
    have h1 := Finset.mem_coe.1 hP'
    have h2 := Finset.mem_coe.1 hP''
    refine treeobs_disjoint_time hC hρ 𝒯 hT hsep.prop2 (Finset.mem_filter.1 h1).1
      (Finset.mem_filter.1 h2).1 hne ?_
    rw [(Finset.mem_filter.1 h1).2, (Finset.mem_filter.1 h2).2]
  have hint : ∀ P' ∈ F, IntegrableOn (P.I.weight 2) P'.I.toSet := fun P' _ =>
    (P.I.integrable_weight (le_refl 2)).integrableOn
  calc ∑ P' ∈ F, ‖pairing (P.wavePacket ch) (P'.wavePacket ch)‖
      ≤ ∑ P' ∈ F, K₀ * ∫ x in P'.I.toSet, P.I.weight 2 x := Finset.sum_le_sum hterm
    _ = K₀ * ∫ x in ⋃ P' ∈ F, P'.I.toSet, P.I.weight 2 x := by
        rw [← Finset.mul_sum, integral_biUnion_finset F (fun P' _ => P'.I.measurableSet_toSet)
          hdisj hint]
    _ ≤ K₀ * ∫ x, P.I.weight 2 x := by
        apply mul_le_mul_of_nonneg_left _ hK₀0
        exact setIntegral_le_integral (P.I.integrable_weight (le_refl 2))
          (Eventually.of_forall fun x => P.I.weight_nonneg 2 x)
    _ = 2 * K₀ := by
        rw [Dyadic.integral_weight (le_refl 2)]; norm_num; ring

/-! ### Orthogonality inside an `l`-overlapping tree -/

/-- **Orthogonality inside an `l`-overlapping tree** ([O+] L1373-L1380): there is a constant `K`
(independent of everything below) such that for every `1`- or `2`-index `ρ` with `m, n ∈ {1, …, 4}`,
every admissible `C₁ > C₂ > C₃ ≥ 1`, every profile choice, every `l`-overlapping tree `T` of
`ρ`-multitiles with (separationofscales) and (separationprop2), and every coefficients `c`:
`∫ |∑_{P ∈ T} c_P φ_P|² ≤ K ∑_{P ∈ T} |c_P|²`. -/
theorem exists_tree_orthogonality :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ},
      AdmissibleConstants C₁ C₂ C₃ → ρ.IsStd → ∀ (ch : ProfileChoice) (𝒯 : MultitileTree ρ),
      𝒯.IsTree C₁ C₂ M → 𝒯.IsOverlapping C₂ → Separated C₁ C₂ C₃ (𝒯.T : Set (Multitile ρ)) →
      ∀ c : Multitile ρ → ℂ,
        ∫ x, ‖∑ P ∈ 𝒯.T, c P • P.wavePacket ch x‖ ^ 2 ≤ K * ∑ P ∈ 𝒯.T, ‖c P‖ ^ 2 := by
  obtain ⟨K₀, hK₀0, hK₀⟩ := Multitile.exists_norm_pairing_wavePacket_le 2
  refine ⟨2 * K₀, by positivity, fun {ρ} _ {C₁ C₂ C₃} {M} hC hρ ch 𝒯 hT hov hsep c => ?_⟩
  have hexp := integral_norm_sq_sum_eq 𝒯.T (fun P : Multitile ρ => P.wavePacket ch) c
    (fun P => ch.isProfile.memLp_wavePacketOf P.I P.ωu)
  have hschur := norm_sum_sum_le_of_row_sum_le 𝒯.T c
    (fun P P' => pairing (P.wavePacket ch) (P'.wavePacket ch))
    (K := 2 * K₀) (fun P P' => norm_pairing_comm _ _)
    (fun P hP => sum_norm_pairing_le hC hρ ch 𝒯 hT hov hsep hK₀ hK₀0 hP)
  simp only [smul_eq_mul]
  have hnn : 0 ≤ ∫ x, ‖∑ P ∈ 𝒯.T, c P * P.wavePacket ch x‖ ^ 2 :=
    integral_nonneg fun x => by positivity
  have h1 : ∫ x, ‖∑ P ∈ 𝒯.T, c P * P.wavePacket ch x‖ ^ 2 =
      ‖∑ P ∈ 𝒯.T, ∑ P' ∈ 𝒯.T, c P * (starRingEnd ℂ) (c P') *
        pairing (P.wavePacket ch) (P'.wavePacket ch)‖ := by
    rw [← hexp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  rw [h1]
  exact hschur

/-! ### Duality: a Riesz upper bound gives a Bessel inequality -/

/-- If `∫ |∑ c_i φ_i|² ≤ K ∑ |c_i|²` for all coefficients (`K > 0`), then
`∑ |⟨g, φ_i⟩|² ≤ K ∫ |g|²` for `g ∈ L²`. -/
theorem sum_norm_sq_pairing_le_of_orthogonality {ι : Type*} (T : Finset ι) (φ : ι → ℝ → ℂ)
    (hφ : ∀ i, MemLp (φ i) 2 volume) {K : ℝ} (hK : 0 < K)
    (horth : ∀ c : ι → ℂ, ∫ x, ‖∑ i ∈ T, c i * φ i x‖ ^ 2 ≤ K * ∑ i ∈ T, ‖c i‖ ^ 2)
    {g : ℝ → ℂ} (hg : MemLp g 2 volume) :
    ∑ i ∈ T, ‖pairing g (φ i)‖ ^ 2 ≤ K * ∫ x, ‖g x‖ ^ 2 := by
  set a : ι → ℂ := fun i => pairing g (φ i) with ha
  set S : ℝ → ℂ := fun x => ∑ i ∈ T, a i * φ i x with hS
  set A : ℝ := ∑ i ∈ T, ‖a i‖ ^ 2 with hA
  have hSmem : MemLp S 2 volume := by
    refine memLp_finsetSum (f := fun i x => a i * φ i x) T fun i _ => ?_
    exact (hφ i).const_mul (a i)
  have hSnorm : MemLp (fun x => ‖S x‖) 2 volume := hSmem.norm
  have hgnorm : MemLp (fun x => ‖g x‖) 2 volume := hg.norm
  -- `A = ∫ conj g * S`
  have hconj : ∀ i, (starRingEnd ℂ) (a i) = ∫ x, (starRingEnd ℂ) (g x) * φ i x := by
    intro i
    rw [ha]
    simp only
    unfold pairing
    rw [← integral_conj]
    congr 1; funext x
    simp [mul_comm]
  have hint_i : ∀ i, Integrable (fun x => (starRingEnd ℂ) (g x) * φ i x) := fun i =>
    hg.star.integrable_mul (hφ i)
  have hAeq : (A : ℂ) = ∫ x, (starRingEnd ℂ) (g x) * S x := by
    rw [hA]
    push_cast
    have : ∫ x, (starRingEnd ℂ) (g x) * S x =
        ∑ i ∈ T, a i * ∫ x, (starRingEnd ℂ) (g x) * φ i x := by
      simp only [hS, Finset.mul_sum]
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [← integral_const_mul]
        congr 1; funext x; ring
      · intro i _
        have := (hint_i i).const_mul (a i)
        refine this.congr (Eventually.of_forall fun x => ?_)
        simp only; ring
    rw [this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hconj i, Complex.mul_conj, ← Complex.ofReal_pow, Complex.sq_norm]
  have hA_le : A ≤ ∫ x, ‖g x‖ * ‖S x‖ := by
    have h1 : A = (((A : ℝ) : ℂ)).re := by simp
    rw [h1, hAeq]
    calc (∫ x, (starRingEnd ℂ) (g x) * S x).re ≤ ‖∫ x, (starRingEnd ℂ) (g x) * S x‖ :=
          Complex.re_le_norm _
      _ ≤ ∫ x, ‖(starRingEnd ℂ) (g x) * S x‖ := norm_integral_le_integral_norm _
      _ = ∫ x, ‖g x‖ * ‖S x‖ := by
          congr 1; funext x; rw [norm_mul, Complex.norm_conj]
  have hnormS : ∫ x, ‖S x‖ ^ 2 ≤ K * A := horth a
  have hint1 : Integrable (fun x => ‖g x‖ ^ 2) := hgnorm.integrable_sq
  have hint2 : Integrable (fun x => ‖S x‖ ^ 2) := hSnorm.integrable_sq
  have hint3 : Integrable (fun x => ‖g x‖ * ‖S x‖) := hgnorm.integrable_mul hSnorm
  have hAMGM : ∫ x, ‖g x‖ * ‖S x‖ ≤
      ∫ x, (K / 2 * ‖g x‖ ^ 2 + 1 / (2 * K) * ‖S x‖ ^ 2) := by
    refine integral_mono hint3 ((hint1.const_mul _).add (hint2.const_mul _)) fun x => ?_
    have : 0 ≤ (Real.sqrt K * ‖g x‖ - ‖S x‖ / Real.sqrt K) ^ 2 := sq_nonneg _
    have hsq : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK.le
    have hs0 : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
    have e1 : (Real.sqrt K * ‖g x‖ - ‖S x‖ / Real.sqrt K) ^ 2 =
        K * ‖g x‖ ^ 2 - 2 * (‖g x‖ * ‖S x‖) + ‖S x‖ ^ 2 / K := by
      field_simp
      rw [hsq]
      ring
    have : 2 * (‖g x‖ * ‖S x‖) ≤ K * ‖g x‖ ^ 2 + ‖S x‖ ^ 2 / K := by nlinarith
    have e2 : 1 / (2 * K) * ‖S x‖ ^ 2 = ‖S x‖ ^ 2 / K / 2 := by field_simp
    rw [e2]
    linarith
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => by positivity
  have hfin : A ≤ K / 2 * (∫ x, ‖g x‖ ^ 2) + A / 2 := by
    calc A ≤ ∫ x, ‖g x‖ * ‖S x‖ := hA_le
      _ ≤ ∫ x, (K / 2 * ‖g x‖ ^ 2 + 1 / (2 * K) * ‖S x‖ ^ 2) := hAMGM
      _ = K / 2 * (∫ x, ‖g x‖ ^ 2) + 1 / (2 * K) * ∫ x, ‖S x‖ ^ 2 := by
          rw [integral_add (hint1.const_mul _) (hint2.const_mul _), integral_const_mul,
            integral_const_mul]
      _ ≤ K / 2 * (∫ x, ‖g x‖ ^ 2) + 1 / (2 * K) * (K * A) := by
          gcongr
      _ = K / 2 * (∫ x, ‖g x‖ ^ 2) + A / 2 := by field_simp
  linarith

/-! ### The far-field tail -/

/-- The measure of a dyadic interval is its length (real-valued). -/
theorem Dyadic.volume_real_toSet (I : Dyadic) : volume.real I.toSet = I.length := by
  simp [Measure.real, Dyadic.volume_toSet, I.length_pos.le]

/-- A dyadic interval inside `J` has length `|J| 2^{-d}` with `d = k_J - k_I ≥ 0`. -/
theorem Dyadic.length_eq_mul_half_pow {I J : Dyadic} (h : I.toSet ⊆ J.toSet) :
    I.length = J.length * (1 / 2) ^ (J.k - I.k).toNat := by
  have hk : I.k ≤ J.k := Dyadic.k_le_of_toSet_subset h
  obtain ⟨d, hd⟩ : ∃ d : ℕ, J.k - I.k = d := ⟨(J.k - I.k).toNat, by omega⟩
  have hd' : (J.k - I.k).toNat = d := by omega
  rw [hd']
  have : I.k = J.k - d := by omega
  unfold Dyadic.length
  rw [this, zpow_sub₀ (by norm_num), zpow_natCast, one_div, inv_pow, div_eq_mul_inv]

/-- A geometric sum over a finite set of exponents: `∑_{j ∈ t} (1/4)^{N j} ≤ 4/3` for `N ≥ 1`. -/
theorem sum_geometric_le (t : Finset ℕ) {N : ℕ} (hN : 1 ≤ N) :
    ∑ j ∈ t, ((1 / 2 : ℝ) ^ j) ^ (2 * N) ≤ 4 / 3 := by
  have hr : ((1 / 2 : ℝ) ^ 2 * 1) ^ N ≤ 1 / 4 := by
    have : ((1 / 2 : ℝ) ^ 2) ^ N ≤ (1 / 2 : ℝ) ^ 2 := by
      calc ((1 / 2 : ℝ) ^ 2) ^ N ≤ ((1 / 2 : ℝ) ^ 2) ^ 1 :=
            pow_le_pow_of_le_one (by positivity) (by norm_num) hN
        _ = _ := pow_one _
    simpa using (this.trans (by norm_num))
  set r : ℝ := ((1 / 2 : ℝ) ^ 2) ^ N with hr_def
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := lt_of_le_of_lt (by simpa [hr_def] using hr) (by norm_num)
  have hterm : ∀ j : ℕ, ((1 / 2 : ℝ) ^ j) ^ (2 * N) = r ^ j := by
    intro j
    rw [hr_def, ← pow_mul, ← pow_mul, ← pow_mul]
    congr 1; ring
  simp_rw [hterm]
  calc ∑ j ∈ t, r ^ j ≤ ∑' j, r ^ j :=
        (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum t (fun j _ => by positivity)
    _ = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1
    _ ≤ 4 / 3 := by
        have : r ≤ 1 / 4 := by simpa [hr_def] using hr
        rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]
        linarith

/-- **Counting by scales** (L1391-L1393): in a tree satisfying (separationprop2), the packets of
one scale have disjoint time intervals inside `I_T`, hence `∑_{P ∈ T} |I| (|I|/|I_T|)^{2N} ≤
(4/3)|I_T|` for `N ≥ 1`. -/
theorem sum_length_mul_ratio_pow_le (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    (𝒯 : MultitileTree ρ) (hT : 𝒯.IsTree C₁ C₂ M)
    (hsep : SeparationProp2 C₁ (𝒯.T : Set (Multitile ρ))) {N : ℕ} (hN : 1 ≤ N) :
    ∑ P ∈ 𝒯.T, P.I.length * (P.I.length / 𝒯.I.length) ^ (2 * N) ≤ 4 / 3 * 𝒯.I.length := by
  classical
  have hIT := 𝒯.I.length_pos
  set jf : Multitile ρ → ℕ := fun P => (𝒯.I.k - P.I.k).toNat with hjf
  have hlen : ∀ P ∈ 𝒯.T, P.I.length = 𝒯.I.length * (1 / 2) ^ jf P := fun P hP =>
    Dyadic.length_eq_mul_half_pow (hT.time P hP)
  have hclass : ∀ j : ℕ, ∑ P ∈ 𝒯.T.filter (fun P => jf P = j), P.I.length ≤ 𝒯.I.length := by
    intro j
    set F := 𝒯.T.filter (fun P => jf P = j) with hF
    have hdisj : Set.PairwiseDisjoint (F : Set (Multitile ρ)) (fun P => P.I.toSet) := by
      intro P hP P' hP' hne
      have h1 := Finset.mem_filter.1 (Finset.mem_coe.1 hP)
      have h2 := Finset.mem_filter.1 (Finset.mem_coe.1 hP')
      refine treeobs_disjoint_time hC hρ 𝒯 hT hsep h1.1 h2.1 hne ?_
      rw [Dyadic.length_eq_iff]
      have e1 : P.I.length = P'.I.length := by
        rw [hlen P h1.1, hlen P' h2.1, h1.2, h2.2]
      have := Dyadic.length_eq_iff.1 e1
      have a1 := P.area
      have a2 := P'.area
      omega
    have hsub : (⋃ P ∈ F, P.I.toSet) ⊆ 𝒯.I.toSet := by
      intro x hx
      obtain ⟨P, hP, hxP⟩ := Set.mem_iUnion₂.1 hx
      exact hT.time P (Finset.mem_filter.1 hP).1 hxP
    have h1 := measureReal_biUnion_finset (μ := volume) hdisj
      (fun P _ => P.I.measurableSet_toSet) (fun P _ => by simp [Dyadic.volume_toSet])
    have h2 : volume.real (⋃ P ∈ F, P.I.toSet) ≤ volume.real 𝒯.I.toSet :=
      measureReal_mono hsub (by simp [Dyadic.volume_toSet])
    rw [h1] at h2
    simpa only [Dyadic.volume_real_toSet] using h2
  have hmaps : ∀ P ∈ 𝒯.T, jf P ∈ 𝒯.T.image jf := fun P hP => Finset.mem_image_of_mem _ hP
  calc ∑ P ∈ 𝒯.T, P.I.length * (P.I.length / 𝒯.I.length) ^ (2 * N)
      = ∑ j ∈ 𝒯.T.image jf, ∑ P ∈ 𝒯.T.filter (fun P => jf P = j),
          P.I.length * (P.I.length / 𝒯.I.length) ^ (2 * N) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ j ∈ 𝒯.T.image jf, ((1 / 2 : ℝ) ^ j) ^ (2 * N) *
          ∑ P ∈ 𝒯.T.filter (fun P => jf P = j), P.I.length := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun P hP => ?_
        have h1 := Finset.mem_filter.1 hP
        have : P.I.length / 𝒯.I.length = (1 / 2 : ℝ) ^ j := by
          rw [hlen P h1.1, h1.2]; field_simp
        rw [this]; ring
    _ ≤ ∑ j ∈ 𝒯.T.image jf, ((1 / 2 : ℝ) ^ j) ^ (2 * N) * 𝒯.I.length :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hclass j) (by positivity)
    _ = (∑ j ∈ 𝒯.T.image jf, ((1 / 2 : ℝ) ^ j) ^ (2 * N)) * 𝒯.I.length := by
        rw [Finset.sum_mul]
    _ ≤ 4 / 3 * 𝒯.I.length :=
        mul_le_mul_of_nonneg_right (sum_geometric_le _ hN) hIT.le

/-- **The far-field bound for one packet** (L1387-L1390): for `P = (I, ω_u)` with `I ⊆ J` and `f`
bounded by `1` and vanishing on `3J`, `|⟨f, φ_P⟩| ≤ A |I|^{1/2} (|I|/|J|)^N`, with `A` depending
only on `N`. -/
theorem Multitile.exists_norm_coeff_le_far (N : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (ρ : Idx) (ch : ProfileChoice) (P : Multitile ρ) (J : Dyadic),
      P.I.toSet ⊆ J.toSet → ∀ {f : ℝ → ℂ}, (∀ᵐ x, ‖f x‖ ≤ 1) → (∀ x ∈ J.dilate 3, f x = 0) →
      ‖P.coeff ch f‖ ≤ A * √P.I.length * (P.I.length / J.length) ^ N := by
  obtain ⟨A₀, hA₀, hA⟩ := Multitile.exists_norm_wavePacket_le (N + 2)
  refine ⟨2 * A₀, by positivity, fun ρ ch P J hPJ f hf hf0 => ?_⟩
  have hL := P.I.length_pos
  have hLT := J.length_pos
  set L := P.I.length with hLdef
  set LT := J.length with hLT_def
  set r : ℝ := L / LT with hr
  have hr0 : 0 < r := by positivity
  set B : ℝ → ℝ := fun x => A₀ * (√L)⁻¹ * r ^ N * (1 + |x - P.I.center| / L) ^ (-(2 : ℤ)) with hB
  have hBint : Integrable B := by
    have := integrable_one_add_abs_div_zpow (N := 2) (le_refl 2) P.I.center hL
    have h22 : (-((2 : ℕ) : ℤ)) = -(2 : ℤ) := by norm_num
    rw [h22] at this
    exact this.const_mul _
  have hpt : ∀ᵐ x, ‖f x * (starRingEnd ℂ) (P.wavePacket ch x)‖ ≤ B x := by
    filter_upwards [hf] with x hfx
    by_cases hx : x ∈ J.dilate 3
    · rw [hf0 x hx, zero_mul, norm_zero]
      have : 0 ≤ (1 + |x - P.I.center| / L) ^ (-(2 : ℤ)) := by positivity
      simp only [hB]; positivity
    · rw [norm_mul, Complex.norm_conj]
      -- `|x - c(I)| ≥ |J|`
      have h1 := Dyadic.half_le_abs_of_not_mem_dilate hx
      have h2 : |P.I.center - J.center| ≤ LT / 2 :=
        Dyadic.abs_sub_center_le (hPJ P.I.center_mem_toSet)
      have h3 : LT ≤ |x - P.I.center| := by
        have : |x - J.center| ≤ |x - P.I.center| + |P.I.center - J.center| := by
          have := abs_add_le (x - P.I.center) (P.I.center - J.center)
          simpa using this
        linarith
      set t : ℝ := |x - P.I.center| / L with ht
      have ht0 : 0 ≤ t := by positivity
      have ht1 : LT / L ≤ t := by rw [ht]; exact div_le_div_of_nonneg_right h3 hL.le
      have hφ := hA ρ ch P x
      rw [← hLdef, ← ht] at hφ
      have h4 : ((1 + t) ^ N)⁻¹ ≤ r ^ N := by
        have : (LT / L) ^ N ≤ (1 + t) ^ N :=
          pow_le_pow_left₀ (by positivity) (by linarith) N
        calc ((1 + t) ^ N)⁻¹ ≤ ((LT / L) ^ N)⁻¹ := inv_anti₀ (by positivity) this
          _ = r ^ N := by rw [← inv_pow, hr, inv_div]
      have h5 : (1 + t) ^ (-((N + 2 : ℕ) : ℤ)) ≤ r ^ N * (1 + t) ^ (-(2 : ℤ)) := by
        rw [zpow_neg, zpow_natCast, zpow_neg, zpow_ofNat, pow_add, mul_inv]
        exact mul_le_mul_of_nonneg_right h4 (by positivity)
      calc ‖f x‖ * ‖P.wavePacket ch x‖ ≤ 1 * (A₀ * (√L)⁻¹ * (1 + t) ^ (-((N + 2 : ℕ) : ℤ))) :=
            mul_le_mul hfx hφ (norm_nonneg _) zero_le_one
        _ ≤ A₀ * (√L)⁻¹ * (r ^ N * (1 + t) ^ (-(2 : ℤ))) := by
            rw [one_mul]
            exact mul_le_mul_of_nonneg_left h5 (by positivity)
        _ = B x := by simp only [hB, ht]; ring
  have h1 : ‖P.coeff ch f‖ ≤ ∫ x, B x := by
    unfold Multitile.coeff pairing
    exact norm_integral_le_of_norm_le hBint hpt
  refine h1.trans (le_of_eq ?_)
  simp only [hB]
  rw [integral_const_mul]
  have h22 := integral_one_add_abs_div_zpow (N := 2) (le_refl 2) P.I.center hL
  have h23 : (-((2 : ℕ) : ℤ)) = -(2 : ℤ) := by norm_num
  rw [h23] at h22
  rw [h22]
  have hs : √L * √L = L := Real.mul_self_sqrt hL.le
  have hs0 : 0 < √L := Real.sqrt_pos.2 hL
  norm_num
  field_simp
  nlinarith [hs]

/-- **Far-field tail** ([O+] L1387-L1394): for every
`N ≥ 1` there is `K` (independent of everything below) such that for every tree `T` of
`ρ`-multitiles with (separationprop2) (neither `l`-overlapping nor (separationofscales) is
needed; `ρ` any `1`- or `2`-index with `m, n ∈ {1, …, 4}`) and every
`f'` with `|f'| ≤ 1_{ℝ ∖ 3 I_T}` (bounded by `1`, vanishing on `3 I_T`):
`|⟨f', φ_P⟩| ≤ K |I|^{1/2} (|I|/|I_T|)^N` for each `P ∈ T`, and `∑_{P ∈ T} |⟨f', φ_P⟩|² ≤ K |I_T|`.
(The printed exponent `N - 1` is covered by the freedom in `N`.) -/
theorem exists_far_field_tail (N : ℕ) (hN : 1 ≤ N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ},
      AdmissibleConstants C₁ C₂ C₃ → ρ.IsStd → ∀ (ch : ProfileChoice) (𝒯 : MultitileTree ρ),
      𝒯.IsTree C₁ C₂ M → SeparationProp2 C₁ (𝒯.T : Set (Multitile ρ)) →
      ∀ {f : ℝ → ℂ}, (∀ᵐ x, ‖f x‖ ≤ 1) → (∀ x ∈ 𝒯.I.dilate 3, f x = 0) →
        (∀ P ∈ 𝒯.T, ‖P.coeff ch f‖ ≤ K * √P.I.length * (P.I.length / 𝒯.I.length) ^ N) ∧
        ∑ P ∈ 𝒯.T, ‖P.coeff ch f‖ ^ 2 ≤ K * 𝒯.I.length := by
  obtain ⟨A, hA0, hA⟩ := Multitile.exists_norm_coeff_le_far N
  refine ⟨A + 2 * A ^ 2, by positivity,
    fun {ρ} _ {C₁ C₂ C₃} {M} hC hρ ch 𝒯 hT hsep f hf hf0 => ⟨fun P hP => ?_, ?_⟩⟩
  · have h1 := hA ρ ch P 𝒯.I (hT.time P hP) hf hf0
    refine h1.trans ?_
    have : 0 ≤ √P.I.length * (P.I.length / 𝒯.I.length) ^ N := by
      have := P.I.length_pos; have := 𝒯.I.length_pos; positivity
    nlinarith [sq_nonneg A]
  · have hIT := 𝒯.I.length_pos
    have hsum := sum_length_mul_ratio_pow_le hC hρ 𝒯 hT hsep hN
    calc ∑ P ∈ 𝒯.T, ‖P.coeff ch f‖ ^ 2
        ≤ ∑ P ∈ 𝒯.T, A ^ 2 * (P.I.length * (P.I.length / 𝒯.I.length) ^ (2 * N)) := by
          refine Finset.sum_le_sum fun P hP => ?_
          have h1 := hA ρ ch P 𝒯.I (hT.time P hP) hf hf0
          have h2 : 0 ≤ ‖P.coeff ch f‖ := norm_nonneg _
          have hL := P.I.length_pos
          calc ‖P.coeff ch f‖ ^ 2 ≤ (A * √P.I.length * (P.I.length / 𝒯.I.length) ^ N) ^ 2 :=
                pow_le_pow_left₀ h2 h1 2
            _ = A ^ 2 * (P.I.length * (P.I.length / 𝒯.I.length) ^ (2 * N)) := by
                rw [mul_pow, mul_pow, Real.sq_sqrt hL.le, ← pow_mul, mul_comm N 2]; ring
      _ = A ^ 2 * ∑ P ∈ 𝒯.T, P.I.length * (P.I.length / 𝒯.I.length) ^ (2 * N) := by
          rw [Finset.mul_sum]
      _ ≤ A ^ 2 * (4 / 3 * 𝒯.I.length) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ (A + 2 * A ^ 2) * 𝒯.I.length := by nlinarith [sq_nonneg A]

/-! ### The universal energy bound -/

/-- The coefficient `⟨f, φ_P⟩` of a bounded measurable `f` is an absolutely convergent integral. -/
theorem integrable_mul_conj_wavePacketOf_of_bdd {χ : ℝ → ℝ} (hχ : IsProfile χ) {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f volume) {B : ℝ} (hB : ∀ᵐ x, ‖f x‖ ≤ B) (I J : Dyadic) :
    Integrable (fun x => f x * (starRingEnd ℂ) (wavePacketOf χ I J x)) := by
  have hc : Integrable (fun x => (starRingEnd ℂ) (wavePacketOf χ I J x)) :=
    (hχ.integrable_wavePacketOf I J).norm.mono'
      (Complex.continuous_conj.comp (hχ.continuous_wavePacketOf I J)).aestronglyMeasurable
      (Eventually.of_forall fun x => by simp)
  exact hc.bdd_mul hf hB

/-- `∫ |f'|² ≤ |3 I|` for `f'` bounded by `1` and supported in `3 I`. -/
theorem integral_norm_sq_le_of_support_dilate {g : ℝ → ℂ} (hB : ∀ᵐ x, ‖g x‖ ≤ 1) (I : Dyadic)
    (hsupp : ∀ x ∉ I.dilate 3, g x = 0) :
    ∫ x, ‖g x‖ ^ 2 ≤ 3 * I.length := by
  have hmeas : MeasurableSet (I.dilate 3) := measurableSet_Ico
  have hI := I.length_pos
  have h1 : ∀ᵐ x, ‖g x‖ ^ 2 ≤ (I.dilate 3).indicator (fun _ => (1 : ℝ)) x := by
    filter_upwards [hB] with x hx
    by_cases hxm : x ∈ I.dilate 3
    · rw [Set.indicator_of_mem hxm]
      nlinarith [norm_nonneg (g x)]
    · rw [Set.indicator_of_notMem hxm, hsupp x hxm]; simp
  have hint : Integrable ((I.dilate 3).indicator (fun _ => (1 : ℝ))) :=
    (integrable_indicator_iff hmeas).2
      (integrableOn_const (by rw [Dyadic.dilate, Real.volume_Ico]; exact ENNReal.ofReal_ne_top))
  calc ∫ x, ‖g x‖ ^ 2 ≤ ∫ x, (I.dilate 3).indicator (fun _ => (1 : ℝ)) x := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity) hint h1
    _ = 3 * I.length := by
        rw [integral_indicator hmeas, setIntegral_const, smul_eq_mul, mul_one]
        simp only [Measure.real, Dyadic.dilate, Real.volume_Ico]
        rw [ENNReal.toReal_ofReal (by nlinarith)]
        ring

/-- **The sum of squared coefficients of an `l`-overlapping tree is at most `K |I_T|`**, for
`|f| ≤ 1`. Proof as in L1368-L1394: split `f = f' + f''`, `f' = 1_{3I_T} f`; tree orthogonality
and duality for `f'`, the far-field tail for `f''`. -/
theorem exists_sum_norm_sq_coeff_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ},
      AdmissibleConstants C₁ C₂ C₃ → ρ.IsStd → ∀ (ch : ProfileChoice) (𝒯 : MultitileTree ρ),
      𝒯.IsTree C₁ C₂ M → 𝒯.IsOverlapping C₂ → Separated C₁ C₂ C₃ (𝒯.T : Set (Multitile ρ)) →
      ∀ {f : ℝ → ℂ}, AEStronglyMeasurable f volume → (∀ᵐ x, ‖f x‖ ≤ 1) →
        ∑ P ∈ 𝒯.T, ‖P.coeff ch f‖ ^ 2 ≤ K * 𝒯.I.length := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_tree_orthogonality
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_far_field_tail 1 le_rfl
  refine ⟨6 * (K₁ + 1) + 2 * K₂, by positivity,
    fun {ρ} _ {C₁ C₂ C₃} {M} hC hρ ch 𝒯 hT hov hsep f hfm hf => ?_⟩
  have hIT := 𝒯.I.length_pos
  set S : Set ℝ := 𝒯.I.dilate 3 with hS
  have hSm : MeasurableSet S := measurableSet_Ico
  set f' : ℝ → ℂ := S.indicator f with hf'
  set f'' : ℝ → ℂ := Sᶜ.indicator f with hf''
  have hff : ∀ x, f x = f' x + f'' x := fun x => by
    simp only [hf', hf'']
    exact (congrFun (Set.indicator_self_add_compl S f) x).symm
  have hf'b : ∀ᵐ x, ‖f' x‖ ≤ 1 := by
    filter_upwards [hf] with x hx
    by_cases h : x ∈ S
    · simpa [hf', h] using hx
    · simp [hf', h]
  have hf''b : ∀ᵐ x, ‖f'' x‖ ≤ 1 := by
    filter_upwards [hf] with x hx
    by_cases h : x ∈ S
    · simp [hf'', h]
    · simpa [hf'', h] using hx
  have hf'm : AEStronglyMeasurable f' volume := hfm.indicator hSm
  have hf''m : AEStronglyMeasurable f'' volume := hfm.indicator hSm.compl
  have hf'supp : ∀ x ∉ 𝒯.I.dilate 3, f' x = 0 := fun x hx => by simp [hf', hS, hx]
  have hf''supp : ∀ x ∈ 𝒯.I.dilate 3, f'' x = 0 := fun x hx => by
    have : x ∈ S := hx
    simp [hf'', this]
  -- the near part
  have hf'mem : MemLp f' 2 volume :=
    memLp_two_of_bounded_of_support_subset_dilate hf'm hf'b (I := 𝒯.I) (C := 3)
      (fun x hx => by
        by_contra h
        exact hx (hf'supp x h))
  have hnear : ∑ P ∈ 𝒯.T, ‖P.coeff ch f'‖ ^ 2 ≤ (K₁ + 1) * (3 * 𝒯.I.length) := by
    have h1 := sum_norm_sq_pairing_le_of_orthogonality 𝒯.T (fun P : Multitile ρ => P.wavePacket ch)
      (fun P => ch.isProfile.memLp_wavePacketOf P.I P.ωu) (K := K₁ + 1) (by linarith)
      (fun c => by
        have := hK₁ hC hρ ch 𝒯 hT hov hsep c
        simp only [smul_eq_mul] at this
        nlinarith [Finset.sum_nonneg (fun P (_ : P ∈ 𝒯.T) => sq_nonneg ‖c P‖)]) hf'mem
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_left (integral_norm_sq_le_of_support_dilate hf'b 𝒯.I hf'supp)
      (by linarith)
  -- the far part
  have hfar : ∑ P ∈ 𝒯.T, ‖P.coeff ch f''‖ ^ 2 ≤ K₂ * 𝒯.I.length :=
    (hK₂ hC hρ ch 𝒯 hT hsep.prop2 hf''b hf''supp).2
  -- combine
  have hsplit : ∀ P ∈ 𝒯.T, ‖P.coeff ch f‖ ^ 2 ≤
      2 * ‖P.coeff ch f'‖ ^ 2 + 2 * ‖P.coeff ch f''‖ ^ 2 := by
    intro P hP
    have : P.coeff ch f = P.coeff ch f' + P.coeff ch f'' := by
      have hi1 : Integrable (fun x => f' x * (starRingEnd ℂ) (P.wavePacket ch x)) :=
        integrable_mul_conj_wavePacketOf_of_bdd ch.isProfile hf'm hf'b P.I P.ωu
      have hi2 : Integrable (fun x => f'' x * (starRingEnd ℂ) (P.wavePacket ch x)) :=
        integrable_mul_conj_wavePacketOf_of_bdd ch.isProfile hf''m hf''b P.I P.ωu
      unfold Multitile.coeff pairing
      rw [← integral_add hi1 hi2]
      congr 1; funext x
      rw [hff x]; ring
    rw [this]
    have h1 := norm_add_le (P.coeff ch f') (P.coeff ch f'')
    nlinarith [norm_nonneg (P.coeff ch f'), norm_nonneg (P.coeff ch f''),
      sq_nonneg (‖P.coeff ch f'‖ - ‖P.coeff ch f''‖), norm_nonneg (P.coeff ch f' + P.coeff ch f'')]
  calc ∑ P ∈ 𝒯.T, ‖P.coeff ch f‖ ^ 2
      ≤ ∑ P ∈ 𝒯.T, (2 * ‖P.coeff ch f'‖ ^ 2 + 2 * ‖P.coeff ch f''‖ ^ 2) :=
        Finset.sum_le_sum hsplit
    _ = 2 * ∑ P ∈ 𝒯.T, ‖P.coeff ch f'‖ ^ 2 + 2 * ∑ P ∈ 𝒯.T, ‖P.coeff ch f''‖ ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 2 * ((K₁ + 1) * (3 * 𝒯.I.length)) + 2 * (K₂ * 𝒯.I.length) := by linarith
    _ = (6 * (K₁ + 1) + 2 * K₂) * 𝒯.I.length := by ring

/-- **The universal energy bound** ([O+] `univ-den-ene-bound`, L1357-L1400): there is a
constant `K` such that for every `1`- or `2`-index `ρ` with `m, n ∈ {1, …, 4}`, every admissible
`C₁ > C₂ > C₃ ≥ 1`, every profile choice, every collection `S` of `ρ`-multitiles satisfying
(separationofscales) and (separationprop2), and every measurable `f` with `|f| ≤ 1` (in particular
`|f| ≤ 1_F`), `energy(S) ≤ K`. -/
theorem exists_energy_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ},
      AdmissibleConstants C₁ C₂ C₃ → ρ.IsStd → ∀ (ch : ProfileChoice) {f : ℝ → ℂ},
      AEStronglyMeasurable f volume → (∀ᵐ x, ‖f x‖ ≤ 1) →
      ∀ (S : Set (Multitile ρ)), Separated C₁ C₂ C₃ S →
        energy C₁ C₂ M ch f S ≤ ENNReal.ofReal K := by
  obtain ⟨K, hK0, hK⟩ := exists_sum_norm_sq_coeff_le
  refine ⟨√K, Real.sqrt_nonneg _,
    fun {ρ} _ {C₁ C₂ C₃} {M} hC hρ ch f hfm hf S hS => ?_⟩
  unfold energy energyOf
  refine iSup_le fun 𝒯 => iSup_le fun hT => iSup_le fun hov => iSup_le fun hsub => ?_
  have hsep : Separated C₁ C₂ C₃ (𝒯.T : Set (Multitile ρ)) := hS.mono hsub
  have hsum := hK hC hρ ch 𝒯 hT hov hsep hfm hf
  have hIT := 𝒯.I.length_pos
  have h1 : ∑ P ∈ 𝒯.T, ‖P.coeff ch f‖ₑ ^ 2 ≤ ENNReal.ofReal (K * 𝒯.I.length) := by
    have : ∑ P ∈ 𝒯.T, ‖P.coeff ch f‖ₑ ^ 2 = ENNReal.ofReal (∑ P ∈ 𝒯.T, ‖P.coeff ch f‖ ^ 2) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun P _ => by positivity)]
      refine Finset.sum_congr rfl fun P _ => ?_
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    rw [this]
    exact ENNReal.ofReal_le_ofReal hsum
  calc ((ENNReal.ofReal 𝒯.I.length)⁻¹ * ∑ P ∈ 𝒯.T, ‖P.coeff ch f‖ₑ ^ 2) ^ (1 / 2 : ℝ)
      ≤ ((ENNReal.ofReal 𝒯.I.length)⁻¹ * ENNReal.ofReal (K * 𝒯.I.length)) ^ (1 / 2 : ℝ) := by
        gcongr
    _ = ENNReal.ofReal (√K) := by
        rw [← ENNReal.ofReal_inv_of_pos hIT, ← ENNReal.ofReal_mul (inv_pos.2 hIT).le]
        have : (𝒯.I.length)⁻¹ * (K * 𝒯.I.length) = K := by field_simp
        rw [this, ENNReal.ofReal_rpow_of_nonneg hK0 (by norm_num), Real.sqrt_eq_rpow]

/-! ### The universal density bound -/

/-- **The universal density bound** ([O+] `univ-den-ene-bound`, L1365-L1368): for every
collection `S` of multitiles, every measurable `E` (indeed every `E`), and linearizing data with
`∑_k |a_k(x)|^{r'} = 1` (`r > 1`), `density(S) ≤ (∫ (1 + |x|)^{-4})^{1/r'} = (2/3)^{1/r'} ≤ 1`;
here `density(S) ≤ 1 < 3`. -/
theorem density_le_one {ρ : Idx} [Fact ρ.IsOneOrTwo] (C₁ C₂ : ℝ) (M : ℤ) {r : ℝ} (hr : 1 < r)
    (L : Linearization r) (E : Set ℝ) (S : Set (Multitile ρ)) :
    density C₁ C₂ M L E S ≤ 1 := by
  have hr' : 0 ≤ Real.conjExponent r := (div_pos (by linarith) (by linarith)).le
  unfold density
  refine iSup_le fun 𝒯 => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => ?_
  have hIT := 𝒯.I.length_pos
  -- the integrand is at most the weight
  have hsum : ∀ x : ℝ, ∑ k : Fin L.K, ‖L.a k x‖ₑ ^ Real.conjExponent r *
      (𝒯.ωT C₂).indicator (fun _ => (1 : ℝ≥0∞)) (L.ξ k.castSucc x) ≤ 1 := by
    intro x
    calc ∑ k : Fin L.K, ‖L.a k x‖ₑ ^ Real.conjExponent r *
          (𝒯.ωT C₂).indicator (fun _ => (1 : ℝ≥0∞)) (L.ξ k.castSucc x)
        ≤ ∑ k : Fin L.K, ‖L.a k x‖ₑ ^ Real.conjExponent r := by
          refine Finset.sum_le_sum fun k _ => ?_
          refine mul_le_of_le_one_right zero_le ?_
          exact Set.indicator_le_self' (fun _ _ => zero_le) _ |>.trans le_rfl
      _ = ENNReal.ofReal (∑ k : Fin L.K, ‖L.a k x‖ ^ Real.conjExponent r) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr', ofReal_norm]
      _ = 1 := by rw [L.sum_norm_rpow x]; simp
  have hw : Integrable (fun x : ℝ => (1 + |x - 𝒯.I.center| / 𝒯.I.length) ^ (-(4 : ℕ) : ℤ)) :=
    integrable_one_add_abs_div_zpow (N := 4) (by norm_num) 𝒯.I.center hIT
  have hwint : ∫⁻ x, ENNReal.ofReal ((1 + |x - 𝒯.I.center| / 𝒯.I.length) ^ (-4 : ℤ)) =
      ENNReal.ofReal (𝒯.I.length * (2 / 3)) := by
    have h4 : (-((4 : ℕ) : ℤ)) = (-4 : ℤ) := by norm_num
    have := integral_one_add_abs_div_zpow (N := 4) (by norm_num) 𝒯.I.center hIT
    rw [h4] at this hw
    rw [← ofReal_integral_eq_lintegral_ofReal hw (Eventually.of_forall fun x => by positivity),
      this]
    norm_num
  have hlint : ∫⁻ x in E, ENNReal.ofReal ((1 + |x - 𝒯.I.center| / 𝒯.I.length) ^ (-4 : ℤ)) *
      ∑ k : Fin L.K, ‖L.a k x‖ₑ ^ Real.conjExponent r *
        (𝒯.ωT C₂).indicator (fun _ => (1 : ℝ≥0∞)) (L.ξ k.castSucc x) ≤
      ENNReal.ofReal (𝒯.I.length * (2 / 3)) := by
    calc _ ≤ ∫⁻ x in E, ENNReal.ofReal ((1 + |x - 𝒯.I.center| / 𝒯.I.length) ^ (-4 : ℤ)) :=
          lintegral_mono fun x => mul_le_of_le_one_right zero_le (hsum x)
      _ ≤ ∫⁻ x, ENNReal.ofReal ((1 + |x - 𝒯.I.center| / 𝒯.I.length) ^ (-4 : ℤ)) :=
          setLIntegral_le_lintegral _ _
      _ = _ := hwint
  have h1 : (ENNReal.ofReal 𝒯.I.length)⁻¹ * ∫⁻ x in E, ENNReal.ofReal
      ((1 + |x - 𝒯.I.center| / 𝒯.I.length) ^ (-4 : ℤ)) * ∑ k : Fin L.K, ‖L.a k x‖ₑ ^
        Real.conjExponent r * (𝒯.ωT C₂).indicator (fun _ => (1 : ℝ≥0∞)) (L.ξ k.castSucc x) ≤ 1 := by
    calc _ ≤ (ENNReal.ofReal 𝒯.I.length)⁻¹ * ENNReal.ofReal (𝒯.I.length * (2 / 3)) :=
          by gcongr
      _ = ENNReal.ofReal (2 / 3) := by
          rw [← ENNReal.ofReal_inv_of_pos hIT, ← ENNReal.ofReal_mul (inv_pos.2 hIT).le]
          congr 1; field_simp
      _ ≤ 1 := by
          rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
  exact ENNReal.rpow_le_one h1 (by positivity)

/-- **`univ-den-ene-bound`** ([O+] L1357-L1363): density and energy of every separated family of
`ρ`-multitiles are bounded by one universal constant `K` (independent of `ρ`, the constants, the
profile choice, `f`, `E`, the linearizing data, the family and `M`). The hypothesis
`|f| ≤ 1_F` is used only through `|f| ≤ 1`. -/
theorem exists_univ_den_ene_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ},
      AdmissibleConstants C₁ C₂ C₃ → ρ.IsStd → ∀ (ch : ProfileChoice) {f : ℝ → ℂ},
      AEStronglyMeasurable f volume → (∀ᵐ x, ‖f x‖ ≤ 1) →
      ∀ {r : ℝ}, 1 < r → ∀ (L : Linearization r) (E : Set ℝ) (S : Set (Multitile ρ)),
        Separated C₁ C₂ C₃ S →
          density C₁ C₂ M L E S ≤ ENNReal.ofReal K ∧ energy C₁ C₂ M ch f S ≤ ENNReal.ofReal K := by
  obtain ⟨K, hK0, hK⟩ := exists_energy_le
  refine ⟨max 1 K, le_max_of_le_left zero_le_one,
    fun {ρ} _ {C₁ C₂ C₃} {M} hC hρ ch f hfm hf r hr L E S hS => ⟨?_, ?_⟩⟩
  · exact (density_le_one C₁ C₂ M hr L E S).trans
      (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · exact (hK hC hρ ch hfm hf S hS).trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))

/-- **Tree orthogonality in the form of L1373-L1380**: for `f' ∈ L²` (indeed any `f'`),
`∫ |∑_{P ∈ T} ⟨f', φ_P⟩ φ_P|² ≤ K ∑_{P ∈ T} |⟨f', φ_P⟩|²`, i.e.
`‖∑ ⟨f', φ_P⟩ φ_P‖_{L²} ≲ (∑ |⟨f', φ_P⟩|²)^{1/2}`. -/
theorem exists_tree_orthogonality_coeff :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ},
      AdmissibleConstants C₁ C₂ C₃ → ρ.IsStd → ∀ (ch : ProfileChoice) (𝒯 : MultitileTree ρ),
      𝒯.IsTree C₁ C₂ M → 𝒯.IsOverlapping C₂ → Separated C₁ C₂ C₃ (𝒯.T : Set (Multitile ρ)) →
      ∀ f : ℝ → ℂ,
        ∫ x, ‖∑ P ∈ 𝒯.T, P.coeff ch f • P.wavePacket ch x‖ ^ 2 ≤
          K * ∑ P ∈ 𝒯.T, ‖P.coeff ch f‖ ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := exists_tree_orthogonality
  exact ⟨K, hK0, fun {ρ} _ {C₁ C₂ C₃} {M} hC hρ ch 𝒯 hT hov hsep f =>
    hK hC hρ ch 𝒯 hT hov hsep (fun P => P.coeff ch f)⟩

end PrimeCarleson.Proof.Oplus
