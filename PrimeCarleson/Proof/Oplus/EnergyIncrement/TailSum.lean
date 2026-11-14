module

public import PrimeCarleson.Proof.Oplus.EnergyIncrement.TailWeight
public import PrimeCarleson.Proof.Oplus.Estimates.All

/-!
# The tail weight sum for a tree ([O+] L1627-L1644)

Source: [O+] `energyincrementprop`, L1627–L1644: "`∑_{P ∈ S_j} |I_P| ⟨w_I, 1_{ℝ∖I_{S_j}}⟩² ≲
∑_{l : 2^l ≤ |I_{S_j}|} 2^l ∑_{P ∈ S_j : |I| = 2^l} ⟨w_I, 1_{ℝ∖I_{S_j}}⟩ ≲ |I_{S_j}| sup_l ∑_{P ∈
S_j : |I| = 2^l} ⟨w_I, 1_{ℝ∖I_{S_j}}⟩ ≲ |I_{S_j}|`; one may check that for each `l`,
`∑_{P ∈ S_j : |I| = 2^l} ⟨w_I, 1_{ℝ∖I_{S_j}}⟩ ≲ 1`".

`exists_sum_length_mul_tail_le`: for every tree `𝒯` (of `ρ`-multitiles, `ρ` any `1`- or `2`-index
with `m, n ∈ {1, …, 4}`) with (separationprop2) and every `N ≥ 3`, with one absolute constant `K`,
(i) for every scale `k`, `∑_{P ∈ 𝒯, k_I = k} ⟨w_I, 1_{ℝ∖I_𝒯}⟩ ≤ K` (the packets of one scale have
disjoint time intervals, Observation (iii); `exists_sum_integral_weight_compl_le`),
(ii) `∑_P |I_P| ⟨w_I, 1_{ℝ∖I_𝒯}⟩ ≤ K |I_𝒯|` (counting by scales, `∑ 2^{-d} ≤ 2`),
(iii) `∑_P |I_P| ⟨w_I, 1_{ℝ∖I_𝒯}⟩² ≤ K |I_𝒯|` (the inner products are `≤ ∫ w_I ≤ 1`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- The inner product `⟨w_I, 1_{ℝ ∖ I_𝒯}⟩` is at most `∫ w_I = 2/(N-1) ≤ 1` for `N ≥ 3`. -/
theorem integral_weight_compl_le_one {N : ℕ} (hN : 3 ≤ N) (I IS : Dyadic) :
    ∫ x in IS.toSetᶜ, I.weight N x ≤ 1 := by
  have hint := I.integrable_weight (show 2 ≤ N by omega)
  have h1 : ∫ x in IS.toSetᶜ, I.weight N x ≤ ∫ x, I.weight N x :=
    setIntegral_le_integral hint (Filter.Eventually.of_forall fun x => I.weight_nonneg N x)
  rw [Dyadic.integral_weight (show 2 ≤ N by omega)] at h1
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  refine h1.trans ?_
  rw [div_le_one (by linarith)]
  linarith

section Tree

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ}

/-- Packets of one scale in a tree have distinct time intervals (Observation (iii)). -/
theorem Multitile.I_injOn_scale (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    (𝒯 : MultitileTree ρ) (hT : 𝒯.IsTree C₁ C₂ M)
    (hp2 : SeparationProp2 C₁ (𝒯.T : Set (Multitile ρ))) (k : ℤ) :
    Set.InjOn Multitile.I ((𝒯.T.filter (fun P => P.I.k = k) : Finset (Multitile ρ)) :
      Set (Multitile ρ)) := by
  classical
  intro P hP P' hP' hI
  by_contra hne
  have h1 := Finset.mem_filter.1 (Finset.mem_coe.1 hP)
  have h2 := Finset.mem_filter.1 (Finset.mem_coe.1 hP')
  have hlen : P.ωu.length = P'.ωu.length := by
    rw [Dyadic.length_eq_iff]
    have := P.area
    have := P'.area
    omega
  have hd := treeobs_disjoint_time hC hρ 𝒯 hT hp2 h1.1 h2.1 hne hlen
  rw [hI] at hd
  have := Set.disjoint_iff_inter_eq_empty.1 hd
  rw [Set.inter_self] at this
  exact (Dyadic.toSet_nonempty P'.I).ne_empty this

/-- **The per-scale bound**: `∑_{P ∈ 𝒯 : k_I = k} ⟨w_I, 1_{ℝ∖I_𝒯}⟩ ≤ K_w`. -/
theorem sum_integral_weight_compl_scale_le {K : ℝ}
    (hK : ∀ (N : ℕ), 3 ≤ N → ∀ (IS : Dyadic) (k : ℤ) (A : Finset Dyadic),
      (∀ I ∈ A, I.k = k ∧ I.toSet ⊆ IS.toSet) → ∑ I ∈ A, ∫ x in IS.toSetᶜ, I.weight N x ≤ K)
    (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd) (N : ℕ) (hN : 3 ≤ N)
    (𝒯 : MultitileTree ρ) (hT : 𝒯.IsTree C₁ C₂ M)
    (hp2 : SeparationProp2 C₁ (𝒯.T : Set (Multitile ρ))) (k : ℤ) :
    ∑ P ∈ 𝒯.T.filter (fun P => P.I.k = k), ∫ x in 𝒯.I.toSetᶜ, P.I.weight N x ≤ K := by
  classical
  set F := 𝒯.T.filter (fun P => P.I.k = k) with hF
  have hinj := Multitile.I_injOn_scale hC hρ 𝒯 hT hp2 k
  have h1 : ∑ P ∈ F, ∫ x in 𝒯.I.toSetᶜ, P.I.weight N x =
      ∑ I ∈ F.image Multitile.I, ∫ x in 𝒯.I.toSetᶜ, I.weight N x := by
    rw [Finset.sum_image hinj]
  rw [h1]
  refine hK N hN 𝒯.I k _ fun I hI => ?_
  obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hI
  have h2 := Finset.mem_filter.1 hP
  exact ⟨h2.2, hT.time P h2.1⟩

/-- **The tail weight sum** (three forms), for a tree with (separationprop2). -/
theorem sum_length_mul_tail_le {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ (N : ℕ), 3 ≤ N → ∀ (IS : Dyadic) (k : ℤ) (A : Finset Dyadic),
      (∀ I ∈ A, I.k = k ∧ I.toSet ⊆ IS.toSet) → ∑ I ∈ A, ∫ x in IS.toSetᶜ, I.weight N x ≤ K)
    (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd) (N : ℕ) (hN : 3 ≤ N)
    (𝒯 : MultitileTree ρ) (hT : 𝒯.IsTree C₁ C₂ M)
    (hp2 : SeparationProp2 C₁ (𝒯.T : Set (Multitile ρ))) :
    ∑ P ∈ 𝒯.T, P.I.length * ∫ x in 𝒯.I.toSetᶜ, P.I.weight N x ≤ 2 * K * 𝒯.I.length := by
  classical
  have hIT := 𝒯.I.length_pos
  set τ : Multitile ρ → ℝ := fun P => ∫ x in 𝒯.I.toSetᶜ, P.I.weight N x with hτ
  set jf : Multitile ρ → ℕ := fun P => (𝒯.I.k - P.I.k).toNat with hjf
  have hlen : ∀ P ∈ 𝒯.T, P.I.length = 𝒯.I.length * (1 / 2) ^ jf P := fun P hP =>
    Dyadic.length_eq_mul_half_pow (hT.time P hP)
  have hmaps : ∀ P ∈ 𝒯.T, jf P ∈ 𝒯.T.image jf := fun P hP => Finset.mem_image_of_mem _ hP
  have hfib : ∀ d : ℕ, ∑ P ∈ 𝒯.T.filter (fun P => jf P = d), τ P ≤ K := by
    intro d
    have hsub : 𝒯.T.filter (fun P => jf P = d) ⊆ 𝒯.T.filter (fun P => P.I.k = 𝒯.I.k - d) := by
      intro P hP
      have h1 := Finset.mem_filter.1 hP
      refine Finset.mem_filter.2 ⟨h1.1, ?_⟩
      have hk : P.I.k ≤ 𝒯.I.k := Dyadic.k_le_of_toSet_subset (hT.time P h1.1)
      have : (𝒯.I.k - P.I.k).toNat = d := h1.2
      omega
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun P _ _ => ?_)
      (sum_integral_weight_compl_scale_le hK hC hρ N hN 𝒯 hT hp2 _)
    exact setIntegral_nonneg 𝒯.I.measurableSet_toSet.compl fun x _ => P.I.weight_nonneg N x
  calc ∑ P ∈ 𝒯.T, P.I.length * τ P
      = ∑ d ∈ 𝒯.T.image jf, ∑ P ∈ 𝒯.T.filter (fun P => jf P = d), P.I.length * τ P :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ d ∈ 𝒯.T.image jf, 𝒯.I.length * (1 / 2) ^ d *
          ∑ P ∈ 𝒯.T.filter (fun P => jf P = d), τ P := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun P hP => ?_
        have h1 := Finset.mem_filter.1 hP
        rw [hlen P h1.1, h1.2]
    _ ≤ ∑ d ∈ 𝒯.T.image jf, 𝒯.I.length * (1 / 2) ^ d * K :=
        Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left (hfib d) (by positivity)
    _ = 𝒯.I.length * K * ∑ d ∈ 𝒯.T.image jf, (1 / 2 : ℝ) ^ d := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        ring
    _ ≤ 𝒯.I.length * K * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_range.2 fun d hd => Nat.lt_succ_of_le
            (Finset.le_sup (f := id) hd)) fun d _ _ => by positivity) ?_
        exact sum_geometric_two_le _
    _ = 2 * K * 𝒯.I.length := by ring

/-- The squared tail sum: `∑_P |I_P| ⟨w_I, 1_{ℝ∖I_𝒯}⟩² ≤ 2K |I_𝒯|`. -/
theorem sum_length_mul_tail_sq_le {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ (N : ℕ), 3 ≤ N → ∀ (IS : Dyadic) (k : ℤ) (A : Finset Dyadic),
      (∀ I ∈ A, I.k = k ∧ I.toSet ⊆ IS.toSet) → ∑ I ∈ A, ∫ x in IS.toSetᶜ, I.weight N x ≤ K)
    (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd) (N : ℕ) (hN : 3 ≤ N)
    (𝒯 : MultitileTree ρ) (hT : 𝒯.IsTree C₁ C₂ M)
    (hp2 : SeparationProp2 C₁ (𝒯.T : Set (Multitile ρ))) :
    ∑ P ∈ 𝒯.T, P.I.length * (∫ x in 𝒯.I.toSetᶜ, P.I.weight N x) ^ 2 ≤ 2 * K * 𝒯.I.length := by
  refine le_trans (Finset.sum_le_sum fun P _ => ?_)
    (sum_length_mul_tail_le hK0 hK hC hρ N hN 𝒯 hT hp2)
  have h0 : 0 ≤ ∫ x in 𝒯.I.toSetᶜ, P.I.weight N x :=
    setIntegral_nonneg 𝒯.I.measurableSet_toSet.compl fun x _ => P.I.weight_nonneg N x
  have h1 := integral_weight_compl_le_one hN P.I 𝒯.I
  have := P.I.length_pos
  exact mul_le_mul_of_nonneg_left (pow_le_of_le_one h0 h1 two_ne_zero) this.le

end Tree

/-- **The tail weight sum** ([O+] `energyincrementprop`, L1627-L1644): there is an absolute constant
`K` such that for every `1`- or `2`-index `ρ` with `m, n ∈ {1, …, 4}`, every admissible
`C₁ > C₂ > C₃ ≥ 1`, every `N ≥ 3` and every tree `𝒯` with (separationprop2) (in particular every
`l`-overlapping tree `S_j` of the selection): (i) for each scale `k`,
`∑_{P ∈ 𝒯 : k_I = k} ⟨w_I, 1_{ℝ∖I_𝒯}⟩ ≤ K`; (ii) `∑_{P ∈ 𝒯} |I_P| ⟨w_I, 1_{ℝ∖I_𝒯}⟩ ≤ K |I_𝒯|`;
(iii) `∑_{P ∈ 𝒯} |I_P| ⟨w_I, 1_{ℝ∖I_𝒯}⟩² ≤ K |I_𝒯|`. -/
theorem exists_sum_length_mul_tail_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ},
      AdmissibleConstants C₁ C₂ C₃ → ρ.IsStd → ∀ (N : ℕ), 3 ≤ N → ∀ (𝒯 : MultitileTree ρ),
      𝒯.IsTree C₁ C₂ M → SeparationProp2 C₁ (𝒯.T : Set (Multitile ρ)) →
      (∀ k : ℤ, ∑ P ∈ 𝒯.T.filter (fun P => P.I.k = k), ∫ x in 𝒯.I.toSetᶜ, P.I.weight N x ≤ K) ∧
      ∑ P ∈ 𝒯.T, P.I.length * ∫ x in 𝒯.I.toSetᶜ, P.I.weight N x ≤ K * 𝒯.I.length ∧
      ∑ P ∈ 𝒯.T, P.I.length * (∫ x in 𝒯.I.toSetᶜ, P.I.weight N x) ^ 2 ≤ K * 𝒯.I.length := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_sum_integral_weight_compl_le
  refine ⟨2 * K₁, by positivity,
    fun {ρ} _ {C₁ C₂ C₃} {M} hC hρ N hN 𝒯 hT hp2 => ⟨fun k => ?_, ?_, ?_⟩⟩
  · exact le_trans (sum_integral_weight_compl_scale_le hK₁ hC hρ N hN 𝒯 hT hp2 k)
      (by linarith)
  · exact sum_length_mul_tail_le hK₁0 hK₁ hC hρ N hN 𝒯 hT hp2
  · exact sum_length_mul_tail_sq_le hK₁0 hK₁ hC hρ N hN 𝒯 hT hp2

end PrimeCarleson.Proof.Oplus
