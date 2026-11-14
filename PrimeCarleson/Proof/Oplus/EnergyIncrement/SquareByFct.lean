module

public import PrimeCarleson.Proof.Oplus.EnergyIncrement.Orthogonality
public import PrimeCarleson.Proof.Oplus.EnergyIncrement.TailSum
public import PrimeCarleson.Proof.Oplus.EnergyIncrement.SquareSum

/-!
# `etreeorth2`, `etreeorth22` and the squared-sum inequality `squarebyfct` ([O+] L1503-L1644)

Source: [O+], L1503–L1505; [O+], L1709–L1714 (L1709-L1737), L1503-L1644, `etreeorth2`,
`etreeorth22`, `claimofdisjointness`. All for an abstract subfamily `J ⊂ {0, …, n-1}` of the
selected trees of `IsSelection`, an abstract `g ∈ L²` and abstract bounds, so that one proof serves
`squarebyfct` (`g = f`, `J` everything) and `squarebyfctanalog` (`g = f' = 1_{2^{ℓ+5}J} f`, `J` the
subsequence `S_{j(ν)}`).

* `sum_integral_weight_le_compl`: the printed claim (L1583-L1590, without the square the source
  drops): `∑_{P'} ⟨w_I, 1_{I'}⟩ ≤ ⟨w_I, 1_{ℝ ∖ I_{S_j}}⟩`, for the `P'` with `|I'| < |I|` whose
  `C₃ ω_{u'}` contain a fixed point (`sup C₃ ω_u` or `inf C₃ ω_u`).
* `sum_norm_pairing_smaller_le`: for `P ∈ S_j`, `∑_{P' ∈ U, |I'| < |I|} |c_{P'}| |⟨φ_P, φ_{P'}⟩| ≤
  2 E K₀ |I|^{1/2} ⟨w_I, 1_{ℝ ∖ I_{S_j}}⟩` (the bounds `|c_{P'}| ≤ E |I'|^{1/2}`, the
  Schwartz estimate, `⟨φ_P, φ_{P'}⟩ = 0` unless the `C₃ ω_u`, `C₃ ω_{u'}` meet, in which case
  `sup` or `inf C₃ ω_u ∈ C₃ ω_{u'}`).
* `sum_sum_smaller_scale_le` (etreeorth2, via etreeorth22 and the tail weight sum).
* `sum_length_le_of_selection`: `λ² ∑_{j ∈ J} |I_{S_j}| ≤ K E² B`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

section Claim

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ} {ch : ProfileChoice} {f : ℝ → ℂ}
  {e : ℝ} {𝔓 : Finset (Multitile ρ)} {n : ℕ} {S T : ℕ → MultitileTree ρ}

omit [Fact ρ.IsOneOrTwo] in
/-- `⟨φ_P, φ_{P'}⟩ = 0` when the `C₃`-dilates of `ω_u, ω_{u'}` are disjoint. -/
theorem pairing_eq_zero_of_disjoint_ωuDil (hC : AdmissibleConstants C₁ C₂ C₃)
    (ch ch' : ProfileChoice) {P P' : Multitile ρ}
    (hd : Disjoint (P.ωuDil C₃) (P'.ωuDil C₃)) :
    pairing (P.wavePacket ch) (P'.wavePacket ch') = 0 :=
  pairing_wavePacketOf_eq_zero_of_support ch.isProfile ch'.isProfile P.I P.ωu P'.I P'.ωu
    ((subset_tsupport _).trans (hC.packet_support ch P.I P.ωu))
    ((subset_tsupport _).trans (hC.packet_support ch' P'.I P'.ωu)) hd

/-- **`claimofdisjointness`, the weight-integral form** ([O+] L1583-L1622): for `P ∈ S_j` and a
finite set `A` of multitiles of the selected trees with `|I'| < |I|`, `Near C₃ P P'` and a common
point `x₀ ∈ C₃ ω_{u'}` (`x₀ = sup C₃ ω_u` or `inf C₃ ω_u`), the intervals `I'` are pairwise
disjoint and disjoint from `I_{S_j}`, so `∑_{P' ∈ A} ⟨w_I, 1_{I'}⟩ ≤ ⟨w_I, 1_{ℝ ∖ I_{S_j}}⟩`. -/
theorem sum_integral_weight_le_compl {N : ℕ} (hN : 2 ≤ N) (hC : AdmissibleConstants C₁ C₂ C₃)
    (hρ : ρ.IsStd) (hsep : Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ)))
    (sel : IsSelection C₁ C₂ M ch f e 𝔓 n S T) {j : ℕ} (hj : j < n) {P : Multitile ρ}
    (hP : P ∈ (S j).T) {A : Finset (Multitile ρ)} {x₀ : ℝ}
    (hA : ∀ P' ∈ A, (∃ k, k < n ∧ P' ∈ (S k).T) ∧ P'.I.length < P.I.length ∧
      Multitile.Near C₃ P P' ∧ x₀ ∈ P'.ωuDil C₃) :
    ∑ P' ∈ A, ∫ x in P'.I.toSet, P.I.weight N x ≤ ∫ x in (S j).I.toSetᶜ, P.I.weight N x := by
  classical
  have hdisj : Set.Pairwise (A : Set (Multitile ρ))
      (Function.onFun Disjoint fun P' => P'.I.toSet) := by
    intro P' hP' P'' hP'' hne
    obtain ⟨⟨k, hk, hPk⟩, hl, hn, hx⟩ := hA P' hP'
    obtain ⟨⟨k', hk', hPk'⟩, hl', hn', hx'⟩ := hA P'' hP''
    have hnear : Multitile.Near C₃ P' P'' := Multitile.Near.of_inter ⟨x₀, hx, hx'⟩
    rcases le_total P''.I.length P'.I.length with h | h
    · exact (claim_pair hC hρ hsep sel hk hk' hPk hPk' hne h hnear).1
    · exact (claim_pair hC hρ hsep sel hk' hk hPk' hPk hne.symm h hnear.symm).1.symm
  have hsubset : (⋃ P' ∈ A, P'.I.toSet) ⊆ (S j).I.toSetᶜ := by
    intro x hx
    obtain ⟨P', hP', hxP⟩ := Set.mem_iUnion₂.1 hx
    obtain ⟨⟨k, hk, hPk⟩, hl, hn, -⟩ := hA P' hP'
    have hne : P ≠ P' := fun h => absurd hl (by rw [← h]; exact lt_irrefl _)
    have := (claim_pair hC hρ hsep sel hj hk hP hPk hne hl.le hn).2 hl
    intro hxS
    exact Set.disjoint_left.1 this hxP hxS
  have hint : Integrable (P.I.weight N) := P.I.integrable_weight hN
  calc ∑ P' ∈ A, ∫ x in P'.I.toSet, P.I.weight N x
      = ∫ x in ⋃ P' ∈ A, P'.I.toSet, P.I.weight N x :=
        (integral_biUnion_finset A (fun P' _ => P'.I.measurableSet_toSet) hdisj
          (fun P' _ => hint.integrableOn)).symm
    _ ≤ ∫ x in (S j).I.toSetᶜ, P.I.weight N x :=
        setIntegral_mono_set hint.integrableOn
          (Filter.Eventually.of_forall fun x => P.I.weight_nonneg N x)
          (Filter.Eventually.of_forall fun x hx => hsubset hx)

/-- **The smaller-scale interactions of one packet** (L1558-L1581): for `P ∈ S_j`,
`∑_{P' ∈ U : |I'| < |I|} a_{P'} |⟨φ_P, φ_{P'}⟩| ≤ 2 E K₀ |I|^{1/2} ⟨w_I, 1_{ℝ∖I_{S_j}}⟩` if
`a_{P'} ≤ E |I'|^{1/2}` for the `P' ∈ U` (for `a_{P'} = |c_{P'}|` this is the use at L1564-L1566,
for `a_{P'} = |I'|^{1/2}`, `E = 1`, it is the display of `etreeorth22`, L1574-L1581). -/
theorem sum_norm_pairing_smaller_le (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    (hsep : Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ)))
    (sel : IsSelection C₁ C₂ M ch f e 𝔓 n S T) {K₀ : ℝ} (hK₀0 : 0 ≤ K₀) (hK₀ : SchwartzBound K₀)
    {E : ℝ} (hE : 0 ≤ E) (a : Multitile ρ → ℝ) {U : Finset (Multitile ρ)}
    (hU : ∀ P ∈ U, ∃ k, k < n ∧ P ∈ (S k).T)
    (hE2 : ∀ P ∈ U, a P ≤ E * √P.I.length) {j : ℕ} (hj : j < n) {P : Multitile ρ}
    (hP : P ∈ (S j).T) :
    ∑ P' ∈ U.filter (fun P' => P'.I.length < P.I.length),
      a P' * ‖pairing (P.wavePacket ch) (P'.wavePacket ch)‖ ≤
      2 * (E * K₀ * √P.I.length * ∫ x in (S j).I.toSetᶜ, P.I.weight 3 x) := by
  classical
  have hC₃ : 0 ≤ C₃ := by linarith [hC.one_le]
  have hI := P.I.length_pos
  set F := U.filter (fun P' => P'.I.length < P.I.length) with hF
  set sp : ℝ := P.ωu.center + C₃ * P.ωu.length / 2 with hsp
  set sm : ℝ := P.ωu.center - C₃ * P.ωu.length / 2 with hsm
  set t : Multitile ρ → ℝ := fun P' => E * K₀ * √P.I.length * ∫ x in P'.I.toSet, P.I.weight 3 x
    with ht
  have ht0 : ∀ P', 0 ≤ t P' := fun P' => by
    have : 0 ≤ ∫ x in P'.I.toSet, P.I.weight 3 x :=
      setIntegral_nonneg P'.I.measurableSet_toSet fun x _ => P.I.weight_nonneg 3 x
    simp only [ht]; positivity
  -- the bound for one term
  have hterm : ∀ P' ∈ F, a P' * ‖pairing (P.wavePacket ch) (P'.wavePacket ch)‖ ≤
      t P' := by
    intro P' hP'
    obtain ⟨hPU, hlt⟩ := Finset.mem_filter.1 hP'
    have hle := hK₀ ρ ρ ch ch P P' hlt.le
    have hcoef := hE2 P' hPU
    have hI' := P'.I.length_pos
    have hs' : 0 < √P'.I.length := Real.sqrt_pos.2 hI'
    calc a P' * ‖pairing (P.wavePacket ch) (P'.wavePacket ch)‖
        ≤ (E * √P'.I.length) * (K₀ * √(P.I.length / P'.I.length) *
            ∫ x in P'.I.toSet, P.I.weight 3 x) :=
          mul_le_mul hcoef hle (norm_nonneg _) (by positivity)
      _ = t P' := by
          rw [Real.sqrt_div hI.le]
          simp only [ht]
          field_simp
  -- the case distinction
  have hsum : ∑ P' ∈ F, a P' * ‖pairing (P.wavePacket ch) (P'.wavePacket ch)‖ ≤
      ∑ P' ∈ F, ((if sp ∈ P'.ωuDil C₃ then t P' else 0) +
        (if sm ∈ P'.ωuDil C₃ then t P' else 0)) := by
    refine Finset.sum_le_sum fun P' hP' => ?_
    have hlt := (Finset.mem_filter.1 hP').2
    by_cases hd : Disjoint (P.ωuDil C₃) (P'.ωuDil C₃)
    · rw [pairing_eq_zero_of_disjoint_ωuDil hC ch ch hd, norm_zero, mul_zero]
      have h1 : 0 ≤ if sp ∈ P'.ωuDil C₃ then t P' else 0 := by split_ifs <;> simp [ht0 P']
      have h2 : 0 ≤ if sm ∈ P'.ωuDil C₃ then t P' else 0 := by split_ifs <;> simp [ht0 P']
      linarith
    · have hinter : (P.ωuDil C₃ ∩ P'.ωuDil C₃).Nonempty :=
        Set.not_disjoint_iff_nonempty_inter.1 hd
      have hb := hterm P' hP'
      rcases Multitile.mem_dilate_of_inter_of_length_lt hinter
        (Multitile.ωu_length_lt_of_I_length_lt hlt) with h | h
      · have h2 : 0 ≤ if sm ∈ P'.ωuDil C₃ then t P' else 0 := by
          split_ifs <;> simp [ht0 P']
        have h' : sp ∈ P'.ωuDil C₃ := h
        have h3 : (if sp ∈ P'.ωuDil C₃ then t P' else 0) = t P' := by simp [h']
        linarith
      · have h2 : 0 ≤ if sp ∈ P'.ωuDil C₃ then t P' else 0 := by
          split_ifs <;> simp [ht0 P']
        have h' : sm ∈ P'.ωuDil C₃ := h
        have h3 : (if sm ∈ P'.ωuDil C₃ then t P' else 0) = t P' := by simp [h']
        linarith
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter] at hsum
  -- the two sums are bounded by the claim
  have hclaim : ∀ x₀ : ℝ, (∀ P' ∈ F, x₀ ∈ P'.ωuDil C₃ → Multitile.Near C₃ P P') →
      ∑ P' ∈ F.filter (fun P' => x₀ ∈ P'.ωuDil C₃), t P' ≤
        E * K₀ * √P.I.length * ∫ x in (S j).I.toSetᶜ, P.I.weight 3 x := by
    intro x₀ hnear
    rw [show ∑ P' ∈ F.filter (fun P' => x₀ ∈ P'.ωuDil C₃), t P' =
      E * K₀ * √P.I.length * ∑ P' ∈ F.filter (fun P' => x₀ ∈ P'.ωuDil C₃),
        ∫ x in P'.I.toSet, P.I.weight 3 x from by simp only [ht, Finset.mul_sum]]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine sum_integral_weight_le_compl (N := 3) (by norm_num) hC hρ hsep sel hj hP (x₀ := x₀)
      fun P' hP' => ?_
    obtain ⟨hF', hx⟩ := Finset.mem_filter.1 hP'
    obtain ⟨hPU, hlt⟩ := Finset.mem_filter.1 hF'
    exact ⟨hU P' hPU, hlt, hnear P' hF' hx, hx⟩
  have h1 := hclaim sp (fun P' _ hx => Multitile.Near.of_right_mem hC₃ hx)
  have h2 := hclaim sm (fun P' _ hx => Multitile.Near.of_left_mem hC₃ hx)
  linarith

end Claim

section Main

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ} {ch : ProfileChoice} {f : ℝ → ℂ}
  {e : ℝ} {𝔓 : Finset (Multitile ρ)} {n : ℕ} {S T : ℕ → MultitileTree ρ}

/-- **`etreeorth2` and `etreeorth22`** ([O+] L1558-L1644): for the packets of the trees
`S_j`, `j ∈ J`, with `∑_{P ∈ S_j} |c_P|² ≤ E² |I_{S_j}|`, `|c_P| ≤ E |I_P|^{1/2}`, and the tail
weight sum `∑_{P ∈ S_j} |I_P| ⟨w_I, 1_{ℝ∖I_{S_j}}⟩² ≤ K_t |I_{S_j}|` (etreeorth22):
`∑_{P ∈ U} ∑_{P' ∈ U : |I'| < |I|} |c_P||c_{P'}||⟨φ_P, φ_{P'}⟩| ≤ 2 K₀ √K_t E² ∑_j |I_{S_j}|`. -/
theorem sum_sum_smaller_scale_le (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    (hsep : Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ)))
    (sel : IsSelection C₁ C₂ M ch f e 𝔓 n S T) {K₀ Kt : ℝ} (hK₀0 : 0 ≤ K₀)
    (hK₀ : SchwartzBound K₀)
    (hKt : ∀ j < n, ∑ P ∈ (S j).T, P.I.length *
      (∫ x in (S j).I.toSetᶜ, P.I.weight 3 x) ^ 2 ≤ Kt * (S j).I.length)
    {E : ℝ} (hE : 0 ≤ E) {g : ℝ → ℂ} {J : Finset ℕ} (hJ : ∀ j ∈ J, j < n)
    (hE1 : ∀ j ∈ J, ∑ P ∈ (S j).T, ‖P.coeff ch g‖ ^ 2 ≤ E ^ 2 * (S j).I.length)
    (hE2 : ∀ j ∈ J, ∀ P ∈ (S j).T, ‖P.coeff ch g‖ ≤ E * √P.I.length) :
    ∑ P ∈ J.biUnion (fun j => (S j).T),
      ∑ P' ∈ (J.biUnion (fun j => (S j).T)).filter (fun P' => P'.I.length < P.I.length),
        ‖P.coeff ch g‖ * ‖P'.coeff ch g‖ *
          ‖pairing (P.wavePacket ch) (P'.wavePacket ch)‖ ≤
      2 * K₀ * √Kt * E ^ 2 * ∑ j ∈ J, (S j).I.length := by
  classical
  set U := J.biUnion (fun j => (S j).T) with hU
  have hUsel : ∀ P ∈ U, ∃ k, k < n ∧ P ∈ (S k).T := fun P hP => by
    obtain ⟨j, hj, hPj⟩ := Finset.mem_biUnion.1 hP
    exact ⟨j, hJ j hj, hPj⟩
  have hdisj : (↑J : Set ℕ).PairwiseDisjoint (fun j => (S j).T) := by
    intro j hj k hk hne
    exact sel.disjoint_S_S (hJ j hj) (hJ k hk) hne
  have hE2U : ∀ P ∈ U, ‖P.coeff ch g‖ ≤ E * √P.I.length := fun P hP => by
    obtain ⟨j, hj, hPj⟩ := Finset.mem_biUnion.1 hP
    exact hE2 j hj P hPj
  rw [Finset.sum_biUnion hdisj, Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjn := hJ j hj
  set Λ := (S j).I.length with hΛ
  have hΛ0 : 0 < Λ := (S j).I.length_pos
  set τ : Multitile ρ → ℝ := fun P => ∫ x in (S j).I.toSetᶜ, P.I.weight 3 x with hτ
  set g' : Multitile ρ → ℝ := fun P => 2 * (E * K₀ * √P.I.length * τ P) with hg'
  have hkey : ∀ P ∈ (S j).T,
      ∑ P' ∈ U.filter (fun P' => P'.I.length < P.I.length),
        ‖P.coeff ch g‖ * ‖P'.coeff ch g‖ * ‖pairing (P.wavePacket ch) (P'.wavePacket ch)‖ ≤
      ‖P.coeff ch g‖ * g' P := by
    intro P hP
    have := sum_norm_pairing_smaller_le hC hρ hsep sel hK₀0 hK₀ hE (fun P => ‖P.coeff ch g‖)
      hUsel hE2U hjn hP
    calc ∑ P' ∈ U.filter (fun P' => P'.I.length < P.I.length),
          ‖P.coeff ch g‖ * ‖P'.coeff ch g‖ * ‖pairing (P.wavePacket ch) (P'.wavePacket ch)‖
        = ‖P.coeff ch g‖ * ∑ P' ∈ U.filter (fun P' => P'.I.length < P.I.length),
          ‖P'.coeff ch g‖ * ‖pairing (P.wavePacket ch) (P'.wavePacket ch)‖ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun P' _ => by ring
      _ ≤ ‖P.coeff ch g‖ * g' P := mul_le_mul_of_nonneg_left this (norm_nonneg _)
  have hg2 : ∑ P ∈ (S j).T, g' P ^ 2 ≤ (2 * E * K₀) ^ 2 * Kt * Λ := by
    calc ∑ P ∈ (S j).T, g' P ^ 2
        = (2 * E * K₀) ^ 2 * ∑ P ∈ (S j).T, P.I.length * (τ P) ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun P _ => ?_
          simp only [hg']
          have := Real.sq_sqrt P.I.length_pos.le
          calc (2 * (E * K₀ * √P.I.length * τ P)) ^ 2
              = (2 * E * K₀) ^ 2 * ((√P.I.length) ^ 2 * (τ P) ^ 2) := by ring
            _ = _ := by rw [this]
      _ ≤ (2 * E * K₀) ^ 2 * (Kt * Λ) :=
          mul_le_mul_of_nonneg_left (hKt j hjn) (sq_nonneg _)
      _ = (2 * E * K₀) ^ 2 * Kt * Λ := by ring
  calc ∑ P ∈ (S j).T, ∑ P' ∈ U.filter (fun P' => P'.I.length < P.I.length),
        ‖P.coeff ch g‖ * ‖P'.coeff ch g‖ * ‖pairing (P.wavePacket ch) (P'.wavePacket ch)‖
      ≤ ∑ P ∈ (S j).T, ‖P.coeff ch g‖ * g' P := Finset.sum_le_sum hkey
    _ ≤ √(∑ P ∈ (S j).T, ‖P.coeff ch g‖ ^ 2) * √(∑ P ∈ (S j).T, g' P ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ √(E ^ 2 * Λ) * √((2 * E * K₀) ^ 2 * Kt * Λ) :=
        mul_le_mul (Real.sqrt_le_sqrt (hE1 j hj)) (Real.sqrt_le_sqrt hg2) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = √((E ^ 2 * Λ) * ((2 * E * K₀) ^ 2 * Kt * Λ)) := (Real.sqrt_mul (by positivity) _).symm
    _ = √((2 * E ^ 2 * K₀ * Λ) ^ 2 * Kt) := by congr 1; ring
    _ = 2 * E ^ 2 * K₀ * Λ * √Kt := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    _ = 2 * K₀ * √Kt * E ^ 2 * Λ := by ring

/-- **The squared-sum inequality, abstract form** (`squarebyfct`, [O+] L1503-L1556, and its
analogue `squarebyfctanalog`, L1709-L1737): for `g ∈ L²` with `∫ |g|² ≤ B`, the selected trees
`S_j`, `j ∈ J` with `∑_{P ∈ S_j} |c_P|² ≤ E² |I_{S_j}|`, `|c_P|² ≤ E² |I_P|` and
`(1/|I_{S_j}|) ∑_{P ∈ S_j} |c_P|² ≥ λ` (`c_P = ⟨g, φ_P⟩`):
`λ² ∑_{j ∈ J} |I_{S_j}| ≤ (K₀ + 4 K₀ √K_t) E² B`. -/
theorem sum_length_le_of_selection (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    (hsep : Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ)))
    (sel : IsSelection C₁ C₂ M ch f e 𝔓 n S T) {K₀ Kt : ℝ} (hK₀0 : 0 ≤ K₀)
    (hK₀ : SchwartzBound K₀)
    (hKt : ∀ j < n, ∑ P ∈ (S j).T, P.I.length *
      (∫ x in (S j).I.toSetᶜ, P.I.weight 3 x) ^ 2 ≤ Kt * (S j).I.length)
    {J : Finset ℕ} (hJ : ∀ j ∈ J, j < n) {g : ℝ → ℂ} (hg : MemLp g 2 volume)
    {B E lam : ℝ} (hB : ∫ x, ‖g x‖ ^ 2 ≤ B) (hE : 0 ≤ E) (hlam : 0 < lam)
    (hE1 : ∀ j ∈ J, ∑ P ∈ (S j).T, ‖P.coeff ch g‖ ^ 2 ≤ E ^ 2 * (S j).I.length)
    (hE2 : ∀ j ∈ J, ∀ P ∈ (S j).T, ‖P.coeff ch g‖ ^ 2 ≤ E ^ 2 * P.I.length)
    (hlarge : ∀ j ∈ J, lam * (S j).I.length ≤ ∑ P ∈ (S j).T, ‖P.coeff ch g‖ ^ 2) :
    lam ^ 2 * ∑ j ∈ J, (S j).I.length ≤ (K₀ + 4 * K₀ * √Kt) * E ^ 2 * B := by
  classical
  set U := J.biUnion (fun j => (S j).T) with hU
  set Λ : ℝ := ∑ j ∈ J, (S j).I.length with hΛdef
  have hΛ0 : 0 ≤ Λ := Finset.sum_nonneg fun j _ => (S j).I.length_pos.le
  have hUsub : (U : Set (Multitile ρ)) ⊆ 𝔓 := by
    intro P hP
    obtain ⟨j, hj, hPj⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hP)
    exact (mem_remainingFamily.1 (sel.S_subset_rem (hJ j hj) hPj)).1
  have hdisj : (↑J : Set ℕ).PairwiseDisjoint (fun j => (S j).T) := by
    intro j hj k hk hne
    exact sel.disjoint_S_S (hJ j hj) (hJ k hk) hne
  have hE2' : ∀ j ∈ J, ∀ P ∈ (S j).T, ‖P.coeff ch g‖ ≤ E * √P.I.length := by
    intro j hj P hP
    calc ‖P.coeff ch g‖ = |‖P.coeff ch g‖| := (abs_of_nonneg (norm_nonneg _)).symm
      _ ≤ √(E ^ 2 * P.I.length) := Real.abs_le_sqrt (hE2 j hj P hP)
      _ = E * √P.I.length := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hE]
  -- the sum `A`
  set A : ℝ := ∑ P ∈ U, ‖P.coeff ch g‖ ^ 2 with hA
  have hAeq : A = ∑ j ∈ J, ∑ P ∈ (S j).T, ‖P.coeff ch g‖ ^ 2 := by
    rw [hA, hU, Finset.sum_biUnion hdisj]
  have hAlow : lam * Λ ≤ A := by
    rw [hAeq, hΛdef, Finset.mul_sum]
    exact Finset.sum_le_sum hlarge
  have hAup : A ≤ E ^ 2 * Λ := by
    rw [hAeq, hΛdef, Finset.mul_sum]
    exact Finset.sum_le_sum hE1
  -- the double sum `Γ`
  set Γ : ℝ := ∑ P ∈ U, ∑ P' ∈ U, ‖P.coeff ch g‖ * ‖P'.coeff ch g‖ *
    ‖pairing (P.wavePacket ch) (P'.wavePacket ch)‖ with hΓ
  have hΓ0 : 0 ≤ Γ := Finset.sum_nonneg fun P _ => Finset.sum_nonneg fun P' _ => by positivity
  set h : Multitile ρ → Multitile ρ → ℝ := fun P P' => ‖P.coeff ch g‖ * ‖P'.coeff ch g‖ *
    ‖pairing (P.wavePacket ch) (P'.wavePacket ch)‖ with hh
  have hsymm : ∀ P P', h P P' = h P' P := fun P P' => by
    simp only [hh]
    rw [norm_pairing_comm (P.wavePacket ch) (P'.wavePacket ch)]
    ring
  have hsplit : ∀ P : Multitile ρ, ∑ P' ∈ U, h P P' =
      ∑ P' ∈ U.filter (fun P' => P'.I.length = P.I.length), h P P' +
      ∑ P' ∈ U.filter (fun P' => P'.I.length < P.I.length), h P P' +
      ∑ P' ∈ U.filter (fun P' => P.I.length < P'.I.length), h P P' := by
    intro P
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun P' _ => ?_
    rcases lt_trichotomy P'.I.length P.I.length with hlt | heq | hgt
    · simp [hlt, hlt.ne, not_lt.2 hlt.le]
    · simp [heq]
    · simp [hgt, hgt.ne', not_lt.2 hgt.le]
  have hO3 : ∑ P ∈ U, ∑ P' ∈ U.filter (fun P' => P.I.length < P'.I.length), h P P' =
      ∑ P ∈ U, ∑ P' ∈ U.filter (fun P' => P'.I.length < P.I.length), h P P' := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun P' _ => ?_
    by_cases hc : P'.I.length < P.I.length
    · simp [hc, hsymm P P']
    · simp [hc]
  have hΓsplit : Γ = ∑ P ∈ U, ∑ P' ∈ U.filter (fun P' => P'.I.length = P.I.length), h P P' +
      2 * ∑ P ∈ U, ∑ P' ∈ U.filter (fun P' => P'.I.length < P.I.length), h P P' := by
    rw [hΓ]
    change ∑ P ∈ U, ∑ P' ∈ U, h P P' = _
    simp_rw [hsplit, Finset.sum_add_distrib, hO3]
    ring
  -- the bounds
  have hO1 := sum_sum_same_scale_le hC hsep hK₀0 hK₀ ch hUsub (fun P => P.coeff ch g)
  have hO2 := sum_sum_smaller_scale_le hC hρ hsep sel hK₀0 hK₀ hKt hE hJ hE1
    (fun j hj P hP => hE2' j hj P hP)
  have hO1' : ∑ P ∈ U, ∑ P' ∈ U.filter (fun P' => P'.I.length = P.I.length), h P P' ≤
      K₀ * (E ^ 2 * Λ) := by
    refine hO1.trans ?_
    exact mul_le_mul_of_nonneg_left hAup hK₀0
  have hΓle : Γ ≤ (K₀ + 4 * K₀ * √Kt) * E ^ 2 * Λ := by
    rw [hΓsplit]
    have : 2 * ∑ P ∈ U, ∑ P' ∈ U.filter (fun P' => P'.I.length < P.I.length), h P P' ≤
        2 * (2 * K₀ * √Kt * E ^ 2 * Λ) := by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact hO2
    nlinarith
  -- Cauchy-Schwarz
  have hsq := sq_sum_norm_sq_coeff_le ch U hg
  have hB0 : 0 ≤ ∫ x, ‖g x‖ ^ 2 := integral_nonneg fun x => by positivity
  have hmain : (lam * Λ) ^ 2 ≤ B * ((K₀ + 4 * K₀ * √Kt) * E ^ 2 * Λ) := by
    have h1 : (lam * Λ) ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (by positivity) hAlow 2
    have h2 : A ^ 2 ≤ B * Γ := hsq.trans (mul_le_mul_of_nonneg_right hB hΓ0)
    have h3 : B * Γ ≤ B * ((K₀ + 4 * K₀ * √Kt) * E ^ 2 * Λ) :=
      mul_le_mul_of_nonneg_left hΓle (hB0.trans hB)
    linarith
  have hK0 : 0 ≤ K₀ + 4 * K₀ * √Kt := by positivity
  rcases hΛ0.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    have := hB0.trans hB
    positivity
  · have : lam ^ 2 * Λ * Λ ≤ ((K₀ + 4 * K₀ * √Kt) * E ^ 2 * B) * Λ := by nlinarith
    exact le_of_mul_le_mul_right this hpos

end Main

end PrimeCarleson.Proof.Oplus
