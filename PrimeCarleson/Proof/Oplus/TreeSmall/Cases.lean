module

public import PrimeCarleson.Proof.Oplus.TreeSmall.Intervals

/-!
# The three cases of the density step ([O+] L2166-L2193)

Source: [O+] `usedensitybound`, L2166–L2193 (the three cases of `l⁺`-overlapping, `l⁻`-overlapping
and `l`-lacunary trees): for `J ∈ 𝒥`, the multitile `P*` and the dyadic interval `J'` of the nearby
tile and interval (L2158-L2165), the one-multitile tree `T' = ({P*}, ξ', J')` is a tree with
`Ω_J ⊂ ω_{T'}`, where `Ω_J = ⋃_{P ∈ T, |I| ≥ C''|J|} ω_l` and `C'' = 8 C₁/(C₂ - 1)`, in the three
situations
* `T` is `l⁺`-overlapping (`ξ_T > inf ω_l` for every `P ∈ T`): `ξ' = ξ_T`;
* `T` is `l⁻`-overlapping (`ξ_T ≤ inf ω_l` for every `P ∈ T`): `ξ' = ξ_T + (C₂ - 1)/(4|J'|)`;
* `T` is `l`-lacunary: `ξ' = ξ_T - (C₂ - 1)/(4|J'|)`.

The printed shifts are `±(C₂ - 1)/(4|J|)`; with `|J| ≤ |J'| ≤ 4|J|` the inclusion `Ω_J ⊂ ω_{T'}`
can fail at an end point of `ω_{T'}` for the shift by `|J|` (for example `inf ω_l = ξ_T` in the
`l⁻` case when `|J'| > |J|`), so the shifts here are in terms of the interval `J'` of the tree
`T'` itself; this is the reading under which the three statements are true. The proofs are
coordinate computations with `ω_m(P) = [c - sL - C₂L/2, c + C₂L/2)` (`s = m + 1`, `L = |ω_u|`,
`c = c(ω_u)`; `Multitile.ωm_eq_Ico`) and use the two numerical consequences of the geometric
properties, `C₂ ≤ m + 1` and `2(m + 1) + C₂ ≤ C₁`.

Hypotheses: `T` a tree of multitiles inside the square `[-2^M, 2^M]²` (the top data of `T'` must
lie in `[-2^M, 2^M)` and `𝒳_top`, which is where the ambient `M = M_o + 3` enters; the source does
not check this), `J'` a dyadic interval with `I* ⊂ J'`, `|J'| ≤ 4|J|` and `J' ⊂ [-2^M, 2^M)`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- The constant `C'' = 8 C₁ (C₂ - 1)⁻¹` (L2090-L2091). -/
def Cpp (C₁ C₂ : ℝ) : ℝ := 8 * C₁ / (C₂ - 1)

/-- `C'' (C₂ - 1) = 8 C₁`. -/
theorem Cpp_mul_sub_one {C₁ C₂ : ℝ} (hC₂ : 1 < C₂) : Cpp C₁ C₂ * (C₂ - 1) = 8 * C₁ := by
  have : C₂ - 1 ≠ 0 := by linarith
  unfold Cpp; field_simp

/-- `C'' ≥ 8`. -/
theorem eight_le_Cpp {C₁ C₂ C₃ : ℝ} (hC : AdmissibleConstants C₁ C₂ C₃) : 8 ≤ Cpp C₁ C₂ := by
  have h1 : 1 < C₂ := lt_of_le_of_lt hC.one_le hC.lt₁
  unfold Cpp
  rw [le_div_iff₀ (by linarith)]
  linarith [hC.lt₂]

namespace MultitileTree

variable {ρ : Idx}

/-- `Ω_J = ⋃_{P ∈ T : |I| ≥ C''|J|} ω_l` (L2152). -/
def OmegaJ (𝒯 : MultitileTree ρ) (C : ℝ) (J : Dyadic) : Set ℝ :=
  {y | ∃ P ∈ 𝒯.T, C * J.length ≤ P.I.length ∧ y ∈ P.ωl}

/-- `𝒯` is `l⁺`-overlapping in the sense of L2066: `ξ_T > inf ω_l` for every `P ∈ T`. -/
def IsPlus (𝒯 : MultitileTree ρ) : Prop :=
  ∀ P ∈ 𝒯.T, (ρ.ωlDyadic P.ωu).left < 𝒯.ξ

/-- `𝒯` is `l⁻`-overlapping in the sense of L2064: `ξ_T ≤ inf ω_l` for every `P ∈ T`. -/
def IsMinus (𝒯 : MultitileTree ρ) : Prop :=
  ∀ P ∈ 𝒯.T, 𝒯.ξ ≤ (ρ.ωlDyadic P.ωu).left

/-- The three kinds of trees treated in the proof of the tree estimate (L2073-L2076): `l`-lacunary,
`l⁺`-overlapping, `l⁻`-overlapping. -/
def IsSpecial [Fact ρ.IsOneOrTwo] (C₂ : ℝ) (𝒯 : MultitileTree ρ) : Prop :=
  𝒯.IsLacunary C₂ ∨ (𝒯.IsOverlapping C₂ ∧ 𝒯.IsPlus) ∨ (𝒯.IsOverlapping C₂ ∧ 𝒯.IsMinus)

end MultitileTree

section Coordinates

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ}

/-- `y ∈ ω_l ↔ c - sL - L/2 ≤ y < c - sL + L/2` (`s = m + 1`). -/
theorem Multitile.mem_ωl_iff (P : Multitile ρ) {y : ℝ} :
    y ∈ P.ωl ↔ P.ωu.center - ((ρ.m : ℝ) + 1) * P.ωu.length - P.ωu.length / 2 ≤ y ∧
      y < P.ωu.center - ((ρ.m : ℝ) + 1) * P.ωu.length + P.ωu.length / 2 := by
  rw [P.ωl_eq_toSet_ωlDyadic Fact.out, Dyadic.mem_toSet]
  have e1 := (ρ.ωlDyadic P.ωu).center_eq
  have e2 := (ρ.ωlDyadic P.ωu).right_eq
  rw [Idx.center_ωlDyadic, Idx.length_ωlDyadic] at e1
  rw [Idx.length_ωlDyadic] at e2
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The left end point of `ω_l` is `c - sL - L/2`. -/
theorem Idx.left_ωlDyadic (ρ : Idx) (u : Dyadic) :
    (ρ.ωlDyadic u).left = u.center - ((ρ.m : ℝ) + 1) * u.length - u.length / 2 := by
  have e1 := (ρ.ωlDyadic u).center_eq
  rw [Idx.center_ωlDyadic, Idx.length_ωlDyadic] at e1
  linarith

/-- **`ξ_𝒯` lies in the interior of `ω_m(P)`** for every `P ∈ T` of a tree. -/
theorem tree_xi_bounds (hC : AdmissibleConstants C₁ C₂ C₃) {𝒯 : MultitileTree ρ}
    (hT : 𝒯.IsTree C₁ C₂ M) {P : Multitile ρ} (hP : P ∈ 𝒯.T) :
    P.ωu.center - ((ρ.m : ℝ) + 1) * P.ωu.length - C₂ * P.ωu.length / 2 < 𝒯.ξ ∧
      𝒯.ξ < P.ωu.center + C₂ * P.ωu.length / 2 := by
  have hC₂ : 1 < C₂ := lt_of_le_of_lt hC.one_le hC.lt₁
  have hI := 𝒯.I.length_pos
  have hr : 0 < (C₂ - 1) / (4 * 𝒯.I.length) := by apply div_pos <;> linarith
  obtain ⟨h1, h2⟩ := (𝒯.ωT_subset_ωm_iff hC₂ P).1 (hT.freq P hP)
  constructor <;> linarith

omit [Fact ρ.IsOneOrTwo] in
/-- A tree top interval `J'` containing `I*` has `(C₂ - 1)/(4|J'|) ≤ (C₂ - 1)|ω_u*|/2`. -/
theorem sub_one_div_le (hC₂ : 1 < C₂) {P : Multitile ρ} {J' : Dyadic}
    (h : P.I.length ≤ J'.length) : (C₂ - 1) / (4 * J'.length) ≤ (C₂ - 1) * P.ωu.length / 2 := by
  have hI := P.I.length_pos
  have hL := P.ωu.length_pos
  have hJ' := J'.length_pos
  have harea := P.length_I_mul_length_ωu
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have h1 : 1 ≤ 2 * P.ωu.length * J'.length := by
    have := mul_le_mul_of_nonneg_right h hL.le
    linarith only [this, harea]
  have h2 : 0 < C₂ - 1 := by linarith
  have h3 := mul_le_mul_of_nonneg_left h1 h2.le
  linarith only [h3]

omit [Fact ρ.IsOneOrTwo] in
/-- **The key size inequality**: for `P ∈ T` with `|I| ≥ C''|J|` and `|J'| ≤ 4|J|`,
`C₁ |ω_u| ≤ (C₂ - 1)/(4|J'|)`. -/
theorem C₁_mul_le_sub_one_div (hC₂ : 1 < C₂) (C₁ : ℝ) (hC₁ : 0 ≤ C₁) {P : Multitile ρ}
    {J J' : Dyadic} (hlarge : Cpp C₁ C₂ * J.length ≤ P.I.length) (h4 : J'.length ≤ 4 * J.length) :
    C₁ * P.ωu.length ≤ (C₂ - 1) / (4 * J'.length) := by
  have hI := P.I.length_pos
  have hL := P.ωu.length_pos
  have hJ := J.length_pos
  have hJ' := J'.length_pos
  have harea := P.length_I_mul_length_ωu
  have h1 : 8 * C₁ * J.length ≤ P.I.length * (C₂ - 1) := by
    have := mul_le_mul_of_nonneg_right hlarge (show (0 : ℝ) ≤ C₂ - 1 by linarith)
    rw [mul_assoc, mul_comm J.length, ← mul_assoc, Cpp_mul_sub_one hC₂] at this
    linarith
  rw [le_div_iff₀ (by positivity)]
  have h2 : C₁ * P.ωu.length * (4 * J'.length) ≤ C₁ * P.ωu.length * (16 * J.length) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h3 : C₁ * P.ωu.length * (16 * J.length) = 2 * P.ωu.length * (8 * C₁ * J.length) := by ring
  have h4' : 2 * P.ωu.length * (8 * C₁ * J.length) ≤
      2 * P.ωu.length * (P.I.length * (C₂ - 1)) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h5 : 2 * P.ωu.length * (P.I.length * (C₂ - 1)) = (C₂ - 1) := by
    have : 2 * P.ωu.length * (P.I.length * (C₂ - 1)) = 2 * (P.I.length * P.ωu.length) * (C₂ - 1)
      := by ring
    rw [this, harea]; ring
  linarith

end Coordinates

/-! ### The tree `T' = ({P*}, ξ', J')` -/

/-- The one-multitile tree `({P}, J', ξ')` with top interval `J'` and top frequency `ξ'`. -/
def MultitileTree.single {ρ : Idx} (P : Multitile ρ) (J' : Dyadic) (ξ' : ℝ) : MultitileTree ρ :=
  ⟨{P}, J', ξ'⟩

@[simp] theorem MultitileTree.single_T {ρ : Idx} (P : Multitile ρ) (J' : Dyadic) (ξ' : ℝ) :
    (MultitileTree.single P J' ξ').T = {P} := rfl

@[simp] theorem MultitileTree.single_I {ρ : Idx} (P : Multitile ρ) (J' : Dyadic) (ξ' : ℝ) :
    (MultitileTree.single P J' ξ').I = J' := rfl

@[simp] theorem MultitileTree.single_ξ {ρ : Idx} (P : Multitile ρ) (J' : Dyadic) (ξ' : ℝ) :
    (MultitileTree.single P J' ξ').ξ = ξ' := rfl

/-- A dyadic interval of length at most `2^M` that meets `[-2^M, 2^M)` lies in it. -/
theorem Dyadic.subset_Ico_of_length_le {M : ℤ} {J' : Dyadic} {z : ℝ} (hz : z ∈ J'.toSet)
    (hzM : z ∈ Ico (-(2 : ℝ) ^ M) ((2 : ℝ) ^ M)) (hlen : J'.length ≤ (2 : ℝ) ^ M) :
    J'.toSet ⊆ Ico (-(2 : ℝ) ^ M) ((2 : ℝ) ^ M) := by
  have hk : J'.k ≤ M := by
    have : (2 : ℝ) ^ J'.k ≤ (2 : ℝ) ^ M := hlen
    exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 this
  have hX : (0 : ℝ) < (2 : ℝ) ^ M := zpow_pos (by norm_num) _
  rcases lt_or_ge z 0 with hneg | hnn
  · -- `z ∈ [-2^M, 0)`
    let A : Dyadic := ⟨M, -1⟩
    have hzA : z ∈ A.toSet := by
      refine ⟨?_, ?_⟩
      · change (2 : ℝ) ^ M * ((-1 : ℤ) : ℝ) ≤ z
        push_cast; linarith [hzM.1]
      · change z < (2 : ℝ) ^ M * (((-1 : ℤ) : ℝ) + 1)
        push_cast; linarith
    rcases J'.toSet_subset_or_disjoint_of_k_le A hk with h | h
    · refine h.trans ?_
      intro w hw
      obtain ⟨hw1, hw2⟩ := hw
      change (2 : ℝ) ^ M * ((-1 : ℤ) : ℝ) ≤ w at hw1
      change w < (2 : ℝ) ^ M * (((-1 : ℤ) : ℝ) + 1) at hw2
      push_cast at hw1 hw2
      constructor <;> linarith
    · exact absurd h (Set.not_disjoint_iff.2 ⟨z, hz, hzA⟩)
  · let B : Dyadic := ⟨M, 0⟩
    have hzB : z ∈ B.toSet := by
      refine ⟨?_, ?_⟩
      · change (2 : ℝ) ^ M * ((0 : ℤ) : ℝ) ≤ z
        push_cast; linarith
      · change z < (2 : ℝ) ^ M * (((0 : ℤ) : ℝ) + 1)
        push_cast; linarith [hzM.2]
    rcases J'.toSet_subset_or_disjoint_of_k_le B hk with h | h
    · refine h.trans ?_
      intro w hw
      obtain ⟨hw1, hw2⟩ := hw
      change (2 : ℝ) ^ M * ((0 : ℤ) : ℝ) ≤ w at hw1
      change w < (2 : ℝ) ^ M * (((0 : ℤ) : ℝ) + 1) at hw2
      push_cast at hw1 hw2
      constructor <;> linarith
    · exact absurd h (Set.not_disjoint_iff.2 ⟨z, hz, hzB⟩)

section Trees

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ}

/-- **The shifted top frequency lies in `𝒳_top`**: `ξ_𝒯 + z (C₂ - 1)/(4|J'|) ∈ 𝒳_top` for
`z ∈ {-1, 0, 1}`, `P ∈ T` in the square `[-2^M, 2^M]²`, and `J' ⊃ I*` inside `[-2^M, 2^M)`. -/
theorem shifted_mem_Xtop (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    {𝒯 : MultitileTree ρ} (hT : 𝒯.IsTree C₁ C₂ M) {P : Multitile ρ} (hP : P ∈ 𝒯.T)
    (hsq : P.InSquare M) {J' : Dyadic} (hJ'sub : P.I.toSet ⊆ J'.toSet)
    (hJ'M : J'.toSet ⊆ Ico (-(2 : ℝ) ^ M) ((2 : ℝ) ^ M)) (z : ℤ) (hz : |z| ≤ 1) :
    𝒯.ξ + (z : ℝ) * ((C₂ - 1) / (4 * J'.length)) ∈ Xtop C₁ M := by
  have hC₂ : 1 < C₂ := lt_of_le_of_lt hC.one_le hC.lt₁
  have hC₁ : 1 < C₁ := lt_trans hC₂ hC.lt₂
  obtain ⟨k₂, hk₂⟩ := hC.nat_C₂
  obtain ⟨hξabs, n, hn⟩ := hT.ξ_mem
  have hX : (0 : ℝ) < (2 : ℝ) ^ M := zpow_pos (by norm_num) _
  have hJ'len := Dyadic.length_le_of_subset_Icc (hJ'M.trans Ico_subset_Icc_self)
  have hJ'k : J'.k ≤ M + 1 := by
    have : (2 : ℝ) ^ J'.k ≤ (2 : ℝ) ^ (M + 1) := by
      rw [zpow_add_one₀ (by norm_num)]; change J'.length ≤ _ ; linarith
    exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 this
  have hJ'pos := J'.length_pos
  have hrpos : 0 ≤ (C₂ - 1) / (4 * J'.length) := by
    apply div_nonneg <;> linarith
  have hIle : P.I.length ≤ J'.length :=
    Dyadic.length_le_iff.2 (Dyadic.k_le_of_toSet_subset hJ'sub)
  have hrle := sub_one_div_le hC₂ hIle
  have hL2 := Dyadic.length_le_of_subset_Icc hsq.2
  have hc := Dyadic.abs_center_le_of_subset_Icc hsq.2
  have hL := P.ωu.length_pos
  have hm4 : (ρ.m : ℝ) ≤ 4 := by exact_mod_cast hρ.2.1
  have hm0 : (0 : ℝ) ≤ ρ.m := Nat.cast_nonneg _
  obtain ⟨hlo, hhi⟩ := tree_xi_bounds hC hT hP
  constructor
  · -- the size
    have h3 : (2 : ℝ) ^ (M + 10) = (2 : ℝ) ^ M * 1024 := by
      rw [zpow_add₀ (by norm_num)]; norm_num
    rw [h3]
    have e1 : ((ρ.m : ℝ) + 1) * P.ωu.length ≤ 5 * (2 * (2 : ℝ) ^ M) :=
      mul_le_mul (by linarith) hL2 hL.le (by norm_num)
    have e2 : C₂ * P.ωu.length ≤ C₂ * (2 * (2 : ℝ) ^ M) :=
      mul_le_mul_of_nonneg_left hL2 (by linarith)
    have e3 : C₂ * (2 : ℝ) ^ M ≤ C₁ * (2 : ℝ) ^ M :=
      mul_le_mul_of_nonneg_right hC.lt₂.le hX.le
    have e4 : (C₂ - 1) * P.ωu.length / 2 ≤ (C₂ - 1) * (2 : ℝ) ^ M := by
      have := mul_le_mul_of_nonneg_left hL2 (by linarith only [hC₂] : (0 : ℝ) ≤ C₂ - 1)
      linarith only [this]
    have e5 : 1 * (2 : ℝ) ^ M ≤ C₁ * (2 : ℝ) ^ M :=
      mul_le_mul_of_nonneg_right hC₁.le hX.le
    have e6 : C₁ * 1 ≤ C₁ * 1 := le_rfl
    rw [abs_le] at hc ⊢
    have hz' : |(z : ℝ)| ≤ 1 := by exact_mod_cast hz
    have hzr : |(z : ℝ) * ((C₂ - 1) / (4 * J'.length))| ≤ (C₂ - 1) / (4 * J'.length) := by
      rw [abs_mul, abs_of_nonneg hrpos]
      exact mul_le_of_le_one_left hrpos hz'
    rw [abs_le] at hzr
    have hC₁X : 0 ≤ C₁ * (2 : ℝ) ^ M := by positivity
    constructor <;> linarith [hc.1, hc.2, hzr.1, hzr.2]
  · -- the lattice
    have hk' : 0 ≤ M + 8 - J'.k := by omega
    have e : (2 : ℝ) ^ (-M - 10) * (2 : ℝ) ^ ((M + 8 - J'.k).toNat) = (4 * J'.length)⁻¹ := by
      rw [← zpow_natCast, Int.toNat_of_nonneg hk', ← zpow_add₀ (by norm_num)]
      have : (-M - 10 + (M + 8 - J'.k)) = -(J'.k) - 2 := by ring
      rw [this, zpow_sub₀ (by norm_num), zpow_neg]
      unfold Dyadic.length
      field_simp
      norm_num
    refine ⟨n + z * ((k₂ : ℤ) - 1) * (2 : ℤ) ^ ((M + 8 - J'.k).toNat), ?_⟩
    have : (C₂ - 1) / (4 * J'.length) = ((k₂ : ℝ) - 1) * (4 * J'.length)⁻¹ := by
      rw [hk₂]; ring
    rw [this, hn, ← e]
    push_cast
    ring

end Trees

/-! ### The three cases -/

section Cases

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ}

omit [Fact ρ.IsOneOrTwo] in
/-- Membership of the top frequency interval of a one-multitile tree. -/
theorem MultitileTree.mem_ωT_single {P : Multitile ρ} {J' : Dyadic} {ξ' y : ℝ} :
    y ∈ (MultitileTree.single P J' ξ').ωT C₂ ↔
      ξ' - (C₂ - 1) / (4 * J'.length) ≤ y ∧ y < ξ' + (C₂ - 1) / (4 * J'.length) := Iff.rfl

/-- **The case of `l⁺`-overlapping trees** ([O+] L2166-L2177). If `T` is `l⁺`-overlapping, `P* ∈ T`
and `J'` is a dyadic interval `⊃ I*` of length `≤ 4|J|` in `[-2^M, 2^M)`, then
`T' = ({P*}, ξ_T, J')` is a tree and `Ω_J ⊂ ω_{T'}`. -/
theorem case_plus_overlapping (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    {𝒯 : MultitileTree ρ} (hT : 𝒯.IsTree C₁ C₂ M) (hov : 𝒯.IsOverlapping C₂)
    (hplus : 𝒯.IsPlus) {P : Multitile ρ} (hP : P ∈ 𝒯.T) {J J' : Dyadic}
    (h4 : J'.length ≤ 4 * J.length) (hJ'sub : P.I.toSet ⊆ J'.toSet)
    (hJ'M : J'.toSet ⊆ Ico (-(2 : ℝ) ^ M) ((2 : ℝ) ^ M)) :
    (MultitileTree.single P J' 𝒯.ξ).IsTree C₁ C₂ M ∧
      𝒯.OmegaJ (Cpp C₁ C₂) J ⊆ (MultitileTree.single P J' 𝒯.ξ).ωT C₂ := by
  have hC₂ : 1 < C₂ := lt_of_le_of_lt hC.one_le hC.lt₁
  have hC₁ : 1 < C₁ := lt_trans hC₂ hC.lt₂
  have hIle : P.I.length ≤ J'.length :=
    Dyadic.length_le_iff.2 (Dyadic.k_le_of_toSet_subset hJ'sub)
  have hrle := sub_one_div_le hC₂ hIle
  have hL := P.ωu.length_pos
  have hJ'pos := J'.length_pos
  have hrpos : 0 < (C₂ - 1) / (4 * J'.length) := by apply div_pos <;> linarith
  have hs := hC.le_m_add_one hρ
  refine ⟨⟨hJ'M, hT.ξ_mem, fun Q hQ => ?_, fun Q hQ => ?_⟩, ?_⟩
  · rw [MultitileTree.single_T, Finset.mem_singleton] at hQ
    subst hQ; exact hJ'sub
  · rw [MultitileTree.single_T, Finset.mem_singleton] at hQ
    subst hQ
    rw [MultitileTree.ωT_subset_ωm_iff hC₂]
    simp only [MultitileTree.single_I, MultitileTree.single_ξ]
    have h1 := hov Q hP
    rw [Multitile.ωlDil_eq] at h1
    have h2 := hplus Q hP
    rw [Idx.left_ωlDyadic] at h2
    have key : 0 ≤ ((ρ.m : ℝ) + 1 - C₂ / 2 + 1 / 2) * Q.ωu.length :=
      mul_nonneg (by linarith) hL.le
    constructor <;> linarith [h1.1, h1.2]
  · intro y hy
    obtain ⟨Q, hQ, hlarge, hyQ⟩ := hy
    have hLr := C₁_mul_le_sub_one_div hC₂ C₁ (by linarith) hlarge h4
    have hLQ := Q.ωu.length_pos
    have h1 := hov Q hQ
    rw [Multitile.ωlDil_eq] at h1
    rw [Multitile.mem_ωl_iff] at hyQ
    have hk : (C₂ + 1) / 2 * Q.ωu.length ≤ C₁ * Q.ωu.length :=
      mul_le_mul_of_nonneg_right (by linarith [hC.lt₂]) hLQ.le
    rw [MultitileTree.mem_ωT_single]
    constructor <;> linarith [h1.1, h1.2, hyQ.1, hyQ.2]

/-- **The case of `l⁻`-overlapping trees** ([O+] L2180-L2185). If `T` is `l⁻`-overlapping, then
`T' = ({P*}, ξ_T + (C₂ - 1)/(4|J'|), J')` is a tree and `Ω_J ⊂ ω_{T'}`. -/
theorem case_minus_overlapping (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    {𝒯 : MultitileTree ρ} (hT : 𝒯.IsTree C₁ C₂ M) (hov : 𝒯.IsOverlapping C₂)
    (hminus : 𝒯.IsMinus) {P : Multitile ρ} (hP : P ∈ 𝒯.T) (hsq : P.InSquare M) {J J' : Dyadic}
    (h4 : J'.length ≤ 4 * J.length) (hJ'sub : P.I.toSet ⊆ J'.toSet)
    (hJ'M : J'.toSet ⊆ Ico (-(2 : ℝ) ^ M) ((2 : ℝ) ^ M)) :
    (MultitileTree.single P J' (𝒯.ξ + (C₂ - 1) / (4 * J'.length))).IsTree C₁ C₂ M ∧
      𝒯.OmegaJ (Cpp C₁ C₂) J ⊆
        (MultitileTree.single P J' (𝒯.ξ + (C₂ - 1) / (4 * J'.length))).ωT C₂ := by
  have hC₂ : 1 < C₂ := lt_of_le_of_lt hC.one_le hC.lt₁
  have hC₁ : 1 < C₁ := lt_trans hC₂ hC.lt₂
  have hIle : P.I.length ≤ J'.length :=
    Dyadic.length_le_iff.2 (Dyadic.k_le_of_toSet_subset hJ'sub)
  have hrle := sub_one_div_le hC₂ hIle
  have hL := P.ωu.length_pos
  have hJ'pos := J'.length_pos
  have hrpos : 0 < (C₂ - 1) / (4 * J'.length) := by apply div_pos <;> linarith
  have hs := hC.le_m_add_one hρ
  have hξ : 𝒯.ξ + (C₂ - 1) / (4 * J'.length) ∈ Xtop C₁ M := by
    have := shifted_mem_Xtop hC hρ hT hP hsq hJ'sub hJ'M 1 (by norm_num)
    simpa using this
  refine ⟨⟨hJ'M, hξ, fun Q hQ => ?_, fun Q hQ => ?_⟩, ?_⟩
  · rw [MultitileTree.single_T, Finset.mem_singleton] at hQ
    subst hQ; exact hJ'sub
  · rw [MultitileTree.single_T, Finset.mem_singleton] at hQ
    subst hQ
    rw [MultitileTree.ωT_subset_ωm_iff hC₂]
    simp only [MultitileTree.single_I, MultitileTree.single_ξ]
    obtain ⟨h0, -⟩ := tree_xi_bounds hC hT hP
    have h2 := hminus Q hP
    rw [Idx.left_ωlDyadic] at h2
    have key : 0 ≤ ((ρ.m : ℝ) + 1 - C₂ / 2 + 3 / 2) * Q.ωu.length :=
      mul_nonneg (by linarith) hL.le
    constructor <;> linarith
  · intro y hy
    obtain ⟨Q, hQ, hlarge, hyQ⟩ := hy
    have hLr := C₁_mul_le_sub_one_div hC₂ C₁ (by linarith) hlarge h4
    have hLQ := Q.ωu.length_pos
    have h1 := hov Q hQ
    rw [Multitile.ωlDil_eq] at h1
    have h2 := hminus Q hQ
    rw [Idx.left_ωlDyadic] at h2
    rw [Multitile.mem_ωl_iff] at hyQ
    have hk : (C₂ + 1) / 2 * Q.ωu.length ≤ C₁ * Q.ωu.length :=
      mul_le_mul_of_nonneg_right (by linarith [hC.lt₂]) hLQ.le
    rw [MultitileTree.mem_ωT_single]
    constructor <;> linarith [h1.1, h1.2, hyQ.1, hyQ.2]

/-- **The case of `l`-lacunary trees** ([O+] L2187-L2193). If `T` is `l`-lacunary, then
`T' = ({P*}, ξ_T - (C₂ - 1)/(4|J'|), J')` is a tree and `Ω_J ⊂ ω_{T'}`. -/
theorem case_lacunary (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    {𝒯 : MultitileTree ρ} (hT : 𝒯.IsTree C₁ C₂ M) (hlac : 𝒯.IsLacunary C₂)
    {P : Multitile ρ} (hP : P ∈ 𝒯.T) (hsq : P.InSquare M) {J J' : Dyadic}
    (h4 : J'.length ≤ 4 * J.length) (hJ'sub : P.I.toSet ⊆ J'.toSet)
    (hJ'M : J'.toSet ⊆ Ico (-(2 : ℝ) ^ M) ((2 : ℝ) ^ M)) :
    (MultitileTree.single P J' (𝒯.ξ - (C₂ - 1) / (4 * J'.length))).IsTree C₁ C₂ M ∧
      𝒯.OmegaJ (Cpp C₁ C₂) J ⊆
        (MultitileTree.single P J' (𝒯.ξ - (C₂ - 1) / (4 * J'.length))).ωT C₂ := by
  have hC₂ : 1 < C₂ := lt_of_le_of_lt hC.one_le hC.lt₁
  have hC₁ : 1 < C₁ := lt_trans hC₂ hC.lt₂
  have hIle : P.I.length ≤ J'.length :=
    Dyadic.length_le_iff.2 (Dyadic.k_le_of_toSet_subset hJ'sub)
  have hrle := sub_one_div_le hC₂ hIle
  have hL := P.ωu.length_pos
  have hJ'pos := J'.length_pos
  have hrpos : 0 < (C₂ - 1) / (4 * J'.length) := by apply div_pos <;> linarith
  have hs := hC.le_m_add_one hρ
  have hs2 := hC.two_m_add_one_add_le hρ
  have hξ : 𝒯.ξ - (C₂ - 1) / (4 * J'.length) ∈ Xtop C₁ M := by
    have := shifted_mem_Xtop hC hρ hT hP hsq hJ'sub hJ'M (-1) (by norm_num)
    simpa [sub_eq_add_neg] using this
  -- lacunary: `ξ_T ≥ c - sL + C₂ L/2` for every `Q ∈ T`
  have hlacQ : ∀ Q ∈ 𝒯.T, Q.ωu.center - ((ρ.m : ℝ) + 1) * Q.ωu.length +
      C₂ * Q.ωu.length / 2 ≤ 𝒯.ξ := by
    intro Q hQ
    have h1 := hlac Q hQ
    rw [Multitile.ωlDil_eq] at h1
    have h2 := (tree_xi_bounds hC hT hQ).1
    by_contra hcon
    exact h1 ⟨by linarith, by linarith⟩
  refine ⟨⟨hJ'M, hξ, fun Q hQ => ?_, fun Q hQ => ?_⟩, ?_⟩
  · rw [MultitileTree.single_T, Finset.mem_singleton] at hQ
    subst hQ; exact hJ'sub
  · rw [MultitileTree.single_T, Finset.mem_singleton] at hQ
    subst hQ
    rw [MultitileTree.ωT_subset_ωm_iff hC₂]
    simp only [MultitileTree.single_I, MultitileTree.single_ξ]
    obtain ⟨-, h0⟩ := tree_xi_bounds hC hT hP
    have h2 := hlacQ Q hP
    constructor <;> linarith
  · intro y hy
    obtain ⟨Q, hQ, hlarge, hyQ⟩ := hy
    have hLr := C₁_mul_le_sub_one_div hC₂ C₁ (by linarith) hlarge h4
    have hLQ := Q.ωu.length_pos
    have h1 := hlacQ Q hQ
    obtain ⟨-, h0⟩ := tree_xi_bounds hC hT hQ
    rw [Multitile.mem_ωl_iff] at hyQ
    have hk : (((ρ.m : ℝ) + 1) + (C₂ + 1) / 2) * Q.ωu.length ≤ C₁ * Q.ωu.length :=
      mul_le_mul_of_nonneg_right (by linarith [hC.lt₂]) hLQ.le
    have hk2 : 0 ≤ (C₂ - 1) / 2 * Q.ωu.length := mul_nonneg (by linarith) hLQ.le
    rw [MultitileTree.mem_ωT_single]
    constructor <;> linarith [hyQ.1, hyQ.2]

end Cases

end PrimeCarleson.Proof.Oplus
