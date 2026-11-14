module

public import PrimeCarleson.Proof.Oplus.Defs.Multitile
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Data.Int.Interval

/-!
# Trees, energy, density and the separation assumptions of [O+] (L1206-L1345)

[O+]:

* L1206-L1259 (Source: [O+], L1206–L1259): "Consider a triple `𝒯 = (T_𝒯, I_𝒯, ξ_𝒯)`, with
  a set of multitiles `T_𝒯`, a dyadic interval `I_𝒯 ⊂ [-2^{M_o}, 2^{M_o})` and a point
  `ξ_𝒯 ∈ 𝒳_top`. `𝒯` is a tree if (i) `I ⊂ I_𝒯` for all `P = (I, ω_u) ∈ T_𝒯`; (ii) `ω_𝒯 :=
  [ξ_𝒯 - (C₂-1)/(4|I_𝒯|), ξ_𝒯 + (C₂-1)/(4|I_𝒯|))` is contained in `ω_m`, the convex hull of
  `C₂ ω_u ∪ C₂ ω_l`, for every `P ∈ T_𝒯`. A tree is `l`-overlapping if `ξ_T ∈ C₂ ω_l` for every
  `P ∈ T` and `l`-lacunary if `ξ_T ∉ C₂ ω_l` for every `P ∈ T`." Here
  `𝒳_top = {η : |η| ≤ C₁ 2^{M_o + 10}, η ∈ 2^{-M_o-10} ℤ}` (L1196-L1200). The integer `M_o = M_o(𝔓)`
  ("the smallest integer `M` for which all tiles are contained in the square `[-2^M, 2^M]²`") is
  the explicit parameter `M` of the definitions: `Multitile.InSquare M` says that a multitile lies
  in the square `[-2^M, 2^M]²`, and `Multitile.exists_inSquare` that every multitile lies in some
  such square. `C₁, C₂` (and `C₃`) are explicit
  parameters (`Defs/Constants.lean`: `C₁ = 12`, `C₂ = 2`, `C₃ = 11/10`). Trees, `ω_m`, energy
  and density are defined for `1`- and `2`-indices only (`[Fact ρ.IsOneOrTwo]`, as in [O+]
  L1160-L1163: the `3`-indices are reduced to `2`-indices by the reflection of L1099-L1121).
* L1275-L1282 (Source: [O+], L1275–L1282): the separation assumptions
  `SeparationOfScales` and `SeparationProp2`.
* L1313-L1345 (Source: [O+], L1313–L1345): `energy(𝔓) = sup_T
  ((1/|I_T|) ∑_{P ∈ T} |⟨f, φ_P⟩|²)^{1/2}` over the `l`-overlapping trees `T ⊂ 𝔓` and
  `density(𝔓) = sup_T ((1/|I_T|) ∫_E (1 + |x - c(I_T)|/|I_T|)^{-4} ∑_{k=1}^K |a_k(x)|^{r'}
  1_{ω_T}(ξ_{k-1}(x)) dx)^{1/r'}` over the nonempty trees `T ⊂ 𝔓`, valued in `ℝ≥0∞`.
  `energyOf` takes the coefficient family `c : Multitile ρ → ℂ` as an argument (`energy` is the
  case `c P = ⟨f, φ_P⟩`), so that the later estimates can be proved for any packet family
  (both profiles `√ν_i`, `√ν_i(-·)`, all indices).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-! ### Top frequencies, `M_o` -/

/-- The set `𝒳_top = {η : |η| ≤ C₁ 2^{M+10}, η = n 2^{-M-10}, n ∈ ℤ}` of admissible top frequencies
(L1196-L1200, with `M = M_o`). -/
def Xtop (C₁ : ℝ) (M : ℤ) : Set ℝ :=
  {η | |η| ≤ C₁ * (2 : ℝ) ^ (M + 10) ∧ ∃ n : ℤ, η = n * (2 : ℝ) ^ (-M - 10)}

/-- `𝒳_top` is finite (this makes the choice of a maximal top frequency possible, L1467-L1468). -/
theorem finite_Xtop (C₁ : ℝ) (M : ℤ) : (Xtop C₁ M).Finite := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (-M - 10) := zpow_pos (by norm_num) _
  have h3 : (2 : ℝ) ^ (M + 10) * (2 : ℝ) ^ (-M - 10) = 1 := by
    rw [← zpow_add₀ (by norm_num)]; simp
  set N : ℤ := ⌈C₁ * (2 : ℝ) ^ (M + 10) * (2 : ℝ) ^ (M + 10)⌉ with hN
  refine ((Finset.Icc (-N) N).finite_toSet.image fun n : ℤ => (n : ℝ) * (2 : ℝ) ^ (-M - 10)).subset
    ?_
  rintro η ⟨hη, n, rfl⟩
  refine ⟨n, ?_, rfl⟩
  have hn : |(n : ℝ)| ≤ C₁ * (2 : ℝ) ^ (M + 10) * (2 : ℝ) ^ (M + 10) := by
    rw [abs_mul, abs_of_pos h2] at hη
    have h4 : (0 : ℝ) < (2 : ℝ) ^ (M + 10) := zpow_pos (by norm_num) _
    have := mul_le_mul_of_nonneg_right hη h4.le
    calc |(n : ℝ)| = |(n : ℝ)| * ((2 : ℝ) ^ (-M - 10) * (2 : ℝ) ^ (M + 10)) := by
          rw [mul_comm ((2 : ℝ) ^ (-M - 10)), h3, mul_one]
      _ = |(n : ℝ)| * (2 : ℝ) ^ (-M - 10) * (2 : ℝ) ^ (M + 10) := by ring
      _ ≤ _ := this
  have h5 : |n| ≤ N := by
    have : (|n| : ℝ) ≤ (N : ℝ) := by
      calc (|n| : ℝ) = |(n : ℝ)| := by rfl
        _ ≤ _ := hn
        _ ≤ N := Int.le_ceil _
    exact_mod_cast this
  simp only [Finset.coe_Icc, mem_Icc]
  exact ⟨by linarith [neg_abs_le n], by linarith [le_abs_self n]⟩

/-- The tile `I × ω_u` of `P` lies in the square `[-2^M, 2^M]²`. -/
def Multitile.InSquare {ρ : Idx} (M : ℤ) (P : Multitile ρ) : Prop :=
  P.I.toSet ⊆ Icc (-(2 : ℝ) ^ M) ((2 : ℝ) ^ M) ∧ P.ωu.toSet ⊆ Icc (-(2 : ℝ) ^ M) ((2 : ℝ) ^ M)

/-- Squares are nested: `InSquare` is monotone in `M`. -/
theorem Multitile.InSquare.mono {ρ : Idx} {P : Multitile ρ} {M M' : ℤ} (h : P.InSquare M)
    (hM : M ≤ M') : P.InSquare M' := by
  have h2 : (2 : ℝ) ^ M ≤ (2 : ℝ) ^ M' := zpow_le_zpow_right₀ (by norm_num) hM
  exact ⟨h.1.trans (Icc_subset_Icc (by linarith) h2), h.2.trans (Icc_subset_Icc (by linarith) h2)⟩

/-- Every dyadic interval lies in some `[-2^M, 2^M]`. -/
theorem Dyadic.exists_subset_Icc (I : Dyadic) :
    ∃ M : ℤ, I.toSet ⊆ Icc (-(2 : ℝ) ^ M) ((2 : ℝ) ^ M) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (|(I.m : ℝ)| + 1) (by norm_num : (1 : ℝ) < 2)
  refine ⟨I.k + (n : ℤ), fun x hx => ?_⟩
  have hpos : (0 : ℝ) < (2 : ℝ) ^ I.k := zpow_pos (by norm_num) _
  have hk : (2 : ℝ) ^ (I.k + (n : ℤ)) = (2 : ℝ) ^ I.k * (2 : ℝ) ^ n := by
    rw [zpow_add₀ (by norm_num), zpow_natCast]
  have hb1 : -|(I.m : ℝ)| ≤ (I.m : ℝ) := neg_abs_le _
  have hb2 : (I.m : ℝ) ≤ |(I.m : ℝ)| := le_abs_self _
  obtain ⟨h1, h2⟩ := hx
  simp only [Dyadic.left, Dyadic.right] at h1 h2
  rw [mem_Icc, hk]
  constructor <;> nlinarith

/-- Every multitile lies in some square `[-2^M, 2^M]²`. -/
theorem Multitile.exists_inSquare {ρ : Idx} (P : Multitile ρ) : ∃ M : ℤ, P.InSquare M := by
  obtain ⟨M₁, h₁⟩ := P.I.exists_subset_Icc
  obtain ⟨M₂, h₂⟩ := P.ωu.exists_subset_Icc
  have hmono : ∀ {M M' : ℤ}, M ≤ M' →
      Icc (-(2 : ℝ) ^ M) ((2 : ℝ) ^ M) ⊆ Icc (-(2 : ℝ) ^ M') ((2 : ℝ) ^ M') := fun {M M'} h =>
    Icc_subset_Icc (by linarith [zpow_le_zpow_right₀ (a := (2 : ℝ)) (by norm_num) h])
      (zpow_le_zpow_right₀ (by norm_num) h)
  exact ⟨max M₁ M₂, h₁.trans (hmono (le_max_left _ _)), h₂.trans (hmono (le_max_right _ _))⟩

/-! ### Trees -/

/-- The convex hull `ω_m` of `C₂ ω_u ∪ C₂ ω_l` (L1228-L1230), for a `1`- or `2`-index. -/
def Multitile.ωm {ρ : Idx} [Fact ρ.IsOneOrTwo] (P : Multitile ρ) (C₂ : ℝ) : Set ℝ :=
  convexHull ℝ (P.ωuDil C₂ ∪ P.ωlDil C₂)

/-- The data `(T_𝒯, I_𝒯, ξ_𝒯)` of a tree (L1219-L1222): a finite set of `ρ`-multitiles, the top
interval and the top frequency. Whether it is a tree is `MultitileTree.IsTree`. -/
structure MultitileTree (ρ : Idx) where
  /-- The multitiles `T_𝒯`. -/
  T : Finset (Multitile ρ)
  /-- The top interval `I_𝒯`. -/
  I : Dyadic
  /-- The top frequency `ξ_𝒯`. -/
  ξ : ℝ

namespace MultitileTree

variable {ρ : Idx} (𝒯 : MultitileTree ρ)

/-- The top frequency interval `ω_𝒯 = [ξ_𝒯 - (C₂ - 1)/(4|I_𝒯|), ξ_𝒯 + (C₂ - 1)/(4|I_𝒯|))`
(L1229-L1230). -/
def ωT (C₂ : ℝ) : Set ℝ :=
  Ico (𝒯.ξ - (C₂ - 1) / (4 * 𝒯.I.length)) (𝒯.ξ + (C₂ - 1) / (4 * 𝒯.I.length))

variable [Fact ρ.IsOneOrTwo]

/-- `𝒯` is a tree (L1219-L1233, with `M = M_o` and the constants `C₁, C₂`):
`I_𝒯 ⊂ [-2^M, 2^M)`, `ξ_𝒯 ∈ 𝒳_top`, (i) `I ⊂ I_𝒯` for all `P ∈ T_𝒯` and (ii)
`ω_𝒯 ⊂ ω_m` for all `P ∈ T_𝒯`. -/
structure IsTree (C₁ C₂ : ℝ) (M : ℤ) : Prop where
  top_subset : 𝒯.I.toSet ⊆ Ico (-(2 : ℝ) ^ M) ((2 : ℝ) ^ M)
  ξ_mem : 𝒯.ξ ∈ Xtop C₁ M
  time : ∀ P ∈ 𝒯.T, P.I.toSet ⊆ 𝒯.I.toSet
  freq : ∀ P ∈ 𝒯.T, 𝒯.ωT C₂ ⊆ P.ωm C₂

/-- `𝒯` is `l`-overlapping: `ξ_T ∈ C₂ ω_l` for every `P ∈ T` (L1244-L1245). -/
def IsOverlapping (C₂ : ℝ) : Prop := ∀ P ∈ 𝒯.T, 𝒯.ξ ∈ P.ωlDil C₂

/-- `𝒯` is `l`-lacunary: `ξ_T ∉ C₂ ω_l` for every `P ∈ T` (L1247-L1248). -/
def IsLacunary (C₂ : ℝ) : Prop := ∀ P ∈ 𝒯.T, 𝒯.ξ ∉ P.ωlDil C₂

end MultitileTree

/-! ### Separation assumptions -/

/-- (separationofscales), L1276-L1277: if `|ω_u'| < |ω_u|` then
`|ω_u'| ≤ ((C₂ - C₃)/(2 C₁)) |ω_u|`, for all `P, P'` of the collection. -/
def SeparationOfScales {ρ : Idx} (C₁ C₂ C₃ : ℝ) (S : Set (Multitile ρ)) : Prop :=
  ∀ P ∈ S, ∀ P' ∈ S, P'.ωu.length < P.ωu.length →
    P'.ωu.length ≤ (C₂ - C₃) / (2 * C₁) * P.ωu.length

/-- (separationprop2), L1280-L1282: if `C₁ ω_u ∩ C₁ ω_u' ≠ ∅` and `|ω_u| = |ω_u'|` then
`ω_u = ω_u'`, for all `P, P'` of the collection. -/
def SeparationProp2 {ρ : Idx} (C₁ : ℝ) (S : Set (Multitile ρ)) : Prop :=
  ∀ P ∈ S, ∀ P' ∈ S, (P.ωuDil C₁ ∩ P'.ωuDil C₁).Nonempty → P.ωu.length = P'.ωu.length →
    P.ωu = P'.ωu

/-- The separation assumptions (separationofscales) and (separationprop2) of L1275-L1282. -/
structure Separated {ρ : Idx} (C₁ C₂ C₃ : ℝ) (S : Set (Multitile ρ)) : Prop where
  scales : SeparationOfScales C₁ C₂ C₃ S
  prop2 : SeparationProp2 C₁ S

/-! ### Energy and density -/

/-- The energy of the collection `S` for the coefficient family `c` (`c P` plays the role of
`⟨f, φ_P⟩`): `sup_T ((1/|I_T|) ∑_{P ∈ T} |c P|²)^{1/2}` over the `l`-overlapping trees
`T ⊂ S` (L1325-L1331); `ℝ≥0∞`-valued. -/
def energyOf {ρ : Idx} [Fact ρ.IsOneOrTwo] (C₁ C₂ : ℝ) (M : ℤ) (c : Multitile ρ → ℂ)
    (S : Set (Multitile ρ)) : ℝ≥0∞ :=
  ⨆ (𝒯 : MultitileTree ρ) (_ : 𝒯.IsTree C₁ C₂ M) (_ : 𝒯.IsOverlapping C₂)
      (_ : (𝒯.T : Set (Multitile ρ)) ⊆ S),
    ((ENNReal.ofReal 𝒯.I.length)⁻¹ * ∑ P ∈ 𝒯.T, ‖c P‖ₑ ^ 2) ^ (1 / 2 : ℝ)

/-- The energy of `S` with respect to `f` (L1325-L1331): the coefficients are
`⟨f, φ_P⟩` for the wave packets of the profile choice `ch`. -/
def energy {ρ : Idx} [Fact ρ.IsOneOrTwo] (C₁ C₂ : ℝ) (M : ℤ) (ch : ProfileChoice)
    (f : ℝ → ℂ) (S : Set (Multitile ρ)) : ℝ≥0∞ :=
  energyOf C₁ C₂ M (fun P => P.coeff ch f) S

/-- The density of the collection `S` with respect to `E` and the linearizing data `L`:
`sup_T ((1/|I_T|) ∫_E (1 + |x - c(I_T)|/|I_T|)^{-4} ∑_{k=1}^K |a_k(x)|^{r'}
1_{ω_T}(ξ_{k-1}(x)) dx)^{1/r'}` over the nonempty trees `T ⊂ S` (L1336-L1345); `ℝ≥0∞`-valued. -/
def density {ρ : Idx} [Fact ρ.IsOneOrTwo] (C₁ C₂ : ℝ) (M : ℤ) {r : ℝ} (L : Linearization r)
    (E : Set ℝ) (S : Set (Multitile ρ)) : ℝ≥0∞ :=
  ⨆ (𝒯 : MultitileTree ρ) (_ : 𝒯.IsTree C₁ C₂ M) (_ : 𝒯.T.Nonempty)
      (_ : (𝒯.T : Set (Multitile ρ)) ⊆ S),
    ((ENNReal.ofReal 𝒯.I.length)⁻¹ *
      ∫⁻ x in E, ENNReal.ofReal ((1 + |x - 𝒯.I.center| / 𝒯.I.length) ^ (-4 : ℤ)) *
        ∑ k : Fin L.K, ‖L.a k x‖ₑ ^ Real.conjExponent r *
          (𝒯.ωT C₂).indicator (fun _ => (1 : ℝ≥0∞)) (L.ξ k.castSucc x)) ^ (1 / Real.conjExponent r)

/-- The energy is monotone in the collection. -/
theorem energyOf_mono {ρ : Idx} [Fact ρ.IsOneOrTwo] (C₁ C₂ : ℝ) (M : ℤ) (c : Multitile ρ → ℂ)
    {S S' : Set (Multitile ρ)} (h : S ⊆ S') : energyOf C₁ C₂ M c S ≤ energyOf C₁ C₂ M c S' := by
  refine iSup_mono fun 𝒯 => iSup_mono fun _ => iSup_mono fun _ => ?_
  exact iSup_le fun hS => le_iSup_of_le (hS.trans h) le_rfl

/-- The density is monotone in the collection. -/
theorem density_mono {ρ : Idx} [Fact ρ.IsOneOrTwo] (C₁ C₂ : ℝ) (M : ℤ) {r : ℝ}
    (L : Linearization r) (E : Set ℝ) {S S' : Set (Multitile ρ)} (h : S ⊆ S') :
    density C₁ C₂ M L E S ≤ density C₁ C₂ M L E S' := by
  refine iSup_mono fun 𝒯 => iSup_mono fun _ => iSup_mono fun _ => ?_
  exact iSup_le fun hS => le_iSup_of_le (hS.trans h) le_rfl

end PrimeCarleson.Proof.Oplus
