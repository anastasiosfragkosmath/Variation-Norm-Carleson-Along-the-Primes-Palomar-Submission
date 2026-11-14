module

public import PrimeCarleson.Proof.Oplus.Defs.Index
public import PrimeCarleson.Proof.Oplus.Defs.WavePacket

/-!
# The constants `C₁, C₂, C₃` of [O+] (L1166-L1184)

Source: [O+], L1168–L1184:
"Fix `1 ≤ C₃ < C₂ < C₁`, with `C₂ ∈ ℕ`, such that for every multitile `P`,
`supp(φ̂_P) ⊂ C₃ ω_u`, `C₂ ω_u ∩ C₂ ω_l = ∅`, `C₂ ω_u ∩ ω_h = ∅`, `C₂ ω_l ⊂ C₁ ω_u`,
`C₂ ω_u ⊂ C₁ ω_l`; recall that dilations of finite intervals are with respect to their center. One
may check that the values `C₃ = 11/10`, `C₂ = 2`, and `C₁ = 12` satisfy all these properties."

* `PacketSupport C₃`: for every profile choice (`√ν_i` or `√ν_i(-·)`, `i ∈ {-1, 0, 1}`) and every
  tiles `I × J`, `supp φ̂_P ⊆ C₃ J`.
* `GeometricProperties C₁ C₂`: the four relations between `C₂ ω_u`, `C₂ ω_l`, `ω_h`, `C₁ ω_u`,
  `C₁ ω_l`, for every `ρ` with `i ∈ {1, 2}` and `m, n ∈ {1, …, 4}` (including the indices outside
  `R` obtained by the reflection of L1113-L1118, which has `m, n` swapped) and every dyadic
  `ω_u`. The quantifier of the paper ("every multitile") does not say which indices are meant; the
  3-indices are excluded because their `ω_l` is a half-line, which has no dilate (they are
  reflected to 2-indices, L1099-L1121).
* `AdmissibleConstants C₁ C₂ C₃` bundles these with `1 ≤ C₃ < C₂ < C₁`, `C₂ ∈ ℕ`, and
  `admissibleConstants_std : AdmissibleConstants 12 2 (11/10)` proves the claim of L1183-L1184.

Dilates are the half-open dilates of `Dyadic.dilate` (the closed dilate would make
`C₂ ω_u ∩ C₂ ω_l` a point for `m = 1`).
-/

@[expose] public noncomputable section

open Set
open scoped FourierTransform

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- `supp φ̂_P ⊂ C₃ ω_u` for every wave packet of every profile choice (L1171). -/
def PacketSupport (C₃ : ℝ) : Prop :=
  ∀ (c : ProfileChoice) (I J : Dyadic), tsupport (𝓕 (wavePacketOf c.fn I J)) ⊆ J.dilate C₃

/-- The four geometric relations of L1172-L1177, for all `1`- and `2`-indices with
`m, n ∈ {1, …, 4}` and all dyadic `ω_u`:
`C₂ ω_u ∩ C₂ ω_l = ∅`, `C₂ ω_u ∩ ω_h = ∅`, `C₂ ω_l ⊂ C₁ ω_u`, `C₂ ω_u ⊂ C₁ ω_l`. -/
def GeometricProperties (C₁ C₂ : ℝ) : Prop :=
  ∀ ρ : Idx, ρ.IsStd → ρ.IsOneOrTwo → ∀ u : Dyadic,
    Disjoint (u.dilate C₂) ((ρ.ωlDyadic u).dilate C₂) ∧
    Disjoint (u.dilate C₂) (ρ.ωh u) ∧
    (ρ.ωlDyadic u).dilate C₂ ⊆ u.dilate C₁ ∧
    u.dilate C₂ ⊆ (ρ.ωlDyadic u).dilate C₁

/-- The constants of L1168-L1177: `1 ≤ C₃ < C₂ < C₁`, `C₂ ∈ ℕ`, and the support and geometric
properties. -/
structure AdmissibleConstants (C₁ C₂ C₃ : ℝ) : Prop where
  one_le : 1 ≤ C₃
  lt₁ : C₃ < C₂
  lt₂ : C₂ < C₁
  nat_C₂ : ∃ k : ℕ, C₂ = k
  packet_support : PacketSupport C₃
  geometry : GeometricProperties C₁ C₂

/-- `supp φ̂_P ⊂ (11/10) ω_u` for every wave packet (L1171 of [O+]). -/
theorem packetSupport_std : PacketSupport (11 / 10) := fun c I J =>
  tsupport_fourier_wavePacketOf_subset_dilate c.isProfile I J (by norm_num)

/-- The four geometric relations of L1172-L1177 hold for `C₁ = 12`, `C₂ = 2`. -/
theorem geometricProperties_std : GeometricProperties 12 2 := by
  intro ρ hρ h12 u
  obtain ⟨hm1, hm4, hn1, hn4⟩ := hρ
  have hm1' : (1 : ℝ) ≤ ρ.m := by exact_mod_cast hm1
  have hm4' : (ρ.m : ℝ) ≤ 4 := by exact_mod_cast hm4
  have hn1' : (1 : ℝ) ≤ ρ.n := by exact_mod_cast hn1
  have hL := u.length_pos
  have hcen := u.center_eq
  have hr := u.right_eq
  have hlc : (ρ.ωlDyadic u).center = u.center - ((ρ.m : ℝ) + 1) * u.length := by
    unfold Idx.ωlDyadic; rw [Dyadic.center_shift]; push_cast; ring
  have hll : (ρ.ωlDyadic u).length = u.length := rfl
  have hmL : (1 : ℝ) * u.length ≤ ρ.m * u.length := mul_le_mul_of_nonneg_right hm1' hL.le
  have hmL4 : (ρ.m : ℝ) * u.length ≤ 4 * u.length := mul_le_mul_of_nonneg_right hm4' hL.le
  have hnL : (1 : ℝ) * u.length ≤ ρ.n * u.length := mul_le_mul_of_nonneg_right hn1' hL.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Set.disjoint_left.2 fun x hx hy => ?_
    simp only [Dyadic.dilate, mem_Ico, hlc, hll] at hx hy
    nlinarith [hx.1, hx.2, hy.1, hy.2]
  · refine Set.disjoint_left.2 fun x hx hy => ?_
    simp only [Dyadic.dilate, mem_Ico] at hx
    have hy' : u.left + ((ρ.n : ℝ) + 1) * u.length ≤ x := by
      unfold Idx.ωh at hy
      have h : ρ.typ = IdxType.one ∨ ρ.typ = IdxType.two := by
        unfold Idx.IsOneOrTwo at h12; cases h' : ρ.typ <;> simp_all
      rcases h with h | h <;> rw [h] at hy
      · simp only [Dyadic.toSet, Dyadic.left_shift, mem_Ico] at hy
        push_cast at hy; linarith [hy.1]
      · simpa using hy
    nlinarith [hx.1, hx.2]
  · intro x hx
    simp only [Dyadic.dilate, mem_Ico, hlc, hll] at hx ⊢
    constructor <;> nlinarith [hx.1, hx.2]
  · intro x hx
    simp only [Dyadic.dilate, mem_Ico, hlc, hll] at hx ⊢
    constructor <;> nlinarith [hx.1, hx.2]

/-- **The values `C₃ = 11/10`, `C₂ = 2`, `C₁ = 12` satisfy all the required properties**
(L1183-L1184 of [O+]). -/
theorem admissibleConstants_std : AdmissibleConstants 12 2 (11 / 10) where
  one_le := by norm_num
  lt₁ := by norm_num
  lt₂ := by norm_num
  nat_C₂ := ⟨2, by norm_num⟩
  packet_support := packetSupport_std
  geometry := geometricProperties_std

end PrimeCarleson.Proof.Oplus
