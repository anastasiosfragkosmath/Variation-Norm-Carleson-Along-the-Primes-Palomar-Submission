module

public import PrimeCarleson.Proof.Oplus.Defs.Index
public import PrimeCarleson.Proof.Oplus.Defs.WavePacket
public import PrimeCarleson.Proof.Oplus.Defs.Linearization

/-!
# `ρ`-multitiles, the coefficients `a_P(x)` and their wave packets ([O+] L1069-L1090)

Source: [O+], L1069–L1090:
"A multitile will be a subset of `ℝ²` of the form `I × ω` where `I ∈ 𝒟` and where `ω` is the
union of three intervals `ω_l, ω_u, ω_h`. For each `ρ = (i,m,n,side)` we consider a set of
`ρ`-multitiles parameterized by `{(I, ω_u) : I, ω_u ∈ 𝒟, |I||ω_u| = 1/2` and `ω_u` is the
`side`-child of its parent`}`. [`ω_l`, `ω_h` as in `Idx.ωl`, `Idx.ωh`.] For every `ρ`-multitile
`P`, let `a_P(x) = a_k(x)` if `1 ≤ k ≤ K` and `ξ_{k-1}(x) ∈ ω_l` and `ξ_k(x) ∈ ω_h` (such a `k`
would clearly be unique), and `a_P(x) = 0` if there is no such `k`; ...
`φ_P(x) = √|I| 𝓕⁻¹[√φ_{ω_u,i(ρ)}](x - c(I))` and `𝒫_ρ` denotes the set of all `ρ`-multitiles for
which `I × ω_u` belongs to `𝔓`."

* `Multitile ρ` is the structure `(I, ωu)` with the area and side conditions, for *any* index
  `ρ : Idx` (not only `ρ ∈ R`; the multitile sets of the later sections are proved for every
  `(i, m, n, side)` with `m, n ∈ {1..4}` and for both profiles `√ν_i`, `√ν_i(-·)`).
* `Multitile.ωl`, `Multitile.ωh`, `Multitile.tile`; the dilate `Multitile.ωlDil` of `ω_l` exists in
  [O+] only for `1`- and `2`-indices (for a `3`-index `ω_l` is a half-line), so it carries
  `[Fact ρ.IsOneOrTwo]`.
* `aP L P x` is `a_P(x)` as the sum over `k` of the indicator-weighted `a_k(x)`;
  `aP_eq_of_mem` and `aP_eq_zero_of_not` show it is the paper's definition: `a_k(x)` for the
  (necessarily unique, `ωl_lt_ωh`) `k` with `ξ_{k-1}(x) ∈ ω_l`, `ξ_k(x) ∈ ω_h`, and `0` if there is
  none; `measurable_aP`.
* `Multitile.wavePacket c P` for a profile choice `c : ProfileChoice` (neighbour index
  `i ∈ {-1, 0, 1}` and `ν_i` or `ν_i(-·)`); the paper's `φ_P` of a `ρ`-multitile with `ρ ∈ R` is
  `P.wavePacket ⟨RIdx.i ρ, _, _, Orientation.plain⟩`.
  `Multitile.packetOf χ P` is the same for an arbitrary profile function `χ`.
* `Multitile.coeff c f P = ⟨f, φ_P⟩`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- A `ρ`-multitile `P = (I, ω_u)`: dyadic `I, ω_u` with `|I||ω_u| = 1/2` and `ω_u` the
`side`-child of its dyadic parent, where `ρ = (i, m, n, side)` (L1073). -/
@[ext] structure Multitile (ρ : Idx) where
  /-- The time interval `I`. -/
  I : Dyadic
  /-- The middle frequency interval `ω_u`. -/
  ωu : Dyadic
  /-- The area condition `|I||ω_u| = 1/2`. -/
  area : I.k + ωu.k = -1
  /-- `ω_u` is the `side`-child of its dyadic parent. -/
  side_eq : ωu.side = ρ.side
  deriving DecidableEq

namespace Multitile

variable {ρ : Idx} (P : Multitile ρ)

/-- The tile `I × ω_u` underlying the multitile (L1090: "`I × ω_u` belongs to `𝔓`"). -/
def tile : Tile := ⟨P.I, P.ωu, P.area⟩

/-- A multitile is determined by its tile `I × ω_u`. -/
theorem tile_injective : Function.Injective (tile : Multitile ρ → Tile) := by
  intro P Q h
  have h1 : P.I = Q.I := congrArg Tile.I h
  have h2 : P.ωu = Q.ωu := congrArg Tile.J h
  exact Multitile.ext h1 h2

/-- The lower frequency set `ω_l` of `P`. -/
def ωl : Set ℝ := ρ.ωl P.ωu

/-- The upper frequency set `ω_h` of `P`. -/
def ωh : Set ℝ := ρ.ωh P.ωu

/-- The dilate `C ω_l` of the lower frequency interval (L1170, L1228-L1230), with respect to its
center. [O+] dilates `ω_l` only for `1`- and `2`-indices (L1160-L1163, L1193), where `ω_l` is the
finite interval `ω_u - (m+1)|ω_u|`. For a `3`-index `ω_l` is a half-line, which has no center, and
its dilate is not defined in [O+]: the hypothesis `[Fact ρ.IsOneOrTwo]` restricts the definition
(and everything built on it: `ωm`, trees, energy) to its carrier, so that no value is invented for
a `3`-index. -/
def ωlDil [Fact ρ.IsOneOrTwo] (C : ℝ) : Set ℝ := (ρ.ωlDyadic P.ωu).dilate C

/-- For a `1`- or `2`-index, `ω_l` is the finite dyadic interval `ρ.ωlDyadic ω_u`. -/
theorem ωl_eq_toSet_ωlDyadic (h : ρ.IsOneOrTwo) : P.ωl = (ρ.ωlDyadic P.ωu).toSet := by
  unfold ωl Idx.ωl
  unfold Idx.IsOneOrTwo at h
  cases h' : ρ.typ <;> simp_all

/-- The dilate `C ω_u` of the middle frequency interval. -/
def ωuDil (C : ℝ) : Set ℝ := P.ωu.dilate C

/-- The area condition `|I||ω_u| = 1/2`. -/
theorem length_I_mul_length_ωu : P.I.length * P.ωu.length = 1 / 2 :=
  (Dyadic.area_iff P.I P.ωu).1 P.area

/-- `ω_u ∪ ω_h ∪ ω_l` lie in the order `ω_l < ω_u < ω_h` (used for the uniqueness of `k`). -/
theorem lt_of_mem_ωl_of_mem_ωh {a b : ℝ} (ha : a ∈ P.ωl) (hb : b ∈ P.ωh) : a < b :=
  ρ.ωl_lt_ωh P.ωu ha hb

/-! ### The coefficients `a_P(x)` -/

open Classical in
/-- The coefficient `a_P(x)` of a `ρ`-multitile for the linearizing data `L`
([O+] L1082): `a_k(x)` if `ξ_{k-1}(x) ∈ ω_l` and `ξ_k(x) ∈ ω_h`, and `0` if there is no such
`k`. Written as the sum over `k` of the indicator-weighted `a_k(x)`; at most one summand is
nonzero (`aP_eq_of_mem`). -/
def aP {r : ℝ} (L : Linearization r) (x : ℝ) : ℂ :=
  ∑ k : Fin L.K, if L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh then L.a k x else 0

/-- If `ξ_{k-1}(x) ∈ ω_l` and `ξ_k(x) ∈ ω_h` then `a_P(x) = a_k(x)`: the index `k` is unique. -/
theorem aP_eq_of_mem {r : ℝ} (L : Linearization r) (x : ℝ) {k : Fin L.K}
    (h1 : L.ξ k.castSucc x ∈ P.ωl) (h2 : L.ξ k.succ x ∈ P.ωh) : P.aP L x = L.a k x := by
  classical
  unfold aP
  rw [Finset.sum_eq_single k]
  · simp [h1, h2]
  · intro j _ hj
    refine ite_eq_right_iff.2 fun ⟨hj1, hj2⟩ => ?_
    rcases lt_or_gt_of_ne hj with hlt | hgt
    · -- `j < k`: `ξ_{j}(x) < ξ_{j+1}(x) ≤ ξ_{k-1}(x)`, with `ξ_j(x) ∈ ω_h`, `ξ_{k-1}(x) ∈ ω_l`
      have hle : L.ξ j.succ x ≤ L.ξ k.castSucc x := (L.strictMono_ξ x).monotone (by
        rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; exact Fin.lt_def.1 hlt)
      exact absurd (P.lt_of_mem_ωl_of_mem_ωh h1 hj2) (not_lt.2 hle)
    · have hle : L.ξ k.succ x ≤ L.ξ j.castSucc x := (L.strictMono_ξ x).monotone (by
        rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; exact Fin.lt_def.1 hgt)
      exact absurd (P.lt_of_mem_ωl_of_mem_ωh hj1 h2) (not_lt.2 hle)
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- If no `k` satisfies `ξ_{k-1}(x) ∈ ω_l` and `ξ_k(x) ∈ ω_h` then `a_P(x) = 0`. -/
theorem aP_eq_zero_of_not {r : ℝ} (L : Linearization r) (x : ℝ)
    (h : ∀ k : Fin L.K, ¬ (L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh)) : P.aP L x = 0 := by
  classical
  unfold aP
  exact Finset.sum_eq_zero fun k _ => ite_eq_right_iff.2 fun hc => absurd hc (h k)

/-- The coefficient `a_P` is measurable (`ξ_k, a_k` are measurable, `ω_l, ω_h` are intervals). -/
theorem measurable_aP {r : ℝ} (L : Linearization r) : Measurable (P.aP L) := by
  classical
  unfold aP
  refine Finset.measurable_sum _ fun k _ => ?_
  refine Measurable.ite ?_ (L.measurable_a k) measurable_const
  have h1 : MeasurableSet (L.ξ k.castSucc ⁻¹' P.ωl) :=
    (L.measurable_ξ _) (ρ.measurableSet_ωl P.ωu)
  have h2 : MeasurableSet (L.ξ k.succ ⁻¹' P.ωh) :=
    (L.measurable_ξ _) (ρ.measurableSet_ωh P.ωu)
  exact h1.inter h2

/-! ### Wave packets and coefficients -/

/-- The wave packet of `P` for an arbitrary frequency profile `χ`:
`√|I| 𝓕⁻¹[√χ((· - c(ω_u))/|ω_u|)](x - c(I))`. -/
def packetOf (χ : ℝ → ℝ) : ℝ → ℂ := wavePacketOf χ P.I P.ωu

/-- The wave packet `φ_P` of the multitile for the profile choice `c`
(L1088-L1090: `√|I| 𝓕⁻¹[√φ_{ω_u,i(ρ)}](x - c(I))`; for `ρ ∈ R` the paper's choice is
`i = i(ρ)`, `plain`). -/
def wavePacket (c : ProfileChoice) : ℝ → ℂ := P.packetOf c.fn

/-- The coefficient `⟨f, φ_P⟩` for the profile choice `c`. -/
def coeff (c : ProfileChoice) (f : ℝ → ℂ) : ℂ := pairing f (P.wavePacket c)

/-- The set `𝒫_ρ` of all `ρ`-multitiles whose tile `I × ω_u` belongs to a family `𝔓` of tiles
(L1090). -/
def family (ρ : Idx) (𝔓 : Set Tile) : Set (Multitile ρ) := {P | P.tile ∈ 𝔓}

/-- For a finite family of tiles, `𝒫_ρ` is finite. -/
theorem finite_family {𝔓 : Set Tile} (h : 𝔓.Finite) : (family ρ 𝔓).Finite :=
  h.preimage tile_injective.injOn

end Multitile

end PrimeCarleson.Proof.Oplus
