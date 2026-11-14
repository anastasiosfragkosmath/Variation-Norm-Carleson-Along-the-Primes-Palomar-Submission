/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Nilpotent/BCHSubgroupGridExistence.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import OAI.Combinatorics.Progressions.Estimates.RationalLieSubalgebra
@[expose] public section

namespace OAI

section

namespace Erdos3
variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
namespace NilpotentLieBCHGroup
variable {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def quotientHom (I : LieIdeal ℚ L) :
    NilpotentLieBCHGroup L s hnil →*
      NilpotentLieBCHGroup (L ⧸ I) s (lie_quotient_lowerCentralSeries_eq_bot hnil I) :=
  map (lieQuotientMap I)

@[simp] theorem quotientHom_coord (I : LieIdeal ℚ L) (a : NilpotentLieBCHGroup L s hnil) :
    (quotientHom I a).coord = lieQuotientMap I a.coord := rfl

theorem commute_of_lie_eq_zero (a b : NilpotentLieBCHGroup L s hnil)
    (hab : ⁅a.coord, b.coord⁆ = 0) : Commute a b := by
  apply ext
  change lieBCH s a.coord b.coord = lieBCH s b.coord a.coord
  have hba : ⁅b.coord, a.coord⁆ = 0 := by rw [← lie_skew, hab, neg_zero]
  rw [lieBCH_eq_add_of_lie_eq_zero hnil hab, lieBCH_eq_add_of_lie_eq_zero hnil hba, add_comm]

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

include hnil

theorem lieBCH_sub_add_mem (I : LieIdeal ℚ L) (a b : L) (hab : ⁅a, b⁆ ∈ I) :
    lieBCH s a b - (a + b) ∈ I := by
  apply (lieQuotientMap_eq_zero I _).mp
  have hbracket : ⁅lieQuotientMap I a, lieQuotientMap I b⁆ = 0 := by
    rw [← LieHom.map_lie]
    exact (lieQuotientMap_eq_zero I _).mpr hab
  rw [map_sub, map_add, map_lieBCH,
    lieBCH_eq_add_of_lie_eq_zero (lie_quotient_lowerCentralSeries_eq_bot hnil I) hbracket, sub_self]

namespace NilpotentLieBCHGroup

theorem additive_remainder_mem (I : LieIdeal ℚ L) (r w : L) (hrw : ⁅r, w⁆ ∈ I) :
    (((⟨r⟩ : NilpotentLieBCHGroup L s hnil)⁻¹ * ⟨r + w⟩ * (⟨w⟩ : NilpotentLieBCHGroup L s hnil)⁻¹).coord) ∈ I := by
  have hsum : quotientHom I (⟨r + w⟩ : NilpotentLieBCHGroup L s hnil) =
      quotientHom I (⟨r⟩ : NilpotentLieBCHGroup L s hnil) * quotientHom I (⟨w⟩ : NilpotentLieBCHGroup L s hnil) := by
    apply ext
    change lieQuotientMap I (r + w) = lieBCH s (lieQuotientMap I r) (lieQuotientMap I w)
    rw [map_add]
    apply (lieBCH_eq_add_of_lie_eq_zero (lie_quotient_lowerCentralSeries_eq_bot hnil I) ?_).symm
    rw [← LieHom.map_lie]
    exact (lieQuotientMap_eq_zero I _).mpr hrw
  apply (lieQuotientMap_eq_zero I _).mp
  have h : quotientHom I
      ((⟨r⟩ : NilpotentLieBCHGroup L s hnil)⁻¹ * ⟨r + w⟩ * (⟨w⟩ : NilpotentLieBCHGroup L s hnil)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, map_inv, hsum]
    simp only [inv_mul_cancel_left, mul_inv_cancel]
  exact congrArg coord h

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem coord_pow (g : NilpotentLieBCHGroup L s hnil) (n : ℕ) :
    (g ^ n).coord = n • g.coord := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, coord_mul, ih,
      lieBCH_eq_add_of_lie_eq_zero hnil (by simp [nsmul_lie]), succ_nsmul]

theorem coord_zpow (g : NilpotentLieBCHGroup L s hnil) (n : ℤ) :
    (g ^ n).coord = n • g.coord := by
  cases n with
  | ofNat n =>
    change (g ^ (n : ℤ)).coord = (n : ℤ) • g.coord
    simpa only [zpow_natCast, natCast_zsmul] using coord_pow g n
  | negSucc n =>
    simp only [zpow_negSucc, coord_inv, coord_pow, negSucc_zsmul]

theorem coord_pow_rat (g : NilpotentLieBCHGroup L s hnil) (n : ℕ) :
    (g ^ n).coord = (n : ℚ) • g.coord := by
  rw [coord_pow, Nat.cast_smul_eq_nsmul ℚ]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3
variable (L : Type*) [LieRing L] [LieAlgebra ℚ L]

structure NilpotentLieFiltration (s : ℕ) where
  layer : ℕ → Submodule ℚ L
  antitone : Antitone layer
  one_eq_top : layer 1 = ⊤
  lie_mem : ∀ {i j : ℕ} {a b : L}, a ∈ layer i → b ∈ layer j → ⁅a, b⁆ ∈ layer (i + j)
  terminal : layer (s + 1) = ⊥

namespace NilpotentLieFiltration
variable {L} {s : ℕ} (F : NilpotentLieFiltration L s)
include F

def layerIdeal (i : ℕ) : LieIdeal ℚ L :=
  { F.layer i with
    lie_mem := by
      intro x y hy
      have hx : x ∈ F.layer 1 := by simp [F.one_eq_top]
      exact F.antitone (Nat.le_add_left i 1) (F.lie_mem hx hy) }

@[simp] theorem mem_layerIdeal (i : ℕ) (a : L) : a ∈ F.layerIdeal i ↔ a ∈ F.layer i := Iff.rfl

theorem lowerCentralSeries_le (n : ℕ) :
    LieModule.lowerCentralSeries ℚ L L n ≤ F.layerIdeal (n + 1) := by
  induction n with
  | zero =>
    intro a _
    change a ∈ F.layer 1
    simp [F.one_eq_top]
  | succ n ih =>
    rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lie_le_iff]
    intro a _ b hb
    have ha : a ∈ F.layer 1 := by simp [F.one_eq_top]
    have h := F.lie_mem ha (ih hb)
    change ⁅a, b⁆ ∈ F.layer (n + 1 + 1)
    simpa only [Nat.add_comm 1 (n + 1)] using h

theorem lowerCentralSeries_eq_bot : LieModule.lowerCentralSeries ℚ L L s = ⊥ := by
  apply bot_unique
  intro a ha
  have h := F.lowerCentralSeries_le s ha
  change a ∈ F.layer (s + 1) at h
  change a = 0
  simpa only [F.terminal, Submodule.mem_bot] using h

abbrev Group := NilpotentLieBCHGroup L s F.lowerCentralSeries_eq_bot

def subgroup (i : ℕ) : Subgroup F.Group :=
  NilpotentLieBCHGroup.subgroup (F.layerIdeal i).toLieSubalgebra

@[simp] theorem mem_subgroup (i : ℕ) (a : F.Group) : a ∈ F.subgroup i ↔ a.coord ∈ F.layer i := Iff.rfl

theorem subgroup_one : F.subgroup 1 = ⊤ := by
  apply top_unique
  intro a _
  change a.coord ∈ F.layer 1
  simp [F.one_eq_top]

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

def bchSubgroupCoordinates (e : Basis ι ℚ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) :
    Set (ι → ℚ) := {x | (⟨e.equivFun.symm x⟩ : NilpotentLieBCHGroup L s hL) ∈ Γ}

variable [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] in

theorem bchSubgroupCoordinates_comap (b : Basis κ ℚ M) (e : Basis ι ℚ L)
    (φ : M →ₗ⁅ℚ⁆ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) :
    bchSubgroupCoordinates b (Γ.comap (NilpotentLieBCHGroup.map (hnil := hM) φ)) =
      (LinearMap.toMatrix b e φ.toLinearMap).mulVec ⁻¹' bchSubgroupCoordinates e Γ := by
  ext x
  change ((⟨φ (b.equivFun.symm x)⟩ : NilpotentLieBCHGroup L s hL) ∈ Γ) ↔
    ((⟨e.equivFun.symm (LinearMap.toMatrix b e φ.toLinearMap *ᵥ x)⟩ :
      NilpotentLieBCHGroup L s hL) ∈ Γ)
  rw [basisMatrix_mulVec, LinearEquiv.symm_apply_apply]
  rfl

theorem exists_bchSubgroup_comap_grid_exp_bound (b : Basis κ ℚ M) (e : Basis ι ℚ L)
    (φ : M →ₗ⁅ℚ⁆ L) (hφ : Function.Injective φ)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) {H l : ℕ} (hHpos : 1 ≤ H) (hlpos : 0 < l)
    (hB : ∀ i j, RationalHeightLE (LinearMap.toMatrix b e φ.toLinearMap i j) H)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p) (hr : (Fintype.card κ : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates b
        (Γ.comap (NilpotentLieBCHGroup.map (hnil := hM) φ)) ∧
      bchSubgroupCoordinates b (Γ.comap (NilpotentLieBCHGroup.map (hnil := hM) φ)) ⊆ denominatorGrid N := by
  rw [bchSubgroupCoordinates_comap b e φ Γ]
  exact exists_preimage_grid_exp_bound (LinearMap.toMatrix b e φ.toLinearMap)
    (Matrix.mulVec_injective_iff.mp (basisMatrix_injective b e φ.toLinearMap hφ))
    hHpos hlpos hB _ hinner houter hp hd hr hH hl

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup
variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
variable {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def conjugationCoord (g : NilpotentLieBCHGroup L s hnil) (x : L) : L :=
  (g * (⟨x⟩ : NilpotentLieBCHGroup L s hnil) * g⁻¹).coord

theorem conjugationCoord_nsmul (g : NilpotentLieBCHGroup L s hnil) (n : ℕ) (x : L) :
    conjugationCoord g (n • x) = n • conjugationCoord g x := by
  have he : (⟨n • x⟩ : NilpotentLieBCHGroup L s hnil) =
      (⟨x⟩ : NilpotentLieBCHGroup L s hnil) ^ n := by
    apply ext
    exact (coord_pow _ _).symm
  change ((MulAut.conj g) (⟨n • x⟩ : NilpotentLieBCHGroup L s hnil)).coord = _
  rw [he, map_pow, coord_pow]
  rfl

theorem conjugationCoord_zsmul (g : NilpotentLieBCHGroup L s hnil) (n : ℤ) (x : L) :
    conjugationCoord g (n • x) = n • conjugationCoord g x := by
  have he : (⟨n • x⟩ : NilpotentLieBCHGroup L s hnil) =
      (⟨x⟩ : NilpotentLieBCHGroup L s hnil) ^ n := by
    apply ext
    exact (coord_zpow _ _).symm
  change ((MulAut.conj g) (⟨n • x⟩ : NilpotentLieBCHGroup L s hnil)).coord = _
  rw [he, map_zpow, coord_zpow]
  rfl

theorem conjugationCoord_rat_smul (g : NilpotentLieBCHGroup L s hnil) (q : ℚ) (x : L) :
    conjugationCoord g (q • x) = q • conjugationCoord g x := by
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hq : (q.den : ℚ) * q = (q.num : ℚ) := by
    calc
      _ = (q.den : ℚ) * ((q.num : ℚ) / q.den) :=
        congrArg ((q.den : ℚ) * ·) (Rat.num_div_den q).symm
      _ = _ := by field_simp
  apply smul_right_injective L hd
  dsimp only
  calc
    _ = conjugationCoord g ((q.den : ℚ) • (q • x)) := by
      simpa only [Nat.cast_smul_eq_nsmul] using (conjugationCoord_nsmul g q.den (q • x)).symm
    _ = conjugationCoord g ((q.num : ℚ) • x) := by rw [smul_smul, hq]
    _ = (q.num : ℚ) • conjugationCoord g x := by
      simpa only [Int.cast_smul_eq_zsmul] using conjugationCoord_zsmul g q.num x
    _ = _ := by rw [smul_smul, hq]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module

end Erdos3

end

end OAI
