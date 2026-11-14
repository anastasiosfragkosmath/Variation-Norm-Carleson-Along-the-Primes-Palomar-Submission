/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Nilpotent/RealPolynomialBCH.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Geometry.ConjugationCoordinates
@[expose] public section

namespace OAI

section

namespace Erdos3

open Module MvPolynomial

def differenceInput {ι : Type*} (a b : ι → ℚ) : Fin 3 × ι → ℚ :=
  fun ji => ![-a ji.2, b ji.2, 0] ji.1

theorem differenceInput_mem_denominatorGrid {ι : Type*} (a b : ι → ℚ) (q : ℕ)
    (ha : a ∈ denominatorGrid q) (hb : b ∈ denominatorGrid q) :
    differenceInput a b ∈ denominatorGrid q := by
  obtain ⟨za, hza⟩ := ha
  obtain ⟨zb, hzb⟩ := hb
  refine ⟨fun ji => ![-za ji.2, zb ji.2, 0] ji.1, ?_⟩
  rintro ⟨j, i⟩
  have hai : (q : ℚ) * a i = (za i : ℚ) := hza i
  have hbi : (q : ℚ) * b i = (zb i : ℚ) := hzb i
  fin_cases j <;> simp [differenceInput, Pi.smul_apply, smul_eq_mul, hai, hbi]

theorem differenceInput_sub_mem_scaledGrid {ι : Type*} (a b : ι → ℚ) (m : ℕ)
    (hba : b - a ∈ scaledIntegerGrid m) :
    differenceInput a b - differenceInput a a ∈ scaledIntegerGrid m := by
  obtain ⟨z, hz⟩ := hba
  refine ⟨fun ji => ![0, z ji.2, 0] ji.1, ?_⟩
  funext ⟨j, i⟩
  have hi := congrFun hz i
  change b i - a i = (m : ℚ) * (z i : ℚ) at hi
  fin_cases j <;> simp [differenceInput, Pi.smul_apply, smul_eq_mul, hi]

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem differenceCoordinate_eval (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (a b : NilpotentLieBCHGroup L s hnil) (i : ι) :
    eval (differenceInput (e.equivFun a.coord) (e.equivFun b.coord))
      (conjugationCoordinatePolynomial e s i) = e.repr (a⁻¹ * b).coord i := by
  let f : Fin 3 → NilpotentLieBCHGroup L s hnil := ![a⁻¹, b, 1]
  have he := bchProductCoordinatePolynomial_eval e s hnil (fun j => (f j).coord) [0, 1, 2] i
  have hp := lieBCHList_group_prod s hnil (fun j => (f j).coord) [0, 1, 2]
  rw [← hp] at he
  have hmap : ([0, 1, 2].map (fun j => (⟨(f j).coord⟩ : NilpotentLieBCHGroup L s hnil))) =
      [a⁻¹, b, 1] := by simp [f]; exact ⟨rfl, rfl⟩
  rw [hmap] at he
  simp only [List.prod_cons, List.prod_nil, mul_one] at he
  have hi : (fun ji : Fin 3 × ι => e.repr (f ji.1).coord ji.2) =
      differenceInput (e.equivFun a.coord) (e.equivFun b.coord) := by
    funext ⟨j, k⟩
    fin_cases j <;> simp [f, differenceInput]
  change eval (fun ji : Fin 3 × ι => e.repr (f ji.1).coord ji.2)
    (conjugationCoordinatePolynomial e s i) = _ at he
  rwa [hi] at he

theorem differenceCoordinate_same (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (a : NilpotentLieBCHGroup L s hnil) (i : ι) :
    eval (differenceInput (e.equivFun a.coord) (e.equivFun a.coord))
      (conjugationCoordinatePolynomial e s i) = 0 := by
  simpa using differenceCoordinate_eval e hnil a a i

theorem bch_coset_eq_of_coordinate_congruence (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (q l : ℕ) (hq : 0 < q)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (a b : NilpotentLieBCHGroup L s hnil)
    (ha : e.equivFun a.coord ∈ denominatorGrid q) (hb : e.equivFun b.coord ∈ denominatorGrid q)
    (hba : e.equivFun b.coord - e.equivFun a.coord ∈ scaledIntegerGrid
      (l * polynomialFamilyDenominator (conjugationCoordinatePolynomial e s) * q ^ s)) :
    (QuotientGroup.mk a : _ ⧸ Γ) = QuotientGroup.mk b := by
  apply QuotientGroup.eq.mpr
  apply (bchSubgroupCoordinates_repr e Γ _).mp
  apply hinner
  have h := rational_polynomial_family_eval_sub_mem_grid
    (conjugationCoordinatePolynomial e s) q s l hq (conjugationCoordinatePolynomial_degree e s)
    (differenceInput (e.equivFun a.coord) (e.equivFun b.coord))
    (differenceInput (e.equivFun a.coord) (e.equivFun a.coord))
    (differenceInput_mem_denominatorGrid _ _ q ha hb)
    (differenceInput_mem_denominatorGrid _ _ q ha ha)
    (differenceInput_sub_mem_scaledGrid _ _ _ hba)
  simp only [differenceCoordinate_same] at h
  simpa only [differenceCoordinate_eval, sub_zero,
    ← Basis.equivFun_apply] using h

end Erdos3

end

section

namespace Erdos3

open Module MvPolynomial

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

noncomputable def polynomialBCHMap (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (P : ι → MvPolynomial σ ℚ) (x : σ → ℤ) : NilpotentLieBCHGroup L s hnil :=
  ⟨e.equivFun.symm (fun i => eval (fun j => (x j : ℚ)) (P i))⟩

omit [Fintype σ] in
@[simp] theorem polynomialBCHMap_coordinates (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (P : ι → MvPolynomial σ ℚ) (x : σ → ℤ) :
    e.equivFun (polynomialBCHMap e hnil P x).coord = fun i => eval (fun j => (x j : ℚ)) (P i) :=
  e.equivFun.apply_symm_apply _

noncomputable def polynomialBCHPeriod (e : Basis ι ℚ L) (s l : ℕ)
    (P : ι → MvPolynomial σ ℚ) : ℕ :=
  (l * polynomialFamilyDenominator (conjugationCoordinatePolynomial e s) *
    polynomialFamilyDenominator P ^ s) * polynomialFamilyDenominator P

theorem polynomialBCHMap_coset_eq (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l r : ℕ)
    (P : ι → MvPolynomial σ ℚ) (hdegree : ∀ i, (P i).totalDegree ≤ r)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (x y : σ → ℤ) (hxy : ∀ j, (polynomialBCHPeriod e s l P : ℤ) ∣ x j - y j) :
    (QuotientGroup.mk (polynomialBCHMap e hnil P x) : _ ⧸ Γ) =
      QuotientGroup.mk (polynomialBCHMap e hnil P y) := by
  apply Eq.symm
  apply bch_coset_eq_of_coordinate_congruence e hnil Γ (polynomialFamilyDenominator P) l
    (polynomialFamilyDenominator_pos _) hinner
  · simpa only [polynomialBCHMap_coordinates] using polynomial_family_integer_values_grid P y
  · simpa only [polynomialBCHMap_coordinates] using polynomial_family_integer_values_grid P x
  · simp only [polynomialBCHMap_coordinates]
    exact polynomial_family_integer_congruence P r _ hdegree x y hxy

end Erdos3

end

section

namespace Erdos3

open Module MvPolynomial
open scoped Manifold ContDiff TensorProduct

variable {ι σ L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def realPolynomialBCHMap (e : Basis ι ℝ L)
    (P : ι → MvPolynomial σ ℚ) (x : σ → ℝ) : NilpotentLieBCHGroup L s hnil :=
  ⟨e.equivFun.symm (fun i => aeval x (P i))⟩

@[simp] theorem realPolynomialBCHMap_coordinates (e : Basis ι ℝ L)
    (P : ι → MvPolynomial σ ℚ) (x : σ → ℝ) :
    e.equivFun (realPolynomialBCHMap (hnil := hnil) e P x).coord =
      fun i => aeval x (P i) :=
  e.equivFun.apply_symm_apply _

section Smooth

variable [Fintype σ] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]

end Smooth

end Erdos3

namespace Erdos3

open Module MvPolynomial
open scoped TensorProduct

variable {ι σ L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem realPolynomialBCHMap_integer (e : Basis ι ℚ L)
    (P : ι → MvPolynomial σ ℚ) (x : σ → ℤ) :
    realPolynomialBCHMap (hnil := realification_lowerCentralSeries_eq_bot hnil)
      (e.baseChange ℝ) P (fun j => (x j : ℝ)) =
        NilpotentLieBCHGroup.realificationHom (polynomialBCHMap e hnil P x) := by
  apply NilpotentLieBCHGroup.ext
  apply (e.baseChange ℝ).equivFun.injective
  rw [realPolynomialBCHMap_coordinates, NilpotentLieBCHGroup.realificationHom_coordinates]
  funext i
  change aeval (fun j => (x j : ℝ)) (P i) =
    ((e.equivFun (polynomialBCHMap e hnil P x).coord i : ℚ) : ℝ)
  rw [polynomialBCHMap_coordinates]
  change aeval (fun j => (x j : ℝ)) (P i) = ((eval (fun j => (x j : ℚ)) (P i) : ℚ) : ℝ)
  induction P i using MvPolynomial.induction_on with
  | C a => simp only [aeval_C, eval_C]; rfl
  | add p q hp hq => simp only [map_add, Rat.cast_add, hp, hq]
  | mul_X p j hp => simp only [map_mul, aeval_X, eval_X, Rat.cast_mul, hp,
      Rat.cast_intCast]

theorem realification_coset_eq
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (a b : NilpotentLieBCHGroup L s hnil)
    (hab : (QuotientGroup.mk a : _ ⧸ Γ) = QuotientGroup.mk b) :
    (QuotientGroup.mk (NilpotentLieBCHGroup.realificationHom a) :
      _ ⧸ Γ.map NilpotentLieBCHGroup.realificationHom) =
        QuotientGroup.mk (NilpotentLieBCHGroup.realificationHom b) := by
  apply QuotientGroup.eq.mpr
  rw [← map_inv, ← map_mul]
  exact Subgroup.mem_map.mpr ⟨a⁻¹ * b, QuotientGroup.eq.mp hab, rfl⟩

variable [Fintype σ]

end Erdos3

end

end OAI
