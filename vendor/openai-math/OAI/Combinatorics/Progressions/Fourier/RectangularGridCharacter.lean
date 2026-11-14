/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Fourier/RectangularGridCharacter.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Instances.AddCircle.Real
@[expose] public section

namespace OAI

section

open scoped BigOperators ComplexConjugate ENNReal Real

open Finset Function MeasureTheory Set

namespace Erdos3.CircleFourier

noncomputable section

abbrev Circle := UnitAddCircle

abbrev circleHaar : Measure Circle := AddCircle.haarAddCircle

def integerDistance (x : Circle) : ℝ := ‖x‖

theorem integerDistance_nonneg (x : Circle) : 0 ≤ integerDistance x := norm_nonneg x

theorem integerDistance_le_half (x : Circle) : integerDistance x ≤ 1 / 2 := by
  simpa [integerDistance] using AddCircle.norm_le_half_period (1 : ℝ) one_ne_zero (x := x)

@[simp]
theorem integerDistance_coe (x : ℝ) :
    integerDistance (x : Circle) = |x - round x| := by
  simp [integerDistance, UnitAddCircle.norm_eq]

def character (x : Circle) : ℂ := AddCircle.toCircle x

@[simp]
theorem character_zero : character 0 = 1 := by
  simp [character]

@[simp]
theorem character_add (x y : Circle) : character (x + y) = character x * character y := by
  unfold character
  rw [AddCircle.toCircle_add]
  rfl

@[simp]
theorem character_neg (x : Circle) : character (-x) = star (character x) := by
  unfold character
  rw [AddCircle.toCircle_neg, _root_.Circle.coe_inv, Complex.inv_def,
    _root_.Circle.normSq_coe]
  simp

@[simp]
theorem character_nsmul (n : ℕ) (x : Circle) : character (n • x) = character x ^ n := by
  unfold character
  rw [AddCircle.toCircle_nsmul]
  rfl

@[simp]
theorem character_zsmul (n : ℤ) (x : Circle) : character (n • x) = character x ^ n := by
  unfold character
  rw [AddCircle.toCircle_zsmul]
  rfl

@[simp]
theorem character_finset_sum {I : Type*} (s : Finset I) (f : I → Circle) :
    character (∑ i ∈ s, f i) = ∏ i ∈ s, character (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih, character_add]

@[simp]
theorem character_fintype_sum {I : Type*} [Fintype I] (f : I → Circle) :
    character (∑ i, f i) = ∏ i, character (f i) := by
  simp

@[simp]
theorem norm_character (x : Circle) : ‖character x‖ = 1 := by
  exact Circle.norm_coe _

theorem character_eq_one_iff (x : Circle) : character x = 1 ↔ x = 0 := by
  constructor
  · intro h
    apply AddCircle.injective_toCircle one_ne_zero
    apply Subtype.ext
    simpa [character] using h
  · rintro rfl
    exact character_zero

def geometricCharacterSum (N : ℕ) (x : Circle) : ℂ :=
  ∑ n ∈ range N, character (n • x)

theorem geometricCharacterSum_mul (N : ℕ) (x : Circle) :
    geometricCharacterSum N x * (character x - 1) = character (N • x) - 1 := by
  simp only [geometricCharacterSum, character_nsmul]
  exact geom_sum_mul (character x) N

theorem norm_character_sub_one_le_two (x : Circle) : ‖character x - 1‖ ≤ 2 := by
  calc
    ‖character x - 1‖ ≤ ‖character x‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num

theorem four_mul_integerDistance_le_norm_character_sub_one (x : Circle) :
    4 * integerDistance x ≤ ‖character x - 1‖ := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective x
  let y : ℝ := r - round r
  have hyabs : |y| ≤ 1 / 2 := by
    simpa [y] using abs_sub_round r
  have hypi_abs : |π * y| ≤ π / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hsin : 2 * |y| ≤ |Real.sin (π * y)| := by
    have h := Real.mul_abs_le_abs_sin hypi_abs
    calc
      2 * |y| = (2 / π) * |π * y| := by
        rw [abs_mul, abs_of_pos Real.pi_pos]
        field_simp [Real.pi_ne_zero]
      _ ≤ |Real.sin (π * y)| := h
  have hry : (r : Circle) = (y : Circle) := by
    simp [y, sub_eq_add_neg]
  have hcharacter :
      character (y : Circle) = Complex.exp (Complex.I * (2 * π * y : ℝ)) := by
    unfold character
    rw [AddCircle.toCircle, Function.Periodic.lift_coe, Circle.coe_exp]
    congr 1
    push_cast
    ring
  rw [integerDistance_coe]
  change 4 * |y| ≤ _
  rw [hry, hcharacter, Complex.norm_exp_I_mul_ofReal_sub_one]
  change 4 * |y| ≤ |2 * Real.sin ((2 * π * y) / 2)|
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    4 * |y| = 2 * (2 * |y|) := by ring
    _ ≤ 2 * |Real.sin (π * y)| :=
      mul_le_mul_of_nonneg_left hsin (by norm_num)
    _ = 2 * |Real.sin ((2 * π * y) / 2)| := by ring_nf

theorem two_mul_integerDistance_mul_norm_geometricCharacterSum_le_one
    (N : ℕ) (x : Circle) :
    2 * integerDistance x * ‖geometricCharacterSum N x‖ ≤ 1 := by
  have hprod :
      ‖geometricCharacterSum N x‖ * ‖character x - 1‖ ≤ 2 := by
    rw [← norm_mul, geometricCharacterSum_mul]
    exact norm_character_sub_one_le_two _
  have hden := four_mul_integerDistance_le_norm_character_sub_one x
  have hnorm : 0 ≤ ‖geometricCharacterSum N x‖ := norm_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hden hnorm]

theorem geometricCharacterSum_eq_sum_fin (N : ℕ) (x : Circle) :
    geometricCharacterSum N x = ∑ n : Fin N, character ((n : ℕ) • x) := by
  rw [Finset.sum_fin_eq_sum_range]
  rw [geometricCharacterSum]
  apply Finset.sum_congr rfl
  intro n hn
  simp [Finset.mem_range.mp hn]

end
end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped Real NNReal

noncomputable def characterLipConstant : ℝ≥0 := ⟨2 * Real.pi, by positivity⟩

theorem coe_characterLipConstant : (characterLipConstant : ℝ) = 2 * Real.pi := rfl

theorem character_coe_exp (r : ℝ) :
    character (r : Circle) = Complex.exp (Complex.I * (2 * Real.pi * r : ℝ)) := by
  unfold character
  rw [AddCircle.toCircle, Function.Periodic.lift_coe, _root_.Circle.coe_exp]
  congr 1
  push_cast
  ring

theorem norm_character_sub_one_le (x : Circle) :
    ‖character x - 1‖ ≤ 2 * Real.pi * ‖x‖ := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective x
  let y : ℝ := r - round r
  have hry : (r : Circle) = (y : Circle) := by simp [y, sub_eq_add_neg]
  change ‖character (r : Circle) - 1‖ ≤ 2 * Real.pi * integerDistance (r : Circle)
  rw [integerDistance_coe]
  change ‖character (r : Circle) - 1‖ ≤ 2 * Real.pi * |y|
  rw [hry, character_coe_exp, Complex.norm_exp_I_mul_ofReal_sub_one]
  have heq : (2 * Real.pi * y) / 2 = Real.pi * y := by ring
  rw [heq, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ 2 * |Real.pi * y| := mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = _ := by rw [abs_mul, abs_of_pos Real.pi_pos]; ring

theorem character_lipschitz : LipschitzWith characterLipConstant character := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hxy : character (x - y) * character y = character x := by
    rw [← character_add, sub_add_cancel]
  have heq : (character (x - y) - 1) * character y = character x - character y := by
    rw [sub_mul, one_mul, hxy]
  have hnorm : ‖character x - character y‖ = ‖character (x - y) - 1‖ := by
    rw [← heq, norm_mul, norm_character, mul_one]
  rw [dist_eq_norm, hnorm, dist_eq_norm]
  exact norm_character_sub_one_le (x - y)

end Erdos3.CircleFourier

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open CircleFourier

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open Module
open scoped BigOperators NNReal

theorem abs_linearMap_le_basis_bound {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℝ V] (e : Basis ι ℝ V) (η : V →ₗ[ℝ] ℝ)
    (A : ℝ≥0) (hη : ∀ i, |η (e i)| ≤ A) (x : V) :
    |η x| ≤ (Fintype.card ι : ℝ) * A * ‖e.equivFun x‖ := by
  have hx : η x = ∑ i, e.repr x i * η (e i) := by
    conv_lhs => rw [← e.sum_repr x]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [hx]
  calc
    _ ≤ ∑ i, |e.repr x i * η (e i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, ‖e.equivFun x‖ * A := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      have he : |e.repr x i| ≤ ‖e.equivFun x‖ := by
        simpa only [Real.norm_eq_abs, Basis.equivFun_apply] using (norm_le_pi_norm (e.equivFun x) i)
      exact mul_le_mul he (hη i) (abs_nonneg _) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem norm_character_real_sub_one_le (r : ℝ) :
    ‖CircleFourier.character (r : CircleFourier.Circle) - 1‖ ≤
      (CircleFourier.characterLipConstant : ℝ) * |r| := by
  apply (CircleFourier.norm_character_sub_one_le _).trans
  exact mul_le_mul_of_nonneg_left
    (by simpa only [Real.norm_eq_abs] using
      (show ‖(r : CircleFourier.Circle)‖ ≤ ‖r‖ from QuotientAddGroup.norm_mk_le_norm))
    (by positivity : 0 ≤ 2 * Real.pi)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

end Erdos3

end

end OAI
