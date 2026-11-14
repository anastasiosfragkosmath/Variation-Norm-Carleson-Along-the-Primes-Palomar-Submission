module

public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Analysis.Normed.Group.Int
public import Mathlib.Tactic.Linarith

/-!
# Distance to the nearest integer: elementary facts

Part of the Vinogradov-type estimates used by the extrapolation step of the iteration of
`C2/CMain.lean` (proof of [F+] Proposition 3.1). The quantity `‖x‖_{ℝ/ℤ}` of Leng's Lemma
`l:vinogradov` (arXiv:2312.10772v5 TeX L1471) is, throughout the
development `PrimeCarleson/Proof/Fplus31/Vinogradov/`, Mathlib's norm of the class of `x` in the
circle group, `‖(x : UnitAddCircle)‖ = |x - round x|`. This file collects the facts used about it:

* `norm_coe_le_abs_sub`, `exists_abs_sub_le_of_norm_coe_le`: `‖x‖ ≤ r` iff some integer lies
  within `r` of `x`;
* `norm_coe_add_le`, `norm_coe_neg`, `norm_coe_sub_le`: triangle inequality and symmetry;
* `norm_intCast_mul_coe_le`, `norm_natCast_mul_coe_le`: `‖n x‖ ≤ |n| ‖x‖` for an integer `n`
  (resp. `≤ n ‖x‖` for a natural number `n`);
* `norm_coe_add_intCast`: invariance under integer translation.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- The distance to the nearest integer: `‖(x : ℝ/ℤ)‖ = |x - round x|`. -/
theorem norm_coe_eq_abs_sub_round (x : ℝ) : ‖(x : UnitAddCircle)‖ = |x - round x| :=
  UnitAddCircle.norm_eq

/-- `‖x‖_{ℝ/ℤ} ≤ |x - m|` for every integer `m`. -/
theorem norm_coe_le_abs_sub (x : ℝ) (m : ℤ) : ‖(x : UnitAddCircle)‖ ≤ |x - m| := by
  rw [norm_coe_eq_abs_sub_round]
  exact round_le x m

/-- If `‖x‖_{ℝ/ℤ} ≤ r` then some integer lies within `r` of `x`. -/
theorem exists_abs_sub_le_of_norm_coe_le {x r : ℝ} (h : ‖(x : UnitAddCircle)‖ ≤ r) :
    ∃ m : ℤ, |x - m| ≤ r :=
  ⟨round x, by rwa [norm_coe_eq_abs_sub_round] at h⟩

/-- The triangle inequality for the distance to the nearest integer. -/
theorem norm_coe_add_le (x y : ℝ) :
    ‖((x + y : ℝ) : UnitAddCircle)‖ ≤ ‖(x : UnitAddCircle)‖ + ‖(y : UnitAddCircle)‖ := by
  rw [AddCircle.coe_add]
  exact norm_add_le _ _

/-- `‖-x‖_{ℝ/ℤ} = ‖x‖_{ℝ/ℤ}`. -/
theorem norm_coe_neg (x : ℝ) : ‖((-x : ℝ) : UnitAddCircle)‖ = ‖(x : UnitAddCircle)‖ := by
  rw [AddCircle.coe_neg, norm_neg]

/-- `‖x - y‖_{ℝ/ℤ} ≤ ‖x‖_{ℝ/ℤ} + ‖y‖_{ℝ/ℤ}`. -/
theorem norm_coe_sub_le (x y : ℝ) :
    ‖((x - y : ℝ) : UnitAddCircle)‖ ≤ ‖(x : UnitAddCircle)‖ + ‖(y : UnitAddCircle)‖ := by
  rw [sub_eq_add_neg, ← norm_coe_neg y]
  exact norm_coe_add_le _ _

/-- `‖n x‖_{ℝ/ℤ} ≤ |n| ‖x‖_{ℝ/ℤ}` for an integer `n`. -/
theorem norm_intCast_mul_coe_le (n : ℤ) (x : ℝ) :
    ‖(((n : ℝ) * x : ℝ) : UnitAddCircle)‖ ≤ |(n : ℝ)| * ‖(x : UnitAddCircle)‖ := by
  have h : (((n : ℝ) * x : ℝ) : UnitAddCircle) = n • (x : UnitAddCircle) := by
    rw [← AddCircle.coe_zsmul]
    simp
  rw [h]
  calc _ ≤ ‖n‖ * ‖(x : UnitAddCircle)‖ := norm_zsmul_le _ _
    _ = _ := by rw [Int.norm_eq_abs]

/-- `‖n x‖_{ℝ/ℤ} ≤ n ‖x‖_{ℝ/ℤ}` for a natural number `n`. -/
theorem norm_natCast_mul_coe_le (n : ℕ) (x : ℝ) :
    ‖(((n : ℝ) * x : ℝ) : UnitAddCircle)‖ ≤ n * ‖(x : UnitAddCircle)‖ := by
  have h := norm_intCast_mul_coe_le (n : ℤ) x
  simpa using h

/-- `‖x + m‖_{ℝ/ℤ} = ‖x‖_{ℝ/ℤ}` for an integer `m`. -/
theorem norm_coe_add_intCast (x : ℝ) (m : ℤ) :
    ‖((x + m : ℝ) : UnitAddCircle)‖ = ‖(x : UnitAddCircle)‖ := by
  rw [AddCircle.coe_add]
  have h : ((m : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨m, by simp⟩
  rw [h, add_zero]

end PrimeCarleson.Proof.Fplus31
