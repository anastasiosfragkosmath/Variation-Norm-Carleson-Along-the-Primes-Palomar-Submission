module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith

/-!
# The abstract model of the extrapolation: a graded step-two Lie algebra and its group

Part of the abstract extrapolation (the extrapolation step of the iteration of `C2/CMain.lean`,
proof of [F+] Proposition 3.1). Mathlib only: no niltest plumbing.

A graded Lie algebra `g = g₁ ⊕ g₂` of step two over `ℚ`, with a basis adapted to the grading, is
given by its structure constants (`Step2Algebra`): `ι₁` and `ι₂` index the bases of `g₁` and `g₂`
and `c i j k` is the `k`-th coordinate of the bracket `β(b_i, b_j) ∈ g₂` of two basis vectors of
`g₁` (`g₂` is central, so there is nothing else).  The group of the symbol is the BCH group of
`ℝ ⊗ g`: `SymbolGroup a` with product `(x₁, x₂)(y₁, y₂) = (x₁ + y₁, x₂ + y₂ + ½ β(x₁, y₁))`.

* `Step2Algebra.br`: the bilinear map `β` on `K`-vectors, `K = ℚ` or `ℝ`;
* `SymbolGroup`, `SymbolGroup.dil`: the group and the grading dilations
  `δ_t(x₁, x₂) = (t x₁, t² x₂)`;

The graded subalgebras `GradedSubalg` and the data `Datum` are in `Datum.lean`.

`ratLogHeight q = log (max |num q| (den q))` is the definition of the vendored library's
`rationalLogHeight`
(`OAI/Combinatorics/Progressions/Nilpotent/NiltestBasepointNormalization.lean:352`).
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- The logarithmic height of a rational number: `log (max |numerator| denominator)`.  This is
the definition of `OAI.Erdos3.rationalLogHeight`. -/
def ratLogHeight (q : ℚ) : ℝ :=
  Real.log (max (q.num.natAbs : ℝ) (q.den : ℝ))

/-- A graded step-two Lie algebra over `ℚ` with a basis adapted to the grading: `ι₁` indexes the
basis of `g₁`, `ι₂` that of `g₂`, and `c i j k` is the `k`-th coordinate of the bracket of the
`i`-th and `j`-th basis vectors of `g₁` (an alternating map `g₁ × g₁ → g₂`). -/
structure Step2Algebra (ι₁ ι₂ : Type*) where
  /-- The structure constants. -/
  c : ι₁ → ι₁ → ι₂ → ℚ
  /-- Antisymmetry of the bracket. -/
  c_neg : ∀ i j k, c j i k = -c i j k

namespace Step2Algebra

variable {ι₁ ι₂ : Type*} [Fintype ι₁] (a : Step2Algebra ι₁ ι₂)
variable {K : Type*} [Field K]

/-- The bracket `β : g₁ × g₁ → g₂`, extended bilinearly to `K`-vectors. -/
def br (x y : ι₁ → K) : ι₂ → K :=
  fun k => ∑ i, ∑ j, x i * y j * (a.c i j k : K)

theorem br_apply (x y : ι₁ → K) (k : ι₂) :
    a.br x y k = ∑ i, ∑ j, x i * y j * (a.c i j k : K) := rfl

theorem br_add_left (x x' y : ι₁ → K) : a.br (x + x') y = a.br x y + a.br x' y := by
  ext k
  simp [br_apply, add_mul, Finset.sum_add_distrib]

theorem br_add_right (x y y' : ι₁ → K) : a.br x (y + y') = a.br x y + a.br x y' := by
  ext k
  simp [br_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem br_smul_left (t : K) (x y : ι₁ → K) : a.br (t • x) y = t • a.br x y := by
  ext k
  simp only [br_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem br_smul_right (t : K) (x y : ι₁ → K) : a.br x (t • y) = t • a.br x y := by
  ext k
  simp only [br_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

@[simp] theorem br_zero_left (y : ι₁ → K) : a.br 0 y = 0 := by
  ext k
  simp [br_apply]

@[simp] theorem br_zero_right (x : ι₁ → K) : a.br x 0 = 0 := by
  ext k
  simp [br_apply]

theorem br_neg_left (x y : ι₁ → K) : a.br (-x) y = -a.br x y := by
  have := a.br_smul_left (-1 : K) x y
  simpa using this

theorem br_neg_right (x y : ι₁ → K) : a.br x (-y) = -a.br x y := by
  have := a.br_smul_right (-1 : K) x y
  simpa using this

section CharZero

variable [CharZero K]

/-- The bracket is alternating: `β(x, x) = 0`. -/
theorem br_self (x : ι₁ → K) : a.br x x = 0 := by
  ext k
  have h : a.br x x k = -a.br x x k := by
    conv_lhs => rw [br_apply, Finset.sum_comm]
    rw [br_apply, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [a.c_neg i j k]
    push_cast
    ring
  have h2 : (2 : K) * a.br x x k = 0 := by linear_combination h
  have h3 : a.br x x k = 0 := by
    rcases mul_eq_zero.mp h2 with h4 | h4
    · exact absurd h4 two_ne_zero
    · exact h4
  simpa using h3

end CharZero

end Step2Algebra

/-- The group of the symbol of a graded step-two Lie algebra: the BCH group of `ℝ ⊗ g`,
`(x₁, x₂)(y₁, y₂) = (x₁ + y₁, x₂ + y₂ + ½ β(x₁, y₁))`. -/
@[ext] structure SymbolGroup {ι₁ ι₂ : Type*} (_a : Step2Algebra ι₁ ι₂) where
  /-- The layer-one coordinates. -/
  fst : ι₁ → ℝ
  /-- The layer-two coordinates. -/
  snd : ι₂ → ℝ

namespace SymbolGroup

variable {ι₁ ι₂ : Type*} {a : Step2Algebra ι₁ ι₂}

instance : One (SymbolGroup a) := ⟨⟨0, 0⟩⟩

instance : Inv (SymbolGroup a) := ⟨fun x => ⟨-x.fst, -x.snd⟩⟩

@[simp] theorem one_fst : (1 : SymbolGroup a).fst = 0 := rfl

@[simp] theorem one_snd : (1 : SymbolGroup a).snd = 0 := rfl

@[simp] theorem inv_fst (x : SymbolGroup a) : x⁻¹.fst = -x.fst := rfl

@[simp] theorem inv_snd (x : SymbolGroup a) : x⁻¹.snd = -x.snd := rfl

variable [Fintype ι₁]

instance : Mul (SymbolGroup a) :=
  ⟨fun x y => ⟨x.fst + y.fst, x.snd + y.snd + (1 / 2 : ℝ) • a.br x.fst y.fst⟩⟩

@[simp] theorem mul_fst (x y : SymbolGroup a) : (x * y).fst = x.fst + y.fst := rfl

@[simp] theorem mul_snd (x y : SymbolGroup a) :
    (x * y).snd = x.snd + y.snd + (1 / 2 : ℝ) • a.br x.fst y.fst := rfl

instance : Group (SymbolGroup a) where
  mul_assoc x y z := by
    ext1
    · simp [add_assoc]
    · simp only [mul_snd, mul_fst, Step2Algebra.br_add_left, Step2Algebra.br_add_right, smul_add]
      abel
  one_mul x := by
    ext1 <;> simp
  mul_one x := by
    ext1 <;> simp
  inv_mul_cancel x := by
    ext1
    · simp
    · simp [Step2Algebra.br_neg_left, Step2Algebra.br_self]

/-- The coordinates of a triple product `E * P * R`. -/
theorem mul₃_fst (e p r : SymbolGroup a) : (e * p * r).fst = e.fst + p.fst + r.fst := by
  simp

theorem mul₃_snd (e p r : SymbolGroup a) :
    (e * p * r).snd = e.snd + p.snd + r.snd +
      (1 / 2 : ℝ) • (a.br e.fst p.fst + a.br e.fst r.fst + a.br p.fst r.fst) := by
  simp only [mul_snd, mul_fst, Step2Algebra.br_add_left, smul_add]
  abel

/-- The grading dilation `δ_t(x₁, x₂) = (t x₁, t² x₂)`, a group endomorphism. -/
def dil (t : ℝ) : SymbolGroup a →* SymbolGroup a where
  toFun x := ⟨t • x.fst, (t ^ 2) • x.snd⟩
  map_one' := by ext1 <;> simp
  map_mul' x y := by
    ext1
    · simp [smul_add]
    · simp only [mul_snd, Step2Algebra.br_smul_left, Step2Algebra.br_smul_right]
      ext k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring

@[simp] theorem dil_fst (t : ℝ) (x : SymbolGroup a) : (dil t x).fst = t • x.fst := rfl

@[simp] theorem dil_snd (t : ℝ) (x : SymbolGroup a) : (dil t x).snd = (t ^ 2) • x.snd := rfl

theorem dil_dil_inv {t : ℝ} (ht : t ≠ 0) (x : SymbolGroup a) : dil t⁻¹ (dil t x) = x := by
  ext1
  · ext i
    simp [ht]
  · ext k
    simp [ht]

end SymbolGroup

end PrimeCarleson.Proof.Fplus31
