module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Ring.Periodic

/-!
# One period as a Hilbert space

The proof of Proposition `p:goal0` formalized here (`sources/Variational_Carleson.tex`
L2545–L2817) works with `N`-periodic functions `f : ℤ → ℂ` and the unnormalised norm
`(∑_{x ∈ [0, N)} |f x|²)^{1/2}` (the paper's normalised norms on `[N]` and `(-N, 2N]` differ by
constant factors that cancel in every operator-norm ratio). This file provides

* `l2 N F`, the `ℓ²` norm of `F : ℤ → ℝ` over one period, with Minkowski's inequality;
* the bridge `toFun` / `ofFun` between `EuclideanSpace ℂ (Fin N)` and `N`-periodic functions,
  under which the norm and inner product become sums over one period. The abstract energy
  decrement (`PrimeCarleson.Proof.Goal0.le_of_inverse_theorem`) is applied in this space.
-/

@[expose] public noncomputable section

open Finset
open scoped InnerProductSpace ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Goal0

/-- The unnormalised `ℓ²` norm of `F` over one period `[0, N)`. -/
def l2 (N : ℕ) (F : ℤ → ℝ) : ℝ := √(∑ x ∈ range N, F x ^ 2)

theorem l2_nonneg (N : ℕ) (F : ℤ → ℝ) : 0 ≤ l2 N F := Real.sqrt_nonneg _

theorem l2_sq (N : ℕ) (F : ℤ → ℝ) : l2 N F ^ 2 = ∑ x ∈ range N, F x ^ 2 :=
  Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)

/-- `l2` is monotone on nonnegative functions. -/
theorem l2_mono {N : ℕ} {F G : ℤ → ℝ} (hF : ∀ x, 0 ≤ F x) (h : ∀ x, F x ≤ G x) :
    l2 N F ≤ l2 N G :=
  Real.sqrt_le_sqrt (sum_le_sum fun x _ => pow_le_pow_left₀ (hF x) (h x) 2)

theorem l2_const_mul (N : ℕ) {c : ℝ} (hc : 0 ≤ c) (F : ℤ → ℝ) :
    l2 N (fun x => c * F x) = c * l2 N F := by
  simp only [l2, mul_pow, ← mul_sum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

theorem l2_zero (N : ℕ) : l2 N (fun _ => 0) = 0 := by simp [l2]

/-- `l2 N F` is the norm of the vector `(F 0, …, F (N - 1))`. -/
theorem l2_eq_norm (N : ℕ) (F : ℤ → ℝ) :
    l2 N F = ‖(WithLp.toLp 2 (fun i : Fin N => F (i : ℕ)) : EuclideanSpace ℝ (Fin N))‖ := by
  rw [EuclideanSpace.norm_eq, l2]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun x : ℕ => F x ^ 2)]
  simp

/-- Minkowski's inequality over one period. -/
theorem l2_add_le (N : ℕ) (F G : ℤ → ℝ) : l2 N (fun x => F x + G x) ≤ l2 N F + l2 N G := by
  rw [l2_eq_norm, l2_eq_norm N F, l2_eq_norm N G]
  exact (congrArg norm (by ext; simp)).trans_le (norm_add_le _ _)

theorem l2_sum_le {ι : Type*} (N : ℕ) (s : Finset ι) (F : ι → ℤ → ℝ) :
    l2 N (fun x => ∑ i ∈ s, F i x) ≤ ∑ i ∈ s, l2 N (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l2_zero]
  | insert a s ha ih =>
    simp only [sum_insert ha]
    exact (l2_add_le N (F a) fun x => ∑ i ∈ s, F i x).trans (by linarith)

variable {N : ℕ} [NeZero N]

theorem toNat_emod_lt (x : ℤ) : (x % (N : ℤ)).toNat < N := by
  have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_neZero N
  have h0 := Int.emod_nonneg x hN.ne'
  have h1 := Int.emod_lt_of_pos x hN
  omega

/-- The `N`-periodic function with values `v 0, …, v (N - 1)` on one period. -/
def toFun (v : EuclideanSpace ℂ (Fin N)) (x : ℤ) : ℂ :=
  v ⟨(x % (N : ℤ)).toNat, toNat_emod_lt x⟩

/-- The vector of values of `f` on one period. -/
def ofFun (f : ℤ → ℂ) : EuclideanSpace ℂ (Fin N) := WithLp.toLp 2 fun i => f (i : ℕ)

theorem toFun_natCast (v : EuclideanSpace ℂ (Fin N)) (i : Fin N) : toFun v (i : ℕ) = v i := by
  have h : ((i : ℕ) : ℤ) % (N : ℤ) = (i : ℕ) := Int.emod_eq_of_lt (by omega) (by exact_mod_cast i.2)
  have hi : (⟨(((i : ℕ) : ℤ) % (N : ℤ)).toNat, toNat_emod_lt _⟩ : Fin N) = i :=
    Fin.ext (by simp only [h, Int.toNat_natCast])
  unfold toFun
  rw [hi]

theorem toFun_periodic (v : EuclideanSpace ℂ (Fin N)) : Function.Periodic (toFun v) N := by
  intro x
  simp [toFun, Int.add_emod_right]

theorem toFun_ofFun {f : ℤ → ℂ} (hf : Function.Periodic f N) : toFun (ofFun (N := N) f) = f := by
  funext x
  simp only [toFun, ofFun, PiLp.toLp_apply]
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne N : N ≠ 0)
  have h0 : 0 ≤ x % (N : ℤ) := Int.emod_nonneg x hN
  rw [Int.toNat_of_nonneg h0, Int.emod_def]
  simpa only [Int.cast_id, mul_comm] using hf.sub_int_mul_eq (x := x) (x / (N : ℤ))

theorem toFun_add (v w : EuclideanSpace ℂ (Fin N)) : toFun (v + w) = toFun v + toFun w := by
  funext x
  simp [toFun]

theorem toFun_smul (c : ℂ) (v : EuclideanSpace ℂ (Fin N)) : toFun (c • v) = c • toFun v := by
  funext x
  simp [toFun]

theorem toFun_zero : toFun (0 : EuclideanSpace ℂ (Fin N)) = 0 := by
  funext x
  simp [toFun]

theorem norm_eq_l2 (v : EuclideanSpace ℂ (Fin N)) : ‖v‖ = l2 N fun x => ‖toFun v x‖ := by
  rw [EuclideanSpace.norm_eq, l2]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun x : ℕ => ‖toFun v x‖ ^ 2)]
  simp only [toFun_natCast]

theorem inner_eq_sum (v w : EuclideanSpace ℂ (Fin N)) :
    ⟪v, w⟫_ℂ = ∑ x ∈ range N, conj (toFun v x) * toFun w x := by
  rw [PiLp.inner_apply, ← Fin.sum_univ_eq_sum_range (fun x : ℕ => conj (toFun v x) * toFun w x)]
  simp only [toFun_natCast, RCLike.inner_apply']

end PrimeCarleson.Proof.Goal0
