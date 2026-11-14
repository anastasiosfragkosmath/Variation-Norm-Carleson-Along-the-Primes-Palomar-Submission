module

public import PrimeCarleson.Frozen.Exp
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Exponential and periodic-sum lemmas for the proof of `p:goal0`

Elementary identities for `PrimeCarleson.e` and for sums of periodic functions over one
period, used for the Ramanujan-sum identities (`sources/Variational_Carleson.tex`,
(e:ram) L587-L589, the proof of the periodic-fiber lemma L2308-L2312, and the proof of
(e:supLest) L2611-L2621):

* `e_add`, `e_zero`, `e_intCast`, `e_add_intCast`, `norm_e`, `e_neg`: the additive-character
  properties of `e`;
* `sum_range_e_mul_div`: orthogonality of the characters of `ℤ / D`;
* `sum_range_add_of_periodic`, `sum_range_sub_of_periodic`: a sum over one period of a
  periodic function is invariant under shifts and reflections;
* `sum_range_mul_eq`: splitting `[0, d D)` as `a + d s`.
-/

@[expose] public noncomputable section

open Finset
open scoped ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Goal0

/-- `e` converts addition to multiplication. -/
theorem e_add (s t : ℝ) : e (s + t) = e s * e t := by
  unfold e
  rw [← Complex.exp_add]
  push_cast
  ring_nf

/-- `e 0 = 1`. -/
theorem e_zero : e 0 = 1 := by
  simp [e]

/-- `e k = 1` for integer `k`. -/
theorem e_intCast (k : ℤ) : e k = 1 := by
  unfold e
  have := Complex.exp_int_mul_two_pi_mul_I k
  rw [← this]
  congr 1
  push_cast
  ring

/-- `e` is `1`-periodic. -/
theorem e_add_intCast (t : ℝ) (k : ℤ) : e (t + k) = e t := by
  rw [e_add, e_intCast, mul_one]

/-- `e` takes values on the unit circle. -/
theorem norm_e (t : ℝ) : ‖e t‖ = 1 := by
  unfold e
  have : (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/-- `e (-t)` is the complex conjugate of `e t`. -/
theorem e_neg (t : ℝ) : e (-t) = (starRingEnd ℂ) (e t) := by
  unfold e
  rw [← Complex.exp_conj]
  congr 1
  simp [map_mul, map_ofNat]

/-- Orthogonality of characters of `ℤ / D`. -/
theorem sum_range_e_mul_div {D : ℕ} (hD : 0 < D) (k : ℤ) :
    ∑ l ∈ Finset.range D, e ((l : ℝ) * k / D) = if (D : ℤ) ∣ k then (D : ℂ) else 0 := by
  set z : ℂ := e ((k : ℝ) / D) with hz
  have hterm : ∀ l : ℕ, e ((l : ℝ) * k / D) = z ^ l := by
    intro l
    induction l with
    | zero => simp [e_zero]
    | succ n ih =>
      have : ((n + 1 : ℕ) : ℝ) * k / D = (n : ℝ) * k / D + (k : ℝ) / D := by
        push_cast; ring
      rw [this, e_add, ih, pow_succ]
  simp_rw [hterm]
  split_ifs with hdvd
  · obtain ⟨m, rfl⟩ := hdvd
    have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    have : ((D : ℤ) * m : ℤ) = (D : ℝ) * m := by push_cast; ring
    have hz1 : z = 1 := by
      rw [hz]
      have : (((D : ℤ) * m : ℤ) : ℝ) / D = (m : ℝ) := by
        push_cast; field_simp
      rw [this, e_intCast]
    simp [hz1]
  · have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    have hz1 : z ≠ 1 := by
      intro h
      rw [hz, e, Complex.exp_eq_one_iff] at h
      obtain ⟨n, hn⟩ := h
      apply hdvd
      refine ⟨n, ?_⟩
      have h2 : ((k : ℝ) / D : ℝ) = n := by
        have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
          simp [Real.pi_ne_zero]
        have : (((k : ℝ) / D : ℝ) : ℂ) = (n : ℂ) := by
          apply mul_right_cancel₀ hpi
          rw [← hn]
          ring
        exact_mod_cast this
      have h3 : (k : ℝ) = D * n := by
        field_simp at h2
        linarith
      exact_mod_cast h3
    have hzD : z ^ D = 1 := by
      rw [← hterm D]
      have : (D : ℝ) * k / D = (k : ℝ) := by field_simp
      rw [this, e_intCast]
    rw [geom_sum_eq hz1, hzD]
    simp

/-- A sum over one period is invariant under shifts. -/
theorem sum_range_add_of_periodic {M : Type*} [AddCommMonoid M] {F : ℤ → M} {D : ℕ}
    (hF : Function.Periodic F D) (c : ℤ) :
    ∑ l ∈ Finset.range D, F (l + c) = ∑ l ∈ Finset.range D, F l := by
  have step : ∀ c : ℤ, ∑ l ∈ Finset.range D, F (l + (c + 1)) = ∑ l ∈ Finset.range D, F (l + c) := by
    intro c
    rcases Nat.eq_zero_or_pos D with rfl | hD
    · simp
    obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
    set G : ℕ → M := fun l => F (l + c) with hG
    have h1 := Finset.sum_range_succ' G D'
    have h2 := Finset.sum_range_succ (fun l : ℕ => G (l + 1)) D'
    have h3 : G (D' + 1) = G 0 := by
      simp only [hG]
      have := hF ((0 : ℕ) + c)
      rw [← this]
      push_cast
      ring_nf
    have h4 : ∀ l : ℕ, F (l + (c + 1)) = G (l + 1) := by
      intro l
      simp only [hG]
      push_cast
      ring_nf
    simp_rw [h4]
    rw [h2, h3]
    rw [h1]
  induction c using Int.induction_on with
  | zero => simp
  | succ i ih => rw [← ih, step]
  | pred i ih => rw [← ih, ← step (-(i : ℤ) - 1), sub_add_cancel]

/-- A sum over one period of a reflected function is invariant under shifts. -/
theorem sum_range_sub_of_periodic {M : Type*} [AddCommMonoid M] {F : ℤ → M} {D : ℕ}
    (hF : Function.Periodic F D) (c : ℤ) :
    ∑ l ∈ Finset.range D, F (c - l) = ∑ l ∈ Finset.range D, F l := by
  rw [← Finset.sum_range_reflect (fun l : ℕ => F (c - l)) D]
  rw [← sum_range_add_of_periodic hF (c - D + 1)]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Finset.mem_range] at hl
  congr 1
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

/-- Splitting `[0, d D)` as `a + d s`. -/
theorem sum_range_mul_eq {M : Type*} [AddCommMonoid M] (d D : ℕ) (F : ℕ → M) :
    ∑ x ∈ Finset.range (d * D), F x =
      ∑ a ∈ Finset.range d, ∑ s ∈ Finset.range D, F (a + d * s) := by
  induction D with
  | zero => simp
  | succ D ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp_rw [Finset.sum_range_succ]
    rw [Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [add_comm]

end PrimeCarleson.Proof.Goal0
