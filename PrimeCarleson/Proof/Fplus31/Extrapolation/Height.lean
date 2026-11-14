module

public import PrimeCarleson.Proof.Fplus31.Extrapolation.Model
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Int.Interval
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

/-!
# Heights of rational numbers and vectors (the extrapolation step)

Part of the abstract extrapolation (the extrapolation step of the iteration of `C2/CMain.lean`,
proof of [F+] Proposition 3.1). Elementary facts about `ratLogHeight q = log (max |num q| (den q))`:

* `num_den_le_exp`: numerator and denominator of a rational of log-height at most `p` are at
  most `e^p`;
* `ratBall N`: the finite set of rationals with numerator and denominator at most `N`, of
  cardinality at most `(2 N + 1) N` (the count behind the pigeonhole of Step 1);
* `exists_clear_denominators`: a vector of `n` rationals of log-height at most `p` becomes an
  integer vector of sup norm at most `e^{p n}` after multiplication by a positive integer.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

theorem ratLogHeight_zero : ratLogHeight 0 = 0 := by
  simp [ratLogHeight]

theorem one_le_max_num_den (q : ℚ) : (1 : ℝ) ≤ max (q.num.natAbs : ℝ) (q.den : ℝ) := by
  have : (1 : ℝ) ≤ q.den := by exact_mod_cast q.den_pos
  exact this.trans (le_max_right _ _)

/-- A rational of log-height at most `p` has numerator and denominator at most `e^p`. -/
theorem num_den_le_exp {q : ℚ} {p : ℝ} (h : ratLogHeight q ≤ p) :
    (q.num.natAbs : ℝ) ≤ Real.exp p ∧ (q.den : ℝ) ≤ Real.exp p := by
  have h1 : max (q.num.natAbs : ℝ) (q.den : ℝ) ≤ Real.exp p :=
    (Real.log_le_iff_le_exp (lt_of_lt_of_le one_pos (one_le_max_num_den q))).mp h
  exact ⟨(le_max_left _ _).trans h1, (le_max_right _ _).trans h1⟩

/-- Conversely, bounds on numerator and denominator bound the log-height. -/
theorem ratLogHeight_le_of_le {q : ℚ} {p : ℝ} (h1 : (q.num.natAbs : ℝ) ≤ Real.exp p)
    (h2 : (q.den : ℝ) ≤ Real.exp p) : ratLogHeight q ≤ p := by
  unfold ratLogHeight
  rw [Real.log_le_iff_le_exp (lt_of_lt_of_le one_pos (one_le_max_num_den q))]
  exact max_le h1 h2

/-- The rationals whose numerator and denominator are at most `N`. -/
def ratBall (N : ℕ) : Finset ℚ :=
  ((Finset.Icc (-(N : ℤ)) N) ×ˢ (Finset.Icc 1 N)).image fun x => (x.1 : ℚ) / (x.2 : ℚ)

theorem mem_ratBall {N : ℕ} {q : ℚ} (h1 : q.num.natAbs ≤ N) (h2 : q.den ≤ N) : q ∈ ratBall N := by
  unfold ratBall
  rw [Finset.mem_image]
  refine ⟨(q.num, q.den), ?_, ?_⟩
  · rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨q.den_pos, h2⟩⟩
    · omega
    · omega
  · simp [Rat.num_div_den]

theorem card_ratBall_le (N : ℕ) : (ratBall N).card ≤ (2 * N + 1) * N := by
  unfold ratBall
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_product, Int.card_Icc, Nat.card_Icc]
  have : (↑N + 1 - -(N : ℤ)).toNat = 2 * N + 1 := by omega
  rw [this]
  simp

/-- A rational of log-height at most `p` lies in `ratBall ⌊e^p⌋`. -/
theorem mem_ratBall_of_ratLogHeight_le {q : ℚ} {p : ℝ} (h : ratLogHeight q ≤ p) :
    q ∈ ratBall ⌊Real.exp p⌋₊ := by
  obtain ⟨h1, h2⟩ := num_den_le_exp h
  exact mem_ratBall (Nat.le_floor h1) (Nat.le_floor h2)

/-- **Clearing denominators.**  A vector of rationals of log-height at most `p` becomes an integer
vector of sup norm at most `e^{p n}` after multiplication by a positive integer. -/
theorem exists_clear_denominators {ι : Type*} [Fintype ι] {p : ℝ} (x : ι → ℚ)
    (hx : ∀ i, ratLogHeight (x i) ≤ p) :
    ∃ L : ℕ, 0 < L ∧ ∃ z : ι → ℤ, (∀ i, (L : ℚ) * x i = z i) ∧
      ∀ i, |(z i : ℝ)| ≤ Real.exp (p * Fintype.card ι) := by
  classical
  refine ⟨∏ i, (x i).den, Finset.prod_pos fun i _ => (x i).den_pos,
    fun i => (x i).num * ((∏ j ∈ Finset.univ.erase i, (x j).den : ℕ) : ℤ), ?_, ?_⟩
  · intro i
    have h1 : ((∏ i, (x i).den : ℕ) : ℚ) =
        ((x i).den : ℚ) * ((∏ j ∈ Finset.univ.erase i, (x j).den : ℕ) : ℚ) := by
      rw [← Nat.cast_mul,
        Finset.mul_prod_erase Finset.univ (fun j => (x j).den) (Finset.mem_univ i)]
    rw [h1]
    have h2 : ((x i).den : ℚ) ≠ 0 := by exact_mod_cast (x i).den_nz
    simp only [Int.cast_mul, Int.cast_natCast]
    linear_combination (((∏ j ∈ Finset.univ.erase i, (x j).den : ℕ) : ℚ)) * Rat.den_mul_eq_num (x i)
  · intro i
    obtain ⟨hn, hd⟩ := num_den_le_exp (hx i)
    have hprod : ((∏ j ∈ Finset.univ.erase i, (x j).den : ℕ) : ℝ) ≤
        (Real.exp p) ^ (Finset.univ.erase i).card := by
      rw [Nat.cast_prod]
      calc ∏ j ∈ Finset.univ.erase i, ((x j).den : ℝ)
          ≤ ∏ _j ∈ Finset.univ.erase i, Real.exp p :=
            Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
              fun j _ => (num_den_le_exp (hx j)).2
        _ = (Real.exp p) ^ (Finset.univ.erase i).card := Finset.prod_const _
    have hcard : (Finset.univ.erase i).card + 1 = Fintype.card ι := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
      have : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
      omega
    have hcast : |(((x i).num * ((∏ j ∈ Finset.univ.erase i, (x j).den : ℕ) : ℤ) : ℤ) : ℝ)| =
        ((x i).num.natAbs : ℝ) * ((∏ j ∈ Finset.univ.erase i, (x j).den : ℕ) : ℝ) := by
      push_cast
      rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ ∏ j ∈ Finset.univ.erase i, ((x j).den : ℝ) from
        Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _), Nat.cast_natAbs, Int.cast_abs]
    rw [hcast]
    calc ((x i).num.natAbs : ℝ) * ((∏ j ∈ Finset.univ.erase i, (x j).den : ℕ) : ℝ)
        ≤ Real.exp p * (Real.exp p) ^ (Finset.univ.erase i).card :=
          mul_le_mul hn hprod (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (p * Fintype.card ι) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add, ← hcard]
          congr 1
          push_cast
          ring

end PrimeCarleson.Proof.Fplus31
