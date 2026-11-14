module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# Brun's pure sieve: the finite combinatorics

Elementary finite combinatorics behind the pure sieve of Brun, for a finite set `s` of "primes":

* `esymm_le`: the elementary symmetric bound `j! · e_j(f) ≤ (∑ f)^j` for nonnegative `f`, with
  `e_j(f) = ∑_{D ⊆ s, |D| = j} ∏_{p ∈ D} f p`;
* `sum_Ico_pow_div_factorial_le`: the Taylor tail `∑_{j > k} S^j / j! ≤ exp S · S^{k+1} / (k+1)!`;
* `sum_range_neg_one_pow_mul_choose`: the truncated alternating binomial sum
  `∑_{j ≤ k} (-1)^j C(c, j) = (-1)^k C(c - 1, k)` for `c ≥ 1`;
* `abs_ite_sub_alternating_choose_le`: the Bonferroni inequality
  `|1_{c = 0} - ∑_{j ≤ k} (-1)^j C(c, j)| ≤ C(c, k+1)`.
-/

@[expose] public noncomputable section

open Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- The first two terms of the binomial expansion: `σ^(i+1) + (i+1) x σ^i ≤ (σ + x)^(i+1)`
for `σ, x ≥ 0`. -/
theorem pow_add_mul_le_pow_add {σ x : ℝ} (hσ : 0 ≤ σ) (hx : 0 ≤ x) (i : ℕ) :
    σ ^ (i + 1) + (i + 1) * x * σ ^ i ≤ (σ + x) ^ (i + 1) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 : 0 ≤ (i + 1 : ℝ) * x ^ 2 * σ ^ i := by positivity
    have e : (σ + x) * (σ ^ (i + 1) + (i + 1) * x * σ ^ i) =
        σ ^ (i + 1 + 1) + ((i + 1 : ℕ) + 1) * x * σ ^ (i + 1) + (i + 1) * x ^ 2 * σ ^ i := by
      push_cast
      ring
    calc σ ^ (i + 1 + 1) + ((i + 1 : ℕ) + 1) * x * σ ^ (i + 1)
        ≤ (σ + x) * (σ ^ (i + 1) + (i + 1) * x * σ ^ i) := by
          rw [e]
          linarith [h1]
      _ ≤ (σ + x) * (σ + x) ^ (i + 1) :=
          mul_le_mul_of_nonneg_left ih (add_nonneg hσ hx)
      _ = (σ + x) ^ (i + 1 + 1) := by ring

/-- The elementary symmetric bound `j! · e_j(f) ≤ (∑ f)^j` for nonnegative `f`:
`∑_{D ⊆ s, |D| = j} ∏_{p ∈ D} f p ≤ (∑_{p ∈ s} f p)^j / j!`. -/
theorem esymm_le {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ p ∈ s, 0 ≤ f p) (j : ℕ) :
    (j.factorial : ℝ) * ∑ D ∈ s.powersetCard j, ∏ p ∈ D, f p ≤ (∑ p ∈ s, f p) ^ j := by
  classical
  induction s using Finset.induction_on generalizing j with
  | empty =>
    cases j with
    | zero => simp
    | succ j =>
      rw [Finset.powersetCard_eq_empty.mpr (by simp)]
      simp
  | insert a s ha ih =>
    have hfa : 0 ≤ f a := hf a (mem_insert_self a s)
    have hfs : ∀ p ∈ s, 0 ≤ f p := fun p hp => hf p (mem_insert_of_mem hp)
    cases j with
    | zero => simp
    | succ i =>
      have hdisj : Disjoint (s.powersetCard (i + 1)) ((s.powersetCard i).image (insert a)) := by
        rw [Finset.disjoint_left]
        intro D hD hD'
        obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hD'
        have := (Finset.mem_powersetCard.mp hD).1 (Finset.mem_insert_self a E)
        exact ha this
      have hinj : Set.InjOn (insert a) (s.powersetCard i : Set (Finset α)) := by
        intro D hD E hE hDE
        have hD' : a ∉ D := fun h => ha ((Finset.mem_powersetCard.mp hD).1 h)
        have hE' : a ∉ E := fun h => ha ((Finset.mem_powersetCard.mp hE).1 h)
        rw [← Finset.erase_insert hD', hDE, Finset.erase_insert hE']
      have hsum : ∑ D ∈ (insert a s).powersetCard (i + 1), ∏ p ∈ D, f p =
          ∑ D ∈ s.powersetCard (i + 1), ∏ p ∈ D, f p +
            f a * ∑ D ∈ s.powersetCard i, ∏ p ∈ D, f p := by
        rw [powersetCard_succ_insert ha, Finset.sum_union hdisj, Finset.sum_image hinj,
          Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun D hD => ?_
        have hD' : a ∉ D := fun h => ha ((Finset.mem_powersetCard.mp hD).1 h)
        rw [Finset.prod_insert hD']
      rw [hsum, Finset.sum_insert ha]
      have h1 := ih hfs (i + 1)
      have h2 := ih hfs i
      have hσ : 0 ≤ ∑ p ∈ s, f p := Finset.sum_nonneg hfs
      have hfac : ((i + 1).factorial : ℝ) = (i + 1) * i.factorial := by
        rw [Nat.factorial_succ]; push_cast; ring
      calc ((i + 1).factorial : ℝ) *
            (∑ D ∈ s.powersetCard (i + 1), ∏ p ∈ D, f p +
              f a * ∑ D ∈ s.powersetCard i, ∏ p ∈ D, f p)
          = ((i + 1).factorial : ℝ) * ∑ D ∈ s.powersetCard (i + 1), ∏ p ∈ D, f p +
              (i + 1) * f a * ((i.factorial : ℝ) * ∑ D ∈ s.powersetCard i, ∏ p ∈ D, f p) := by
            rw [hfac]; ring
        _ ≤ (∑ p ∈ s, f p) ^ (i + 1) + (i + 1) * f a * (∑ p ∈ s, f p) ^ i := by
            gcongr
        _ ≤ (f a + ∑ p ∈ s, f p) ^ (i + 1) := by
            have := pow_add_mul_le_pow_add hσ hfa i
            rw [add_comm (f a)]
            linarith

/-- The Taylor tail: `∑_{k < j < m} S^j / j! ≤ exp S · S^{k+1} / (k+1)!` for `S ≥ 0`. -/
theorem sum_Ico_pow_div_factorial_le {S : ℝ} (hS : 0 ≤ S) (k m : ℕ) :
    ∑ j ∈ Finset.Ico (k + 1) m, S ^ j / (j.factorial : ℝ) ≤
      Real.exp S * (S ^ (k + 1) / ((k + 1).factorial : ℝ)) := by
  rw [Finset.sum_Ico_eq_sum_range]
  calc ∑ i ∈ range (m - (k + 1)), S ^ (k + 1 + i) / ((k + 1 + i).factorial : ℝ)
      ≤ ∑ i ∈ range (m - (k + 1)),
          (S ^ (k + 1) / ((k + 1).factorial : ℝ)) * (S ^ i / (i.factorial : ℝ)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hdvd := Nat.factorial_mul_factorial_dvd_factorial_add (k + 1) i
        have hle : ((k + 1).factorial : ℝ) * (i.factorial : ℝ) ≤ ((k + 1 + i).factorial : ℝ) := by
          exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) hdvd
        have hpos1 : (0 : ℝ) < ((k + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
        have hpos2 : (0 : ℝ) < (i.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
        rw [pow_add, div_mul_div_comm]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hle
    _ = (S ^ (k + 1) / ((k + 1).factorial : ℝ)) *
          ∑ i ∈ range (m - (k + 1)), S ^ i / (i.factorial : ℝ) := by
        rw [← Finset.mul_sum]
    _ ≤ (S ^ (k + 1) / ((k + 1).factorial : ℝ)) * Real.exp S :=
        mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hS _) (by positivity)
    _ = Real.exp S * (S ^ (k + 1) / ((k + 1).factorial : ℝ)) := by ring

/-- The truncated alternating binomial sum `∑_{j ≤ k} (-1)^j C(c, j) = (-1)^k C(c - 1, k)`
for `c ≥ 1`. -/
theorem sum_range_neg_one_pow_mul_choose {c : ℕ} (hc : 1 ≤ c) (k : ℕ) :
    ∑ j ∈ range (k + 1), ((-1 : ℤ) ^ j * (c.choose j : ℤ)) = (-1) ^ k * ((c - 1).choose k : ℤ) := by
  obtain ⟨n, rfl⟩ : ∃ n, c = n + 1 := ⟨c - 1, by omega⟩
  simpa using Int.alternating_sum_range_choose_eq_choose (n := n) (m := k)

/-- **Bonferroni.** `|1_{c = 0} - ∑_{j ≤ k} (-1)^j C(c, j)| ≤ C(c, k + 1)`. -/
theorem abs_ite_sub_alternating_choose_le (c k : ℕ) :
    |(if c = 0 then (1 : ℤ) else 0) - ∑ j ∈ range (k + 1), ((-1 : ℤ) ^ j * (c.choose j : ℤ))| ≤
      (c.choose (k + 1) : ℤ) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp [Finset.sum_range_succ', Nat.choose_zero_succ]
  · rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega)), sum_range_neg_one_pow_mul_choose hc k]
    obtain ⟨n, rfl⟩ : ∃ n, c = n + 1 := ⟨c - 1, by omega⟩
    simp only [zero_sub, abs_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      Nat.add_sub_cancel, Nat.abs_cast]
    rw [Nat.choose_succ_succ']
    push_cast
    omega

/-- Truncating a finite sum at `j ≤ k`: if `f j = 0` for `j ≥ m`, then
`∑_{j < m} 1_{j ≤ k} f j = ∑_{j ≤ k} f j`. -/
theorem sum_range_ite_le {M : Type*} [AddCommMonoid M] (f : ℕ → M) (k m : ℕ)
    (hf : ∀ j, m ≤ j → f j = 0) :
    ∑ j ∈ range m, (if j ≤ k then f j else 0) = ∑ j ∈ range (k + 1), f j := by
  rw [← Finset.sum_filter]
  refine Finset.sum_subset ?_ ?_
  · intro j hj
    rw [Finset.mem_filter] at hj
    exact Finset.mem_range.mpr (by omega)
  · intro j hj hj'
    refine hf j ?_
    by_contra hlt
    exact hj' (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by
      have := Finset.mem_range.mp hj
      omega⟩)

/-- `∏_{p ∈ s} (1 - f p) = ∑_{j < M} (-1)^j e_j(f)` for any `M > |s|`. -/
theorem prod_one_sub_eq_sum_range {α : Type*} (s : Finset α) (f : α → ℝ) (M : ℕ)
    (hM : s.card + 1 ≤ M) :
    ∏ p ∈ s, (1 - f p) =
      ∑ j ∈ range M, (-1 : ℝ) ^ j * ∑ D ∈ s.powersetCard j, ∏ p ∈ D, f p := by
  have h1 : ∏ p ∈ s, (1 - f p) = ∑ D ∈ s.powerset, ∏ p ∈ D, (-f p) := by
    rw [← Finset.prod_one_add]
    simp [sub_eq_add_neg]
  rw [h1, Finset.sum_powerset]
  have h2 : ∑ j ∈ range (s.card + 1), ∑ D ∈ s.powersetCard j, ∏ p ∈ D, (-f p) =
      ∑ j ∈ range (s.card + 1), (-1 : ℝ) ^ j * ∑ D ∈ s.powersetCard j, ∏ p ∈ D, f p := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun D hD => ?_
    rw [Finset.prod_neg, (Finset.mem_powersetCard.mp hD).2]
  rw [h2]
  refine Finset.sum_subset (Finset.range_subset_range.mpr hM) fun j hj hj' => ?_
  have : s.card < j := by
    have := Finset.mem_range.mp hj
    have := mt Finset.mem_range.mpr hj'
    omega
  rw [Finset.powersetCard_eq_empty.mpr this]
  simp

/-- The truncated inclusion-exclusion expansion of `∏_{p ∈ s} (1 - f p)`: the error of stopping at
`j ≤ k` is at most `exp(∑ f) (∑ f)^{k+1}/(k+1)!` (Brun's pure sieve, main term). -/
theorem abs_prod_one_sub_sub_le {α : Type*} (s : Finset α) (f : α → ℝ) (hf : ∀ p ∈ s, 0 ≤ f p)
    (k : ℕ) :
    |∏ p ∈ s, (1 - f p) -
        ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * ∑ D ∈ s.powersetCard j, ∏ p ∈ D, f p| ≤
      Real.exp (∑ p ∈ s, f p) * ((∑ p ∈ s, f p) ^ (k + 1) / ((k + 1).factorial : ℝ)) := by
  set M := k + s.card + 2 with hMdef
  have hM : s.card + 1 ≤ M := by omega
  have hkM : k + 1 ≤ M := by omega
  rw [prod_one_sub_eq_sum_range s f M hM, ← Finset.sum_range_add_sum_Ico _ hkM, add_sub_cancel_left]
  have hS : 0 ≤ ∑ p ∈ s, f p := Finset.sum_nonneg hf
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans ?_
    (sum_Ico_pow_div_factorial_le hS k M))
  refine Finset.sum_le_sum fun j _ => ?_
  have hfac : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hnn : 0 ≤ ∑ D ∈ s.powersetCard j, ∏ p ∈ D, f p :=
    Finset.sum_nonneg fun D hD => Finset.prod_nonneg fun p hp =>
      hf p ((Finset.mem_powersetCard.mp hD).1 hp)
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hnn, le_div_iff₀ hfac,
    mul_comm]
  exact esymm_le s f hf j

end PrimeCarleson.Proof.Fplus31
