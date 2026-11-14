module

public import PrimeCarleson.Proof.Fplus31.Comparison.Basic
public import PrimeCarleson.Proof.FplusProp21.Application
public import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Cramér–Heath-Brown comparison, step 2: the dyadic blocks `T' < q ≤ R` (`D₁`)

Piece `D₁` of the comparison of the Cramér model with the Heath-Brown model: the block weight of the
divisors of `P` in `(2^J, 2^{J'}]` is the sum of the dyadic sub-blocks
`B_j = {q ∣ P : 2^{j-1} < q ≤ 2^j}`, `J < j ≤ J'`, each of which is controlled by [F+] Proposition
2.1 for arbitrary blocks (`FplusProp21.exists_gowersNormInterval_blockWeight_le`, `ε = 1/8`,
`Q = 2^j`, `Q^{20} ≤ N`):

* `exists_gowersNormInterval_dpart_le`: `‖dpart P 2^J 2^{J'}‖_{U³[N]} ≤ K (2^{J+1})^{-1/4}`
  whenever `J ≤ J'` and `(2^{J'})^{20} ≤ N`, with `K` absolute.
-/

@[expose] public noncomputable section

open Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open PrimeCarleson

/-- `(2^j)^(-1/4) = ρ^j`, `ρ = 2^(-1/4)`. -/
theorem two_pow_rpow (j : ℕ) (a : ℝ) : ((2 : ℝ) ^ j) ^ a = ((2 : ℝ) ^ a) ^ j := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
    Real.rpow_natCast]

/-- **The dyadic blocks `(2^J, 2^{J'}]` of `Λ_{C,w} - Λ_{≤T}`** (`D₁` of the comparison): by
Proposition 2.1 for arbitrary blocks,
`‖∑_{q ∣ P, 2^J < q ≤ 2^{J'}} μ(q)/φ(q) c_q‖_{U³[N]} ≤ K 2^{-(J+1)/4}` whenever `2^{20 J'} ≤ N`. -/
theorem exists_gowersNormInterval_dpart_le :
    ∃ K : ℝ, ∀ (P J J' : ℕ) (N : ℕ+), J ≤ J' → ((2 : ℝ) ^ J') ^ 20 ≤ (N : ℝ) →
      gowersNormInterval 3 N (dpart P (2 ^ J) (2 ^ J')) ≤
        K * ((2 : ℝ) ^ (J + 1)) ^ (-(1 : ℝ) / 4) := by
  obtain ⟨C, hC⟩ :=
    FplusProp21.exists_gowersNormInterval_blockWeight_le (ε := 1 / 8) (by norm_num)
  set ρ : ℝ := (2 : ℝ) ^ (-(1 : ℝ) / 4) with hρ
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg (by norm_num) _
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  refine ⟨max C 0 / (1 - ρ), fun P J J' N hJ hN => ?_⟩
  have hfun : dpart P (2 ^ J) (2 ^ J') =
      fun n => ∑ j ∈ Ioc J J', dpart P (2 ^ j / 2) (2 ^ j) n := by
    funext n
    exact dpart_two_pow P hJ n
  have hblock : ∀ j ∈ Ioc J J', gowersNormInterval 3 N (dpart P (2 ^ j / 2) (2 ^ j)) ≤
      max C 0 * ρ ^ j := by
    intro j hj
    rw [mem_Ioc] at hj
    have h := hC ((2 : ℝ) ^ j) (one_le_pow₀ (by norm_num))
      ((Ioc (2 ^ j / 2) (2 ^ j)).filter (· ∣ P)) ?_ N ?_
    · have h' : ((2 : ℝ) ^ j) ^ ((1 : ℝ) / 8 - 3 / 8) = ρ ^ j := by
        rw [two_pow_rpow, hρ]
        norm_num
      rw [h'] at h
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hρ0 _))
    · intro q hq
      rw [mem_filter, mem_Ioc] at hq
      have h2 : 2 ^ j ≤ 2 * q := by omega
      have h2' : ((2 : ℝ) ^ j) ≤ 2 * q := by exact_mod_cast h2
      have h3 : q ≤ 2 ^ j := hq.1.2
      refine ⟨by linarith, by exact_mod_cast h3⟩
    · refine le_trans ?_ hN
      exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hj.2) 20
  rw [hfun]
  refine (gowersNormInterval_sum_le N (Ioc J J')
    (fun j n => dpart P (2 ^ j / 2) (2 ^ j) n)).trans ?_
  refine (Finset.sum_le_sum hblock).trans ?_
  rw [← Finset.mul_sum]
  have hIoc : Ioc J J' = Ico (J + 1) (J' + 1) := by
    ext x; simp only [mem_Ioc, mem_Ico]; omega
  rw [hIoc]
  have hgeom := geom_sum_Ico_le_of_lt_one hρ0 hρ1 (m := J + 1) (n := J' + 1)
  have hr : ((2 : ℝ) ^ (J + 1)) ^ (-(1 : ℝ) / 4) = ρ ^ (J + 1) := by
    rw [two_pow_rpow]
  rw [hr]
  calc max C 0 * ∑ i ∈ Ico (J + 1) (J' + 1), ρ ^ i ≤ max C 0 * (ρ ^ (J + 1) / (1 - ρ)) :=
        mul_le_mul_of_nonneg_left hgeom (le_max_right _ _)
    _ = max C 0 / (1 - ρ) * ρ ^ (J + 1) := by ring

end PrimeCarleson.Proof.Fplus31
