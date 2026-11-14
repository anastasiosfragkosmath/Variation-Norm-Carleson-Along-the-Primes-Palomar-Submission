module

public import PrimeCarleson.Proof.Fplus31.Comparison.Basic
public import PrimeCarleson.Proof.Fplus31.Comparison.Orth
public import PrimeCarleson.Proof.Fplus31.Comparison.Rankin

/-!
# Cramér–Heath-Brown comparison, step 5: the `L²` norm of the tail `D₂`

Piece `D₂` of the comparison of the Cramér model with the Heath-Brown model. Write `P = P(w)`,
`S = P/φ(P)`, `T_R = ∑_{q ∣ P, q ≤ R} μ(q)/φ(q) c_q`, `S_R = ∑_{q ∣ P, q ≤ R} 1/φ(q)`,
`M = ∑_{n ≤ N} Λ_{C,w}(n)`.

* `blockWeight_tail_eq`: `Λ_{C,w} = T_R + D₂` with `D₂ = ∑_{q ∣ P, q > R} μ(q)/φ(q) c_q`;
* `cramerModel_mul_ramR`: `Λ_{C,w}(n) c_q(n) = μ(q) Λ_{C,w}(n)` for `q ∣ P`;
* `sum_cramerModel_mul_truncSum`: `∑_n Λ_{C,w} T_R = S_R M` (with `Λ_{C,w}² = S Λ_{C,w}` for the
  other cross term, `cramerModel_mul_self`);
* `sum_norm_sq_tail_le`: `∑_{n ≤ N} |D₂(n)|² ≤ tail · M + (S - tail)(N - M) + R⁴`, where
  `tail = S - S_R = ∑_{q ∣ P, q > R} 1/φ(q)` (orthogonality: `sum_sq_mobTot_ramR_le`).
-/

@[expose] public noncomputable section

open Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open PrimeCarleson

/-- On the support of `Λ_{C,w}` and for `q ∣ P(w)`: `Λ_{C,w}(n) c_q(n) = μ(q) Λ_{C,w}(n)`. -/
theorem cramerModel_mul_ramR {w q : ℕ} (hq : q ∣ primorialBelow w) (n : ℤ) :
    cramerModel w n * ramR q n = ((ArithmeticFunction.moebius q : ℤ) : ℝ) * cramerModel w n := by
  by_cases hc : Int.gcd n (primorialBelow w : ℤ) = 1
  · have hq0 : 0 < q := Nat.pos_of_dvd_of_pos hq (primorialBelow_pos w)
    have hcq : Int.gcd n q = 1 := by
      rw [Int.gcd, Int.natAbs_natCast] at hc ⊢
      exact Nat.Coprime.coprime_dvd_right hq hc
    have h := ramanujanSum_eq_moebius hq0 hcq
    rw [ramanujanSum_eq_ofReal] at h
    have h' : ramR q n = ((ArithmeticFunction.moebius q : ℤ) : ℝ) := by exact_mod_cast h
    rw [h', mul_comm]
  · have : cramerModel w n = 0 := by
      unfold cramerModel
      rw [ite_eq_right_iff]
      exact fun h => absurd h hc
    rw [this]
    simp


/-- `μ(q)/φ(q) · μ(q) = 1/φ(q)` for squarefree `q`. -/
theorem mobTot_mul_moebius {q : ℕ} (hq : Squarefree q) :
    mobTot q * ((ArithmeticFunction.moebius q : ℤ) : ℝ) = 1 / (Nat.totient q : ℝ) := by
  have h : ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hq
  rw [mobTot, div_mul_eq_mul_div, ← sq, h]

/-- `μ(q)²/φ(q) = 1/φ(q)` for squarefree `q`. -/
theorem moebius_sq_div_totient {q : ℕ} (hq : Squarefree q) :
    ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) =
      1 / (Nat.totient q : ℝ) := by
  have h : ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hq
  rw [h]

/-- The truncation `T_R(n) = ∑_{q ∣ P(w), q ≤ R} μ(q)/φ(q) c_q(n)` (a real number). -/
def truncSum (w R : ℕ) (n : ℤ) : ℝ :=
  ∑ q ∈ (primorialBelow w).divisors.filter (fun q => q ≤ R), mobTot q * ramR q n

/-- `Λ_{C,w} = T_R + D₂`, with `D₂` the block weight of the divisors of `P(w)` above `R`. -/
theorem blockWeight_tail_eq (w R : ℕ) (n : ℤ) :
    blockWeight ((primorialBelow w).divisors.filter (fun q => R < q)) n =
      ((cramerModel w n - truncSum w R n : ℝ) : ℂ) := by
  have h := cramerModel_eq_blockWeight w n
  rw [blockWeight_eq_sum_ramWeight] at h
  rw [blockWeight_eq_sum_ramWeight]
  have hsplit := Finset.sum_filter_add_sum_filter_not (primorialBelow w).divisors
    (fun q => q ≤ R) (fun q => ramWeight n q)
  simp only [not_le] at hsplit
  have hT : ∑ q ∈ (primorialBelow w).divisors.filter (fun q => q ≤ R), ramWeight n q =
      (truncSum w R n : ℂ) := by
    rw [truncSum, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun q _ => ramWeight_eq_ofReal n q
  rw [hT] at hsplit
  push_cast
  rw [h, ← hsplit]
  ring


/-- The sum `S_R = ∑_{q ∣ P(w), q ≤ R} 1/φ(q)`. -/
def headSum (w R : ℕ) : ℝ :=
  ∑ q ∈ (primorialBelow w).divisors.filter (fun q => q ≤ R), 1 / (Nat.totient q : ℝ)

/-- The tail `∑_{q ∣ P(w), q > R} 1/φ(q)`. -/
def tailSum (w R : ℕ) : ℝ :=
  ∑ q ∈ (primorialBelow w).divisors.filter (fun q => R < q), 1 / (Nat.totient q : ℝ)

/-- `S_R + (S - S_R) = S = P(w)/φ(P(w))`. -/
theorem headSum_add_tailSum (w R : ℕ) :
    headSum w R + tailSum w R = (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) := by
  rw [← sum_divisors_inv_totient, headSum, tailSum, ← Finset.sum_filter_add_sum_filter_not
    (primorialBelow w).divisors (fun q => q ≤ R)]
  simp only [not_le]

/-- `∑_n Λ_{C,w}(n) T_R(n) = S_R ∑_n Λ_{C,w}(n)`. -/
theorem sum_cramerModel_mul_truncSum (w R N : ℕ) :
    ∑ n ∈ Icc (1 : ℤ) N, cramerModel w n * truncSum w R n =
      headSum w R * ∑ n ∈ Icc (1 : ℤ) N, cramerModel w n := by
  have hL : ∑ n ∈ Icc (1 : ℤ) N, cramerModel w n * truncSum w R n =
      ∑ q ∈ (primorialBelow w).divisors.filter (fun q => q ≤ R),
        ∑ n ∈ Icc (1 : ℤ) N, cramerModel w n * (mobTot q * ramR q n) := by
    unfold truncSum
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  rw [hL, headSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [mem_filter, Nat.mem_divisors] at hq
  have hsq : Squarefree q := (squarefree_primorialBelow w).squarefree_of_dvd hq.1.1
  have h1 : ∀ n ∈ Icc (1 : ℤ) N, cramerModel w n * (mobTot q * ramR q n) =
      (1 / (Nat.totient q : ℝ)) * cramerModel w n := by
    intro n _
    calc cramerModel w n * (mobTot q * ramR q n) = mobTot q * (cramerModel w n * ramR q n) := by
          ring
      _ = mobTot q * (((ArithmeticFunction.moebius q : ℤ) : ℝ) * cramerModel w n) := by
          rw [cramerModel_mul_ramR hq.1.1]
      _ = _ := by rw [← mul_assoc, mobTot_mul_moebius hsq]
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]

/-- **The `L²` norm of the tail `D₂`** (`E|D₂|² = (S - S_R) m + S_R (1 - m) + O(R⁴/N)`): with
`M = ∑_{n ≤ N} Λ_{C,w}(n)`, `∑_{n ≤ N} |D₂(n)|² ≤ tail · M + (S - tail)(N - M) + R⁴`. -/
theorem sum_norm_sq_tail_le (w R N : ℕ) :
    ∑ n ∈ Icc (1 : ℤ) N,
        ‖blockWeight ((primorialBelow w).divisors.filter (fun q => R < q)) n‖ ^ 2 ≤
      tailSum w R * ∑ n ∈ Icc (1 : ℤ) N, cramerModel w n +
        ((primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) - tailSum w R) *
          ((N : ℝ) - ∑ n ∈ Icc (1 : ℤ) N, cramerModel w n) + (R : ℝ) ^ 4 := by
  set P := primorialBelow w with hP
  set S : ℝ := (P : ℝ) / (Nat.totient P : ℝ) with hS
  set M : ℝ := ∑ n ∈ Icc (1 : ℤ) N, cramerModel w n with hM
  set Q := P.divisors.filter (fun q => q ≤ R) with hQ
  have hnorm : ∀ n : ℤ, ‖blockWeight (P.divisors.filter (fun q => R < q)) n‖ ^ 2 =
      (cramerModel w n - truncSum w R n) ^ 2 := by
    intro n
    rw [blockWeight_tail_eq, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [hnorm]
  have hexp : ∑ n ∈ Icc (1 : ℤ) N, (cramerModel w n - truncSum w R n) ^ 2 =
      S * M - 2 * (headSum w R * M) + ∑ n ∈ Icc (1 : ℤ) N, truncSum w R n ^ 2 := by
    have h1 : ∑ n ∈ Icc (1 : ℤ) N, cramerModel w n ^ 2 = S * M := by
      rw [hM, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [sq, cramerModel_mul_self]
    have h2 := sum_cramerModel_mul_truncSum w R N
    calc ∑ n ∈ Icc (1 : ℤ) N, (cramerModel w n - truncSum w R n) ^ 2
        = ∑ n ∈ Icc (1 : ℤ) N, (cramerModel w n ^ 2 - 2 * (cramerModel w n * truncSum w R n) +
            truncSum w R n ^ 2) := Finset.sum_congr rfl fun n _ => by ring
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, ← Finset.mul_sum, h2]
  have hT2 : ∑ n ∈ Icc (1 : ℤ) N, truncSum w R n ^ 2 ≤
      N * headSum w R + (R : ℝ) ^ 4 := by
    have hQpos : ∀ q ∈ Q, 0 < q := fun q hq =>
      Nat.pos_of_dvd_of_pos (Nat.mem_divisors.1 (mem_filter.1 hq).1).1 (primorialBelow_pos w)
    have h := sum_sq_mobTot_ramR_le Q hQpos N
    have hsq : ∑ q ∈ Q, ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) =
        headSum w R := by
      rw [headSum]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [mem_filter, Nat.mem_divisors] at hq
      exact moebius_sq_div_totient ((squarefree_primorialBelow w).squarefree_of_dvd hq.1.1)
    have hsum : (∑ q ∈ Q, (q : ℝ)) ≤ (R : ℝ) * R := by
      calc (∑ q ∈ Q, (q : ℝ)) ≤ ∑ _q ∈ Q, (R : ℝ) :=
            Finset.sum_le_sum fun q hq => by exact_mod_cast (mem_filter.1 hq).2
        _ = Q.card * (R : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ R * R := by
            refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg R)
            have : Q ⊆ Icc 1 R := fun q hq => by
              rw [mem_Icc]
              exact ⟨hQpos q hq, (mem_filter.1 hq).2⟩
            exact_mod_cast (Finset.card_le_card this).trans (by simp)
    have hsum0 : 0 ≤ ∑ q ∈ Q, (q : ℝ) := Finset.sum_nonneg fun q _ => Nat.cast_nonneg q
    rw [hsq] at h
    have h4 : (∑ q ∈ Q, (q : ℝ)) ^ 2 ≤ (R : ℝ) ^ 4 := by
      calc (∑ q ∈ Q, (q : ℝ)) ^ 2 ≤ ((R : ℝ) * R) ^ 2 := pow_le_pow_left₀ hsum0 hsum 2
        _ = (R : ℝ) ^ 4 := by ring
    unfold truncSum
    linarith
  have hS : headSum w R + tailSum w R = S := headSum_add_tailSum w R
  rw [hexp]
  have : S * M - 2 * (headSum w R * M) + (N * headSum w R + (R : ℝ) ^ 4) =
      tailSum w R * M + (S - tailSum w R) * ((N : ℝ) - M) + (R : ℝ) ^ 4 := by
    have : headSum w R = S - tailSum w R := by linarith
    rw [this]
    ring
  linarith

end PrimeCarleson.Proof.Fplus31
