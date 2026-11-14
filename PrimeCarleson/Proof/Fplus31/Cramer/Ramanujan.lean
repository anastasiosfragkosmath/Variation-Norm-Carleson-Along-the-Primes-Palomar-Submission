module

public import PrimeCarleson.Proof.Fplus31.Cramer.Model
public import PrimeCarleson.Proof.Goal0.Ramanujan
public import PrimeCarleson.Frozen.BlockWeight

/-!
# The Ramanujan-sum expansion of the Cramér model

Step 1 of the comparison of the Cramér model with the Heath-Brown model:
`Λ_{C,w}(n) = ∑_{q ∣ P(w)} μ(q) c_q(n) / φ(q)`, since each prime factor contributes
`1 - c_p(n)/(p - 1) = 0` if `p ∣ n` and `p/(p - 1)` if `p ∤ n`.

* `ramanujanSum_prime`: `c_p(n) = p 1_{p ∣ n} - 1`;
* `ramanujanSum_eq_moebius`: `c_q(n) = μ(q)` when `gcd(n, q) = 1`;
* `cramerModel_eq_sum_ramanujanSum`: the identity, as a sum over the divisors of `P(w)`;
* `cramerModel_eq_blockWeight`: the same, as the `blockWeight` of the divisor set.
-/

@[expose] public noncomputable section

open Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- `c_p(n) = p 1_{p ∣ n} - 1` for a prime `p`. -/
theorem ramanujanSum_prime {p : ℕ} (hp : p.Prime) (n : ℤ) :
    PrimeCarleson.ramanujanSum p n = (if (p : ℤ) ∣ n then (p : ℂ) else 0) - 1 := by
  rw [Goal0.ramanujanSum_eq_sum_divisors, Finset.sum_filter, hp.divisors,
    Finset.sum_pair hp.one_lt.ne]
  simp [ArithmeticFunction.moebius_apply_prime hp, Nat.div_self hp.pos]
  split_ifs <;> ring

/-- `c_q(n) = μ(q)` when `gcd(n, q) = 1` (in particular on the support of `Λ_{C,w}` for
`q ∣ P(w)`). -/
theorem ramanujanSum_eq_moebius {q : ℕ} (hq : 0 < q) {n : ℤ} (h : Int.gcd n q = 1) :
    PrimeCarleson.ramanujanSum q n = ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  rw [Goal0.ramanujanSum_eq_sum_divisors, Finset.sum_eq_single 1]
  · simp
  · intro f hf hf1
    exfalso
    rw [Finset.mem_filter, Nat.mem_divisors] at hf
    obtain ⟨⟨hfq, _⟩, hfn⟩ := hf
    have hfn' : f ∣ n.natAbs := Int.natCast_dvd.mp hfn
    have : f ∣ Nat.gcd n.natAbs q := Nat.dvd_gcd hfn' hfq
    rw [Int.gcd] at h
    simp only [Int.natAbs_natCast] at h
    rw [h] at this
    exact hf1 (Nat.dvd_one.mp this)
  · intro h1
    exfalso
    exact h1 (by simp [Nat.mem_divisors, hq.ne'])

/-- `c_1(n) = 1`. -/
theorem ramanujanSum_one (n : ℤ) : PrimeCarleson.ramanujanSum 1 n = 1 := by
  rw [Goal0.ramanujanSum_eq_sum_divisors]
  simp [Finset.sum_filter]

/-- `q ↦ μ(q) c_q(n) / φ(q)` as an arithmetic function. -/
def ramanujanTerm (n : ℤ) : ArithmeticFunction ℂ :=
  ⟨fun q => if q = 0 then 0 else
    ((((ArithmeticFunction.moebius q : ℤ) : ℝ) / (Nat.totient q : ℝ) : ℝ) : ℂ) *
      PrimeCarleson.ramanujanSum q n, by simp⟩

theorem ramanujanTerm_apply (n : ℤ) {q : ℕ} (hq : q ≠ 0) :
    ramanujanTerm n q =
      ((((ArithmeticFunction.moebius q : ℤ) : ℝ) / (Nat.totient q : ℝ) : ℝ) : ℂ) *
        PrimeCarleson.ramanujanSum q n := by
  simp [ramanujanTerm, hq]

theorem isMultiplicative_ramanujanTerm (n : ℤ) : (ramanujanTerm n).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [ramanujanTerm_apply, ramanujanSum_one], fun {m k} hm hk hmk => ?_⟩
  rw [ramanujanTerm_apply n (Nat.mul_ne_zero hm hk), ramanujanTerm_apply n hm,
    ramanujanTerm_apply n hk, Goal0.ramanujanSum_mul hmk,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmk, Nat.totient_mul hmk]
  push_cast
  ring

/-- **Ramanujan's identity for the Cramér model.**
`Λ_{C,w}(n) = ∑_{q ∣ P(w)} (μ(q)/φ(q)) c_q(n)`. -/
theorem cramerModel_eq_sum_ramanujanSum (w : ℕ) (n : ℤ) :
    (cramerModel w n : ℂ) =
      ∑ q ∈ (primorialBelow w).divisors,
        ((((ArithmeticFunction.moebius q : ℤ) : ℝ) / (Nat.totient q : ℝ) : ℝ) : ℂ) *
          PrimeCarleson.ramanujanSum q n := by
  have h1 : ∑ q ∈ (primorialBelow w).divisors,
      ((((ArithmeticFunction.moebius q : ℤ) : ℝ) / (Nat.totient q : ℝ) : ℝ) : ℂ) *
        PrimeCarleson.ramanujanSum q n = ∑ q ∈ (primorialBelow w).divisors, ramanujanTerm n q := by
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [ramanujanTerm_apply n (Nat.ne_of_gt (Nat.pos_of_mem_divisors hq))]
  rw [h1, ← (isMultiplicative_ramanujanTerm n).prodPrimeFactors_one_add_of_squarefree
    (squarefree_primorialBelow w), primeFactors_primorialBelow]
  have h2 : ∀ p ∈ Nat.primesBelow w, 1 + ramanujanTerm n p =
      if ¬ (p : ℤ) ∣ n then ((1 + 1 / ((p : ℝ) - 1) : ℝ) : ℂ) else 0 := by
    intro p hp
    have hpp := Nat.prime_of_mem_primesBelow hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have h1' : (p : ℝ) - 1 ≠ 0 := by linarith
    have h1'' : (p : ℂ) - 1 ≠ 0 := by
      have : ((p : ℝ) - 1 : ℝ) ≠ 0 := h1'
      exact_mod_cast this
    rw [ramanujanTerm_apply n hpp.ne_zero, ramanujanSum_prime hpp,
      ArithmeticFunction.moebius_apply_prime hpp, Nat.totient_prime hpp]
    by_cases hd : (p : ℤ) ∣ n
    · simp only [hd, ↓reduceIte, not_true_eq_false]
      push_cast [Nat.cast_sub hpp.one_le]
      field_simp
      ring
    · simp only [hd, ↓reduceIte, not_false_eq_true]
      push_cast [Nat.cast_sub hpp.one_le]
      field_simp
      ring
  rw [Finset.prod_congr rfl h2, Finset.prod_ite_zero, cramerModel, primorialBelow_div_totient]
  have h3 : (Int.gcd n (primorialBelow w : ℤ) = 1) ↔ ∀ p ∈ Nat.primesBelow w, ¬ (p : ℤ) ∣ n :=
    gcd_primorialBelow_eq_one_iff w n
  by_cases hc : ∀ p ∈ Nat.primesBelow w, ¬ (p : ℤ) ∣ n
  · rw [ite_eq_left hc, ite_eq_left (h3.mpr hc)]
    push_cast
    rfl
  · rw [ite_eq_right hc, ite_eq_right (fun h => hc (h3.mp h))]
    simp

/-- The Cramér model as the block weight of the divisors of `P(w)`:
`Λ_{C,w}(n) = ∑_{q ∣ P(w)} μ(q) c_q(n)/φ(q) = w_{P(w)'s divisors}(n)`. -/
theorem cramerModel_eq_blockWeight (w : ℕ) (n : ℤ) :
    (cramerModel w n : ℂ) = PrimeCarleson.blockWeight (primorialBelow w).divisors n := by
  rw [cramerModel_eq_sum_ramanujanSum, PrimeCarleson.blockWeight]
  refine Finset.sum_congr rfl fun q _ => ?_
  push_cast
  rfl

end PrimeCarleson.Proof.Fplus31
