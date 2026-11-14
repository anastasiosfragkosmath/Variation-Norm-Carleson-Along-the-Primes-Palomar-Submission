module

public import PrimeCarleson.Proof.FplusProp21.Expansion
public import PrimeCarleson.Proof.Goal0.Divisors
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The arithmetic core: the diagonal sum is `≲_ε Q^{-3+ε}`

The arithmetic part of the proof of [F+] Proposition 2.1
([F+] TeX L788–L911). The steps, with their sources:

* [F+] `expansion-u3-norm-3`, L847–L861 (`diagSum_le_sum_numerators`, `prod_totient_eq`): the
  diagonal sum regrouped by denominators, `S_0 ≤ ∑_q ∏_ω μ²(q_ω)/φ(q_ω) · Δ_q`, and
  `∏_ω φ(q_ω) = ∏_{p ∣ R} (p - 1)^{v_p(R)}` for squarefree `q_ω` (multiplicativity of `φ`);
* [F+] L872–L887 (`perPrimeBound_div_le`): per prime, `N(v, p) / (p-1)^v ≤ 16 p^{-2} (p^v)^{-1/4}`
  (the loss `p/(p-1) ≤ 2`);
* [F+] L889–L911 (the parametrization of the tuples and the dyadic sum over `r`), by the direct
  route via `rad(s) ≥ s^{1/4}`: for every tuple, `∏ μ²/φ · Δ_q ≤ 16^{ω(r)} r^{-2} R^{-1/4}` with
  `r = lcm(q_ω) = rad R`, `R = ∏ q_ω` (`prod_muSqDivTotient_mul_card_le`), and `R ≥ (Q/2)⁸`; the
  grouping of the tuples by `r ∈ [Q/2, Q⁸]` and the final summation are in
  `PrimeCarleson.Proof.FplusProp21.DiagSum` (`exists_diagSum_le`, [F+] `expansion-u3-norm-2`,
  L788–L791).
-/

@[expose] public noncomputable section

open Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.FplusProp21

/-- `μ²(q) / φ(q)`. -/
def muSqDivTotient (q : ℕ) : ℝ := ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ)

/-- The diagonal sum `S_0 = ∑_{(q_ω, a_ω) : L_j ∈ ℤ} ∏_ω μ²(q_ω)/φ(q_ω)` of
(expansion-u3-norm-2). -/
def diagSum (B : Finset ℕ) : ℝ :=
  ∑ τ ∈ (Fintype.piFinset fun _ : Cube => qaPairs B).filter (fun τ => CubeDiag (tupleTheta τ)),
    ∏ ω, muSqDivTotient (τ ω).1

/-- `μ²(q)/φ(q) ≥ 0`. -/
theorem muSqDivTotient_nonneg (q : ℕ) : 0 ≤ muSqDivTotient q := by
  unfold muSqDivTotient
  positivity

/-- **Regrouping by denominators** (Source: [F+] `expansion-u3-norm-3`, L847–L851):
`S_0 ≤ ∑_{q ∈ B⁸} ∏_ω μ²(q_ω)/φ(q_ω) · Δ_q`. -/
theorem diagSum_le_sum_numerators (B : Finset ℕ) (hB : ∀ q ∈ B, q ≠ 0) :
    diagSum B ≤ ∑ q ∈ Fintype.piFinset (fun _ : Cube => B),
      (∏ ω, muSqDivTotient (q ω)) * ((numerators q).filter (FaceIntegral q)).card := by
  classical
  unfold diagSum
  rw [← sum_fiberwise_of_maps_to (g := fun τ (ω : Cube) => (τ ω).1)
    (t := Fintype.piFinset fun _ : Cube => B)]
  · refine sum_le_sum fun q hq => ?_
    rw [Fintype.mem_piFinset] at hq
    have hconst : ∀ τ ∈ ((Fintype.piFinset fun _ : Cube => qaPairs B).filter
        (fun τ => CubeDiag (tupleTheta τ))).filter (fun τ => (fun ω => (τ ω).1) = q),
        ∏ ω, muSqDivTotient (τ ω).1 = ∏ ω, muSqDivTotient (q ω) := by
      intro τ hτ
      rw [mem_filter] at hτ
      rw [← hτ.2]
    rw [sum_congr rfl hconst, sum_const, nsmul_eq_mul, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (prod_nonneg fun ω _ => muSqDivTotient_nonneg _)
    norm_cast
    refine card_le_card_of_injOn (fun τ ω => (τ ω).2) (fun τ hτ => ?_) (fun τ hτ τ' hτ' h => ?_)
    · rw [mem_coe, mem_filter, mem_filter, Fintype.mem_piFinset] at hτ
      obtain ⟨⟨hτB, hdiag⟩, hfst⟩ := hτ
      have hτq : ∀ ω, (τ ω).1 = q ω := fun ω => congrFun hfst ω
      rw [mem_coe, mem_filter, mem_numerators]
      refine ⟨fun ω => ?_, ?_⟩
      · have := hτB ω
        simp only [qaPairs, mem_sigma, mem_filter, mem_Icc] at this
        rw [← hτq ω]
        exact ⟨this.2.1.1, this.2.1.2, this.2.2⟩
      · refine faceIntegral_of_cubeDiag (fun ω => hB _ (hq ω)) ?_
        have : tupleTheta τ = cubeTheta q (fun ω => (τ ω).2) := by
          funext ω
          simp [tupleTheta, cubeTheta, hτq ω]
        rwa [← this]
    · rw [mem_coe, mem_filter] at hτ hτ'
      funext ω
      have h1 : (τ ω).1 = (τ' ω).1 := by
        rw [congrFun hτ.2 ω, congrFun hτ'.2 ω]
      have h2 : (τ ω).2 = (τ' ω).2 := congrFun h ω
      exact Sigma.ext h1 (heq_of_eq h2)
  · intro τ hτ
    rw [mem_filter, Fintype.mem_piFinset] at hτ
    rw [Fintype.mem_piFinset]
    intro ω
    have := hτ.1 ω
    simp only [qaPairs, mem_sigma] at this
    exact this.1

/-! ### Products over the cube as products over primes -/

/-- For squarefree `q_ω`, the prime factors of `q_ω` are the primes `p ∣ r` with `p ∣ q_ω`. -/
theorem primeFactors_eq_filter {q : Cube → ℕ} (hq : ∀ ω, Squarefree (q ω)) (ω : Cube) :
    (q ω).primeFactors = (cubeLcm q).primeFactors.filter (fun p => p ∣ q ω) := by
  ext p
  simp only [Nat.mem_primeFactors, mem_filter]
  constructor
  · rintro ⟨hp, hpq, hq0⟩
    exact ⟨⟨hp, hpq.trans (dvd_cubeLcm q ω), cubeLcm_ne_zero fun ω => (hq ω).ne_zero⟩, hpq⟩
  · rintro ⟨⟨hp, -, -⟩, hpq⟩
    exact ⟨hp, hpq, (hq ω).ne_zero⟩

/-- **Products over the cube as products over primes**: for squarefree `q_ω`,
`∏_ω ∏_{p ∣ q_ω} f(p) = ∏_{p ∣ r} f(p)^{|S_p|}`. -/
theorem prod_prod_primeFactors_eq {M : Type*} [CommMonoid M] {q : Cube → ℕ}
    (hq : ∀ ω, Squarefree (q ω)) (f : ℕ → M) :
    ∏ ω, ∏ p ∈ (q ω).primeFactors, f p =
      ∏ p ∈ (cubeLcm q).primeFactors, f p ^ (primeSupport q p).card := by
  classical
  simp_rw [primeFactors_eq_filter hq, prod_filter]
  rw [prod_comm]
  refine prod_congr rfl fun p _ => ?_
  rw [← prod_filter, prod_const]
  rfl

/-- `φ(q) = ∏_{p ∣ q} (p - 1)` for squarefree `q`. -/
theorem totient_eq_prod_of_squarefree {n : ℕ} (hn : Squarefree n) :
    n.totient = ∏ p ∈ n.primeFactors, (p - 1) := by
  have h := Nat.totient_mul_prod_primeFactors n
  rw [Nat.prod_primeFactors_of_squarefree hn] at h
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn.ne_zero
  rw [mul_comm n] at h
  exact Nat.eq_of_mul_eq_mul_right hn0 h

/-- `∏_ω φ(q_ω) = ∏_{p ∣ r} (p - 1)^{|S_p|}` for squarefree `q_ω` (multiplicativity of `φ`, [F+]
L852–L855). -/
theorem prod_totient_eq {q : Cube → ℕ} (hq : ∀ ω, Squarefree (q ω)) :
    ∏ ω, (q ω).totient = ∏ p ∈ (cubeLcm q).primeFactors, (p - 1) ^ (primeSupport q p).card := by
  simp_rw [totient_eq_prod_of_squarefree (hq _)]
  exact prod_prod_primeFactors_eq hq _

/-- `∏_ω q_ω = ∏_{p ∣ r} p^{|S_p|}` for squarefree `q_ω`. -/
theorem prod_eq_prod_pow {q : Cube → ℕ} (hq : ∀ ω, Squarefree (q ω)) :
    ∏ ω, q ω = ∏ p ∈ (cubeLcm q).primeFactors, p ^ (primeSupport q p).card := by
  conv_lhs => rw [show (fun ω => q ω) = fun ω => ∏ p ∈ (q ω).primeFactors, p from
    funext fun ω => (Nat.prod_primeFactors_of_squarefree (hq ω)).symm]
  exact prod_prod_primeFactors_eq hq id

/-- `|S_p| ≤ 8`. -/
theorem card_primeSupport_le (q : Cube → ℕ) (p : ℕ) : (primeSupport q p).card ≤ 8 := by
  calc (primeSupport q p).card ≤ (univ : Finset Cube).card := card_le_univ _
    _ = 8 := by simp

/-! ### The per-prime loss -/

/-- `(x^n)^{1/4}` at `n = 4`. -/
theorem rpow_quarter_pow_four {x : ℝ} (hx : 0 ≤ x) : (x ^ 4) ^ ((1 : ℝ) / 4) = x := by
  have := Real.pow_rpow_inv_natCast hx (n := 4) (by norm_num)
  rwa [show ((4 : ℕ) : ℝ)⁻¹ = (1 : ℝ) / 4 by norm_num] at this

/-- **Divisor and totient losses, per prime** (Source: [F+] L872–L887):
`N(v, p) / (p - 1)^v ≤ 16 / (p² (p^v)^{1/4})` for `v ≤ 8`. -/
theorem perPrimeBound_div_le {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : n ≤ 8) :
    (perPrimeBound p n : ℝ) / ((p : ℝ) - 1) ^ n ≤
      16 / ((p : ℝ) ^ 2 * ((p : ℝ) ^ n) ^ ((1 : ℝ) / 4)) := by
  have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hP1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hP2 : (p : ℝ) ≤ 2 * ((p : ℝ) - 1) := by linarith
  have hPpos : (0 : ℝ) < p := by linarith
  have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp.one_le]
    simp
  have hrhs : 0 < (p : ℝ) ^ 2 * ((p : ℝ) ^ n) ^ ((1 : ℝ) / 4) := by positivity
  unfold perPrimeBound
  split_ifs with h3 h4
  · simp only [Nat.cast_zero, zero_div]
    positivity
  · -- `n = 4`
    subst h4
    rw [hcast, rpow_quarter_pow_four hPpos.le, div_le_div_iff₀ (by positivity) (by positivity)]
    have h8 : (p : ℝ) ^ 3 ≤ 16 * ((p : ℝ) - 1) ^ 3 := by
      calc (p : ℝ) ^ 3 ≤ (2 * ((p : ℝ) - 1)) ^ 3 := pow_le_pow_left₀ hPpos.le hP2 3
        _ = 8 * ((p : ℝ) - 1) ^ 3 := by ring
        _ ≤ 16 * ((p : ℝ) - 1) ^ 3 := by nlinarith [pow_pos hP1 3]
    nlinarith [pow_pos hP1 3]
  · -- `5 ≤ n ≤ 8`
    rw [Nat.cast_pow, hcast]
    have hsplit : ((p : ℝ) - 1) ^ n = ((p : ℝ) - 1) ^ (n - 4) * ((p : ℝ) - 1) ^ 4 := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit, div_mul_cancel_left₀ (by positivity), inv_eq_one_div,
      div_le_div_iff₀ (by positivity) hrhs, one_mul]
    have hroot : ((p : ℝ) ^ n) ^ ((1 : ℝ) / 4) ≤ (p : ℝ) ^ 2 := by
      calc ((p : ℝ) ^ n) ^ ((1 : ℝ) / 4) ≤ (((p : ℝ) ^ 2) ^ 4) ^ ((1 : ℝ) / 4) := by
            refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
            rw [← pow_mul]
            exact pow_le_pow_right₀ (by linarith) (by omega)
        _ = (p : ℝ) ^ 2 := rpow_quarter_pow_four (by positivity)
    have h16 : (p : ℝ) ^ 4 ≤ 16 * ((p : ℝ) - 1) ^ 4 := by
      calc (p : ℝ) ^ 4 ≤ (2 * ((p : ℝ) - 1)) ^ 4 := pow_le_pow_left₀ hPpos.le hP2 4
        _ = 16 * ((p : ℝ) - 1) ^ 4 := by ring
    calc (p : ℝ) ^ 2 * ((p : ℝ) ^ n) ^ ((1 : ℝ) / 4) ≤ (p : ℝ) ^ 2 * (p : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hroot (by positivity)
      _ = (p : ℝ) ^ 4 := by ring
      _ ≤ 16 * ((p : ℝ) - 1) ^ 4 := h16

/-! ### The bound for one tuple of denominators -/

/-- **The bound for one denominator tuple** (the direct route): for squarefree `q_ω`, with
`r = lcm(q_ω)` and `R = ∏ q_ω`, `∏_ω μ²(q_ω)/φ(q_ω) · Δ_q ≤ 16^{ω(r)} / (r² R^{1/4})`. -/
theorem prod_muSqDivTotient_mul_card_le {q : Cube → ℕ} (hq : ∀ ω, Squarefree (q ω)) :
    (∏ ω, muSqDivTotient (q ω)) * ((numerators q).filter (FaceIntegral q)).card ≤
      16 ^ (cubeLcm q).primeFactors.card /
        ((cubeLcm q : ℝ) ^ 2 * ((∏ ω, q ω : ℕ) : ℝ) ^ ((1 : ℝ) / 4)) := by
  classical
  set P := (cubeLcm q).primeFactors with hPdef
  set v : ℕ → ℕ := fun p => (primeSupport q p).card with hv
  have hprime : ∀ p ∈ P, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  -- the Möbius factors are `1`
  have hmu : ∏ ω, muSqDivTotient (q ω) = 1 / ∏ ω, ((q ω).totient : ℝ) := by
    rw [one_div, ← prod_inv_distrib]
    refine prod_congr rfl fun ω _ => ?_
    unfold muSqDivTotient
    have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree (hq ω)
    have h1 : ((ArithmeticFunction.moebius (q ω) : ℤ) : ℝ) ^ 2 = 1 := by exact_mod_cast this
    rw [h1, one_div]
  -- the totients
  have htot : ∏ ω, ((q ω).totient : ℝ) = ∏ p ∈ P, ((p : ℝ) - 1) ^ v p := by
    have := congrArg (fun n : ℕ => (n : ℝ)) (prod_totient_eq hq)
    simp only [Nat.cast_prod, Nat.cast_pow] at this
    rw [this]
    refine prod_congr rfl fun p hp => ?_
    rw [Nat.cast_sub (hprime p hp).one_le]
    simp [hv]
  -- the count
  have hcount : (((numerators q).filter (FaceIntegral q)).card : ℝ) ≤
      ∏ p ∈ P, (perPrimeBound p (v p) : ℝ) := by
    exact_mod_cast card_filter_numerators_le_prod q hq
  have hR : ((∏ ω, q ω : ℕ) : ℝ) = ∏ p ∈ P, (p : ℝ) ^ v p := by
    rw [prod_eq_prod_pow hq]
    push_cast
    rfl
  have hr : (cubeLcm q : ℝ) = ∏ p ∈ P, (p : ℝ) := by
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree (squarefree_cubeLcm hq)]
    push_cast
    rfl
  have hpos : ∀ p ∈ P, (0 : ℝ) < ((p : ℝ) - 1) ^ v p := fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
    exact pow_pos (by linarith) _
  rw [hmu, htot, hR, hr]
  calc 1 / (∏ p ∈ P, ((p : ℝ) - 1) ^ v p) * (((numerators q).filter (FaceIntegral q)).card : ℝ)
      ≤ 1 / (∏ p ∈ P, ((p : ℝ) - 1) ^ v p) * ∏ p ∈ P, (perPrimeBound p (v p) : ℝ) :=
        mul_le_mul_of_nonneg_left hcount
          (div_nonneg zero_le_one (prod_nonneg fun p hp => (hpos p hp).le))
    _ = ∏ p ∈ P, ((perPrimeBound p (v p) : ℝ) / ((p : ℝ) - 1) ^ v p) := by
        rw [prod_div_distrib]
        ring
    _ ≤ ∏ p ∈ P, (16 / ((p : ℝ) ^ 2 * ((p : ℝ) ^ v p) ^ ((1 : ℝ) / 4))) :=
        prod_le_prod₀ (fun p hp => div_nonneg (Nat.cast_nonneg _) (hpos p hp).le)
          (fun p hp => perPrimeBound_div_le (hprime p hp) (card_primeSupport_le q p))
    _ = 16 ^ P.card / ((∏ p ∈ P, (p : ℝ)) ^ 2 *
          (∏ p ∈ P, (p : ℝ) ^ v p) ^ ((1 : ℝ) / 4)) := by
        rw [prod_div_distrib, prod_const, prod_mul_distrib, prod_pow,
          Real.finsetProd_rpow _ _ (fun p _ => by positivity)]

end PrimeCarleson.Proof.FplusProp21
