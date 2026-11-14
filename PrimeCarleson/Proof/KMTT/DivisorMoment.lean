module

public import PrimeCarleson.Proof.KMTT.TypeICoeff
public import Mathlib.NumberTheory.ArithmeticFunction.Zeta
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The moment of the truncated divisor function

Source: [KMTT] `bounds`, proof of Lemma 4.6, L890–L923
([KMTT] TeX): `∑_{n ≤ M} τ(n, Q)^k ≤ C_k M ⟨Log Q⟩^(2^k - 1)` for
`Q ≥ 8`.

Deviation from KMTT (same conclusion, one-variable Euler product only). KMTT expands `τ(n, Q)^k`
over `k`-tuples `ℓ₁, …, ℓ_k < Q`, counts the `n ≤ N` divisible by `[ℓ₁, …, ℓ_k]`, applies Rankin's
trick to each `ℓ_i` and factors the `k`-variable series into an Euler product. Here the `k`-variable
structure is hidden in a multiplicative function of `n`:

* Rankin's trick ([KMTT], L899–L902): for `ℓ < Q` and `σ = 1/⟨Log Q⟩`, `1 ≤ 4 ℓ^(-σ)`, so
  `τ(n, Q) ≤ 4 τ_σ(n)` with `τ_σ(n) = ∑_{ℓ ∣ n} ℓ^(-σ)`, a multiplicative function of `n`;
* `H = τ_σ^k` is multiplicative, and `H = 1 * g` with `g = μ * H` nonnegative and multiplicative
  (`g(p^{a+1}) = H(p^{a+1}) - H(p^a) ≥ 0`, `g(p) = (1 + p^(-σ))^k - 1`, `g(p^a) ≤ (a+1)^k`);
* `∑_{n ≤ M} H(n) = ∑_{d ≤ M} g(d) ⌊M/d⌋ ≤ M ∑_{d ≤ M} g(d)/d` (this replaces the lcm expansion);
* finite Euler product: `∑_{d ≤ M} g(d)/d ≤ ∏_{p ≤ M} (1 + g(p)/p + K_k/p²)`;
* `g(p)/p ≤ (2^k - 1)/p` (Mertens for `p < Q`) and `g(p)/p ≤ k 2^k p^(-σ)/p` (Chebyshev tail for
  `p ≥ Q`, `sum_primes_le_log_log_add`), so the product is at most
  `exp ((2^k - 1)(log log Q + 4) + 60 k 2^k + K_k) ≲_k (log Q)^(2^k - 1) ≲ ⟨Log Q⟩^(2^k - 1)`.
-/

@[expose] public noncomputable section

open PrimeCarleson ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

set_option autoImplicit false

namespace PrimeCarleson.Proof.KMTT

open PrimeCarleson.Proof.Common

/-- The arithmetic function `n ↦ n^(-σ)` (`0 ↦ 0`). -/
def powNeg (σ : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else (n : ℝ) ^ (-σ), by simp⟩

/-- `n^(-σ)` at `n ≠ 0`. -/
theorem powNeg_apply (σ : ℝ) {n : ℕ} (hn : n ≠ 0) : powNeg σ n = (n : ℝ) ^ (-σ) := by
  simp [powNeg, hn]

/-- `n ↦ n^(-σ)` is multiplicative. -/
theorem isMultiplicative_powNeg (σ : ℝ) : (powNeg σ).IsMultiplicative := by
  refine ⟨by simp [powNeg], fun {m n} _ => ?_⟩
  by_cases hm : m = 0
  · simp [powNeg, hm]
  by_cases hn : n = 0
  · simp [powNeg, hn]
  rw [powNeg_apply σ hm, powNeg_apply σ hn, powNeg_apply σ (mul_ne_zero hm hn), Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]

/-- `τ_σ(n) = ∑_{ℓ ∣ n} ℓ^(-σ)` as an arithmetic function. -/
def tauSigma (σ : ℝ) : ArithmeticFunction ℝ := (ζ : ArithmeticFunction ℝ) * powNeg σ

/-- `τ_σ(n) = ∑_{ℓ ∣ n} ℓ^(-σ)`. -/
theorem tauSigma_apply (σ : ℝ) (n : ℕ) :
    tauSigma σ n = ∑ ℓ ∈ n.divisors, (ℓ : ℝ) ^ (-σ) := by
  unfold tauSigma
  rw [coe_zeta_mul_apply]
  exact Finset.sum_congr rfl fun ℓ hℓ => powNeg_apply σ (Nat.pos_of_mem_divisors hℓ).ne'

/-- `τ_σ` is multiplicative (Dirichlet convolution of multiplicative functions). -/
theorem isMultiplicative_tauSigma (σ : ℝ) : (tauSigma σ).IsMultiplicative :=
  isMultiplicative_zeta.natCast.mul (isMultiplicative_powNeg σ)

/-- `τ_σ(n) ≥ 0`. -/
theorem tauSigma_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ tauSigma σ n := by
  rw [tauSigma_apply]
  exact Finset.sum_nonneg fun ℓ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- `τ_σ` is monotone for divisibility (all terms are nonnegative). -/
theorem tauSigma_le_of_dvd (σ : ℝ) {m n : ℕ} (hn : n ≠ 0) (h : m ∣ n) :
    tauSigma σ m ≤ tauSigma σ n := by
  rw [tauSigma_apply, tauSigma_apply]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Nat.divisors_subset_of_dvd hn h)
    fun ℓ _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- `τ_σ(p^a) ≤ a + 1` for `σ ≥ 0`. -/
theorem tauSigma_prime_pow_le (σ : ℝ) (hσ : 0 ≤ σ) {p : ℕ} (hp : p.Prime) (a : ℕ) :
    tauSigma σ (p ^ a) ≤ a + 1 := by
  rw [tauSigma_apply, Nat.sum_divisors_prime_pow hp]
  calc ∑ x ∈ range (a + 1), ((p ^ x : ℕ) : ℝ) ^ (-σ) ≤ ∑ _x ∈ range (a + 1), (1 : ℝ) := by
        refine Finset.sum_le_sum fun x _ => ?_
        have h1 : (1 : ℝ) ≤ ((p ^ x : ℕ) : ℝ) := by
          exact_mod_cast Nat.one_le_pow _ _ hp.pos
        exact Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
    _ = a + 1 := by simp

/-- `τ_σ(p) = 1 + p^(-σ)` for a prime `p`. -/
theorem tauSigma_prime (σ : ℝ) {p : ℕ} (hp : p.Prime) :
    tauSigma σ p = 1 + (p : ℝ) ^ (-σ) := by
  rw [tauSigma_apply, hp.divisors, Finset.sum_pair hp.one_lt.ne]
  simp

/-- `H = τ_σ^k` (`k ≥ 1`) as an arithmetic function. -/
def tauPow (σ : ℝ) (k : ℕ) : ArithmeticFunction ℝ := (tauSigma σ).ppow k

/-- `H(n) = τ_σ(n)^k` for `k ≥ 1`. -/
theorem tauPow_apply (σ : ℝ) {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    tauPow σ k n = tauSigma σ n ^ k := ppow_apply hk

/-- `H = τ_σ^k` is multiplicative. -/
theorem isMultiplicative_tauPow (σ : ℝ) (k : ℕ) : (tauPow σ k).IsMultiplicative :=
  (isMultiplicative_tauSigma σ).ppow

/-- The Möbius transform `g = μ * H`, so that `H = 1 * g`. -/
def tauMoeb (σ : ℝ) (k : ℕ) : ArithmeticFunction ℝ :=
  ((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) * tauPow σ k

/-- `g = μ * H` is multiplicative. -/
theorem isMultiplicative_tauMoeb (σ : ℝ) (k : ℕ) : (tauMoeb σ k).IsMultiplicative :=
  isMultiplicative_moebius.intCast.mul (isMultiplicative_tauPow σ k)

/-- `1 * g = H` (Möbius inversion). -/
theorem zeta_mul_tauMoeb (σ : ℝ) (k : ℕ) :
    (ζ : ArithmeticFunction ℝ) * tauMoeb σ k = tauPow σ k := by
  unfold tauMoeb
  rw [← mul_assoc, coe_zeta_mul_coe_moebius, one_mul]

/-- `∑_{d ∣ n} g(d) = H(n)`. -/
theorem sum_divisors_tauMoeb (σ : ℝ) (k : ℕ) (n : ℕ) :
    ∑ d ∈ n.divisors, tauMoeb σ k d = tauPow σ k n := by
  rw [← coe_zeta_mul_apply, zeta_mul_tauMoeb]

/-- `H(1) = 1`. -/
theorem tauPow_one (σ : ℝ) (k : ℕ) : tauPow σ k 1 = 1 := (isMultiplicative_tauPow σ k).map_one

/-- `g(1) = 1`. -/
theorem tauMoeb_one (σ : ℝ) (k : ℕ) : tauMoeb σ k 1 = 1 := (isMultiplicative_tauMoeb σ k).map_one

/-- `H` is monotone for divisibility. -/
theorem tauPow_le_of_dvd (σ : ℝ) {k : ℕ} (hk : 1 ≤ k) {m n : ℕ} (hn : n ≠ 0) (h : m ∣ n) :
    tauPow σ k m ≤ tauPow σ k n := by
  rw [tauPow_apply σ hk, tauPow_apply σ hk]
  exact pow_le_pow_left₀ (tauSigma_nonneg σ m) (tauSigma_le_of_dvd σ hn h) k

/-- `g(p^{a+1}) = H(p^{a+1}) - H(p^a)`. -/
theorem tauMoeb_prime_pow_succ (σ : ℝ) (k : ℕ) {p : ℕ} (hp : p.Prime) (a : ℕ) :
    tauMoeb σ k (p ^ (a + 1)) = tauPow σ k (p ^ (a + 1)) - tauPow σ k (p ^ a) := by
  have h1 := sum_divisors_tauMoeb σ k (p ^ (a + 1))
  have h2 := sum_divisors_tauMoeb σ k (p ^ a)
  rw [Nat.sum_divisors_prime_pow hp] at h1 h2
  rw [Finset.sum_range_succ] at h1
  linarith

/-- `g ≥ 0`: `g` is multiplicative and `g(p^{a+1}) = H(p^{a+1}) - H(p^a) ≥ 0`. -/
theorem tauMoeb_nonneg (σ : ℝ) {k : ℕ} (hk : 1 ≤ k) (n : ℕ) : 0 ≤ tauMoeb σ k n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => rw [tauMoeb_one]; exact zero_le_one
  | prime_pow p a hp ha =>
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rw [tauMoeb_prime_pow_succ σ k hp, sub_nonneg]
    exact tauPow_le_of_dvd σ hk (pow_ne_zero _ hp.ne_zero) (pow_dvd_pow p (Nat.le_succ b))
  | coprime a b _ _ hab iha ihb =>
    rw [(isMultiplicative_tauMoeb σ k).map_mul_of_coprime hab]
    exact mul_nonneg iha ihb

/-- `g(n) ≤ H(n)` (one term of `∑_{d ∣ n} g(d) = H(n)`). -/
theorem tauMoeb_le_tauPow (σ : ℝ) {k : ℕ} (hk : 1 ≤ k) {n : ℕ} (hn : n ≠ 0) :
    tauMoeb σ k n ≤ tauPow σ k n := by
  rw [← sum_divisors_tauMoeb]
  exact Finset.single_le_sum (f := tauMoeb σ k) (fun d _ => tauMoeb_nonneg σ hk d)
    (Nat.mem_divisors_self n hn)

/-- `g(p) = (1 + p^(-σ))^k - 1` for a prime `p`. -/
theorem tauMoeb_prime (σ : ℝ) {k : ℕ} (hk : 1 ≤ k) {p : ℕ} (hp : p.Prime) :
    tauMoeb σ k p = (1 + (p : ℝ) ^ (-σ)) ^ k - 1 := by
  have h := tauMoeb_prime_pow_succ σ k hp 0
  rw [zero_add, pow_one, pow_zero, tauPow_one, tauPow_apply σ hk, tauSigma_prime σ hp] at h
  exact h

/-- `H(p^a) ≤ (a + 1)^k` for `σ ≥ 0`. -/
theorem tauPow_prime_pow_le (σ : ℝ) (hσ : 0 ≤ σ) {k : ℕ} (hk : 1 ≤ k) {p : ℕ} (hp : p.Prime)
    (a : ℕ) : tauPow σ k (p ^ a) ≤ ((a : ℝ) + 1) ^ k := by
  rw [tauPow_apply σ hk]
  exact pow_le_pow_left₀ (tauSigma_nonneg σ _) (tauSigma_prime_pow_le σ hσ hp a) k

/-- `∑_{n ≤ M} H(n) ≤ M ∑_{d ≤ M} g(d)/d` (replaces the lcm expansion). -/
theorem sum_tauPow_le (σ : ℝ) {k : ℕ} (hk : 1 ≤ k) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, tauPow σ k n ≤
      M * ∑ d ∈ Finset.Icc 1 M, tauMoeb σ k d / d := by
  have h1 : ∀ n ∈ Finset.Icc 1 M,
      tauPow σ k n = ((tauMoeb σ k) * (ζ : ArithmeticFunction ℝ)) n := by
    intro n _
    rw [mul_comm, zeta_mul_tauMoeb]
  rw [Finset.sum_congr rfl h1]
  have h2 : Finset.Icc 1 M = Finset.Ioc 0 M := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [h2, sum_Ioc_mul_eq_sum_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun d hd => ?_
  rw [Finset.mem_Ioc] at hd
  have hz : ∑ m ∈ Finset.Ioc 0 (M / d), (ζ : ArithmeticFunction ℝ) m = ((M / d : ℕ) : ℝ) := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ))]
    · simp
    · intro m hm
      have : m ≠ 0 := by have := (Finset.mem_Ioc.mp hm).1; omega
      simp [this]
  rw [hz]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
  have hdiv : ((M / d : ℕ) : ℝ) ≤ (M : ℝ) / d := Nat.cast_div_le
  calc tauMoeb σ k d * ((M / d : ℕ) : ℝ) ≤ tauMoeb σ k d * ((M : ℝ) / d) :=
        mul_le_mul_of_nonneg_left hdiv (tauMoeb_nonneg σ hk d)
    _ = M * (tauMoeb σ k d / d) := by ring

/-- `F(d) = g(d) / d`, the multiplicative function of the Euler product. -/
def tauMoebDiv (σ : ℝ) (k : ℕ) (d : ℕ) : ℝ := tauMoeb σ k d / d

/-- `F ≥ 0`. -/
theorem tauMoebDiv_nonneg (σ : ℝ) {k : ℕ} (hk : 1 ≤ k) (d : ℕ) : 0 ≤ tauMoebDiv σ k d :=
  div_nonneg (tauMoeb_nonneg σ hk d) (Nat.cast_nonneg d)

/-- `F(1) = 1`. -/
theorem tauMoebDiv_one (σ : ℝ) (k : ℕ) : tauMoebDiv σ k 1 = 1 := by
  simp [tauMoebDiv, tauMoeb_one]

/-- `F` is multiplicative on coprime arguments. -/
theorem tauMoebDiv_mul (σ : ℝ) (k : ℕ) {m n : ℕ} (h : Nat.Coprime m n) :
    tauMoebDiv σ k (m * n) = tauMoebDiv σ k m * tauMoebDiv σ k n := by
  unfold tauMoebDiv
  rw [(isMultiplicative_tauMoeb σ k).map_mul_of_coprime h, Nat.cast_mul, div_mul_div_comm]

/-- `∑ (b + c)^k r^b` converges for `0 < r < 1`. -/
theorem summable_add_pow_mul_geometric (k c : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable fun b : ℕ => ((b : ℝ) + c) ^ k * r ^ b := by
  have h := (summable_nat_add_iff c).mpr
    (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) k (r := r)
      (by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1))
  have h2 := h.mul_left ((r ^ c)⁻¹)
  refine h2.congr fun b => ?_
  have hrc : r ^ c ≠ 0 := pow_ne_zero _ hr0.ne'
  push_cast
  rw [pow_add]
  field_simp

/-- The constant of the tail of the Euler factors. -/
def eulerTailConst (k : ℕ) : ℝ := ∑' b : ℕ, ((b : ℝ) + 3) ^ k * (1 / 2 : ℝ) ^ b

/-- `K_k ≥ 0`. -/
theorem eulerTailConst_nonneg (k : ℕ) : 0 ≤ eulerTailConst k :=
  tsum_nonneg fun b => by positivity

/-- `F(p^a) ≤ (a + 1)^k p^(-a)`. -/
theorem tauMoebDiv_prime_pow_le (σ : ℝ) (hσ : 0 ≤ σ) {k : ℕ} (hk : 1 ≤ k) {p : ℕ}
    (hp : p.Prime) (a : ℕ) :
    tauMoebDiv σ k (p ^ a) ≤ ((a : ℝ) + 1) ^ k * (1 / (p : ℝ)) ^ a := by
  unfold tauMoebDiv
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have h1 := (tauMoeb_le_tauPow σ hk (pow_ne_zero a hp.ne_zero)).trans
    (tauPow_prime_pow_le σ hσ hk hp a)
  rw [one_div, inv_pow, Nat.cast_pow, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right h1 (by positivity)

/-- `a ↦ F(p^a)` is summable for `σ ≥ 0` and a prime `p`. -/
theorem summable_tauMoebDiv_prime_pow (σ : ℝ) (hσ : 0 ≤ σ) {k : ℕ} (hk : 1 ≤ k) {p : ℕ}
    (hp : p.Prime) : Summable fun a : ℕ => tauMoebDiv σ k (p ^ a) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hr0 : 0 < 1 / (p : ℝ) := by positivity
  have hr1 : 1 / (p : ℝ) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  have hs := summable_add_pow_mul_geometric k 1 hr0 hr1
  refine Summable.of_nonneg_of_le (fun a => tauMoebDiv_nonneg σ hk _)
    (fun a => ?_) hs
  simpa using tauMoebDiv_prime_pow_le σ hσ hk hp a

/-- The Euler factor at `p`: `∑_a g(p^a)/p^a ≤ 1 + g(p)/p + K_k / p²`. -/
theorem tsum_tauMoebDiv_prime_pow_le (σ : ℝ) (hσ : 0 ≤ σ) {k : ℕ} (hk : 1 ≤ k) {p : ℕ}
    (hp : p.Prime) :
    ∑' a : ℕ, tauMoebDiv σ k (p ^ a) ≤
      1 + tauMoeb σ k p / p + eulerTailConst k / (p : ℝ) ^ 2 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hs := summable_tauMoebDiv_prime_pow σ hσ hk hp
  rw [← hs.sum_add_tsum_nat_add 2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
    tauMoebDiv_one]
  have hq : Summable fun b : ℕ => ((b : ℝ) + 3) ^ k * (1 / 2 : ℝ) ^ b :=
    summable_add_pow_mul_geometric k 3 (by norm_num) (by norm_num)
  have hq2 : Summable fun b : ℕ => ((b : ℝ) + 3) ^ k * (1 / 2 : ℝ) ^ b * (1 / (p : ℝ)) ^ 2 :=
    hq.mul_right _
  have hs2 : Summable fun b : ℕ => tauMoebDiv σ k (p ^ (b + 2)) :=
    (summable_nat_add_iff (f := fun a : ℕ => tauMoebDiv σ k (p ^ a)) 2).mpr hs
  have hcmp : ∑' b : ℕ, tauMoebDiv σ k (p ^ (b + 2)) ≤
      ∑' b : ℕ, ((b : ℝ) + 3) ^ k * (1 / 2 : ℝ) ^ b * (1 / (p : ℝ)) ^ 2 := by
    refine Summable.tsum_le_tsum (fun b => ?_) hs2 hq2
    have h1 := tauMoebDiv_prime_pow_le σ hσ hk hp (b + 2)
    refine h1.trans ?_
    have hpow : (1 / (p : ℝ)) ^ (b + 2) ≤ (1 / 2 : ℝ) ^ b * (1 / (p : ℝ)) ^ 2 := by
      rw [pow_add]
      gcongr
    have : ((↑(b + 2) : ℝ) + 1) = (b : ℝ) + 3 := by push_cast; ring
    rw [this]
    calc ((b : ℝ) + 3) ^ k * (1 / (p : ℝ)) ^ (b + 2)
        ≤ ((b : ℝ) + 3) ^ k * ((1 / 2 : ℝ) ^ b * (1 / (p : ℝ)) ^ 2) := by gcongr
      _ = ((b : ℝ) + 3) ^ k * (1 / 2 : ℝ) ^ b * (1 / (p : ℝ)) ^ 2 := by ring
  rw [tsum_mul_right] at hcmp
  have hK : (∑' x : ℕ, ((x : ℝ) + 3) ^ k * (1 / 2 : ℝ) ^ x) = eulerTailConst k := rfl
  rw [hK] at hcmp
  have : eulerTailConst k * (1 / (p : ℝ)) ^ 2 = eulerTailConst k / (p : ℝ) ^ 2 := by
    rw [one_div, inv_pow, ← div_eq_mul_inv]
  rw [← this]
  have e : tauMoebDiv σ k p = tauMoeb σ k p / p := rfl
  linarith

/-- `(1 + x)^k - 1 ≤ k 2^k x` for `0 ≤ x ≤ 1`. -/
theorem pow_one_add_sub_one_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    (1 + x) ^ k - 1 ≤ k * 2 ^ k * x := by
  have h := geom_sum_mul (1 + x) k
  rw [add_sub_cancel_left] at h
  rw [← h]
  have : ∑ i ∈ range k, (1 + x) ^ i ≤ k * 2 ^ k := by
    calc ∑ i ∈ range k, (1 + x) ^ i ≤ ∑ _i ∈ range k, (2 : ℝ) ^ k := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i ≤ k := (Finset.mem_range.mp hi).le
          calc (1 + x) ^ i ≤ 2 ^ i := pow_le_pow_left₀ (by linarith) (by linarith) i
            _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hi'
      _ = k * 2 ^ k := by simp
  nlinarith

/-- `(1 + x)^k ≤ 2^k` for `0 ≤ x ≤ 1`. -/
theorem pow_one_add_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) : (1 + x) ^ k ≤ 2 ^ k :=
  pow_le_pow_left₀ (by linarith) (by linarith) k

/-- The prime sum of the Euler factors: `∑_{p ≤ M} (g(p)/p + K_k/p²) ≤ (2^k - 1)(log log Q + 4)
+ 60 k 2^k + K_k` for `Q ≥ 8` and `σ = 1/⟨Log Q⟩` ([KMTT], L912–L916 and L919–L922). -/
theorem sum_tauMoeb_div_le {Q : ℝ} (hQ : 8 ≤ Q) {k : ℕ} (hk : 1 ≤ k) (M : ℕ) :
    ∑ p ∈ (M + 1).primesBelow,
        (tauMoeb (1 / logBracket Q) k p / p + eulerTailConst k / (p : ℝ) ^ 2) ≤
      ((2 ^ k - 1 : ℕ) : ℝ) * (Real.log (Real.log Q) + 4) + 60 * (k * 2 ^ k) +
        eulerTailConst k := by
  set σ : ℝ := 1 / logBracket Q with hσdef
  have hL := logBracket_pos Q
  have hσ : 0 < σ := by positivity
  have hσ1 : σ ≤ 1 := by
    rw [hσdef, div_le_one hL]; exact one_le_logBracket Q
  have hσQ : 1 / 2 ≤ σ * Real.log Q := half_le_inv_logBracket_mul_log hQ
  have hprime : ∀ p ∈ (M + 1).primesBelow, p.Prime := fun p hp => Nat.prime_of_mem_primesBelow hp
  have hx : ∀ p : ℕ, p.Prime → 0 ≤ (p : ℝ) ^ (-σ) ∧ (p : ℝ) ^ (-σ) ≤ 1 := by
    intro p hp
    have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    exact ⟨Real.rpow_nonneg (by linarith) _,
      Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)⟩
  have hA : ((2 ^ k - 1 : ℕ) : ℝ) = 2 ^ k - 1 := by
    rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow]; simp
  rw [Finset.sum_add_distrib]
  have h1 : ∑ p ∈ (M + 1).primesBelow, tauMoeb σ k p / p ≤
      ((2 ^ k - 1 : ℕ) : ℝ) * (Real.log (Real.log Q) + 4) + 60 * (k * 2 ^ k) := by
    refine sum_primes_le_log_log_add (Q := Q) (σ := σ) (by linarith) hσ hσ1 hσQ
      (fun p => tauMoeb σ k p / p) (A := ((2 ^ k - 1 : ℕ) : ℝ)) (B := (k * 2 ^ k : ℝ))
      (by positivity) (by positivity) ?_ ?_ _ hprime
    · intro p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      rw [tauMoeb_prime σ hk hp, hA]
      refine div_le_div_of_nonneg_right ?_ hp0.le
      linarith [pow_one_add_le (hx p hp).1 (hx p hp).2 k]
    · intro p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      rw [tauMoeb_prime σ hk hp]
      rw [← mul_div_assoc]
      refine div_le_div_of_nonneg_right ?_ hp0.le
      exact pow_one_add_sub_one_le (hx p hp).1 (hx p hp).2 k
  have h2 : ∑ p ∈ (M + 1).primesBelow, eulerTailConst k / (p : ℝ) ^ 2 ≤ eulerTailConst k := by
    have hK := eulerTailConst_nonneg k
    calc ∑ p ∈ (M + 1).primesBelow, eulerTailConst k / (p : ℝ) ^ 2
        ≤ ∑ p ∈ (M + 1).primesBelow, eulerTailConst k * (1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
          rw [div_eq_mul_one_div]
          refine mul_le_mul_of_nonneg_left ?_ hK
          rw [div_le_div_iff₀ (by positivity) (mul_pos (by linarith) (by linarith))]
          nlinarith
      _ = eulerTailConst k * ∑ p ∈ (M + 1).primesBelow, 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
          rw [Finset.mul_sum]
      _ ≤ eulerTailConst k * 1 := by
          gcongr
          calc ∑ p ∈ (M + 1).primesBelow, 1 / ((p : ℝ) * ((p : ℝ) - 1))
              ≤ ∑ n ∈ Finset.Icc 2 M, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
                refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n hn _ => ?_
                · intro p hp
                  rw [Nat.mem_primesBelow] at hp
                  exact Finset.mem_Icc.mpr ⟨hp.2.two_le, by omega⟩
                · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
                  have : 0 < (n : ℝ) * ((n : ℝ) - 1) := mul_pos (by linarith) (by linarith)
                  positivity
            _ ≤ 1 := sum_Icc_inv_mul_pred_le_one M
      _ = eulerTailConst k := mul_one _
  linarith

/-- The Euler product bound for `∑_{n ≤ M} τ_σ(n)^k` ([KMTT], L903–L922). -/
theorem sum_tauPow_le_mul {Q : ℝ} (hQ : 8 ≤ Q) {k : ℕ} (hk : 1 ≤ k) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, tauPow (1 / logBracket Q) k n ≤
      M * (Real.exp (4 * ((2 ^ k - 1 : ℕ) : ℝ) + 60 * (k * 2 ^ k) + eulerTailConst k) *
        Real.log Q ^ (2 ^ k - 1)) := by
  set σ : ℝ := 1 / logBracket Q with hσdef
  have hL := logBracket_pos Q
  have hσ : 0 ≤ σ := by positivity
  have hlogQ : 0 < Real.log Q := Real.log_pos (by linarith)
  have h1 := sum_tauPow_le σ hk M
  have h2 := sum_Icc_le_prod_primesBelow (F := tauMoebDiv σ k) (tauMoebDiv_nonneg σ hk)
    (tauMoebDiv_one σ k) (fun h => tauMoebDiv_mul σ k h)
    (fun hp => summable_tauMoebDiv_prime_pow σ hσ hk hp) M
  have hx : ∀ p ∈ (M + 1).primesBelow,
      0 ≤ tauMoeb σ k p / p + eulerTailConst k / (p : ℝ) ^ 2 := fun p hp => by
    have := eulerTailConst_nonneg k
    exact add_nonneg (div_nonneg (tauMoeb_nonneg σ hk p) (Nat.cast_nonneg p))
      (div_nonneg this (by positivity))
  have h3 : ∏ p ∈ (M + 1).primesBelow, ∑' a : ℕ, tauMoebDiv σ k (p ^ a) ≤
      ∏ p ∈ (M + 1).primesBelow, (1 + (tauMoeb σ k p / p + eulerTailConst k / (p : ℝ) ^ 2)) := by
    refine Finset.prod_le_prod₀ (fun p _ => tsum_nonneg fun a => tauMoebDiv_nonneg σ hk _)
      fun p hp => ?_
    have := tsum_tauMoebDiv_prime_pow_le σ hσ hk (Nat.prime_of_mem_primesBelow hp)
    linarith
  have h4 := prod_one_add_le_exp_sum _ _ hx
  have h5 := sum_tauMoeb_div_le hQ hk M
  have h6 : Real.exp (∑ p ∈ (M + 1).primesBelow,
      (tauMoeb σ k p / p + eulerTailConst k / (p : ℝ) ^ 2)) ≤
      Real.exp (4 * ((2 ^ k - 1 : ℕ) : ℝ) + 60 * (k * 2 ^ k) + eulerTailConst k) *
        Real.log Q ^ (2 ^ k - 1) := by
    refine (Real.exp_le_exp.mpr h5).trans (le_of_eq ?_)
    have : ((2 ^ k - 1 : ℕ) : ℝ) * (Real.log (Real.log Q) + 4) + 60 * (k * 2 ^ k) +
        eulerTailConst k = ((2 ^ k - 1 : ℕ) : ℝ) * Real.log (Real.log Q) +
        (4 * ((2 ^ k - 1 : ℕ) : ℝ) + 60 * (k * 2 ^ k) + eulerTailConst k) := by ring
    rw [this, Real.exp_add, Real.exp_nat_mul, Real.exp_log hlogQ, mul_comm]
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  calc ∑ n ∈ Finset.Icc 1 M, tauPow σ k n ≤ M * ∑ d ∈ Finset.Icc 1 M, tauMoeb σ k d / d := h1
    _ ≤ M * (Real.exp (4 * ((2 ^ k - 1 : ℕ) : ℝ) + 60 * (k * 2 ^ k) + eulerTailConst k) *
        Real.log Q ^ (2 ^ k - 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ hM
        exact h2.trans (h3.trans (h4.trans h6))

/-- Rankin's trick ([KMTT], L899–L902): `τ(n, Q) ≤ 4 τ_σ(n)` for `σ = 1/⟨Log Q⟩`. -/
theorem truncDivisor_le_four_mul_tauSigma {Q : ℝ} (hQ : 1 ≤ Q) (n : ℕ) :
    (truncDivisor n Q : ℝ) ≤ 4 * tauSigma (1 / logBracket Q) n := by
  rw [tauSigma_apply, Finset.mul_sum]
  unfold truncDivisor
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  calc ∑ ℓ ∈ n.divisors.filter (fun l : ℕ => (l : ℝ) < Q), ((1 : ℕ) : ℝ)
      ≤ ∑ ℓ ∈ n.divisors.filter (fun l : ℕ => (l : ℝ) < Q),
        4 * (ℓ : ℝ) ^ (-(1 / logBracket Q)) := by
        refine Finset.sum_le_sum fun ℓ hℓ => ?_
        rw [Finset.mem_filter] at hℓ
        have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast Nat.pos_of_mem_divisors hℓ.1
        have h4 := rpow_inv_logBracket_le_four hQ hℓ0.le hℓ.2.le
        have hpos : (0 : ℝ) < (ℓ : ℝ) ^ (1 / logBracket Q) := Real.rpow_pos_of_pos hℓ0 _
        rw [Real.rpow_neg hℓ0.le, Nat.cast_one]
        rw [← div_eq_mul_inv, le_div_iff₀ hpos]
        linarith
    _ ≤ ∑ ℓ ∈ n.divisors, 4 * (ℓ : ℝ) ^ (-(1 / logBracket Q)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun ℓ _ _ => ?_
        have := Real.rpow_nonneg (Nat.cast_nonneg ℓ) (-(1 / logBracket Q))
        linarith

/-- The moment of the truncated divisor function ([KMTT], L891–L892, with a
sharper exponent): `∑_{n ≤ M} τ(n, Q)^k ≤ C_k M ⟨Log Q⟩^(2^k - 1)` for `Q ≥ 8`. -/
theorem exists_sum_truncDivisor_pow_le {k : ℕ} (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : ℝ) (M : ℕ), 8 ≤ Q →
      ∑ n ∈ Finset.Icc 1 M, (truncDivisor n Q : ℝ) ^ k ≤
        C * M * logBracket Q ^ (2 ^ k - 1) := by
  refine ⟨4 ^ k * Real.exp (4 * ((2 ^ k - 1 : ℕ) : ℝ) + 60 * (k * 2 ^ k) + eulerTailConst k) *
    2 ^ (2 ^ k - 1), by positivity, fun Q M hQ => ?_⟩
  have hQ1 : 1 ≤ Q := by linarith
  have hL := logBracket_pos Q
  have hlogQ : 0 < Real.log Q := Real.log_pos (by linarith)
  set σ : ℝ := 1 / logBracket Q with hσdef
  have h1 : ∀ n ∈ Finset.Icc 1 M, (truncDivisor n Q : ℝ) ^ k ≤ 4 ^ k * tauPow σ k n := by
    intro n _
    rw [tauPow_apply σ hk, ← mul_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (truncDivisor_le_four_mul_tauSigma hQ1 n) k
  have h2 := sum_tauPow_le_mul hQ hk M
  have h3 : Real.log Q ^ (2 ^ k - 1) ≤ (2 * logBracket Q) ^ (2 ^ k - 1) :=
    pow_le_pow_left₀ hlogQ.le (log_le_two_mul_logBracket hQ1) _
  have hE := Real.exp_pos (4 * ((2 ^ k - 1 : ℕ) : ℝ) + 60 * (k * 2 ^ k) + eulerTailConst k)
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  calc ∑ n ∈ Finset.Icc 1 M, (truncDivisor n Q : ℝ) ^ k
      ≤ ∑ n ∈ Finset.Icc 1 M, 4 ^ k * tauPow σ k n := Finset.sum_le_sum h1
    _ = 4 ^ k * ∑ n ∈ Finset.Icc 1 M, tauPow σ k n := by rw [Finset.mul_sum]
    _ ≤ 4 ^ k * (M * (Real.exp (4 * ((2 ^ k - 1 : ℕ) : ℝ) + 60 * (k * 2 ^ k) +
        eulerTailConst k) * (2 * logBracket Q) ^ (2 ^ k - 1))) := by
        gcongr
        calc ∑ n ∈ Finset.Icc 1 M, tauPow σ k n ≤ _ := h2
          _ ≤ _ := by gcongr
    _ = 4 ^ k * Real.exp (4 * ((2 ^ k - 1 : ℕ) : ℝ) + 60 * (k * 2 ^ k) + eulerTailConst k) *
          2 ^ (2 ^ k - 1) * M * logBracket Q ^ (2 ^ k - 1) := by
        rw [mul_pow]; ring

end PrimeCarleson.Proof.KMTT
