module

public import PrimeCarleson.Proof.Fplus31.Brun.Divisors
public import PrimeCarleson.Proof.Fplus31.Brun.Counting

/-!
# Brun's pure sieve on a progression

Part of the proof of [F+] Proposition 3.1 (the Cramér model and its Brun truncation). Notation:
`W = P(w) = ∏_{p < w} p`, `Wφ = W/φ(W)`, `S = ∑_{p < w} 1/p`, `L = hi - lo`, `I = apSet r a lo hi`.
For `1 ≤ r` and `gcd(a, r) = 1`:

* `brun_err1` (used by the Vaughan decomposition, the prime number theorem in progressions and the
  comparison with the Heath-Brown model): the one-sided `L¹` bound
  `∑_{n ∈ I} |Λ_{C,w}(n) - Λ_{C,w}^{(k)}(n)| ≤ Wφ ((L/r) S^{k+1}/(k+1)! + w^{k+1}/(k+1)!)`, with
  `Λ_{C,w}^{(k)} = brunTrunc w k` the type I Brun truncation (level `≤ w^k`);
* `brun_trunc_main`: the truncated main term
  `|∑_{n ∈ I} Λ_{C,w}^{(k)}(n) - Wφ (L/r) ∏_{p < w, p ∤ r} (1 - 1/p)|
    ≤ Wφ ((L/r) e^S S^{k+1}/(k+1)! + (k+1) w^k)`;
* `brun_ap` (used by the prime number theorem in progressions and, with `r = 1`, by the comparison
  with the Heath-Brown model): for `r < w`
  `|∑_{n ∈ I} Λ_{C,w}(n) - L/φ(r)| ≤ Wφ (2 e^S S^{k+1}/(k+1)! (L/r) + 2 (k+1) w^{k+1})`.
-/

@[expose] public noncomputable section

open Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- `e_j(1/p : p < w) ≤ S^j/j!` with `S = ∑_{p < w} 1/p`. -/
theorem sum_prod_inv_powersetCard_le (w j : ℕ) :
    ∑ D ∈ (Nat.primesBelow w).powersetCard j, ∏ p ∈ D, (1 / (p : ℝ)) ≤
      (∑ p ∈ Nat.primesBelow w, (1 : ℝ) / p) ^ j / (j.factorial : ℝ) := by
  have hfac : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  rw [le_div_iff₀ hfac, mul_comm]
  exact esymm_le _ (fun p : ℕ => 1 / (p : ℝ)) (fun p _ => by positivity) j

/-- The number of `j`-subsets of the primes below `w` is at most `w^j / j!`. -/
theorem card_powersetCard_primesBelow_le (w j : ℕ) :
    (((Nat.primesBelow w).powersetCard j).card : ℝ) ≤ (w : ℝ) ^ j / (j.factorial : ℝ) := by
  rw [Finset.card_powersetCard]
  refine le_trans (Nat.choose_le_pow_div j (Nat.primesBelow w).card) ?_
  have hfac : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  refine div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ j) hfac.le
  have : (Nat.primesBelow w).card ≤ w :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans (Finset.card_range w).le
  exact_mod_cast this

/-- **Brun's pure sieve, the one-sided `L¹` bound.** For `1 ≤ r` and `gcd(a, r) = 1`,
`∑_{n ∈ I} |Λ_{C,w}(n) - Λ_{C,w}^{(k)}(n)| ≤ (P/φ(P)) ((L/r) S^{k+1}/(k+1)! + w^{k+1}/(k+1)!)`,
`I = apSet r a lo hi`, `L = hi - lo`, `S = ∑_{p < w} 1/p`. -/
theorem brun_err1 (w k : ℕ) {r : ℕ} (hr : 1 ≤ r) {a : ℤ} (ha : IsCoprime a (r : ℤ))
    {lo hi : ℕ} (h : lo ≤ hi) :
    ∑ n ∈ apSet r a lo hi, |cramerModel w n - brunTrunc w k n| ≤
      (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) *
        (((hi : ℝ) - lo) / r *
            ((∑ p ∈ Nat.primesBelow w, (1 : ℝ) / p) ^ (k + 1) / ((k + 1).factorial : ℝ)) +
          (w : ℝ) ^ (k + 1) / ((k + 1).factorial : ℝ)) := by
  have hW : 0 ≤ (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) := by positivity
  have hL : 0 ≤ ((hi : ℝ) - lo) / r := by
    have : (lo : ℝ) ≤ hi := by exact_mod_cast h
    positivity
  calc ∑ n ∈ apSet r a lo hi, |cramerModel w n - brunTrunc w k n|
      ≤ ∑ n ∈ apSet r a lo hi, (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) *
          (((smallPrimeDivisors w n).card.choose (k + 1) : ℕ) : ℝ) :=
        Finset.sum_le_sum fun n _ => abs_cramerModel_sub_brunTrunc_le w k n
    _ = (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) *
          ∑ D ∈ (Nat.primesBelow w).powersetCard (k + 1),
            (((apSet r a lo hi).filter fun n => (((∏ p ∈ D, p : ℕ) : ℤ) ∣ n)).card : ℝ) := by
        rw [← Finset.mul_sum, sum_choose_smallPrimeDivisors]
    _ ≤ (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) *
          ∑ D ∈ (Nat.primesBelow w).powersetCard (k + 1),
            (((hi : ℝ) - lo) / r * ∏ p ∈ D, (1 / (p : ℝ)) + 1) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun D hD => ?_) hW
        have hprime : ∀ p ∈ D, p.Prime := fun p hp =>
          Nat.prime_of_mem_primesBelow ((Finset.mem_powersetCard.mp hD).1 hp)
        have h1 := abs_card_apSet_prod_dvd_sub_le hr ha h hprime
        have h2 : (if ∀ p ∈ D, ¬ p ∣ r then ((hi : ℝ) - lo) / r * ∏ p ∈ D, (1 / (p : ℝ))
            else 0) ≤ ((hi : ℝ) - lo) / r * ∏ p ∈ D, (1 / (p : ℝ)) := by
          split_ifs
          · exact le_rfl
          · exact mul_nonneg hL (Finset.prod_nonneg fun p _ => by positivity)
        rw [abs_le] at h1
        linarith [h1.2]
    _ = (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) *
          (((hi : ℝ) - lo) / r *
              ∑ D ∈ (Nat.primesBelow w).powersetCard (k + 1), ∏ p ∈ D, (1 / (p : ℝ)) +
            (((Nat.primesBelow w).powersetCard (k + 1)).card : ℝ)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hW
        · exact mul_le_mul_of_nonneg_left (sum_prod_inv_powersetCard_le w (k + 1)) hL
        · exact card_powersetCard_primesBelow_le w (k + 1)

/-- A sum over the `j`-subsets `D` of the primes below `w` with no prime factor of `r` is a sum
over the `j`-subsets of the primes below `w` not dividing `r`. -/
theorem sum_powersetCard_primesBelow_ite (w j r : ℕ) (g : Finset ℕ → ℝ) :
    ∑ D ∈ (Nat.primesBelow w).powersetCard j, (if ∀ p ∈ D, ¬ p ∣ r then g D else 0) =
      ∑ D ∈ ((Nat.primesBelow w).filter fun p => ¬ p ∣ r).powersetCard j, g D := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext D
  simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_iff]
  constructor
  · rintro ⟨⟨hD, hj⟩, hDr⟩
    exact ⟨fun p hp => ⟨hD hp, hDr p hp⟩, hj⟩
  · rintro ⟨hD, hj⟩
    exact ⟨⟨fun p hp => (hD hp).1, hj⟩, fun p hp => (hD hp).2⟩

/-- The number of subsets of the primes below `w` with at most `k` elements is at most
`(k+1) w^k`, `w ≥ 1`. -/
theorem sum_card_powersetCard_primesBelow_le {w : ℕ} (hw : 1 ≤ w) (k : ℕ) :
    ∑ j ∈ range (k + 1), (((Nat.primesBelow w).powersetCard j).card : ℝ) ≤
      (k + 1) * (w : ℝ) ^ k := by
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  calc ∑ j ∈ range (k + 1), (((Nat.primesBelow w).powersetCard j).card : ℝ)
      ≤ ∑ _j ∈ range (k + 1), (w : ℝ) ^ k := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        refine le_trans (card_powersetCard_primesBelow_le w j) ?_
        have hfac : (1 : ℝ) ≤ (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
        calc (w : ℝ) ^ j / (j.factorial : ℝ) ≤ (w : ℝ) ^ j :=
              div_le_self (by positivity) hfac
          _ ≤ (w : ℝ) ^ k := pow_le_pow_right₀ hw' hjk
    _ = (k + 1) * (w : ℝ) ^ k := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- **Brun's pure sieve, the truncated main term.** For `1 ≤ r`, `w ≥ 1` and `gcd(a, r) = 1`,
`|∑_{n ∈ I} Λ_{C,w}^{(k)}(n) - (P/φ(P)) (L/r) ∏_{p < w, p ∤ r} (1 - 1/p)|
  ≤ (P/φ(P)) ((L/r) e^S S^{k+1}/(k+1)! + (k+1) w^k)`. -/
theorem brun_trunc_main (w k : ℕ) (hw : 1 ≤ w) {r : ℕ} (hr : 1 ≤ r) {a : ℤ}
    (ha : IsCoprime a (r : ℤ)) {lo hi : ℕ} (h : lo ≤ hi) :
    |∑ n ∈ apSet r a lo hi, brunTrunc w k n -
        (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) *
          (((hi : ℝ) - lo) / r) *
          ∏ p ∈ (Nat.primesBelow w).filter (fun p => ¬ p ∣ r), (1 - 1 / (p : ℝ))| ≤
      (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) *
        (((hi : ℝ) - lo) / r * (Real.exp (∑ p ∈ Nat.primesBelow w, (1 : ℝ) / p) *
            ((∑ p ∈ Nat.primesBelow w, (1 : ℝ) / p) ^ (k + 1) / ((k + 1).factorial : ℝ))) +
          (k + 1) * (w : ℝ) ^ k) := by
  have hW : 0 ≤ (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) := by positivity
  have hL : 0 ≤ ((hi : ℝ) - lo) / r := by
    have : (lo : ℝ) ≤ hi := by exact_mod_cast h
    positivity
  set Pr' := (Nat.primesBelow w).filter fun p => ¬ p ∣ r with hPr'
  -- the counts and their expected values
  set N : Finset ℕ → ℝ := fun D =>
    (((apSet r a lo hi).filter fun n => (((∏ p ∈ D, p : ℕ) : ℤ) ∣ n)).card : ℝ) with hN
  set m : Finset ℕ → ℝ := fun D =>
    if ∀ p ∈ D, ¬ p ∣ r then ((hi : ℝ) - lo) / r * ∏ p ∈ D, (1 / (p : ℝ)) else 0 with hm
  have hθ : ∀ j, ∀ D ∈ (Nat.primesBelow w).powersetCard j, |N D - m D| ≤ 1 := by
    intro j D hD
    exact abs_card_apSet_prod_dvd_sub_le hr ha h fun p hp =>
      Nat.prime_of_mem_primesBelow ((Finset.mem_powersetCard.mp hD).1 hp)
  -- Step A: the double count
  have hA : ∑ n ∈ apSet r a lo hi, brunTrunc w k n =
      (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) *
        ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * ∑ D ∈ (Nat.primesBelow w).powersetCard j, N D := by
    simp_rw [brunTrunc_eq]
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum, sum_choose_smallPrimeDivisors]
  -- Step B: split `N = m + θ`
  set Θ : ℝ := ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j *
    ∑ D ∈ (Nat.primesBelow w).powersetCard j, (N D - m D) with hΘ
  have hΘb : |Θ| ≤ (k + 1) * (w : ℝ) ^ k := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum fun j _ => ?_) (sum_card_powersetCard_primesBelow_le hw k)
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum fun D hD => hθ j D hD) ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsplit : ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * ∑ D ∈ (Nat.primesBelow w).powersetCard j, N D =
      ((hi : ℝ) - lo) / r * ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j *
          ∑ D ∈ Pr'.powersetCard j, ∏ p ∈ D, (1 / (p : ℝ)) + Θ := by
    have hm' : ∀ j, ∑ D ∈ (Nat.primesBelow w).powersetCard j, m D =
        ((hi : ℝ) - lo) / r * ∑ D ∈ Pr'.powersetCard j, ∏ p ∈ D, (1 / (p : ℝ)) := by
      intro j
      rw [hm, sum_powersetCard_primesBelow_ite w j r
        (fun D => ((hi : ℝ) - lo) / r * ∏ p ∈ D, (1 / (p : ℝ))), Finset.mul_sum]
    rw [hΘ, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_sub_distrib, hm' j, mul_sub, Finset.mul_sum, mul_left_comm]
    ring
  -- Step C: the truncated product expansion
  have hS' : ∑ p ∈ Pr', (1 : ℝ) / p ≤ ∑ p ∈ Nat.primesBelow w, (1 : ℝ) / p :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun p _ _ => by positivity
  have hS'0 : 0 ≤ ∑ p ∈ Pr', (1 : ℝ) / p := Finset.sum_nonneg fun p _ => by positivity
  have hprod := abs_prod_one_sub_sub_le Pr' (fun p : ℕ => 1 / (p : ℝ)) (fun p _ => by positivity) k
  have htail : Real.exp (∑ p ∈ Pr', (1 : ℝ) / p) *
      ((∑ p ∈ Pr', (1 : ℝ) / p) ^ (k + 1) / ((k + 1).factorial : ℝ)) ≤
      Real.exp (∑ p ∈ Nat.primesBelow w, (1 : ℝ) / p) *
        ((∑ p ∈ Nat.primesBelow w, (1 : ℝ) / p) ^ (k + 1) / ((k + 1).factorial : ℝ)) := by
    have hfac : (0 : ℝ) < ((k + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    refine mul_le_mul (Real.exp_le_exp.mpr hS') ?_ (by positivity) (Real.exp_pos _).le
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hS'0 hS' _) hfac.le
  -- Step D: assemble
  rw [hA, hsplit]
  set T : ℝ := ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j *
    ∑ D ∈ Pr'.powersetCard j, ∏ p ∈ D, (1 / (p : ℝ)) with hT
  set Qp : ℝ := ∏ p ∈ Pr', (1 - 1 / (p : ℝ)) with hQp
  have hTQp : |T - Qp| ≤ Real.exp (∑ p ∈ Nat.primesBelow w, (1 : ℝ) / p) *
      ((∑ p ∈ Nat.primesBelow w, (1 : ℝ) / p) ^ (k + 1) / ((k + 1).factorial : ℝ)) := by
    rw [abs_sub_comm]
    exact hprod.trans htail
  have hrw : (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) *
        (((hi : ℝ) - lo) / r * T + Θ) -
      (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) * (((hi : ℝ) - lo) / r) * Qp =
      (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) *
        (((hi : ℝ) - lo) / r * (T - Qp) + Θ) := by ring
  rw [hrw, abs_mul, abs_of_nonneg hW]
  refine mul_le_mul_of_nonneg_left ?_ hW
  refine le_trans (abs_add_le _ _) (add_le_add ?_ hΘb)
  rw [abs_mul, abs_of_nonneg hL]
  exact mul_le_mul_of_nonneg_left hTQp hL

/-- `P(w)/φ(P(w)) · ∏_{p < w, p ∤ r} (1 - 1/p) = r/φ(r)` when every prime factor of `r` is
below `w` (here `1 ≤ r < w`). -/
theorem primorialBelow_div_totient_mul_prod {w r : ℕ} (hr : 1 ≤ r) (hrw : r < w) :
    (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) *
        ∏ p ∈ (Nat.primesBelow w).filter (fun p => ¬ p ∣ r), (1 - 1 / (p : ℝ)) =
      (r : ℝ) / (Nat.totient r : ℝ) := by
  have hW : (0 : ℝ) < primorialBelow w := by exact_mod_cast primorialBelow_pos w
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hfac : ∀ p ∈ Nat.primesBelow w, (1 - 1 / (p : ℝ)) ≠ 0 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast Nat.two_le_of_mem_primesBelow hp
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  have hsplit := Finset.prod_filter_mul_prod_filter_not (Nat.primesBelow w) (fun p => p ∣ r)
    (fun p => (1 - 1 / (p : ℝ)))
  have hpf : (Nat.primesBelow w).filter (fun p => p ∣ r) = r.primeFactors := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesBelow, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨_, hp⟩, hpr⟩
      exact ⟨hp, hpr, hr.trans_lt' (by omega) |>.ne'⟩
    · rintro ⟨hp, hpr, _⟩
      exact ⟨⟨lt_of_le_of_lt (Nat.le_of_dvd hr hpr) hrw, hp⟩, hpr⟩
  rw [hpf] at hsplit
  have hφr : (Nat.totient r : ℝ) = r * ∏ p ∈ r.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have h := Nat.totient_eq_mul_prod_factors r
    have h' := congrArg (fun x : ℚ => (x : ℝ)) h
    simpa using h'
  simp_rw [one_div] at hsplit hfac ⊢
  have hQ'' : ∏ x ∈ r.primeFactors, (1 - (x : ℝ)⁻¹) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp =>
      hfac p ((Finset.mem_filter.mp (hpf ▸ hp)).1)
  have hQ' : ∏ x ∈ (Nat.primesBelow w).filter (fun p => ¬ p ∣ r), (1 - (x : ℝ)⁻¹) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp => hfac p (Finset.mem_filter.mp hp).1
  rw [totient_primorialBelow_eq w, ← hsplit, hφr]
  generalize ∏ x ∈ r.primeFactors, (1 - (x : ℝ)⁻¹) = q1 at *
  generalize ∏ x ∈ (Nat.primesBelow w).filter (fun p => ¬ p ∣ r), (1 - (x : ℝ)⁻¹) = q2 at *
  field_simp

/-- **Brun's pure sieve on a progression** `apSet r a lo hi`.  For `2 ≤ w`, `1 ≤ r < w`,
`gcd(a, r) = 1`, `lo ≤ hi` and every `k`:
`|∑_{n ∈ apSet r a lo hi} Λ_{C,w}(n) - (hi - lo)/φ(r)|
  ≤ (P/φ(P)) (2 e^S S^{k+1}/(k+1)! · (hi - lo)/r + 2 (k+1) w^{k+1})`, `S = ∑_{p < w} 1/p`.
With `r = 1`, `a = 0`, `lo = 0` this is the density `𝔼_{n ≤ hi} Λ_{C,w}(n) = 1 + O(·)`. -/
theorem brun_ap (w k r : ℕ) (hw : 2 ≤ w) (hrw : r < w) (hr : 1 ≤ r) {a : ℤ}
    (ha : IsCoprime a (r : ℤ)) {lo hi : ℕ} (h : lo ≤ hi) :
    |∑ n ∈ apSet r a lo hi, cramerModel w n - ((hi : ℝ) - lo) / (Nat.totient r : ℝ)| ≤
      ((primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ)) *
        (2 * Real.exp (∑ p ∈ Nat.primesBelow w, (1 : ℝ) / p) *
            (∑ p ∈ Nat.primesBelow w, (1 : ℝ) / p) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) *
            (((hi : ℝ) - lo) / r) + 2 * (k + 1) * (w : ℝ) ^ (k + 1)) := by
  have hw1 : 1 ≤ w := by omega
  have hW : 0 ≤ (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) := by positivity
  have hL : 0 ≤ ((hi : ℝ) - lo) / r := by
    have : (lo : ℝ) ≤ hi := by exact_mod_cast h
    positivity
  have e1 := brun_err1 w k hr ha h
  have e2 := brun_trunc_main w k hw1 hr ha h
  have hmain : (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) *
      (((hi : ℝ) - lo) / r) *
      ∏ p ∈ (Nat.primesBelow w).filter (fun p => ¬ p ∣ r), (1 - 1 / (p : ℝ)) =
      ((hi : ℝ) - lo) / (Nat.totient r : ℝ) := by
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
    have h1 := primorialBelow_div_totient_mul_prod hr hrw
    calc _ = ((hi : ℝ) - lo) / r * ((primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) *
          ∏ p ∈ (Nat.primesBelow w).filter (fun p => ¬ p ∣ r), (1 - 1 / (p : ℝ))) := by ring
      _ = ((hi : ℝ) - lo) / r * ((r : ℝ) / (Nat.totient r : ℝ)) := by rw [h1]
      _ = _ := by field_simp
  have hdec : ∑ n ∈ apSet r a lo hi, cramerModel w n - ((hi : ℝ) - lo) / (Nat.totient r : ℝ) =
      ∑ n ∈ apSet r a lo hi, (cramerModel w n - brunTrunc w k n) +
        (∑ n ∈ apSet r a lo hi, brunTrunc w k n -
          (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) *
            (((hi : ℝ) - lo) / r) *
            ∏ p ∈ (Nat.primesBelow w).filter (fun p => ¬ p ∣ r), (1 - 1 / (p : ℝ))) := by
    rw [hmain, Finset.sum_sub_distrib]
    ring
  have e1' : |∑ n ∈ apSet r a lo hi, (cramerModel w n - brunTrunc w k n)| ≤ _ :=
    le_trans (Finset.abs_sum_le_sum_abs _ _) e1
  rw [hdec]
  refine le_trans (abs_add_le _ _) (le_trans (add_le_add e1' e2) ?_)
  set S := ∑ p ∈ Nat.primesBelow w, (1 : ℝ) / p with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun p _ => by positivity
  have hE : 1 ≤ Real.exp S := Real.one_le_exp hS0
  have hfac : (0 : ℝ) < ((k + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hq : 0 ≤ S ^ (k + 1) / ((k + 1).factorial : ℝ) := by positivity
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw1
  have hwk : (w : ℝ) ^ k ≤ (w : ℝ) ^ (k + 1) := pow_le_pow_right₀ hw' (Nat.le_succ k)
  have hwk0 : (0 : ℝ) ≤ (w : ℝ) ^ (k + 1) := by positivity
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg k)
  have hfac1 : (1 : ℝ) ≤ ((k + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hwf : (w : ℝ) ^ (k + 1) / ((k + 1).factorial : ℝ) ≤ (w : ℝ) ^ (k + 1) :=
    div_le_self hwk0 hfac1
  have heq : 2 * Real.exp S * S ^ (k + 1) / ((k + 1).factorial : ℝ) =
      2 * (Real.exp S * (S ^ (k + 1) / ((k + 1).factorial : ℝ))) := by ring
  rw [heq, ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ hW
  have hA : ((hi : ℝ) - lo) / r * (S ^ (k + 1) / ((k + 1).factorial : ℝ)) ≤
      ((hi : ℝ) - lo) / r * (Real.exp S * (S ^ (k + 1) / ((k + 1).factorial : ℝ))) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hq hE) hL
  have hB : (k + 1 : ℝ) * (w : ℝ) ^ k ≤ (k + 1 : ℝ) * (w : ℝ) ^ (k + 1) :=
    mul_le_mul_of_nonneg_left hwk (by positivity)
  have hC : (w : ℝ) ^ (k + 1) ≤ (k + 1 : ℝ) * (w : ℝ) ^ (k + 1) := le_mul_of_one_le_left hwk0 hk1
  linarith only [hA, hB, hC, hwf]

end PrimeCarleson.Proof.Fplus31
