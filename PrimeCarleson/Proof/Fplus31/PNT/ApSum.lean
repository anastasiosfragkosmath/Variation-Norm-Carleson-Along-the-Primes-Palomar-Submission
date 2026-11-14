module

public import PrimeCarleson.Proof.Fplus31.Cramer.Model
public import PrimeCarleson.Proof.Fplus31.Brun.Main
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Data.Nat.Log

/-!
# Von Mangoldt sums over progressions: the number-theoretic part of the assembly

Part of the assembly of the prime number theorem in progressions (`PNTSW/Assembly.lean`).

* `psiAP r a x`: `ψ(x; r, a)` for a natural number `x`;
* `sum_apSet_vonMangoldt`: `∑_{n ∈ (lo, hi], n ≡ a (r)} Λ(n) = ψ(hi; r, a) - ψ(lo; r, a)`;
* `vonMangoldt_apSet_le`, `cramerModel_apSet_le`: the trivial bounds for `r` large;
* `vonMangoldt_apSet_noncoprime_le`: if `gcd(a, r) > 1` then `∑ Λ ≤ log N` (only the powers of one
  prime `p ∣ gcd(a, r)` occur, and `∑_{d ∣ p^K} Λ(d) = K log p`).
-/

@[expose] public noncomputable section

open ArithmeticFunction

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- `ψ(x; r, a) = ∑_{1 ≤ n ≤ x, n ≡ a (r)} Λ(n)` for a natural number `x`. -/
def psiAP (r : ℕ) (a : ℤ) (x : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 x).filter (fun n : ℕ => (n : ℤ) ≡ a [ZMOD r]), Λ n

/-- The sum over the progression `(lo, hi]` is a difference of `ψ`'s. -/
theorem sum_apSet_vonMangoldt (r : ℕ) (a : ℤ) {lo hi : ℕ} (h : lo ≤ hi) :
    ∑ n ∈ apSet r a lo hi, Λ n.toNat = psiAP r a hi - psiAP r a lo := by
  have e1 : ∑ n ∈ apSet r a lo hi, Λ n.toNat =
      ∑ m ∈ (Finset.Ioc lo hi).filter (fun m : ℕ => (m : ℤ) ≡ a [ZMOD r]), Λ m := by
    refine Finset.sum_nbij' (fun n => n.toNat) (fun m => (m : ℤ)) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
    · intro n hn
      obtain ⟨h1, h2, h3⟩ := mem_apSet.mp hn
      have e : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg (by omega)
      rw [Finset.mem_filter, Finset.mem_Ioc, e]
      exact ⟨⟨by omega, by omega⟩, h3⟩
    · intro m hm
      rw [Finset.mem_filter, Finset.mem_Ioc] at hm
      rw [mem_apSet]
      exact ⟨by exact_mod_cast hm.1.1, by exact_mod_cast hm.1.2, hm.2⟩
    · intro n hn
      obtain ⟨h1, _, _⟩ := mem_apSet.mp hn
      exact Int.toNat_of_nonneg (by omega)
    · intro m _
      exact Int.toNat_natCast m
  rw [e1]
  have hI : ∀ x : ℕ, Finset.Icc 1 x = Finset.Ioc 0 x := fun x => by ext k; simp; omega
  unfold psiAP
  simp only [hI, Finset.sum_filter]
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le lo) h]
  ring

/-- The trivial bound `∑_{n ∈ P} Λ(n) ≤ (N/r + 1) log N` for a progression `P ⊆ [1, N]`. -/
theorem vonMangoldt_apSet_le {r : ℕ} (hr : 1 ≤ r) (a : ℤ) {lo hi N : ℕ} (h : lo ≤ hi)
    (hN : hi ≤ N) :
    ∑ n ∈ apSet r a lo hi, Λ n.toNat ≤ ((N : ℝ) / r + 1) * Real.log N := by
  have hterm : ∀ n ∈ apSet r a lo hi, Λ n.toNat ≤ Real.log N := by
    intro n hn
    obtain ⟨h1, h2, _⟩ := mem_apSet.mp hn
    have hn1 : 1 ≤ n.toNat := by omega
    have hnN : n.toNat ≤ N := by omega
    refine vonMangoldt_le_log.trans (Real.log_le_log ?_ ?_)
    · exact_mod_cast hn1
    · exact_mod_cast hnN
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [nsmul_eq_mul]
  have hc := card_apSet_le hr a h
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hD : ((hi : ℝ) - lo) / r ≤ (N : ℝ) / r := by
    refine div_le_div_of_nonneg_right ?_ hr0.le
    have : (hi : ℝ) ≤ N := by exact_mod_cast hN
    have : (0 : ℝ) ≤ lo := by positivity
    linarith
  exact mul_le_mul_of_nonneg_right (hc.trans (by linarith)) hlogN

/-- The trivial bound `∑_{n ∈ P} Λ_{C,w}(n) ≤ (N/r + 1) e⁵ log w`. -/
theorem cramerModel_apSet_le {r w : ℕ} (hr : 1 ≤ r) (hw : 2 ≤ w) (a : ℤ) {lo hi N : ℕ}
    (h : lo ≤ hi) (hN : hi ≤ N) :
    ∑ n ∈ apSet r a lo hi, cramerModel w n ≤
      ((N : ℝ) / r + 1) * (Real.exp 5 * Real.log w) := by
  refine (Finset.sum_le_card_nsmul _ _ _ fun n _ => cramerModel_le w hw n).trans ?_
  rw [nsmul_eq_mul]
  have hc := card_apSet_le hr a h
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hD : ((hi : ℝ) - lo) / r ≤ (N : ℝ) / r := by
    refine div_le_div_of_nonneg_right ?_ hr0.le
    have : (hi : ℝ) ≤ N := by exact_mod_cast hN
    have : (0 : ℝ) ≤ lo := by positivity
    linarith
  have hlogw : 0 ≤ Real.log w := Real.log_natCast_nonneg w
  exact mul_le_mul_of_nonneg_right (hc.trans (by linarith)) (by positivity)

/-- If `gcd(a, r) > 1` then only the powers of a single prime `p ∣ gcd(a, r)` contribute:
`∑_{n ∈ (lo, hi], n ≡ a (r)} Λ(n) ≤ log N` for `1 ≤ N`, `hi ≤ N`. -/
theorem vonMangoldt_apSet_noncoprime_le {r : ℕ} {a : ℤ}
    (hna : ¬ IsCoprime a (r : ℤ)) {lo hi N : ℕ} (hN : hi ≤ N) (hN1 : 1 ≤ N) :
    ∑ n ∈ apSet r a lo hi, Λ n.toNat ≤ Real.log N := by
  rw [Int.isCoprime_iff_gcd_eq_one] at hna
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hna
  have hpa : (p : ℤ) ∣ a := by
    have := Int.gcd_dvd_left (a := a) (b := (r : ℤ))
    exact_mod_cast (Int.natCast_dvd_natCast.mpr hpd).trans this
  have hpr : (p : ℤ) ∣ (r : ℤ) := by
    have := Int.gcd_dvd_right (a := a) (b := (r : ℤ))
    exact (Int.natCast_dvd_natCast.mpr hpd).trans this
  have hpn : ∀ n ∈ apSet r a lo hi, (p : ℤ) ∣ n := fun n hn =>
    ((mem_apSet.mp hn).2.2.of_dvd hpr).dvd_iff.mpr hpa
  set K : ℕ := Nat.log p N with hK
  have hKN : p ^ K ≤ N := Nat.pow_log_le_self p (by omega)
  have hsub : ((apSet r a lo hi).image Int.toNat).filter (fun m => Λ m ≠ 0) ⊆
      (p ^ K).divisors := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_image] at hm
    obtain ⟨⟨n, hn, rfl⟩, hΛ⟩ := hm
    obtain ⟨h1, h2, _⟩ := mem_apSet.mp hn
    have hpdvd : p ∣ n.toNat := by
      have := hpn n hn
      have e : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg (by omega)
      rw [← e] at this
      exact Int.natCast_dvd_natCast.mp this
    obtain ⟨q, k, hq, hk, hqk⟩ := (vonMangoldt_ne_zero_iff.mp hΛ)
    have hq' : q.Prime := Nat.prime_iff.mpr hq
    have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq').mp
      (hp.dvd_of_dvd_pow (hqk ▸ hpdvd))
    subst hpq
    have hle : p ^ k ≤ N := by
      rw [hqk]
      omega
    have hkK : k ≤ K := Nat.le_log_of_pow_le hp.one_lt hle
    rw [Nat.mem_divisors]
    refine ⟨?_, (pow_pos hp.pos K).ne'⟩
    rw [← hqk]
    exact pow_dvd_pow p hkK
  calc ∑ n ∈ apSet r a lo hi, Λ n.toNat
      = ∑ m ∈ (apSet r a lo hi).image Int.toNat, Λ m := by
        rw [Finset.sum_image]
        intro x hx y hy hxy
        have hx' := (mem_apSet.mp hx).1
        have hy' := (mem_apSet.mp hy).1
        omega
    _ = ∑ m ∈ ((apSet r a lo hi).image Int.toNat).filter (fun m => Λ m ≠ 0), Λ m :=
        (Finset.sum_filter_ne_zero _).symm
    _ ≤ ∑ m ∈ (p ^ K).divisors, Λ m :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => vonMangoldt_nonneg
    _ = Real.log ((p ^ K : ℕ) : ℝ) := vonMangoldt_sum
    _ ≤ Real.log N := Real.log_le_log (by exact_mod_cast pow_pos hp.pos K)
        (by exact_mod_cast hKN)

end PrimeCarleson.Proof.Fplus31
