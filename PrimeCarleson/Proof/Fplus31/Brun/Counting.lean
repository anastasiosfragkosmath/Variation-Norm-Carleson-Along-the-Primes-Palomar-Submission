module

public import PrimeCarleson.Proof.Fplus31.Cramer.Model

/-!
# Brun's pure sieve: counting a progression modulo `d`

Chinese remainder counting for the pure sieve of Brun: for the progression
`apSet r a lo hi = {lo < n ≤ hi, n ≡ a mod r}` and a squarefree `d = ∏ D`, `D` a finite set of
primes,

* `filter_apSet_dvd_eq`: if `gcd(d, r) = 1` the elements of the progression divisible by `d`
  form one residue class modulo `r d`;
* `abs_card_apSet_dvd_sub_le`: their number is `(hi - lo)/(r d) + θ`, `|θ| ≤ 1`;
* `card_apSet_dvd_eq_zero`: if `gcd(a, r) = 1` and `gcd(d, r) > 1` there are none;
* `abs_card_apSet_prod_dvd_sub_le`: the combined statement for `d = ∏ D`:
  `#{n ∈ apSet r a lo hi : ∏ D ∣ n} = 1_{∀ p ∈ D, p ∤ r} · ((hi - lo)/r) ∏_{p ∈ D} (1/p) + θ`,
  `|θ| ≤ 1`.
-/

@[expose] public noncomputable section

open Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- If `gcd(d, r) = 1` the elements of `apSet r a lo hi` divisible by `d` form a residue class
modulo `r d`. -/
theorem filter_apSet_dvd_eq {r d : ℕ} (hcop : Nat.Coprime d r) (a : ℤ) (lo hi : ℕ) :
    ∃ v : ℤ, (apSet r a lo hi).filter (fun n => (d : ℤ) ∣ n) =
      (Finset.Ioc (lo : ℤ) hi).filter (fun n => n ≡ v [ZMOD ((r * d : ℕ) : ℤ)]) := by
  have hcop' : IsCoprime (r : ℤ) (d : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
  obtain ⟨u, t, hut⟩ := hcop'
  refine ⟨a * (t * d), ?_⟩
  have hVr : a * (t * (d : ℤ)) ≡ a [ZMOD (r : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨a * u, ?_⟩
    linear_combination (-a) * hut
  have hVd : (d : ℤ) ∣ a * (t * (d : ℤ)) := ⟨a * t, by ring⟩
  have hcopn : (r : ℤ).natAbs.Coprime (d : ℤ).natAbs := by
    simpa using hcop.symm
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc, mem_apSet]
  constructor
  · rintro ⟨⟨hlo, hhi, hn⟩, hdn⟩
    refine ⟨⟨hlo, hhi⟩, ?_⟩
    have h1 : n ≡ a * (t * (d : ℤ)) [ZMOD (r : ℤ)] := hn.trans hVr.symm
    have h2 : n ≡ a * (t * (d : ℤ)) [ZMOD (d : ℤ)] :=
      (Int.modEq_zero_iff_dvd.mpr hdn).trans (Int.modEq_zero_iff_dvd.mpr hVd).symm
    have := (Int.modEq_and_modEq_iff_modEq_mul hcopn).mp ⟨h1, h2⟩
    simpa using this
  · rintro ⟨⟨hlo, hhi⟩, hn⟩
    have hn' : n ≡ a * (t * (d : ℤ)) [ZMOD ((r : ℤ) * (d : ℤ))] := by simpa using hn
    have h1 : n ≡ a * (t * (d : ℤ)) [ZMOD (r : ℤ)] := hn'.of_mul_right _
    have h2 : n ≡ a * (t * (d : ℤ)) [ZMOD (d : ℤ)] := hn'.of_mul_left _
    exact ⟨⟨hlo, hhi, h1.trans hVr⟩, (h2.dvd_iff).mpr hVd⟩

/-- If `gcd(d, r) = 1`, the progression `a mod r` has `(hi - lo)/(r d) + θ`, `|θ| ≤ 1`, elements
divisible by `d`. -/
theorem abs_card_apSet_dvd_sub_le {r d : ℕ} (hr : 1 ≤ r) (hd : 1 ≤ d) (hcop : Nat.Coprime d r)
    (a : ℤ) {lo hi : ℕ} (h : lo ≤ hi) :
    |(((apSet r a lo hi).filter (fun n => (d : ℤ) ∣ n)).card : ℝ) -
        ((hi : ℝ) - lo) / ((r : ℝ) * d)| ≤ 1 := by
  obtain ⟨v, hv⟩ := filter_apSet_dvd_eq hcop a lo hi
  rw [hv]
  have := abs_card_filter_modEq_sub_le (m := r * d) (Nat.mul_pos hr hd) v h
  simpa using this

/-- If `gcd(a, r) = 1` and `gcd(d, r) > 1`, no element of `a mod r` is divisible by `d`. -/
theorem card_apSet_dvd_eq_zero {r d : ℕ} {a : ℤ} (ha : IsCoprime a (r : ℤ))
    (hd : ¬ Nat.Coprime d r) (lo hi : ℕ) :
    ((apSet r a lo hi).filter (fun n => (d : ℤ) ∣ n)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n hn hdn
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show Nat.gcd d r ≠ 1 from hd)
  have hpd' : p ∣ d := hpd.trans (Nat.gcd_dvd_left _ _)
  have hpr : (p : ℤ) ∣ (r : ℤ) := Int.natCast_dvd_natCast.mpr (hpd.trans (Nat.gcd_dvd_right _ _))
  have hpn : (p : ℤ) ∣ n := (Int.natCast_dvd_natCast.mpr hpd').trans hdn
  have hpa : (p : ℤ) ∣ a := (((mem_apSet.mp hn).2.2.of_dvd hpr).dvd_iff).mp hpn
  have hunit := ha.isUnit_of_dvd' hpa hpr
  rw [Int.isUnit_iff_natAbs_eq] at hunit
  exact hp.one_lt.ne' (by simpa using hunit)

/-- **Counting for a squarefree `d = ∏ D`.** For a set `D` of primes and a progression `a mod r`
with `gcd(a, r) = 1`: `#{n ∈ apSet r a lo hi : ∏ D ∣ n}` equals
`1_{∀ p ∈ D, p ∤ r} · ((hi - lo)/r) ∏_{p ∈ D} (1/p)` up to an error of at most `1`. -/
theorem abs_card_apSet_prod_dvd_sub_le {r : ℕ} (hr : 1 ≤ r) {a : ℤ} (ha : IsCoprime a (r : ℤ))
    {lo hi : ℕ} (h : lo ≤ hi) {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) :
    |(((apSet r a lo hi).filter (fun n => (((∏ p ∈ D, p : ℕ) : ℤ) ∣ n))).card : ℝ) -
        (if ∀ p ∈ D, ¬ p ∣ r then ((hi : ℝ) - lo) / r * ∏ p ∈ D, (1 / (p : ℝ)) else 0)| ≤ 1 := by
  by_cases hDr : ∀ p ∈ D, ¬ p ∣ r
  · have hcop : Nat.Coprime (∏ p ∈ D, p) r :=
      Nat.Coprime.prod_left fun p hp => ((hD p hp).coprime_iff_not_dvd.mpr (hDr p hp))
    have hd : 1 ≤ ∏ p ∈ D, p := Finset.prod_pos fun p hp => (hD p hp).pos
    have := abs_card_apSet_dvd_sub_le hr hd hcop a h
    rw [ite_eq_left hDr]
    convert this using 3
    push_cast
    rw [Finset.prod_div_distrib, Finset.prod_const_one]
    field_simp
  · have hcop : ¬ Nat.Coprime (∏ p ∈ D, p) r := by
      intro hc
      obtain ⟨p, hp, hpr⟩ : ∃ p ∈ D, p ∣ r := by
        by_contra hcon
        exact hDr fun p hp hpr => hcon ⟨p, hp, hpr⟩
      have : Nat.Coprime p r := Nat.Coprime.coprime_dvd_left (Finset.dvd_prod_of_mem _ hp) hc
      exact ((hD p hp).coprime_iff_not_dvd.mp this) hpr
    rw [card_apSet_dvd_eq_zero ha hcop, ite_eq_right hDr]
    simp

end PrimeCarleson.Proof.Fplus31
