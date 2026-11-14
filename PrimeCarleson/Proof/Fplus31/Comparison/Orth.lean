module

public import PrimeCarleson.Proof.Fplus31.Comparison.Basic
public import PrimeCarleson.Proof.FplusProp21.ExpSum

/-!
# Cramér–Heath-Brown comparison, step 3: orthogonality of Ramanujan sums on `[1, N]`

The `L²` input of piece `D₂` of the comparison of the Cramér model with the Heath-Brown model: the
Ramanujan sums `c_q`, `q ≤ R`, are orthogonal on `[1, N]` up to an error `O(R⁴)`.

With `A_q = {1 ≤ a ≤ q : (a, q) = 1}` (`coprimeRes`), `c_q(n) c_{q'}(n) = ∑_{(a,a') ∈ A_q × A_{q'}}
e(n (a/q + a'/q'))`; a pair is *diagonal* if `a/q + a'/q' ∈ ℤ`, which forces `q = q'` and `a'`
determined by `a`; every other pair has a geometric sum bounded by `q q'`
(`FplusProp21.norm_sum_e_le_of_intConvex`).

* `abs_ramProd_le_of_ne`: `|∑_{n ≤ N} c_q(n) c_{q'}(n)| ≤ φ(q) φ(q') q q'` for `q ≠ q'`;
* `ramProd_self_le`: `∑_{n ≤ N} c_q(n)² ≤ N φ(q) + φ(q)² q²`;
* `sum_sq_mobTot_ramR_le`: for a finite set `Q` of positive integers,
  `∑_{n ≤ N} (∑_{q ∈ Q} μ(q)/φ(q) c_q(n))² ≤ N ∑_{q ∈ Q} μ(q)²/φ(q) + (∑_{q ∈ Q} q)²`.
-/

@[expose] public noncomputable section

open Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open PrimeCarleson

open PrimeCarleson.Proof.FplusProp21 (IsInt intConvex_Icc norm_sum_e_le_of_intConvex)

/-- The reduced residues `a ∈ [1, q]`, `(a, q) = 1`. -/
def coprimeRes (q : ℕ) : Finset ℕ := (Icc 1 q).filter (fun a => Nat.Coprime a q)

/-- `#A_q = φ(q)`. -/
theorem card_coprimeRes (q : ℕ) : (coprimeRes q).card = Nat.totient q := by
  rw [← Nat.filter_coprime_Ico_eq_totient q 1]
  congr 1
  ext a
  simp only [coprimeRes, mem_filter, mem_Icc, mem_Ico, Nat.coprime_comm]
  omega

/-- `c_q(n) = ∑_{a ∈ A_q} e(n a/q)`. -/
theorem ramanujanSum_eq_sum_coprimeRes (q : ℕ) (n : ℤ) :
    ramanujanSum q n = ∑ a ∈ coprimeRes q, e ((n : ℝ) * ((a : ℝ) / q)) := by
  unfold ramanujanSum coprimeRes
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  ring

/-- The frequency `a/q + a'/q'` of the pair `p = (a, a')`. -/
def freq (q q' : ℕ) (p : ℕ × ℕ) : ℝ := (p.1 : ℝ) / q + (p.2 : ℝ) / q'

/-- `c_q(n) c_{q'}(n) = ∑_{(a, a') ∈ A_q × A_{q'}} e(n (a/q + a'/q'))`. -/
theorem ramanujanSum_mul_eq (q q' : ℕ) (n : ℤ) :
    ramanujanSum q n * ramanujanSum q' n =
      ∑ p ∈ coprimeRes q ×ˢ coprimeRes q', e ((n : ℝ) * freq q q' p) := by
  rw [ramanujanSum_eq_sum_coprimeRes, ramanujanSum_eq_sum_coprimeRes, Finset.sum_mul_sum,
    ← Finset.sum_product']
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Goal0.e_add]
  congr 1
  unfold freq
  ring

/-- A pair with integral frequency contributes `N` to the sum over `[1, N]`. -/
theorem sum_e_freq_of_isInt {N : ℕ} {θ : ℝ} (h : IsInt θ) :
    ∑ n ∈ Icc (1 : ℤ) N, e ((n : ℝ) * θ) = (N : ℂ) := by
  obtain ⟨k, hk⟩ := h
  have : ∀ n ∈ Icc (1 : ℤ) N, e ((n : ℝ) * θ) = 1 := by
    intro n _
    rw [hk, ← Int.cast_mul, Goal0.e_intCast]
  rw [Finset.sum_congr rfl this, Finset.sum_const, Int.card_Icc]
  simp

/-- A pair with non integral frequency contributes at most `q q'`. -/
theorem norm_sum_e_freq_le {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q') {p : ℕ × ℕ}
    (N : ℕ) (h : ¬ IsInt (freq q q' p)) :
    ‖∑ n ∈ Icc (1 : ℤ) N, e ((n : ℝ) * freq q q' p)‖ ≤ (q : ℝ) * q' := by
  have hD : 0 < q * q' := Nat.mul_pos hq hq'
  have hDθ : IsInt (((q * q' : ℕ) : ℝ) * freq q q' p) := by
    refine ⟨(p.1 : ℤ) * q' + p.2 * q, ?_⟩
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have hq0' : (q' : ℝ) ≠ 0 := by exact_mod_cast hq'.ne'
    unfold freq
    push_cast
    field_simp
  have := norm_sum_e_le_of_intConvex (intConvex_Icc 1 N) hD hDθ h
  simpa using this

/-- Off the diagonal `q ≠ q'` no pair of reduced residues has an integral frequency. -/
theorem not_isInt_freq_of_ne {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q') (hne : q ≠ q') {p : ℕ × ℕ}
    (hp : p ∈ coprimeRes q ×ˢ coprimeRes q') : ¬ IsInt (freq q q' p) := by
  rintro ⟨k, hk⟩
  rw [mem_product, coprimeRes, coprimeRes, mem_filter, mem_filter] at hp
  obtain ⟨⟨_, hpq⟩, ⟨_, hpq'⟩⟩ := hp
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hq0' : (q' : ℝ) ≠ 0 := by exact_mod_cast hq'.ne'
  have hR : (p.1 : ℝ) * q' + p.2 * q = k * q * q' := by
    unfold freq at hk
    field_simp at hk
    linarith
  have hZ : (p.1 : ℤ) * q' + p.2 * q = k * q * q' := by exact_mod_cast hR
  have h1 : (q : ℤ) ∣ (p.1 : ℤ) * q' := ⟨k * q' - p.2, by linarith⟩
  have h2 : (q' : ℤ) ∣ (p.2 : ℤ) * q := ⟨k * q - p.1, by linarith⟩
  have h1' : q ∣ p.1 * q' := by exact_mod_cast h1
  have h2' : q' ∣ p.2 * q := by exact_mod_cast h2
  have h3 : q ∣ q' := Nat.Coprime.dvd_of_dvd_mul_left hpq.symm h1'
  have h4 : q' ∣ q := Nat.Coprime.dvd_of_dvd_mul_left hpq'.symm h2'
  exact hne (Nat.dvd_antisymm h3 h4)

/-- `a ∈ A_q` has `1 ≤ a ≤ q`. -/
theorem mem_coprimeRes_bounds {q a : ℕ} (h : a ∈ coprimeRes q) : 1 ≤ a ∧ a ≤ q := by
  rw [coprimeRes, mem_filter, mem_Icc] at h
  exact h.1

open scoped Classical in
/-- On the diagonal `q = q'`, the number of pairs with integral frequency is at most `φ(q)`:
the second residue is determined by the first. -/
theorem card_filter_isInt_diag_le {q : ℕ} (hq : 0 < q) :
    ((coprimeRes q ×ˢ coprimeRes q).filter (fun p => IsInt (freq q q p))).card ≤
      Nat.totient q := by
  rw [← card_coprimeRes]
  refine Finset.card_le_card_of_injOn Prod.fst (fun p hp => ?_) (fun p hp p' hp' hfst => ?_)
  · rw [mem_coe, mem_filter, mem_product] at hp
    exact hp.1.1
  · rw [mem_coe, mem_filter, mem_product] at hp hp'
    obtain ⟨⟨_, hp2⟩, ⟨k, hk⟩⟩ := hp
    obtain ⟨⟨_, hp2'⟩, ⟨k', hk'⟩⟩ := hp'
    ext
    · exact hfst
    · have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
      unfold freq at hk hk'
      rw [hfst] at hk
      have hR : (p.2 : ℝ) - p'.2 = (k - k') * q := by
        field_simp at hk hk'
        linarith
      have hZ : (p.2 : ℤ) - p'.2 = (k - k') * q := by exact_mod_cast hR
      have hdvd : (q : ℤ) ∣ (p.2 : ℤ) - p'.2 := ⟨k - k', by linarith⟩
      have hb := mem_coprimeRes_bounds hp2
      have hb' := mem_coprimeRes_bounds hp2'
      have habs : |(p.2 : ℤ) - p'.2| < q := abs_lt.2 ⟨by omega, by omega⟩
      have := Int.eq_zero_of_abs_lt_dvd hdvd habs
      omega


open scoped Classical in
/-- **Orthogonality of Ramanujan sums on `[1, N]`, with an error of size `φ(q)φ(q') q q'`**:
`∑_{n ≤ N} c_q(n) c_{q'}(n) = N · #{diagonal frequencies} + E`. -/
theorem exists_sum_ramanujanSum_mul (q q' N : ℕ) (hq : 0 < q) (hq' : 0 < q') :
    ∃ E : ℂ, ‖E‖ ≤ (Nat.totient q : ℝ) * Nat.totient q' * q * q' ∧
      ∑ n ∈ Icc (1 : ℤ) N, ramanujanSum q n * ramanujanSum q' n =
        (N : ℂ) * ((((coprimeRes q ×ˢ coprimeRes q').filter
          (fun p => IsInt (freq q q' p))).card : ℕ) : ℂ) + E := by
  set A := coprimeRes q ×ˢ coprimeRes q' with hA
  have h1 : ∑ n ∈ Icc (1 : ℤ) N, ramanujanSum q n * ramanujanSum q' n =
      ∑ p ∈ A, ∑ n ∈ Icc (1 : ℤ) N, e ((n : ℝ) * freq q q' p) := by
    simp_rw [ramanujanSum_mul_eq]
    exact Finset.sum_comm
  refine ⟨∑ p ∈ A.filter (fun p => ¬ IsInt (freq q q' p)),
    ∑ n ∈ Icc (1 : ℤ) N, e ((n : ℝ) * freq q q' p), ?_, ?_⟩
  · refine (norm_sum_le _ _).trans ?_
    calc ∑ p ∈ A.filter (fun p => ¬ IsInt (freq q q' p)),
          ‖∑ n ∈ Icc (1 : ℤ) N, e ((n : ℝ) * freq q q' p)‖
        ≤ ∑ p ∈ A.filter (fun p => ¬ IsInt (freq q q' p)), (q : ℝ) * q' :=
          Finset.sum_le_sum fun p hp => norm_sum_e_freq_le hq hq' N (mem_filter.1 hp).2
      _ = (A.filter (fun p => ¬ IsInt (freq q q' p))).card * ((q : ℝ) * q') := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ A.card * ((q : ℝ) * q') := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast Finset.card_filter_le _ _
      _ = (Nat.totient q : ℝ) * Nat.totient q' * q * q' := by
          rw [hA, Finset.card_product, card_coprimeRes, card_coprimeRes]
          push_cast
          ring
  · rw [h1, ← Finset.sum_filter_add_sum_filter_not A (fun p => IsInt (freq q q' p))]
    congr 1
    rw [Finset.sum_congr rfl (fun p hp => sum_e_freq_of_isInt (mem_filter.1 hp).2),
      Finset.sum_const, nsmul_eq_mul]
    ring

/-- The real orthogonality sum `∑_{n ≤ N} c_q(n) c_{q'}(n)`. -/
def ramProd (q q' N : ℕ) : ℝ := ∑ n ∈ Icc (1 : ℤ) N, ramR q n * ramR q' n

/-- The real sum `ramProd` is the real part of the complex product sum. -/
theorem ramProd_cast (q q' N : ℕ) :
    ((ramProd q q' N : ℝ) : ℂ) =
      ∑ n ∈ Icc (1 : ℤ) N, ramanujanSum q n * ramanujanSum q' n := by
  unfold ramProd
  push_cast
  simp_rw [ramanujanSum_eq_ofReal]

/-- Off the diagonal: `|∑_{n ≤ N} c_q(n) c_{q'}(n)| ≤ φ(q) φ(q') q q'` for `q ≠ q'`. -/
theorem abs_ramProd_le_of_ne {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q') (hne : q ≠ q') (N : ℕ) :
    |ramProd q q' N| ≤ (Nat.totient q : ℝ) * Nat.totient q' * q * q' := by
  classical
  obtain ⟨E, hE, hX⟩ := exists_sum_ramanujanSum_mul q q' N hq hq'
  rw [← ramProd_cast] at hX
  have hΔ : ((coprimeRes q ×ˢ coprimeRes q').filter (fun p => IsInt (freq q q' p))) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro p hp
    exact not_isInt_freq_of_ne hq hq' hne hp
  have hre := congrArg Complex.re hX
  rw [hΔ] at hre
  have hre' : ramProd q q' N = E.re := by simpa using hre
  rw [hre']
  exact (Complex.abs_re_le_norm E).trans hE

/-- On the diagonal: `∑_{n ≤ N} c_q(n)² ≤ N φ(q) + φ(q)² q²`. -/
theorem ramProd_self_le {q : ℕ} (hq : 0 < q) (N : ℕ) :
    ramProd q q N ≤ N * (Nat.totient q : ℝ) + (Nat.totient q : ℝ) * Nat.totient q * q * q := by
  classical
  obtain ⟨E, hE, hX⟩ := exists_sum_ramanujanSum_mul q q N hq hq
  rw [← ramProd_cast] at hX
  have hre := congrArg Complex.re hX
  simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, zero_mul, sub_zero] at hre
  have hcard : (((coprimeRes q ×ˢ coprimeRes q).filter
      (fun p => IsInt (freq q q p))).card : ℝ) ≤ Nat.totient q := by
    exact_mod_cast card_filter_isInt_diag_le hq
  rw [hre]
  have h2 : E.re ≤ ‖E‖ := (Complex.re_le_norm E)
  have h3 : (N : ℝ) * ((coprimeRes q ×ˢ coprimeRes q).filter
      (fun p => IsInt (freq q q p))).card ≤ N * (Nat.totient q : ℝ) :=
    mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg N)
  linarith


/-- `|μ(q)/φ(q)| φ(q) ≤ 1`. -/
theorem abs_mobTot_mul_totient (q : ℕ) (hq : 0 < q) :
    |mobTot q| * (Nat.totient q : ℝ) ≤ 1 := by
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 hq
  rw [mobTot, abs_div, abs_of_pos hφ, div_mul_cancel₀ _ hφ.ne']
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- **The `L²` norm of a short combination of Ramanujan sums** (a one-sided Parseval on `[1, N]`):
`∑_{n ≤ N} (∑_{q ∈ Q} μ(q)/φ(q) c_q(n))² ≤ N ∑_{q ∈ Q} μ(q)²/φ(q) + (∑_{q ∈ Q} q)²`. -/
theorem sum_sq_mobTot_ramR_le (Q : Finset ℕ) (hQ : ∀ q ∈ Q, 0 < q) (N : ℕ) :
    ∑ n ∈ Icc (1 : ℤ) N, (∑ q ∈ Q, mobTot q * ramR q n) ^ 2 ≤
      N * ∑ q ∈ Q, ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) +
        (∑ q ∈ Q, (q : ℝ)) ^ 2 := by
  classical
  have hexp : ∑ n ∈ Icc (1 : ℤ) N, (∑ q ∈ Q, mobTot q * ramR q n) ^ 2 =
      ∑ q ∈ Q, ∑ q' ∈ Q, mobTot q * mobTot q' * ramProd q q' N := by
    simp_rw [sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q' _ => ?_
    unfold ramProd
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  have hterm : ∀ q ∈ Q, ∀ q' ∈ Q, mobTot q * mobTot q' * ramProd q q' N ≤
      (if q = q' then mobTot q ^ 2 * N * (Nat.totient q : ℝ) else 0) + (q : ℝ) * q' := by
    intro q hqQ q' hq'Q
    have hq := hQ q hqQ
    have hq' := hQ q' hq'Q
    have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 hq
    have hφ' : (0 : ℝ) < Nat.totient q' := by exact_mod_cast Nat.totient_pos.2 hq'
    have h1 := abs_mobTot_mul_totient q hq
    have h1' := abs_mobTot_mul_totient q' hq'
    by_cases hqq : q = q'
    · subst hqq
      rw [ite_eq_left rfl]
      have := ramProd_self_le hq N
      have h0 : 0 ≤ mobTot q * mobTot q := mul_self_nonneg _
      calc mobTot q * mobTot q * ramProd q q N
          ≤ mobTot q * mobTot q * (N * (Nat.totient q : ℝ) +
              (Nat.totient q : ℝ) * Nat.totient q * q * q) :=
            mul_le_mul_of_nonneg_left this h0
        _ = mobTot q ^ 2 * N * (Nat.totient q : ℝ) +
              (|mobTot q| * (Nat.totient q : ℝ)) ^ 2 * ((q : ℝ) * q) := by
            rw [mul_pow, sq_abs]; ring
        _ ≤ mobTot q ^ 2 * N * (Nat.totient q : ℝ) + 1 * ((q : ℝ) * q) := by
            have h2 : (|mobTot q| * (Nat.totient q : ℝ)) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) h1
            exact add_le_add_right (mul_le_mul_of_nonneg_right h2 (by positivity)) _
        _ = _ := by ring
    · rw [ite_eq_right hqq, zero_add]
      have h2 := abs_ramProd_le_of_ne hq hq' hqq N
      calc mobTot q * mobTot q' * ramProd q q' N
          ≤ |mobTot q * mobTot q' * ramProd q q' N| := le_abs_self _
        _ = |mobTot q| * |mobTot q'| * |ramProd q q' N| := by rw [abs_mul, abs_mul]
        _ ≤ |mobTot q| * |mobTot q'| * ((Nat.totient q : ℝ) * Nat.totient q' * q * q') :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (|mobTot q| * (Nat.totient q : ℝ)) * (|mobTot q'| * (Nat.totient q' : ℝ)) *
              ((q : ℝ) * q') := by ring
        _ ≤ 1 * 1 * ((q : ℝ) * q') :=
            mul_le_mul_of_nonneg_right (mul_le_mul h1 h1' (by positivity) zero_le_one)
              (by positivity)
        _ = (q : ℝ) * q' := by ring
  rw [hexp]
  refine (Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun q' hq' => hterm q hq q' hq').trans ?_
  simp_rw [Finset.sum_add_distrib]
  have hdiag : ∑ q ∈ Q, ∑ q' ∈ Q, (if q = q' then mobTot q ^ 2 * N * (Nat.totient q : ℝ) else 0) =
      N * ∑ q ∈ Q, ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [Finset.sum_ite_eq Q q, ite_eq_left hq]
    have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 (hQ q hq)
    rw [mobTot]
    field_simp
  rw [hdiag, sq, Finset.sum_mul_sum]

end PrimeCarleson.Proof.Fplus31
