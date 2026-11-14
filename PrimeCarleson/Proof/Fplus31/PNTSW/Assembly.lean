module

public import PrimeCarleson.Proof.Fplus31.PNTSW.PntAp
public import PrimeCarleson.Proof.Fplus31.PNT.Parts

/-!
# The assembly on the classical zero-free region: the target from `pnt_ap_sw` and `brun_ap`

Part of the prime number theorem in progressions on the classical zero-free region
(`PNTSW/Main.lean`). The assembly of the four cases of `PNT.Parts` with the prime number theorem in
progressions `PNTapSW` (the statement of `pnt_ap_sw`: error `x exp (-c √(log x))` for
`log q ≤ c √(log x)`). With `L = (log N)^{1/10}` (`log N = L^{10}`), `r < exp (L/2)` and `x ≤ N`,
`x ≥ exp (L²/(4c²))`, we have `log r ≤ L/2 ≤ c √(log x)`, so the progression `x ≡ a (r)` is covered;
the finitely many smaller `x` are bounded trivially. The four cases of the assembly (`trivial_part`,
`noncoprime_part`, `brun_part` of `PNT.Parts`, and `pnt_part_sw` of `PNTSW/Target.lean`) then give
`c5_core_sw` and `c5_target_sw`.
-/

@[expose] public noncomputable section

open ArithmeticFunction Filter
open scoped Real

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31.PNTSW

/-- The statement of `pnt_ap_sw` (PNT in progressions, classical error term), as a `Prop`. -/
def PNTapSW : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ (q : ℕ), 1 ≤ q → ∀ (a : ℤ) (x : ℝ), x₀ ≤ x →
    Real.log q ≤ c * √(Real.log x) →
    |∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ => (n : ℤ) ≡ a [ZMOD q]), (Λ n : ℝ) -
        (if IsCoprime a (q : ℤ) then x / (Nat.totient q : ℝ) else 0)| ≤
      x * Real.exp (-(c * √(Real.log x)))

/-- `ψ(x; r, a) ≥ 0`. -/
theorem psiAP_nonneg (r : ℕ) (a : ℤ) (x : ℕ) : 0 ≤ psiAP r a x :=
  Finset.sum_nonneg fun _ _ => vonMangoldt_nonneg

/-- `ψ(x; r, a) ≤ x m` if `log n ≤ m` for `1 ≤ n ≤ x` (and `m ≥ 0`). -/
theorem psiAP_le_mul {r : ℕ} {a : ℤ} {x : ℕ} {m : ℝ} (hm0 : 0 ≤ m)
    (hm : ∀ n : ℕ, 1 ≤ n → n ≤ x → Real.log n ≤ m) : psiAP r a x ≤ x * m := by
  unfold psiAP
  calc ∑ n ∈ (Finset.Icc 1 x).filter (fun n : ℕ => (n : ℤ) ≡ a [ZMOD r]), Λ n
      ≤ ∑ n ∈ (Finset.Icc 1 x).filter (fun n : ℕ => (n : ℤ) ≡ a [ZMOD r]), m := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn' := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
        exact vonMangoldt_le_log.trans (hm n hn'.1 hn'.2)
    _ = ((Finset.Icc 1 x).filter (fun n : ℕ => (n : ℤ) ≡ a [ZMOD r])).card * m := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ x * m := by
        have hc : (((Finset.Icc 1 x).filter (fun n : ℕ => (n : ℤ) ≡ a [ZMOD r])).card : ℝ) ≤ x := by
          have := (Finset.card_filter_le (Finset.Icc 1 x) (fun n : ℕ => (n : ℤ) ≡ a [ZMOD r]))
          simp only [Nat.card_Icc, add_tsub_cancel_right] at this
          exact_mod_cast this
        exact mul_le_mul_of_nonneg_right hc hm0

/-- The numerical budget of the small-`x` range: `2 M² + L/2 ≤ L^{10}` for `L` large. -/
theorem budget_small {c L M S l : ℝ} (hc : 0 < c) (hL : 4 ≤ L) (hl : 0 ≤ l)
    (hK : 1 / (2 * c ^ 2) + 2 * l + 1 ≤ L) (hM : M ^ 2 ≤ S ^ 2 + l)
    (hS : S ^ 2 = L ^ 2 / (4 * c ^ 2)) : M ^ 2 + M ^ 2 ≤ L ^ 10 + -(L / 2) := by
  set A : ℝ := 1 / (2 * c ^ 2) with hA
  have hA0 : 0 < A := by positivity
  have hS' : S ^ 2 = L ^ 2 * A / 2 := by rw [hS, hA]; field_simp; ring
  have hL1 : 1 ≤ L := by linarith
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL1
  have hLL : L ≤ L ^ 2 := by
    have := mul_le_mul_of_nonneg_left hL1 (by linarith only [hL1] : (0 : ℝ) ≤ L)
    linarith only [this]
  have h1 : M ^ 2 + M ^ 2 ≤ L ^ 2 * A + 2 * l := by linarith
  have h2 : 2 * l ≤ L ^ 2 * (2 * l) := by
    have := mul_le_mul_of_nonneg_right hL2 (by linarith only [hl] : (0 : ℝ) ≤ 2 * l)
    linarith only [this]
  have h3 : L ^ 2 * A + 2 * l + L / 2 ≤ L ^ 2 * (A + 2 * l + 1) := by
    linarith only [h2, hLL, hL1]
  have h4 : L ^ 2 * (A + 2 * l + 1) ≤ L ^ 2 * L :=
    mul_le_mul_of_nonneg_left hK (by positivity)
  have h5 : L ^ 2 * L ≤ L ^ 10 := by
    have : L ^ 3 ≤ L ^ 10 := pow_le_pow_right₀ hL1 (by norm_num)
    linarith only [this]
  linarith

/-- `PNTapSW` for natural `x ≤ N`, all `L` large, moduli with `log r ≤ L/2`. -/
theorem abs_psiAP_sub_le_sw (hP : PNTapSW) :
    ∃ L₁ : ℝ, 4 ≤ L₁ ∧ ∀ L : ℝ, L₁ ≤ L → ∀ N : ℕ, Real.log N = L ^ 10 → ∀ r : ℕ, 1 ≤ r →
      Real.log r ≤ L / 2 → ∀ a : ℤ, IsCoprime a (r : ℤ) → ∀ x : ℕ, x ≤ N →
      |psiAP r a x - (x : ℝ) / (Nat.totient r : ℝ)| ≤ 2 * ((N : ℝ) * Real.exp (-(L / 2))) := by
  obtain ⟨c, hc, x₀, hx₀, hPP⟩ := hP
  have hlx₀ : 0 ≤ Real.log x₀ := Real.log_nonneg (by linarith)
  refine ⟨max 4 (1 / (2 * c ^ 2) + 2 * Real.log x₀ + 1), le_max_left _ _, ?_⟩
  intro L hL N hN r hr hrL a ha x hxN
  have hL4 : 4 ≤ L := le_trans (le_max_left _ _) hL
  have hK₀ : 1 / (2 * c ^ 2) + 2 * Real.log x₀ + 1 ≤ L := le_trans (le_max_right _ _) hL
  have hL0 : 0 < L := by linarith
  have hN1 : 1 ≤ N := by
    by_contra h
    have : N = 0 := by omega
    subst this
    simp at hN
    have : (0 : ℝ) < L ^ 10 := by positivity
    linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNe : (N : ℝ) = Real.exp (L ^ 10) := by rw [← hN, Real.exp_log hNpos]
  have hxN' : (x : ℝ) ≤ N := by exact_mod_cast hxN
  set S : ℝ := L / (2 * c) with hS
  have hS0 : 0 ≤ S := by positivity
  set M : ℝ := max S (√(Real.log x₀)) with hM
  have hM0 : 0 ≤ M := le_trans hS0 (le_max_left _ _)
  have hcS : c * S = L / 2 := by rw [hS]; field_simp
  have hφ1 : (1 : ℝ) ≤ (Nat.totient r : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hr
  have hxφ : (x : ℝ) / (Nat.totient r : ℝ) ≤ x := div_le_self (Nat.cast_nonneg x) hφ1
  have hxφ0 : 0 ≤ (x : ℝ) / (Nat.totient r : ℝ) := by positivity
  by_cases hbig : Real.exp (M ^ 2) ≤ (x : ℝ)
  · -- the PNT range
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hbig
    have hlogx : M ^ 2 ≤ Real.log x := by
      have := Real.log_le_log (Real.exp_pos _) hbig
      rwa [Real.log_exp] at this
    have hMx : M ≤ √(Real.log x) := Real.le_sqrt_of_sq_le hlogx
    have hx₀x : x₀ ≤ x := by
      have h1 : Real.log x₀ ≤ M ^ 2 := by
        have := Real.sq_sqrt hlx₀
        have h2 : √(Real.log x₀) ≤ M := le_max_right _ _
        have h5 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
        linarith only [this, h5]
      exact (Real.log_le_log_iff (by linarith) hxpos).mp (h1.trans hlogx)
    have hlogr : Real.log r ≤ c * √(Real.log x) := by
      calc Real.log r ≤ L / 2 := hrL
        _ = c * S := hcS.symm
        _ ≤ c * M := mul_le_mul_of_nonneg_left (le_max_left _ _) hc.le
        _ ≤ c * √(Real.log x) := mul_le_mul_of_nonneg_left hMx hc.le
    have h1 := hPP r hr a (x : ℝ) hx₀x hlogr
    simp only [Nat.floor_natCast, ha, ↓reduceIte] at h1
    unfold psiAP
    refine h1.trans ?_
    have h2 : Real.exp (-(c * √(Real.log x))) ≤ Real.exp (-(L / 2)) := by
      refine Real.exp_le_exp.mpr ?_
      have : c * S ≤ c * √(Real.log x) :=
        mul_le_mul_of_nonneg_left (le_trans (le_max_left _ _) hMx) hc.le
      linarith
    have h3 : (x : ℝ) * Real.exp (-(c * √(Real.log x))) ≤ N * Real.exp (-(L / 2)) :=
      mul_le_mul hxN' h2 (Real.exp_pos _).le hNpos.le
    have : 0 ≤ (N : ℝ) * Real.exp (-(L / 2)) := by positivity
    linarith
  · -- small `x`: trivial bounds
    push Not at hbig
    set m : ℝ := M ^ 2 with hm
    have hm0 : 0 ≤ m := by positivity
    have hxm : (x : ℝ) < Real.exp m := hbig
    have hlogm : ∀ n : ℕ, 1 ≤ n → n ≤ x → Real.log n ≤ m := by
      intro n hn1 hnx
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have : (n : ℝ) ≤ Real.exp m := le_trans (by exact_mod_cast hnx) hxm.le
      calc Real.log n ≤ Real.log (Real.exp m) := Real.log_le_log hn0 this
        _ = m := Real.log_exp m
    have hψ0 := psiAP_nonneg r a x
    have hψ1 := psiAP_le_mul (r := r) (a := a) hm0 hlogm
    have habs : |psiAP r a x - (x : ℝ) / (Nat.totient r : ℝ)| ≤ x * m + x := by
      rw [abs_le]
      constructor <;> linarith
    refine habs.trans ?_
    have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
    have h1 : (x : ℝ) * m + x ≤ Real.exp m * Real.exp m := by
      have h2 : m + 1 ≤ Real.exp m := Real.add_one_le_exp m
      calc (x : ℝ) * m + x = x * (m + 1) := by ring
        _ ≤ Real.exp m * Real.exp m :=
            mul_le_mul hxm.le h2 (by linarith) (Real.exp_pos _).le
    refine h1.trans ?_
    rw [← Real.exp_add, hNe, ← Real.exp_add]
    have hM2 : M ^ 2 ≤ S ^ 2 + Real.log x₀ := by
      have := Real.sq_sqrt hlx₀
      rcases le_total S (√(Real.log x₀)) with h | h
      · rw [hM, max_eq_right h]; linarith only [this, sq_nonneg S]
      · rw [hM, max_eq_left h]; linarith only [hlx₀]
    have hS2 : S ^ 2 = L ^ 2 / (4 * c ^ 2) := by rw [hS]; field_simp; ring
    have h4 := Real.exp_le_exp.mpr (budget_small hc hL4 hlx₀ hK₀ hM2 hS2)
    have h5 := Real.exp_pos (L ^ 10 + -(L / 2))
    linarith

end PrimeCarleson.Proof.Fplus31.PNTSW
