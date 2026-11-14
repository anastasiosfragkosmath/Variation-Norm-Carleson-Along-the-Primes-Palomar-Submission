module

public import PrimeCarleson.Proof.Fplus31.PNTSW.Assembly

/-!
# The target on the classical zero-free region: `c5_target_sw` and `c5_terminal_sw`

Part of the prime number theorem in progressions on the classical zero-free region
(`PNTSW/Main.lean`). The assembly of the four cases of `PNT.Parts` with `PNTapSW`:

* `pnt_part_sw`: `r < e^{L/2}`, `gcd(a, r) = 1`: `|∑_P Λ - (hi - lo)/φ(r)| ≤ N e^{-L/3} / 3`;
* `c5_core_sw`, `c5_target_sw`: for every progression `P = apSet r a lo hi ⊆ [1, N]` and every
  Cramér level `w ∈ [e^L / 2, e^L + 1]`, `L = (log N)^{1/10}`,
  `|∑_{n ∈ P} (Λ(n) - Λ_{C,w}(n))| ≤ N exp(-L/3)` ;
* `c5_terminal_sw`: the accuracy `N exp(-(log log N)^{K'})` for every real `K'` which is what the
  iteration of `C2/` consumes.

All conditional on `ClassicalZeroFreeRegion` and `NoSiegelZero` only.
-/

@[expose] public noncomputable section

open ArithmeticFunction Filter
open scoped Real

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31.PNTSW

/-- `r < e^{L/2}`, `gcd(a, r) = 1`: the PNT part of the assembly. -/
theorem pnt_part_sw {L : ℝ} (hL36 : 36 ≤ L) {N : ℕ} (hN : Real.log N = L ^ 10)
    (habs : ∀ r : ℕ, 1 ≤ r → Real.log r ≤ L / 2 → ∀ a : ℤ, IsCoprime a (r : ℤ) → ∀ x : ℕ,
      x ≤ N → |psiAP r a x - (x : ℝ) / (Nat.totient r : ℝ)| ≤
        2 * ((N : ℝ) * Real.exp (-(L / 2))))
    {r : ℕ} (hr : 1 ≤ r) (hrL : (r : ℝ) < Real.exp (L / 2)) {a : ℤ} (ha : IsCoprime a (r : ℤ))
    {lo hi : ℕ} (h : lo ≤ hi) (hhi : hi ≤ N) :
    |∑ n ∈ apSet r a lo hi, Λ n.toNat - ((hi : ℝ) - lo) / (Nat.totient r : ℝ)| ≤
      (1 / 3) * (N * Real.exp (-(1 / 3) * L)) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hlogr : Real.log r ≤ L / 2 := by
    have := Real.log_le_log hr0 hrL.le
    rwa [Real.log_exp] at this
  have hN1 := one_le_nat_of_log (L := L) (by linarith) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  rw [sum_apSet_vonMangoldt r a h]
  have e : psiAP r a hi - psiAP r a lo - ((hi : ℝ) - lo) / (Nat.totient r : ℝ) =
      (psiAP r a hi - (hi : ℝ) / (Nat.totient r : ℝ)) -
        (psiAP r a lo - (lo : ℝ) / (Nat.totient r : ℝ)) := by ring
  rw [e]
  have h1 := habs r hr hlogr a ha hi hhi
  have h2 := habs r hr hlogr a ha lo (h.trans hhi)
  have hsum := (abs_sub _ _).trans (add_le_add h1 h2)
  refine hsum.trans ?_
  set X : ℝ := (N : ℝ) * Real.exp (-(L / 2)) with hX
  have hX0 : 0 ≤ X := by positivity
  have hexp : Real.exp (-(L / 2)) = Real.exp (-(1 / 3) * L) * Real.exp (-(L / 6)) := by
    rw [← Real.exp_add]; ring_nf
  have h12 : 12 * Real.exp (-(L / 6)) ≤ 1 := by
    have hq := Real.quadratic_le_exp_of_nonneg (x := L / 6) (by linarith)
    have : Real.exp (-(L / 6)) = (Real.exp (L / 6))⁻¹ := Real.exp_neg _
    rw [this]
    have hE : (12 : ℝ) ≤ Real.exp (L / 6) := by nlinarith
    have hpos : 0 < Real.exp (L / 6) := Real.exp_pos _
    rw [← div_eq_mul_inv, div_le_one hpos]
    exact hE
  have : 2 * X + 2 * X ≤ (1 / 3) * ((N : ℝ) * Real.exp (-(1 / 3) * L)) := by
    rw [hX, hexp]
    have h3 : 0 ≤ (N : ℝ) * Real.exp (-(1 / 3) * L) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h12 h3]
  exact this

/-- The assembly in terms of `L` with `log N = L^{10}`: all `L ≥ L₀` work. -/
theorem c5_core_sw (hP : PNTapSW) :
    ∃ L₀ : ℝ, 4 ≤ L₀ ∧ ∀ (N : ℕ) (L : ℝ), L₀ ≤ L → Real.log N = L ^ 10 →
      ∀ w : ℕ, Real.exp L / 2 ≤ w → (w : ℝ) ≤ Real.exp L + 1 →
      ∀ (r : ℕ), 1 ≤ r → ∀ (a : ℤ) (lo hi : ℕ), lo ≤ hi → hi ≤ N →
        |∑ n ∈ apSet r a lo hi, (Λ n.toNat - cramerModel w n)| ≤
          N * Real.exp (-(1 / 3) * L) := by
  obtain ⟨L₁', hL₁'4, habsL⟩ := abs_psiAP_sub_le_sw hP
  have e1 := eventually_poly_le_exp 10 (2 * (1 + 2 * Real.exp 5)) (1 / 6) (by norm_num)
  have e3 := eventually_poly_le_exp 2 (24 * Real.exp 9) 1 (by norm_num)
  have e4 := eventually_poly_le_exp 10 (6 * Real.exp 5) 1 (by norm_num)
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp (e1.and (e3.and e4))
  refine ⟨max (max L₁ L₁') 36, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro N L hL hlog w hw1 hw2 r hr a lo hi h hhi
  have hL36 : 36 ≤ L := (le_max_right _ _).trans hL
  have hL4 : 4 ≤ L := by linarith
  have hLL₁ : L₁ ≤ L := ((le_max_left _ _).trans (le_max_left _ _)).trans hL
  have hLL₁' : L₁' ≤ L := ((le_max_right _ _).trans (le_max_left _ _)).trans hL
  obtain ⟨hG1, hG3, hG4⟩ := hL₁ L hLL₁
  have habs := habsL L hLL₁' N hlog
  by_cases hrL : Real.exp (L / 2) ≤ r
  · exact trivial_part hL4 hlog hw1 hw2 hG1 hr hrL a h hhi
  · rw [not_le] at hrL
    have hex2 : (2 : ℝ) ≤ Real.exp (L / 2) := by
      have := Real.add_one_le_exp (L / 2)
      linarith
    have hrw : r < w := by
      have h1 : Real.exp (L / 2) ≤ Real.exp L / 2 := by
        have : Real.exp L = Real.exp (L / 2) * Real.exp (L / 2) := by
          rw [← Real.exp_add]; ring_nf
        rw [this]
        nlinarith [Real.exp_pos (L / 2)]
      have : (r : ℝ) < w := by linarith
      exact_mod_cast this
    by_cases ha : IsCoprime a (r : ℤ)
    · rw [Finset.sum_sub_distrib]
      have hA := pnt_part_sw hL36 hlog (habs) hr hrL ha h hhi
      have hB := brun_part hL4 hlog hw1 hw2 hG3 hG4 hr hrw ha h hhi
      have e : ∑ n ∈ apSet r a lo hi, Λ n.toNat - ∑ n ∈ apSet r a lo hi, cramerModel w n =
          (∑ n ∈ apSet r a lo hi, Λ n.toNat - ((hi : ℝ) - lo) / (Nat.totient r : ℝ)) -
          (∑ n ∈ apSet r a lo hi, cramerModel w n - ((hi : ℝ) - lo) / (Nat.totient r : ℝ)) := by
        ring
      rw [e]
      refine (abs_sub _ _).trans ?_
      linarith
    · exact noncoprime_part hL4 hlog hG4 hr hrw ha hhi

/-- The target from `PNTapSW` (and `brun_ap`). -/
theorem c5_target_of_pnt (hP : PNTapSW) :
    ∃ (c : ℝ) (N₀ : ℕ), 0 < c ∧ ∀ N : ℕ, N₀ ≤ N → ∀ w : ℕ,
      Real.exp (Real.log N ^ ((1 : ℝ) / 10)) / 2 ≤ w →
      (w : ℝ) ≤ Real.exp (Real.log N ^ ((1 : ℝ) / 10)) + 1 →
      ∀ (r : ℕ), 1 ≤ r → ∀ (a : ℤ) (lo hi : ℕ), lo ≤ hi → hi ≤ N →
        |∑ n ∈ apSet r a lo hi, ((vonMangoldt n.toNat : ℝ) - cramerModel w n)| ≤
          N * Real.exp (-c * Real.log N ^ ((1 : ℝ) / 10)) := by
  obtain ⟨L₀, hL₀, hcore⟩ := c5_core_sw hP
  refine ⟨1 / 3, ⌈Real.exp (L₀ ^ 10)⌉₊, by norm_num, ?_⟩
  intro N hN w hw1 hw2 r hr a lo hi h hhi
  have hNge : Real.exp (L₀ ^ 10) ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos _) hNge
  have hlogge : L₀ ^ 10 ≤ Real.log N := (Real.le_log_iff_exp_le hNpos).mpr hNge
  have hlog0 : 0 ≤ Real.log N := le_trans (by positivity) hlogge
  set L : ℝ := Real.log N ^ ((1 : ℝ) / 10) with hL
  have hlog : Real.log N = L ^ 10 := by
    rw [hL, ← Real.rpow_natCast, ← Real.rpow_mul hlog0]
    norm_num
  have hLge : L₀ ≤ L := by
    have h0 : (0 : ℝ) ≤ L₀ := by linarith
    have : (L₀ ^ 10) ^ ((1 : ℝ) / 10) ≤ L := Real.rpow_le_rpow (by positivity) hlogge (by norm_num)
    have e : (L₀ ^ 10) ^ ((1 : ℝ) / 10) = L₀ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h0]
      norm_num
    linarith
  exact hcore N L hLge hlog w hw1 hw2 r hr a lo hi h hhi


/-- **The target of the prime number theorem in progressions on the classical zero-free region** (TT
`equiprop`, Siegel-free form, `Q = w`). -/
theorem c5_target_sw (hZ : ClassicalZeroFreeRegion) (hS : NoSiegelZero) :
    ∃ (c : ℝ) (N₀ : ℕ), 0 < c ∧ ∀ N : ℕ, N₀ ≤ N → ∀ w : ℕ,
      Real.exp (Real.log N ^ ((1 : ℝ) / 10)) / 2 ≤ w →
      (w : ℝ) ≤ Real.exp (Real.log N ^ ((1 : ℝ) / 10)) + 1 →
      ∀ (r : ℕ), 1 ≤ r → ∀ (a : ℤ) (lo hi : ℕ), lo ≤ hi → hi ≤ N →
        |∑ n ∈ apSet r a lo hi, ((vonMangoldt n.toNat : ℝ) - cramerModel w n)| ≤
          N * Real.exp (-c * Real.log N ^ ((1 : ℝ) / 10)) :=
  c5_target_of_pnt (pnt_ap_sw hZ hS)

/-- **The terminal form of the target**: for every real `K'` there is `N₀` such that for `N ≥ N₀`,
every level `w ∈ [e^L / 2, e^L + 1]` (`L = (log N)^{1/10}`) and every progression `P ⊆ [1, N]`,
`|∑_{n ∈ P} (Λ - Λ_{C,w})(n)| ≤ N exp(-(log log N)^{K'})`. -/
theorem c5_terminal_sw (hZ : ClassicalZeroFreeRegion) (hS : NoSiegelZero) (K' : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ w : ℕ,
      Real.exp (Real.log N ^ ((1 : ℝ) / 10)) / 2 ≤ w →
      (w : ℝ) ≤ Real.exp (Real.log N ^ ((1 : ℝ) / 10)) + 1 →
      ∀ (r : ℕ), 1 ≤ r → ∀ (a : ℤ) (lo hi : ℕ), lo ≤ hi → hi ≤ N →
        |∑ n ∈ apSet r a lo hi, ((vonMangoldt n.toNat : ℝ) - cramerModel w n)| ≤
          N * Real.exp (-(Real.log (Real.log N) ^ K')) := by
  obtain ⟨c, N₀, hc, h⟩ := c5_target_sw hZ hS
  set n : ℕ := ⌈K'⌉₊ with hn
  have ev : ∀ᶠ x : ℝ in atTop, 1 / c * x ^ n ≤ Real.exp (1 / 10 * x) ∧ 1 ≤ x :=
    (Fplus31.eventually_poly_le_exp n (1 / c) (1 / 10) (by norm_num)).and (eventually_ge_atTop 1)
  have htend : Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (htend.eventually ev)
  refine ⟨max N₀ (max N₁ 2), ?_⟩
  intro N hN w hw1 hw2 r hr a lo hi hlh hhi
  have hN0 : N₀ ≤ N := (le_max_left _ _).trans hN
  have hN1 : N₁ ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hN2 : 2 ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  obtain ⟨hx1, hx2⟩ := hN₁ N hN1
  refine (h N hN0 w hw1 hw2 r hr a lo hi hlh hhi).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  have hL : Real.log N ^ ((1 : ℝ) / 10) = Real.exp (1 / 10 * Real.log (Real.log N)) := by
    rw [Real.rpow_def_of_pos hlogN]
    ring_nf
  rw [hL]
  have hpow : Real.log (Real.log N) ^ K' ≤ Real.log (Real.log N) ^ (n : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx2 (Nat.le_ceil K')
  rw [Real.rpow_natCast] at hpow
  have : Real.log (Real.log N) ^ n ≤ c * Real.exp (1 / 10 * Real.log (Real.log N)) := by
    have h3 := mul_le_mul_of_nonneg_left hx1 hc.le
    have e : c * (1 / c * Real.log (Real.log N) ^ n) = Real.log (Real.log N) ^ n := by
      field_simp
    linarith
  linarith

end PrimeCarleson.Proof.Fplus31.PNTSW
