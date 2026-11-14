module

public import PrimeCarleson.Proof.Fplus31.C2.CMainStart
public import PrimeCarleson.Proof.Fplus31.Glue.Assembly

/-!
# The Cramér-model comparison, unconditionally: `‖Λ - Λ_{C,w}‖_{U³[N]} ≤ C_A (log N)^{-A}`

Part of the proof of [F+] Proposition 3.1: the comparison of `Λ` with the Cramér model, by an
iteration in the style of the type I / type II analysis of Leng23 (`Glue/Assembly.lean` assembles it
with the comparison of the Cramér model with the Heath-Brown model).
`cMainBoundPoly : CMainBoundPoly` is proved by the iteration (`C2/Iteration*.lean`): if
`‖normLam N‖_{U³[N]} ≥ e^{-p₀}` with `p₀ = (A + 1) log log N + 2`, `start_state` gives a state of
the iteration at the level `(p₀ + K)^K`, which `no_state` excludes in the regime where `Reg N P`
(`log N ≥ 6 P`, the Brun truncation) and `TermOK N P` (the prime number theorem in progressions)
hold; this regime holds for `N ≥ N₀(A)` since `P` is a polynomial in `log log N`. Small `N` are
absorbed in the constant.
-/

@[expose] public noncomputable section

open Filter Asymptotics
open scoped BigOperators

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open PrimeCarleson

/-- `(c log U)^m ≤ ε U` for `U` large. -/
theorem eventually_pow_log_le (c : ℝ) (hc : 0 < c) (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ U₀ : ℝ, ∀ U : ℝ, U₀ ≤ U → (c * Real.log U) ^ m ≤ ε * U := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := m)).bound (by positivity : 0 < ε / c ^ m)
  obtain ⟨U₁, hU₁⟩ := eventually_atTop.mp h
  refine ⟨max U₁ 1, fun U hU => ?_⟩
  have h1 := hU₁ U (le_trans (le_max_left _ _) hU)
  have hU1 : 1 ≤ U := (le_max_right _ _).trans hU
  have hl : 0 ≤ Real.log U := Real.log_nonneg hU1
  rw [Real.norm_of_nonneg (pow_nonneg hl m), id, Real.norm_of_nonneg (by linarith)] at h1
  rw [mul_pow]
  calc c ^ m * Real.log U ^ m ≤ c ^ m * (ε / c ^ m * U) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ε * U := by field_simp

/-- **The normalised Cramér-model comparison in the strict form**: for `N ≥ N₀(A)`,
`‖normLam N‖_{U³[N]} < e^{-((A + 1) log log N + 2)}`. -/
theorem cMain_eventually (A : ℝ) (hA : 1 ≤ A) :
    ∃ N₀ : ℕ, ∀ N : ℕ+, N₀ ≤ (N : ℕ) → 12 ≤ Real.log (N : ℕ) ∧
      gowersNormInterval 3 N (normLam N) <
        Real.exp (-((A + 1) * Real.log (Real.log N) + 2)) := by
  obtain ⟨Ks, hKs, hstart⟩ := start_state
  obtain ⟨Kn, hKn, hno⟩ := no_state
  have hPB : PB (fun p : ℝ => ((p + Ks) ^ Ks + Kn) ^ Kn) :=
    (PB.step Kn).comp (PB.step Ks) (fun p hp => by
      have h2 : (2 : ℝ) ≤ Ks := by exact_mod_cast hKs
      exact one_le_pow₀ (by linarith))
  obtain ⟨Kf, hKf, hKfb⟩ := hPB
  have hKfR : (2 : ℝ) ≤ Kf := by exact_mod_cast hKf
  set c : ℝ := A + Kf + 3 with hc
  have hc0 : 1 ≤ c := by linarith
  obtain ⟨U₁, hU₁⟩ := eventually_pow_log_le c (by linarith) (2 * Kf) (1 / 36) (by norm_num)
  obtain ⟨N₁, hN₁⟩ := termOK_of_large ((Kf : ℝ) + 1)
  set U₀ : ℝ := max (max (3 ^ 10) 12) (max U₁ (Real.exp (c ^ Kf + 1))) with hU₀
  refine ⟨max N₁ ⌈Real.exp U₀⌉₊, fun N hN => ?_⟩
  have hNN : (⌈Real.exp U₀⌉₊ : ℕ) ≤ (N : ℕ) := (le_max_right _ _).trans hN
  have hNN₁ : N₁ ≤ (N : ℕ) := (le_max_left _ _).trans hN
  have hNR : Real.exp U₀ ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNN)
  have hNpos : (0 : ℝ) < (N : ℕ) := by exact_mod_cast N.pos
  set U : ℝ := Real.log (N : ℕ) with hU
  have hUU : U₀ ≤ U := by
    rw [hU, Real.le_log_iff_exp_le hNpos]; exact hNR
  have hmax : max (max ((3 : ℝ) ^ 10) 12) (max U₁ (Real.exp (c ^ Kf + 1))) ≤ U := hUU
  rw [max_le_iff, max_le_iff, max_le_iff] at hmax
  obtain ⟨⟨hU3, hU12⟩, hUa, hUb⟩ := hmax
  have hUpos : 0 < U := by linarith
  have hlogU1 : c ^ Kf + 1 ≤ Real.log U := (Real.le_log_iff_exp_le hUpos).mpr hUb
  have hcK : 1 ≤ c ^ Kf := one_le_pow₀ hc0
  have hlogU : 1 ≤ Real.log U := by linarith
  -- the level
  set u : ℝ := U ^ ((1 : ℝ) / 10) with hu
  have hu3 : 3 ≤ u := by
    have h3 : (3 : ℝ) = ((3 : ℝ) ^ 10) ^ ((1 : ℝ) / 10) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [h3]
    exact Real.rpow_le_rpow (by positivity) hU3 (by norm_num)
  refine ⟨hU12, ?_⟩
  by_contra hcon
  push Not at hcon
  set p₀ : ℝ := (A + 1) * Real.log U + 2 with hp₀
  have hp₀2 : 2 ≤ p₀ := by
    have : 0 ≤ (A + 1) * Real.log U := by positivity
    linarith
  have hnorm : NormOK (N : ℕ) := normOK_of_large (u := u) hu hu3
  set p₁ : ℝ := (p₀ + Ks) ^ Ks with hp₁
  have hp₀1 : 1 ≤ p₀ := by linarith
  have hp₁1 : 1 ≤ p₁ := by
    have h2 : (2 : ℝ) ≤ Ks := by exact_mod_cast hKs
    exact one_le_pow₀ (by linarith)
  have hpp₁ : p₀ ≤ p₁ := le_pow_K (by linarith) hKs
  have hlam : Real.log (1 + U) ≤ p₁ := by
    have h1 : Real.log (1 + U) ≤ Real.log (2 * U) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) hUpos.ne'] at h1
    have := Real.log_two_lt_d9
    have h2 : 0 ≤ (A + 1) * Real.log U := by positivity
    have h3 : (A + 1) * Real.log U ≥ Real.log U := by
      linarith only [mul_nonneg (zero_le_one.trans hA) (zero_le_one.trans hlogU)]
    linarith
  -- the final level
  set Pn : ℝ := (p₁ + Kn) ^ Kn with hPn
  have hPn0 : 0 ≤ Pn := by positivity
  have hPnb : Pn ≤ (p₀ + Kf) ^ Kf := (hKfb p₀ hp₀1).2
  have hpK : p₀ + Kf ≤ c * Real.log U := by
    have : (2 : ℝ) + Kf ≤ (Kf + 2) * Real.log U := by
      have h0 : (0 : ℝ) ≤ Kf + 2 := by linarith only [hKfR]
      linarith only [mul_nonneg h0 (sub_nonneg.mpr hlogU)]
    have e : c * Real.log U = (A + 1) * Real.log U + (Kf + 2) * Real.log U := by
      rw [hc]; ring
    linarith only [this, e, hp₀]
  have hY : (p₀ + Kf) ^ Kf ≤ (c * Real.log U) ^ Kf :=
    pow_le_pow_left₀ (by linarith) hpK _
  have hY2 : ((c * Real.log U) ^ Kf) ^ 2 ≤ 1 / 36 * U := by
    rw [← pow_mul, Nat.mul_comm]
    exact hU₁ U hUa
  have hY0 : 0 ≤ (c * Real.log U) ^ Kf := by positivity
  have hY1 : 1 ≤ (c * Real.log U) ^ Kf := one_le_pow₀ (one_le_mul_of_one_le_of_one_le hc0 hlogU)
  have hPnY : Pn ≤ (c * Real.log U) ^ Kf := hPnb.trans hY
  have hPn2 : Pn ^ 2 ≤ U := by
    have : Pn ^ 2 ≤ ((c * Real.log U) ^ Kf) ^ 2 := pow_le_pow_left₀ hPn0 hPnY 2
    linarith
  have hPn6 : 6 * Pn ≤ U := by
    have : (c * Real.log U) ^ Kf ≤ ((c * Real.log U) ^ Kf) ^ 2 :=
      le_self_pow₀ hY1 (by norm_num)
    linarith
  have hReg : Reg (N : ℕ) Pn :=
    ⟨hU12, hPn6, brunOK_of_large (u := u) hu hu3 hPn0 hPn2, hnorm⟩
  have hTerm : TermOK (N : ℕ) Pn := by
    refine hN₁ N hNN₁ Pn ?_
    have h1 : (c * Real.log U) ^ Kf = c ^ Kf * Real.log U ^ Kf := mul_pow _ _ _
    have h2 : Real.log U ^ ((Kf : ℝ) + 1) = Real.log U ^ Kf * Real.log U := by
      rw [Real.rpow_add (by linarith), Real.rpow_natCast, Real.rpow_one]
    calc Pn ≤ (c * Real.log U) ^ Kf := hPnY
      _ = c ^ Kf * Real.log U ^ Kf := h1
      _ < Real.log U * Real.log U ^ Kf := by
          have : 0 < Real.log U ^ Kf := by positivity
          exact mul_lt_mul_of_pos_right (by linarith only [hlogU1]) this
      _ = Real.log U ^ ((Kf : ℝ) + 1) := by rw [h2]; ring
  have hcon' : Real.exp (-p₀) ≤ gowersNormInterval 3 N (normLam N) := hcon
  exact hno hp₁1 hlam hReg hTerm (hstart hp₀2 hnorm hcon')

/-- The function `Λ - Λ_{C,w}`, `w = cramerLevel N`, as a function on `ℤ`. -/
def lamDiff (N : ℕ+) : ℤ → ℂ := fun n =>
  ((ArithmeticFunction.vonMangoldt n.toNat : ℝ) : ℂ) - ((cramerModel (cramerLevel N) n : ℝ) : ℂ)

/-- `Λ - Λ_{C,w} = 3 log N · normLam N`. -/
theorem lamDiff_eq (N : ℕ+) (hN : 2 ≤ N) :
    lamDiff N = ((3 * Real.log (N : ℕ) : ℝ) : ℂ) • normLam N := by
  have hL := log_pos_of_two_le hN
  funext n
  simp only [Pi.smul_apply, smul_eq_mul, lamDiff]
  unfold normLam
  rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (by positivity), Complex.ofReal_one,
    one_mul]

/-- **The Cramér-model comparison, polylog form, unconditionally.** For every `A ≥ 1` there is `C_A`
with `‖Λ - Λ_{C,w}‖_{U³[N]} ≤ C_A (log N)^{-A}` for all `N ≥ 2`, `w = cramerLevel N`. -/
theorem cMainBoundPoly : CMainBoundPoly := by
  intro A hA
  obtain ⟨N₀, hN₀⟩ := cMain_eventually A hA
  obtain ⟨M, hM'⟩ := Finset.exists_le ((Finset.univ : Finset (Fin N₀)).image
    (fun i : Fin N₀ => gowersNormInterval 3 ⟨(i : ℕ) + 1, Nat.succ_pos _⟩
      (lamDiff ⟨(i : ℕ) + 1, Nat.succ_pos _⟩) /
        Real.log (((i : ℕ) + 1 : ℕ) : ℝ) ^ (-A)))
  have hM : ∀ i : Fin N₀, gowersNormInterval 3 ⟨(i : ℕ) + 1, Nat.succ_pos _⟩
      (lamDiff ⟨(i : ℕ) + 1, Nat.succ_pos _⟩) /
        Real.log (((i : ℕ) + 1 : ℕ) : ℝ) ^ (-A) ≤ M := fun i =>
    hM' _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  refine ⟨max M 3, fun N hN => ?_⟩
  have hL := log_pos_of_two_le hN
  have hLA : 0 < Real.log (N : ℕ) ^ (-A) := Real.rpow_pos_of_pos hL _
  change gowersNormInterval 3 N (lamDiff N) ≤ _
  by_cases hbig : N₀ ≤ (N : ℕ)
  · obtain ⟨-, hsmul, -⟩ := Paper.gowersNormInterval_three_norm_properties N
    rw [lamDiff_eq N hN, hsmul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    obtain ⟨hU12, h1⟩ := hN₀ N hbig
    have hU1 : 1 ≤ Real.log (N : ℕ) := by linarith
    have h2 : Real.exp (-((A + 1) * Real.log (Real.log (N : ℕ)) + 2)) ≤
        Real.log (N : ℕ) ^ (-(A + 1)) := by
      rw [Real.rpow_def_of_pos hL]
      refine Real.exp_le_exp.mpr ?_
      have : 0 ≤ Real.log (Real.log (N : ℕ)) := Real.log_nonneg hU1
      linarith only [this]
    have h3 : 3 * Real.log (N : ℕ) * gowersNormInterval 3 N (normLam N) ≤
        3 * Real.log (N : ℕ) ^ (-A) := by
      calc 3 * Real.log (N : ℕ) * gowersNormInterval 3 N (normLam N) ≤
          3 * Real.log (N : ℕ) * Real.log (N : ℕ) ^ (-(A + 1)) :=
            mul_le_mul_of_nonneg_left (h1.le.trans h2) (by positivity)
        _ = 3 * Real.log (N : ℕ) ^ (-A) := by
          have : Real.log (N : ℕ) * Real.log (N : ℕ) ^ (-(A + 1)) = Real.log (N : ℕ) ^ (-A) := by
            rw [← Real.rpow_one_add' hL.le (by linarith)]
            congr 1; ring
          rw [mul_assoc, this]
    calc 3 * Real.log (N : ℕ) * gowersNormInterval 3 N (normLam N) ≤ 3 * Real.log (N : ℕ) ^ (-A) :=
          h3
      _ ≤ max M 3 * Real.log (N : ℕ) ^ (-A) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hLA.le
  · push Not at hbig
    have hi : (N : ℕ) - 1 < N₀ := by omega
    have h1 : gowersNormInterval 3 (⟨((N : ℕ) - 1) + 1, Nat.succ_pos _⟩ : ℕ+)
        (lamDiff ⟨((N : ℕ) - 1) + 1, Nat.succ_pos _⟩) /
          Real.log ((((N : ℕ) - 1 + 1 : ℕ)) : ℝ) ^ (-A) ≤ M :=
      hM ⟨(N : ℕ) - 1, hi⟩
    have hN' : (⟨((N : ℕ) - 1) + 1, Nat.succ_pos _⟩ : ℕ+) = N := by
      apply PNat.eq
      simp only [PNat.mk_coe]
      have := N.pos
      omega
    rw [hN'] at h1
    have h2 : (((N : ℕ) - 1 + 1 : ℕ) : ℝ) = (N : ℕ) := by
      have := N.pos
      congr 1
      omega
    rw [h2, div_le_iff₀ hLA] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hLA.le)

end PrimeCarleson.Proof.Fplus31
