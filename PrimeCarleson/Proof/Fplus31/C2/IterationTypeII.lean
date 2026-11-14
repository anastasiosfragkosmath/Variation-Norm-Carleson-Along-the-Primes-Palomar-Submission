module

public import PrimeCarleson.Proof.Fplus31.C2.IterationTypeI
public import PrimeCarleson.Proof.Fplus31.C2.TypeIIGlue

/-!
# The iteration, the type II step with budgets

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). From the
type II output of the Vaughan decomposition for the state (`η = 3 log N e^{-p}`; `N < L³, M³ ≤ N²`,
`L M ≥ η N / (16 (1 + log N)^5)` and the four-fold bound with
`x = typeIIx η N ≥ 16 e^{-(30 p + 50)}`): `type_two_extrapolation_of_C3` at the level
`p̃ = 30 p + 50` with the scale `A = x M / (8 q) ≥ e^{U/3 - p̃ - p}`, then
`cellOutput_of_extrapolatedII` (the sub-step for every window centre) at the scale
`A L / 2 ≥ N e^{-(2 p̃ + p)}`.
-/

@[expose] public noncomputable section

open OAI OAI.Erdos3
open scoped TensorProduct BigOperators

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open Module NilpotentLieFiltration Finset

/-- `N < M^3` with `N = e^U` gives `e^{U/3} ≤ M`. -/
theorem exp_le_of_lt_pow_three {N M : ℕ} {U : ℝ} (hN : (N : ℝ) = Real.exp U) (h : N < M ^ 3) :
    Real.exp (U / 3) ≤ M := by
  have h1 : (N : ℝ) < (M : ℝ) ^ 3 := by exact_mod_cast h
  have h2 : (N : ℝ) = Real.exp (U / 3) ^ 3 := by
    rw [hN, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [h2] at h1
  exact (lt_of_pow_lt_pow_left₀ 3 (Nat.cast_nonneg M) h1).le

/-- **The scale of the type II step**: `x M / (8 q) ≥ e^{U/3 - t - p}`. -/
theorem scale_typeII_A {q M : ℕ} {U p t x : ℝ} (hq1 : 1 ≤ q) (hq : (q : ℝ) ≤ Real.exp p)
    (hM : Real.exp (U / 3) ≤ M) (hx : 16 * Real.exp (-t) ≤ x) :
    Real.exp (U / 3 - t - p) ≤ x * M / (8 * q) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  rw [le_div_iff₀ (by positivity)]
  have h1 : Real.exp (U / 3 - t - p) * (8 * q) ≤ Real.exp (U / 3 - t - p) * (8 * Real.exp p) :=
    mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  have h2 : Real.exp (U / 3 - t - p) * (8 * Real.exp p) =
      8 * (Real.exp (-t) * Real.exp (U / 3)) := by
    rw [mul_comm 8, ← mul_assoc, ← Real.exp_add]
    have : U / 3 - t - p + p = -t + U / 3 := by ring
    rw [this, Real.exp_add]; ring
  have h3 : 8 * (Real.exp (-t) * Real.exp (U / 3)) ≤ x * M := by
    have hx0 : 0 ≤ x := le_trans (by positivity) hx
    have h5 := mul_le_mul hx hM (Real.exp_pos _).le hx0
    linarith only [h5, mul_pos (Real.exp_pos (-t)) (Real.exp_pos (U / 3))]
  linarith

/-- **The scale after the extrapolation**: `(x M / (8 q)) L / 2 ≥ N e^{-(2 t + p)}`. -/
theorem scale_typeII_A' {N q L M : ℕ} {p t x : ℝ} (hq1 : 1 ≤ q) (hq : (q : ℝ) ≤ Real.exp p)
    (hx : 16 * Real.exp (-t) ≤ x) (hLM : Real.exp (-t) * N ≤ (L : ℝ) * M) :
    (N : ℝ) * Real.exp (-(2 * t + p)) ≤ x * M / (8 * q) * L / 2 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have h1 : x * M / (8 * q) * L / 2 = x * ((L : ℝ) * M) / (16 * q) := by field_simp; ring
  rw [h1, le_div_iff₀ (by positivity)]
  have h2 : (N : ℝ) * Real.exp (-(2 * t + p)) * (16 * q) ≤
      N * Real.exp (-(2 * t + p)) * (16 * Real.exp p) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h3 : (N : ℝ) * Real.exp (-(2 * t + p)) * (16 * Real.exp p) =
      16 * (Real.exp (-t) * (Real.exp (-t) * N)) := by
    have : Real.exp (-(2 * t + p)) * Real.exp p = Real.exp (-t) * Real.exp (-t) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc (N : ℝ) * Real.exp (-(2 * t + p)) * (16 * Real.exp p) =
        16 * N * (Real.exp (-(2 * t + p)) * Real.exp p) := by ring
      _ = 16 * (Real.exp (-t) * (Real.exp (-t) * N)) := by rw [this]; ring
  have h4 : 16 * (Real.exp (-t) * (Real.exp (-t) * N)) ≤ x * ((L : ℝ) * M) := by
    have h5 := mul_le_mul hx hLM (by positivity) hx0.le
    linarith only [h5]
  linarith

/-- `log (32 q / x) ≤ 3 t` for `q ≤ e^t`, `x ≥ e^{-t}` and `t ≥ 50`. -/
theorem log_inv_div_le {x : ℝ} {q : ℕ} {t : ℝ} (hq1 : 1 ≤ q) (hqE : (q : ℝ) ≤ Real.exp t)
    (hx0 : 0 < x) (hxe : Real.exp (-t) ≤ x) (ht : 50 ≤ t) :
    Real.log (1 / (x / (32 * q))) ≤ 3 * t := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have h1 : 1 / (x / (32 * q)) ≤ Real.exp (3 * t) := by
    rw [one_div_div, div_le_iff₀ hx0]
    have h32 : (32 : ℝ) ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
    calc 32 * (q : ℝ) ≤ 32 * Real.exp t := by linarith
      _ ≤ Real.exp t * Real.exp t := mul_le_mul_of_nonneg_right h32 (Real.exp_pos _).le
      _ = Real.exp (3 * t) * Real.exp (-t) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (3 * t) * x := mul_le_mul_of_nonneg_left hxe (Real.exp_pos _).le
  have h2 := Real.log_le_log (by positivity) h1
  rwa [Real.log_exp] at h2

/-- The levels needed by the type II step at the level `p`. -/
def typeIINeed (C₁ C₃ Cπ : ℕ) (C₂ p : ℝ) : ℝ :=
  (C₂ * (((30 * p + 50 + 2 + Cπ) ^ Cπ + 1 + C₁) ^ C₁ + 3 * (30 * p + 50) + 1) ^ 4 + C₃) ^ C₃ +
    C₂ * (((30 * p + 50 + 2 + Cπ) ^ Cπ + 1 + C₁) ^ C₁ + 3 * (30 * p + 50)) ^ 3 +
    ((30 * p + 50 + 2 + Cπ) ^ Cπ + 1 + C₁) ^ C₁ + 2 * (30 * p + 50) + p

/-- **The budget of the type II step**: the levels of the stage are bounded by `(p + K)^K`. -/
theorem typeII_budget (C₁ C₃ Cπ : ℕ) (C₂ : ℝ) (hC₂ : 1 ≤ C₂) (hC₁ : 2 ≤ C₁) (hC₃ : 2 ≤ C₃) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ p : ℝ, 1 ≤ p →
      0 ≤ typeIINeed C₁ C₃ Cπ C₂ p ∧ typeIINeed C₁ C₃ Cπ C₂ p ≤ (p + K) ^ K := by
  have hC₁R : (2 : ℝ) ≤ C₁ := by exact_mod_cast hC₁
  have hC₃R : (2 : ℝ) ≤ C₃ := by exact_mod_cast hC₃
  have hpt : PB (fun p : ℝ => 30 * p + 50) :=
    ((PB.const 30 (by norm_num)).mul PB.id).add (PB.const 50 (by norm_num))
  have hpt1 : ∀ p : ℝ, 1 ≤ p → 1 ≤ 30 * p + 50 + 2 := fun p hp => by linarith
  have hpbb : PB (fun p : ℝ => (30 * p + 50 + 2 + Cπ) ^ Cπ + 1) :=
    ((PB.step Cπ).comp (hpt.add (PB.const 2 (by norm_num))) hpt1).add
      (PB.const 1 zero_le_one)
  have hpbb1 : ∀ p : ℝ, 1 ≤ p → 1 ≤ (30 * p + 50 + 2 + Cπ) ^ Cπ + 1 := fun p hp => by
    have : (0 : ℝ) ≤ (30 * p + 50 + 2 + Cπ) ^ Cπ := by positivity
    linarith
  have hpt2 : PB (fun p : ℝ => ((30 * p + 50 + 2 + Cπ) ^ Cπ + 1 + C₁) ^ C₁) :=
    (PB.step C₁).comp hpbb hpbb1
  have hb1 : PB (fun p : ℝ =>
      ((30 * p + 50 + 2 + Cπ) ^ Cπ + 1 + C₁) ^ C₁ + 3 * (30 * p + 50) + 1) :=
    (hpt2.add ((PB.const 3 (by norm_num)).mul hpt)).add (PB.const 1 zero_le_one)
  have hph : PB (fun p : ℝ => C₂ *
      (((30 * p + 50 + 2 + Cπ) ^ Cπ + 1 + C₁) ^ C₁ + 3 * (30 * p + 50) + 1) ^ 4) :=
    (PB.const C₂ (by linarith)).mul (hb1.npow 4)
  have hph1 : ∀ p : ℝ, 1 ≤ p → 1 ≤ C₂ *
      (((30 * p + 50 + 2 + Cπ) ^ Cπ + 1 + C₁) ^ C₁ + 3 * (30 * p + 50) + 1) ^ 4 :=
    fun p hp => by
      have h1 : (1 : ℝ) ≤ ((30 * p + 50 + 2 + Cπ) ^ Cπ + 1 + C₁) ^ C₁ + 3 * (30 * p + 50) + 1 := by
        have : (0 : ℝ) ≤ ((30 * p + 50 + 2 + Cπ) ^ Cπ + 1 + C₁) ^ C₁ := by positivity
        linarith
      exact one_le_mul_of_one_le_of_one_le hC₂ (one_le_pow₀ h1)
  have hbb : PB (fun p : ℝ => (C₂ *
      (((30 * p + 50 + 2 + Cπ) ^ Cπ + 1 + C₁) ^ C₁ + 3 * (30 * p + 50) + 1) ^ 4 + C₃) ^ C₃) :=
    (PB.step C₃).comp hph hph1
  have h3 : PB (fun p : ℝ => C₂ *
      (((30 * p + 50 + 2 + Cπ) ^ Cπ + 1 + C₁) ^ C₁ + 3 * (30 * p + 50)) ^ 3) :=
    (PB.const C₂ (by linarith)).mul ((hpt2.add ((PB.const 3 (by norm_num)).mul hpt)).npow 3)
  have hneedPB : PB (fun p : ℝ =>
      (C₂ * (((30 * p + 50 + 2 + Cπ) ^ Cπ + 1 + C₁) ^ C₁ + 3 * (30 * p + 50) + 1) ^ 4 + C₃) ^ C₃ +
        C₂ * (((30 * p + 50 + 2 + Cπ) ^ Cπ + 1 + C₁) ^ C₁ + 3 * (30 * p + 50)) ^ 3 +
        ((30 * p + 50 + 2 + Cπ) ^ Cπ + 1 + C₁) ^ C₁ + 2 * (30 * p + 50) + p) :=
    (((hbb.add h3).add hpt2).add ((PB.const 2 (by norm_num)).mul hpt)).add PB.id
  obtain ⟨K, hK, h⟩ := hneedPB
  exact ⟨K, hK, h⟩

/-- The product-niltest budget at the level `30 p + 50`. -/
def pbT (p : ℝ) : ℝ := productNiltestBudget (30 * p + 50 + 2) + 1

/-- The logarithm of `32 q / x`, `x = typeIIx η N`. -/
def lgT (η : ℝ) (N q : ℕ) : ℝ := Real.log (1 / (typeIIx η N / (32 * q)))

/-- The complexity of the extrapolation of the type II step. -/
def phrT (C₁ : ℕ) (C₂ p η : ℝ) (N q : ℕ) : ℝ :=
  C₂ * (((pbT p + C₁) ^ C₁) + lgT η N q + 1) ^ 4

/-- The box scale `x M / (8 q)` of the type II step. -/
def ATII (η : ℝ) (N q M : ℕ) : ℝ := typeIIx η N * M / (8 * q)

/-- **The numbers of the type II step.**  The bias, the scale conditions of
`type_two_extrapolation_of_C3`, and the scale and budget of the sub-step. -/
theorem typeII_numerics {C₁ C₃ Cπ : ℕ} {C₂ : ℝ} (hC₂ : 1 ≤ C₂) (hC₁ : 2 ≤ C₁) (hC₃ : 2 ≤ C₃)
    (hπ : ∀ p : ℝ, 0 ≤ p → productNiltestBudget p ≤ (p + Cπ) ^ Cπ)
    {N q L M : ℕ} {U p η P : ℝ} (hUN : Real.log N = U) (hp : 1 ≤ p)
    (hlam : Real.log (1 + U) ≤ p) (hU12 : 12 ≤ U)
    (hU6 : 6 * P ≤ U) (hneed : typeIINeed C₁ C₃ Cπ C₂ p ≤ P) (hNe : (N : ℝ) = Real.exp U)
    (hη : η = 3 * U * Real.exp (-p)) (hq1 : 1 ≤ q) (hqp : (q : ℝ) ≤ Real.exp p)
    (hNL : N < L ^ 3) (hNM : N < M ^ 3)
    (hLMlow : η / (16 * (1 + U) ^ 5) * N ≤ (L : ℝ) * M) :
    Real.exp (-pbT p) ≤ typeIIx η N / 16 ∧
    Real.exp ((pbT p + C₁) ^ C₁) ≤ ATII η N q M ∧
    Real.exp (C₂ * (((pbT p + C₁) ^ C₁) + lgT η N q) ^ 3) ≤ ATII η N q M ∧
    Real.exp (C₂ * (((pbT p + C₁) ^ C₁) + lgT η N q) ^ 3) ≤ L ∧
    p ≤ phrT C₁ C₂ p η N q ∧ 1 ≤ phrT C₁ C₂ p η N q ∧
    Real.exp ((phrT C₁ C₂ p η N q + C₃) ^ C₃) ≤ ATII η N q M * L / 2 ∧
    (phrT C₁ C₂ p η N q + C₃) ^ C₃ ≤ P ∧
    (N : ℝ) ≤ ATII η N q M * L / 2 * Real.exp ((phrT C₁ C₂ p η N q + C₃) ^ C₃) := by
  have hC₁R : (2 : ℝ) ≤ C₁ := by exact_mod_cast hC₁
  have hC₃R : (2 : ℝ) ≤ C₃ := by exact_mod_cast hC₃
  have hp0 : 0 ≤ p := by linarith
  have hNpos : (0 : ℝ) < N := by rw [hNe]; exact Real.exp_pos _
  unfold typeIINeed at hneed
  simp only [pbT, phrT, lgT, ATII]
  set pt : ℝ := 30 * p + 50 with hpt_def
  have hpt0 : 0 ≤ pt := by rw [hpt_def]; linarith
  have hptp : p ≤ pt := by rw [hpt_def]; linarith
  have hpt50 : 50 ≤ pt := by rw [hpt_def]; linarith
  set pbb : ℝ := (pt + 2 + Cπ) ^ Cπ + 1 with hpbb_def
  have hpbb0 : 0 ≤ pbb := by positivity
  set pt2 : ℝ := (pbb + C₁) ^ C₁ with hpt2_def
  have hpt2_0 : 0 ≤ pt2 := by positivity
  set phb : ℝ := C₂ * (pt2 + 3 * pt + 1) ^ 4 with hphb
  have hphb0 : 0 ≤ phb := by positivity
  set bbb : ℝ := (phb + C₃) ^ C₃ with hbbb
  have hbbb0 : 0 ≤ bbb := by positivity
  set th3 : ℝ := C₂ * (pt2 + 3 * pt) ^ 3 with hth3
  have hth30 : 0 ≤ th3 := by positivity
  have hpU : p ≤ U / 6 := by linarith
  have hsmallU : bbb + th3 + pt2 + 2 * pt + p ≤ U / 6 := by linarith
  -- the product-niltest budget
  have hπ0 : 0 ≤ productNiltestBudget (pt + 2) := by
    have := productNiltestBudget_geometry (p := pt + 2) (by linarith)
    exact le_trans (sq_nonneg _) this
  have hpb_le : productNiltestBudget (pt + 2) + 1 ≤ pbb := by
    have := hπ (pt + 2) (by linarith)
    rw [hpbb_def]
    linarith
  have hpb_ge : pt ≤ productNiltestBudget (pt + 2) + 1 := by
    have h1 := productNiltestBudget_geometry (p := pt + 2) (by linarith)
    linarith only [h1, sq_nonneg pt, hpt0]
  set pb : ℝ := productNiltestBudget (pt + 2) + 1 with hpb
  have hpb0 : 0 ≤ pb := by rw [hpb]; linarith
  clear_value pb
  -- the parameters
  obtain ⟨-, -, hx16, hη16⟩ := param_bounds hU12 hp0 hlam hη
    (δ := η / (2 ^ 13 * (1 + U) ^ 3)) rfl
  have hxdef : typeIIx η N = min (η ^ 4 / (2 ^ 20 * (1 + U) ^ 18)) 1 := by
    unfold typeIIx; rw [hUN]
  rw [← hxdef] at hx16
  have hη0 : 0 < η := by rw [hη]; positivity
  have hx0 : 0 < typeIIx η N := typeIIx_pos hη0 N
  have hx1 : typeIIx η N ≤ 1 := typeIIx_le_one η N
  have hqE : (q : ℝ) ≤ Real.exp pt := hqp.trans (Real.exp_le_exp.mpr hptp)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hMexp := exp_le_of_lt_pow_three hNe hNM
  have hLexp := exp_le_of_lt_pow_three hNe hNL
  have hlogq : Real.log (1 / (typeIIx η N / (32 * q))) ≤ 3 * pt := by
    refine log_inv_div_le hq1 hqE hx0 ?_ hpt50
    have := Real.exp_pos (-pt)
    linarith
  have hxq1 : typeIIx η N / (32 * q) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    linarith
  have hlogq0 : 0 ≤ Real.log (1 / (typeIIx η N / (32 * q))) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    linarith
  set lg : ℝ := Real.log (1 / (typeIIx η N / (32 * q))) with hlg
  clear_value lg
  have hAlow : Real.exp (U / 3 - pt - p) ≤ typeIIx η N * M / (8 * q) :=
    scale_typeII_A hq1 hqp hMexp hx16
  set A : ℝ := typeIIx η N * M / (8 * q) with hA
  have hLM' : Real.exp (-pt) * N ≤ (L : ℝ) * M := by
    have := mul_le_mul_of_nonneg_right hη16 hNpos.le
    linarith
  have hAfin := scale_typeII_A' (N := N) (q := q) (L := L) (M := M) (p := p) (t := pt) hq1
    hqp hx16 hLM'
  have hbias : Real.exp (-pb) ≤ typeIIx η N / 16 := by
    have : Real.exp (-pb) ≤ Real.exp (-pt) := Real.exp_le_exp.mpr (by linarith)
    have := Real.exp_pos (-pt)
    linarith
  rw [← hA] at hAfin
  have hA0 : 0 ≤ A := (Real.exp_pos _).le.trans hAlow
  clear_value A
  clear_value pbb pt2 phb bbb th3
  have hZ1 : (pb + C₁) ^ C₁ ≤ pt2 := by
    rw [hpt2_def]
    exact pow_le_pow_left₀ (by linarith) (by linarith) _
  have hZ1' : (0 : ℝ) ≤ (pb + C₁) ^ C₁ := by positivity
  have hA1 : Real.exp ((pb + C₁) ^ C₁) ≤ A := by
    refine le_trans (Real.exp_le_exp.mpr ?_) hAlow
    linarith
  have hZ2 : C₂ * (((pb + C₁) ^ C₁) + lg) ^ 3 ≤ th3 := by
    rw [hth3]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    exact pow_le_pow_left₀ (by positivity) (by linarith) 3
  have hA2 : Real.exp (C₂ * (((pb + C₁) ^ C₁) + lg) ^ 3) ≤ A := by
    refine le_trans (Real.exp_le_exp.mpr ?_) hAlow
    linarith
  have hL2 : Real.exp (C₂ * (((pb + C₁) ^ C₁) + lg) ^ 3) ≤ L := by
    refine le_trans (Real.exp_le_exp.mpr ?_) hLexp
    linarith
  set phr : ℝ := C₂ * ((pb + C₁) ^ C₁ + lg + 1) ^ 4 with hphr
  have hbase1 : 1 ≤ (pb + C₁) ^ C₁ + lg + 1 := by linarith
  have hpbC : pb ≤ (pb + C₁) ^ C₁ := by
    have h1 : (1 : ℝ) ≤ pb + C₁ := by linarith
    calc pb ≤ pb + C₁ := by linarith
      _ ≤ (pb + C₁) ^ C₁ := le_self_pow₀ h1 (by omega)
  have hphr_big : 4 * pt ≤ phr := by
    have hb2 : 2 ≤ (pb + C₁) ^ C₁ + lg + 1 := by linarith
    have := four_mul_le_pow_four hb2
    have h3 : ((pb + C₁) ^ C₁ + lg + 1) ^ 4 ≤ phr := by
      rw [hphr]
      exact le_mul_of_one_le_left (by positivity) (by linarith)
    linarith
  have hphr_le : phr ≤ phb := by
    rw [hphr, hphb]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    exact pow_le_pow_left₀ (by linarith) (by linarith) 4
  have hphr0 : 0 ≤ phr := by linarith
  clear_value phr
  have hbphr : (phr + C₃) ^ C₃ ≤ bbb := by
    rw [hbbb]
    exact pow_le_pow_left₀ (by linarith) (by linarith) _
  have hA' : Real.exp ((phr + C₃) ^ C₃) ≤ A * L / 2 := by
    have h2 : (N : ℝ) * Real.exp (-(2 * pt + p)) = Real.exp (U - (2 * pt + p)) := by
      rw [hNe, ← Real.exp_add]; congr 1
    have h1' : Real.exp (U - (2 * pt + p)) ≤ A * L / 2 := by
      rw [← h2]; exact hAfin
    refine le_trans (Real.exp_le_exp.mpr ?_) h1'
    linarith
  refine ⟨hbias, hA1, hA2, hL2, by linarith, by linarith, hA', by linarith, ?_⟩
  have h2 : 2 * pt + p ≤ (phr + C₃) ^ C₃ := by
    have : phr + C₃ ≤ (phr + C₃) ^ C₃ := le_self_pow₀ (by linarith) (by omega)
    linarith
  have h3 : (N : ℝ) = (N : ℝ) * Real.exp (-(2 * pt + p)) * Real.exp (2 * pt + p) := by
    rw [mul_assoc, ← Real.exp_add]; simp
  calc (N : ℝ) = (N : ℝ) * Real.exp (-(2 * pt + p)) * Real.exp (2 * pt + p) := h3
    _ ≤ A * L / 2 * Real.exp ((phr + C₃) ^ C₃) :=
        mul_le_mul hAfin (Real.exp_le_exp.mpr h2) (Real.exp_pos _).le (by positivity)

/-- **The type II step with budgets.** From the type II output of the Vaughan decomposition for a
`LengStart` state at the level `p` (`η = 3 log N e^{-p}`), the sub-step for every window centre, at
the scale `A` with `N ≤ A e^b` and `b ≤ (p + K)^K`, provided `6 (p + K)^K ≤ log N`. -/
theorem typeII_cell (s : ℕ) (hs : s ≤ 1) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {N : ℕ} {p : ℝ} {Q : Finset (Unit → ℤ)} {f : (Unit → ℤ) → ℂ}
      (S : LengStart (s + 1) Q f p) {q : ℕ} {r lo hi : ℤ}, APInv N p q r lo hi → 1 ≤ p →
      Real.log (1 + Real.log N) ≤ p → 12 ≤ Real.log N → 6 * (p + K) ^ K ≤ Real.log N →
      ∀ {η : ℝ}, η = 3 * Real.log N * Real.exp (-p) →
      (∃ L M : ℕ, N < L ^ 3 ∧ L ^ 3 ≤ N ^ 2 ∧ N < M ^ 3 ∧ M ^ 3 ≤ N ^ 2 ∧
        η / (16 * (1 + Real.log N) ^ 5) * N ≤ (L : ℝ) * M ∧ (L : ℝ) * M < 4 * N ∧
        η ^ 4 / (2 ^ 20 * (1 + Real.log N) ^ 18) * (N : ℝ) ^ 2 ≤
          fourFold (fun n : ℕ => typeISequence S.T q r lo hi (n : ℤ)) (dyadicBlock L)
            (dyadicBlock M)) →
      ∃ A b : ℝ, 0 ≤ b ∧ b ≤ (p + K) ^ K ∧ (N : ℝ) ≤ A * Real.exp b ∧
        ∀ z : ℤ, CellOutput s (fun x => S.T.eval (fun _ => x + z)) (CommKilled S.η) A b := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hext⟩ := type_two_extrapolation_of_C3 (s + 1) (by omega) (by omega)
  obtain ⟨C₃, hC₃, hcell⟩ := cellOutput_of_extrapolatedII s hs
  obtain ⟨Cπ, hCπ, hπ⟩ := exists_productNiltestBudget_bound
  obtain ⟨K, hK, hKn⟩ := typeII_budget C₁ C₃ Cπ C₂ hC₂ hC₁ hC₃
  refine ⟨K, hK, ?_⟩
  intro N p Q f S q r lo hi hAP hp hlam hU12 hU6 η hη hII
  obtain ⟨L, M, hNL, hL3, hNM, hM3, hLMlow, hLM, hfour⟩ := hII
  have hp0 : 0 ≤ p := by linarith
  have hN3 := three_le_of_twelve_le_log hU12
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNe : (N : ℝ) = Real.exp (Real.log N) := (Real.exp_log hNpos).symm
  have hpU : p ≤ Real.log N / 6 := by
    linarith only [le_pow_K hp0 hK, hU6]
  have hq3 : q ^ 3 ≤ N := q_pow_three_le hNe hp0 hAP.q_le hpU
  have hptp : p ≤ 30 * p + 50 := by linarith
  obtain ⟨hbias, hA1, hA2, hL2, hpphr, hphr1, hA', hbP, hNfin⟩ := typeII_numerics hC₂ hC₁ hC₃ hπ
    (N := N) (q := q) (L := L) (M := M) (U := Real.log N) rfl hp hlam hU12 hU6 (hKn p hp).2 hNe hη
    hAP.one_le_q hAP.q_le hNL hNM hLMlow
  have hη0 : 0 < η := by
    rw [hη]
    have : 0 < Real.log N := by linarith
    positivity
  have hX := hext (S.mono hptp) hAP.one_le_q (hAP.q_le.trans (Real.exp_le_exp.mpr hptp)) r lo hi
    (N := N) (L := L) (M := M) (η := η) hη0 hq3 hNM hLM hfour hbias (A := ATII η N q M)
    le_rfl hA1 hA2 hL2
  have key := hcell (S.mono hpphr) (A := ATII η N q M * L / 2) hphr1 hA' hX
  exact ⟨ATII η N q M * L / 2, (phrT C₁ C₂ p η N q + C₃) ^ C₃, by
    have := hphr1; positivity, by linarith, hNfin, key⟩

end PrimeCarleson.Proof.Fplus31
