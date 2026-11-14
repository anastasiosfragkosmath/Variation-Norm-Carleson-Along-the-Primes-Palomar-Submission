module

public import PrimeCarleson.Proof.Fplus31.C2.IterationCells
public import PrimeCarleson.Proof.Fplus31.C2.IterationParams
public import PrimeCarleson.Proof.Fplus31.C2.TypeIChain

/-!
# The iteration, the type I step with budgets

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). From the
type I output of the Vaughan decomposition for the state (`η = 3 log N e^{-p}`,
`δ = η / (2^13 (1 + log N)^3)`):

1. `type_one_extrapolation` (the type I step, the engine of `G1/Compose.lean` and the extrapolation
   step) for `S` at the level `p̃ = 30 p + 50` (so that `e^{-p̃} ≤ δ / 3`) and the scale
   `A = δ N / (q L) ≥ e^{U/3 - p̃ - p}` (`U = log N`, by `L ≤ N^{2/3}`), giving the extrapolated
   symbol factorization of the undilated symbol at the scale `A L / 2 = δ N / (2 q)`;
2. `cellOutput_of_extrapolated`: the sub-step for every window centre, with the scale
   `A L / 2 ≥ e^{U - p̃ - p} ≥ N e^{-b}` for the budget `b`.

All the levels are polynomial in `p` and bounded by `P = (p + K)^K` with `6 P ≤ U`
(`PB`, `IterationBudget.lean`).
-/

@[expose] public noncomputable section

open OAI OAI.Erdos3
open scoped TensorProduct BigOperators

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open Module NilpotentLieFiltration Finset

/-- **The scale of the type I step**: for `N = e^U`, `q ≤ e^p`, `L ≤ e^{2U/3}` and `δ ≥ e^{-t}`,
`δ N / (q L) ≥ e^{U/3 - t - p}`. -/
theorem scale_typeI_A {N q L : ℕ} {U p t δ : ℝ} (hN : (N : ℝ) = Real.exp U) (hq1 : 1 ≤ q)
    (hq : (q : ℝ) ≤ Real.exp p) (hL1 : 1 ≤ L) (hL : (L : ℝ) ≤ Real.exp (2 * U / 3))
    (hδ : Real.exp (-t) ≤ δ) :
    Real.exp (U / 3 - t - p) ≤ δ * ((N : ℝ) / (q * L)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL1
  have h1 : Real.exp (U / 3 - p) ≤ (N : ℝ) / (q * L) := by
    rw [le_div_iff₀ (by positivity), hN]
    have : (q : ℝ) * L ≤ Real.exp p * Real.exp (2 * U / 3) :=
      mul_le_mul hq hL hL0.le (Real.exp_pos _).le
    calc Real.exp (U / 3 - p) * (q * L) ≤
          Real.exp (U / 3 - p) * (Real.exp p * Real.exp (2 * U / 3)) :=
          mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
      _ = Real.exp U := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc Real.exp (U / 3 - t - p) = Real.exp (-t) * Real.exp (U / 3 - p) := by
        rw [← Real.exp_add]; congr 1; ring
    _ ≤ δ * ((N : ℝ) / (q * L)) :=
        mul_le_mul hδ h1 (Real.exp_pos _).le ((Real.exp_pos _).le.trans hδ)

/-- **The scale after the extrapolation**: `δ N / (2 q) ≥ N e^{-t - p}` for `δ ≥ e^{-t}`
(in fact `δ N / (2 q) ≥ N e^{-(t + p)} / 2`; we only use it with `δ ≥ 3 e^{-t}`). -/
theorem scale_typeI_A' {N q : ℕ} {p t δ : ℝ} (hq1 : 1 ≤ q) (hq : (q : ℝ) ≤ Real.exp p)
    (hδ : 3 * Real.exp (-t) ≤ δ) :
    (N : ℝ) * Real.exp (-(t + p)) ≤ δ * N / (2 * q) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  rw [le_div_iff₀ (by positivity)]
  have h1 : Real.exp (-(t + p)) * (2 * q) ≤ Real.exp (-(t + p)) * (2 * Real.exp p) :=
    mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  have h2 : Real.exp (-(t + p)) * (2 * Real.exp p) = 2 * Real.exp (-t) := by
    rw [mul_comm 2, ← mul_assoc, ← Real.exp_add]
    have : -(t + p) + p = -t := by ring
    rw [this]; ring
  have h3 : (N : ℝ) * Real.exp (-(t + p)) * (2 * q) ≤ N * (2 * Real.exp (-t)) := by
    calc (N : ℝ) * Real.exp (-(t + p)) * (2 * q) = N * (Real.exp (-(t + p)) * (2 * q)) := by ring
      _ ≤ N * (Real.exp (-(t + p)) * (2 * Real.exp p)) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg N)
      _ = N * (2 * Real.exp (-t)) := by rw [h2]
  have h4 : (N : ℝ) * (2 * Real.exp (-t)) ≤ δ * N := by
    have := mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg (α := ℝ) N)
    have hpos : 0 ≤ (N : ℝ) * Real.exp (-t) := by positivity
    linarith only [this, hpos]
  linarith

/-- `q ≤ e^p`, `p ≤ U / 6` and `N = e^U` give `q^3 ≤ N`. -/
theorem q_pow_three_le {N q : ℕ} {U p : ℝ} (hN : (N : ℝ) = Real.exp U) (hp : 0 ≤ p)
    (hq : (q : ℝ) ≤ Real.exp p) (hpU : p ≤ U / 6) : q ^ 3 ≤ N := by
  have h1 : (q : ℝ) ^ 3 ≤ Real.exp p ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg q) hq 3
  have h2 : Real.exp p ^ 3 = Real.exp (3 * p) := by
    rw [← Real.exp_nat_mul]; congr 1
  have h3 : Real.exp (3 * p) ≤ Real.exp U := Real.exp_le_exp.mpr (by linarith)
  have : (q : ℝ) ^ 3 ≤ N := by rw [hN]; linarith
  exact_mod_cast this

/-- `q ≤ e^p ≤ e^{U/6}` and `L^3 ≤ N^2` give `q L ≤ N`. -/
theorem q_mul_L_le {N q L : ℕ} {U p : ℝ} (hN : (N : ℝ) = Real.exp U) (hp : 0 ≤ p)
    (hq : (q : ℝ) ≤ Real.exp p) (hpU : p ≤ U / 6) (hL3 : L ^ 3 ≤ N ^ 2) : q * L ≤ N := by
  have hq3 : q ^ 3 ≤ N := by
    have h1 : (q : ℝ) ^ 3 ≤ Real.exp p ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg q) hq 3
    have h2 : Real.exp p ^ 3 = Real.exp (3 * p) := by
      rw [← Real.exp_nat_mul]; congr 1
    have h3 : Real.exp (3 * p) ≤ Real.exp U := Real.exp_le_exp.mpr (by linarith)
    have : (q : ℝ) ^ 3 ≤ N := by rw [hN]; linarith
    exact_mod_cast this
  have h3 : (q * L) ^ 3 ≤ N ^ 3 := by
    calc (q * L) ^ 3 = q ^ 3 * L ^ 3 := by ring
      _ ≤ N * N ^ 2 := Nat.mul_le_mul hq3 hL3
      _ = N ^ 3 := by ring
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h3

/-- `L^3 ≤ N^2 = e^{2U}` gives `L ≤ e^{2U/3}`. -/
theorem L_le_exp {N L : ℕ} {U : ℝ} (hN : (N : ℝ) = Real.exp U) (hL3 : L ^ 3 ≤ N ^ 2) :
    (L : ℝ) ≤ Real.exp (2 * U / 3) := by
  have h1 : (L : ℝ) ^ 3 ≤ (N : ℝ) ^ 2 := by exact_mod_cast hL3
  have h2 : (N : ℝ) ^ 2 = Real.exp (2 * U / 3) ^ 3 := by
    rw [hN, ← Real.exp_nat_mul, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [h2] at h1
  exact le_of_pow_le_pow_left₀ (by norm_num) (Real.exp_pos _).le h1

/-- `x ≥ 2` gives `2 x ≤ x^4`. -/
theorem two_mul_le_pow_four {x : ℝ} (hx : 2 ≤ x) : 2 * x ≤ x ^ 4 := by
  have h1 : 4 ≤ x ^ 2 := by nlinarith
  have h2 : 2 ≤ x ^ 3 := by nlinarith
  nlinarith

/-- `x ≥ 2` gives `4 x ≤ x^4`. -/
theorem four_mul_le_pow_four {x : ℝ} (hx : 2 ≤ x) : 4 * x ≤ x ^ 4 := by
  have h3 : (2 : ℝ) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx 3
  calc 4 * x ≤ x ^ 3 * x := mul_le_mul_of_nonneg_right (by norm_num at h3; linarith) (by linarith)
    _ = x ^ 4 := by ring

/-- **The type I step with budgets.** From the type I output of the Vaughan decomposition for a
`LengStart` state at the level `p` (`η = 3 log N e^{-p}`), the sub-step for every window centre, at
the scale `A` with `N ≤ A e^b` and `b ≤ (p + K)^K`, provided `6 (p + K)^K ≤ log N`. -/
theorem typeI_cell (s : ℕ) (hs : s ≤ 1) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {N : ℕ} {p : ℝ} {Q : Finset (Unit → ℤ)} {f : (Unit → ℤ) → ℂ}
      (S : LengStart (s + 1) Q f p) {q : ℕ} {r lo hi : ℤ}, APInv N p q r lo hi → 1 ≤ p →
      Real.log (1 + Real.log N) ≤ p → 12 ≤ Real.log N → 6 * (p + K) ^ K ≤ Real.log N →
      ∀ {η : ℝ}, η = 3 * Real.log N * Real.exp (-p) →
      (∃ N' ≤ N, ∃ L : ℕ, 1 ≤ L ∧ L ^ 3 ≤ N ^ 2 ∧ ∃ Λ' : Finset ℕ,
        (∀ ℓ ∈ Λ', (L : ℝ) / 2 < ℓ ∧ (ℓ : ℝ) ≤ L) ∧
        η / (2 ^ 13 * (1 + Real.log N) ^ 3) * L ≤ Λ'.card ∧
        ∀ ℓ ∈ Λ', η / (2 ^ 13 * (1 + Real.log N) ^ 3) * ((N : ℝ) / L) ≤
          ‖∑ n ∈ Icc 1 ⌊(N' : ℝ) / ℓ⌋₊, typeISequence S.T q r lo hi ((ℓ : ℤ) * n)‖) →
      ∃ A b : ℝ, 0 ≤ b ∧ b ≤ (p + K) ^ K ∧ (N : ℝ) ≤ A * Real.exp b ∧
        ∀ z : ℤ, CellOutput s (fun x => S.T.eval (fun _ => x + z)) (CommKilled S.η) A b := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hext⟩ := type_one_extrapolation (s + 1) (by omega) (by omega)
  obtain ⟨C₃, hC₃, hcell⟩ := cellOutput_of_extrapolated s hs
  have hC₁R : (2 : ℝ) ≤ C₁ := by exact_mod_cast hC₁
  have hC₃R : (2 : ℝ) ≤ C₃ := by exact_mod_cast hC₃
  -- the budget functions
  have hpt : PB (fun p : ℝ => 30 * p + 50) :=
    ((PB.const 30 (by norm_num)).mul PB.id).add (PB.const 50 (by norm_num))
  have hpt1 : ∀ p : ℝ, 1 ≤ p → 1 ≤ 30 * p + 50 := fun p hp => by linarith only [hp]
  have hpt2 : PB (fun p : ℝ => (30 * p + 50 + C₁) ^ C₁) := (PB.step C₁).comp hpt hpt1
  have hb1 : PB (fun p : ℝ => (30 * p + 50 + C₁) ^ C₁ + 2 * (30 * p + 50) + 1) :=
    (hpt2.add ((PB.const 2 (by norm_num)).mul hpt)).add (PB.const 1 zero_le_one)
  have hph : PB (fun p : ℝ => C₂ * ((30 * p + 50 + C₁) ^ C₁ + 2 * (30 * p + 50) + 1) ^ 4) :=
    (PB.const C₂ (by linarith only [hC₂])).mul (hb1.npow 4)
  have hph1 : ∀ p : ℝ, 1 ≤ p → 1 ≤ C₂ * ((30 * p + 50 + C₁) ^ C₁ + 2 * (30 * p + 50) + 1) ^ 4 :=
    fun p hp => by
      have h1 : (1 : ℝ) ≤ (30 * p + 50 + C₁) ^ C₁ + 2 * (30 * p + 50) + 1 := by
        have : (0 : ℝ) ≤ (30 * p + 50 + C₁) ^ C₁ := by positivity
        linarith only [this, hp]
      exact one_le_mul_of_one_le_of_one_le hC₂ (one_le_pow₀ h1)
  have hbb : PB (fun p : ℝ =>
      (C₂ * ((30 * p + 50 + C₁) ^ C₁ + 2 * (30 * p + 50) + 1) ^ 4 + C₃) ^ C₃) :=
    (PB.step C₃).comp hph hph1
  have h3 : PB (fun p : ℝ => C₂ * ((30 * p + 50 + C₁) ^ C₁ + 2 * (30 * p + 50)) ^ 3) :=
    (PB.const C₂ (by linarith only [hC₂])).mul
      ((hpt2.add ((PB.const 2 (by norm_num)).mul hpt)).npow 3)
  have hneedPB : PB (fun p : ℝ =>
      (C₂ * ((30 * p + 50 + C₁) ^ C₁ + 2 * (30 * p + 50) + 1) ^ 4 + C₃) ^ C₃ +
        C₂ * ((30 * p + 50 + C₁) ^ C₁ + 2 * (30 * p + 50)) ^ 3 + (30 * p + 50 + C₁) ^ C₁ +
        (30 * p + 50) + p) :=
    (((hbb.add h3).add hpt2).add hpt).add PB.id
  obtain ⟨K, hK, hKn⟩ := hneedPB
  refine ⟨K, hK, ?_⟩
  intro N p Q f S q r lo hi hAP hp hlam hU12 hU6 η hη hI
  obtain ⟨N', hN', L, hL1, hL3, Λ', hΛ, hcard, hsum⟩ := hI
  have hp0 : 0 ≤ p := by linarith only [hp]
  have hN3 := three_le_of_twelve_le_log hU12
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set U := Real.log N with hU
  have hNe : (N : ℝ) = Real.exp U := (Real.exp_log hNpos).symm
  have hneed := (hKn p hp).2
  set pt : ℝ := 30 * p + 50 with hpt_def
  have hpt0 : 0 ≤ pt := by rw [hpt_def]; linarith only [hp0]
  have hptp : p ≤ pt := by rw [hpt_def]; linarith only [hp0]
  set pt2 : ℝ := (pt + C₁) ^ C₁ with hpt2_def
  have hpt2_0 : 0 ≤ pt2 := by positivity
  have hpt_pt2 : pt ≤ pt2 := by
    have h1 : (1 : ℝ) ≤ pt + C₁ := by linarith only [hpt0, hC₁R]
    calc pt ≤ pt + C₁ := by linarith only [hC₁R, hpt0]
      _ ≤ pt2 := le_self_pow₀ h1 (by omega)
  set phb : ℝ := C₂ * (pt2 + 2 * pt + 1) ^ 4 with hphb
  have hphb0 : 0 ≤ phb := by positivity
  set bbb : ℝ := (phb + C₃) ^ C₃ with hbbb
  have hbbb0 : 0 ≤ bbb := by positivity
  set th3 : ℝ := C₂ * (pt2 + 2 * pt) ^ 3 with hth3
  have hth30 : 0 ≤ th3 := by positivity
  set P : ℝ := (p + K) ^ K with hP
  have hpU : p ≤ U / 6 := by
    linarith only [hneed, hU6, hbbb0, hth30, hpt2_0, hpt0]
  have hsmallU : bbb + th3 + pt2 + pt + p ≤ U / 6 := by linarith only [hneed, hU6]
  -- parameters
  set δ : ℝ := η / (2 ^ 13 * (1 + U) ^ 3) with hδ
  obtain ⟨hδ1, hδ3, -, -⟩ := param_bounds hU12 hp0 hlam hη hδ
  have hδe : Real.exp (-pt) ≤ δ := by
    have := Real.exp_pos (-pt)
    linarith only [this, hδ3]
  have hδpos : 0 < δ := lt_of_lt_of_le (Real.exp_pos _) hδe
  have hqE : (q : ℝ) ≤ Real.exp pt := hAP.q_le.trans (Real.exp_le_exp.mpr hptp)
  have hq1 := hAP.one_le_q
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hqL : q * L ≤ N := q_mul_L_le hNe hp0 hAP.q_le hpU hL3
  have hLexp := L_le_exp hNe hL3
  set S₁ := S.mono hptp with hS₁
  set A : ℝ := δ * ((N : ℝ) / (q * L)) with hA
  -- the logarithm of `q / δ`
  have hlogq : Real.log (1 / (δ / q)) ≤ 2 * pt := by
    have h1 : 1 / (δ / q) ≤ Real.exp (pt + pt) := by
      rw [one_div_div, div_le_iff₀ hδpos]
      calc (q : ℝ) ≤ Real.exp pt := hqE
        _ = Real.exp (pt + pt) * Real.exp (-pt) := by rw [← Real.exp_add]; congr 1; ring
        _ ≤ Real.exp (pt + pt) * δ := mul_le_mul_of_nonneg_left hδe (Real.exp_pos _).le
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_exp] at h2
    linarith only [h2]
  have hδq1 : δ / q ≤ 1 := by
    rw [div_le_one hq0]
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    linarith only [this, hδ1]
  have hlogq0 : 0 ≤ Real.log (1 / (δ / q)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    linarith only [hδq1]
  have hA1 : Real.exp ((pt + C₁) ^ C₁) ≤ A := by
    refine le_trans (Real.exp_le_exp.mpr ?_) (scale_typeI_A hNe hq1 hAP.q_le hL1 hLexp hδe)
    linarith only [hsmallU, hbbb0, hth30, hU12]
  have hA2 : Real.exp (C₂ * (((pt + C₁) ^ C₁) + Real.log (1 / (δ / q))) ^ 3) ≤ A := by
    refine le_trans (Real.exp_le_exp.mpr ?_) (scale_typeI_A hNe hq1 hAP.q_le hL1 hLexp hδe)
    have h1 : C₂ * (pt2 + Real.log (1 / (δ / q))) ^ 3 ≤ th3 := by
      rw [hth3]
      have hb0 : 0 ≤ pt2 + Real.log (1 / (δ / q)) := by linarith only [hpt2_0, hlogq0]
      have hb1 : pt2 + Real.log (1 / (δ / q)) ≤ pt2 + 2 * pt := by linarith only [hlogq]
      have hC20 : 0 ≤ C₂ := by linarith only [hC₂]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hb1 3) hC20
    linarith only [h1, hsmallU, hbbb0, hpt2_0, hU12]
  have hX := hext S₁ hq1 hqE r lo hi (N := N) (N' := N') (L := L) (by omega) hN' hL1 hqL
    (δ := δ) hδpos hδ1 (by linarith only [hδ3]) (Λ := Λ') hΛ hcard hsum (A := A) le_rfl hA1 hA2
  set phr : ℝ := C₂ * (pt2 + Real.log (1 / (δ / q)) + 1) ^ 4 with hphr
  have hbase1 : 1 ≤ pt2 + Real.log (1 / (δ / q)) + 1 := by linarith only [hpt2_0, hlogq0]
  have hphr_big : 2 * pt ≤ phr := by
    have hb2 : 2 ≤ pt2 + Real.log (1 / (δ / q)) + 1 := by
      linarith only [hpt_pt2, hpt_def, hp, hlogq0]
    have := two_mul_le_pow_four hb2
    have h3 : (pt2 + Real.log (1 / (δ / q)) + 1) ^ 4 ≤ phr := by
      have hb0 : 0 ≤ (pt2 + Real.log (1 / (δ / q)) + 1) ^ 4 := by
        have : 0 ≤ pt2 + Real.log (1 / (δ / q)) + 1 := by linarith only [hpt2_0, hlogq0]
        exact pow_nonneg this 4
      rw [hphr]
      exact le_mul_of_one_le_left hb0 hC₂
    linarith only [this, h3, hpt_pt2, hlogq0]
  have hphr_le : phr ≤ phb := by
    have hb0 : 0 ≤ pt2 + Real.log (1 / (δ / q)) + 1 := by linarith only [hpt2_0, hlogq0]
    have hb1 : pt2 + Real.log (1 / (δ / q)) + 1 ≤ pt2 + 2 * pt + 1 := by linarith only [hlogq]
    have hC20 : 0 ≤ C₂ := by linarith only [hC₂]
    rw [hphr, hphb]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hb1 4) hC20
  have hphr0 : 0 ≤ phr := by linarith only [hphr_big, hpt0]
  have hphr1 : 1 ≤ phr := by linarith only [hphr_big, hpt_def, hp]
  have hpphr : p ≤ phr := by linarith only [hphr_big, hptp, hpt0]
  set S₂ := S.mono hpphr with hS₂
  have hAL : A * L / 2 = δ * N / (2 * q) := by
    rw [hA]
    have : (L : ℝ) ≠ 0 := by positivity
    field_simp
  have hbphr : (phr + C₃) ^ C₃ ≤ bbb := by
    have hb0 : 0 ≤ phr + C₃ := by linarith only [hphr0, hC₃R]
    have hb1 : phr + C₃ ≤ phb + C₃ := by linarith only [hphr_le]
    rw [hbbb]
    exact pow_le_pow_left₀ hb0 hb1 _
  have hA' : Real.exp ((phr + C₃) ^ C₃) ≤ A * L / 2 := by
    rw [hAL]
    have h1 := scale_typeI_A' (N := N) (p := p) (t := pt) hq1 hAP.q_le hδ3
    have h2 : (N : ℝ) * Real.exp (-(pt + p)) = Real.exp (U - (pt + p)) := by
      rw [hNe, ← Real.exp_add]; congr 1
    have h1' : Real.exp (U - (pt + p)) ≤ δ * N / (2 * q) := by rw [← h2]; exact h1
    refine le_trans (Real.exp_le_exp.mpr ?_) h1'
    linarith only [hbphr, hsmallU, hth30, hpt2_0, hU12]
  have key := hcell S₂ (A := A * L / 2) hphr1 hA' hX
  refine ⟨A * L / 2, (phr + C₃) ^ C₃, by positivity, ?_, ?_, key⟩
  · linarith only [hbphr, hneed, hth30, hpt2_0, hpt0, hp0]
  · rw [hAL]
    have h1 := scale_typeI_A' (N := N) (p := p) (t := pt) hq1 hAP.q_le hδ3
    have h2 : pt + p ≤ (phr + C₃) ^ C₃ := by
      have hge : 1 ≤ phr + C₃ := by linarith only [hphr1, hC₃R]
      have hC3 : C₃ ≠ 0 := by omega
      have : phr + C₃ ≤ (phr + C₃) ^ C₃ := le_self_pow₀ hge hC3
      linarith only [this, hphr_big, hptp, hC₃R]
    have h3 : (N : ℝ) = (N : ℝ) * Real.exp (-(pt + p)) * Real.exp (pt + p) := by
      rw [mul_assoc, ← Real.exp_add]; simp
    have h4 : 0 ≤ δ * N / (2 * q) := by positivity
    have h5 : (N : ℝ) * Real.exp (-(pt + p)) * Real.exp (pt + p) ≤
        δ * N / (2 * q) * Real.exp ((phr + C₃) ^ C₃) :=
      mul_le_mul h1 (Real.exp_le_exp.mpr h2) (Real.exp_pos _).le h4
    exact h3.le.trans h5

end PrimeCarleson.Proof.Fplus31
