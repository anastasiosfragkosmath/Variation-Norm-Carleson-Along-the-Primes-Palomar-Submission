module

public import PrimeCarleson.Proof.Fplus31.C2.IterationLoop

/-!
# The iteration, the transitions between the states

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). The
transitions:

* `step_core`, `ls_step`, `lsf_step`: a `LengStart` state of degree `s + 1` goes to a flagged
  `LengStart` state of degree `s + 1` or to a niltest state of degree `s`; if the flag holds, only
  to the latter (the potential `(degree, flag)`);
* `ns_step`: a niltest state of degree `s + 1` goes to a niltest state of degree `s` or to a
  `LengStart` state of degree `s + 1` (the start step, then the zero-frequency descent);
* `ns_zero_false`: a niltest state of degree zero contradicts the prime number theorem in
  progressions (`TermOK`).
-/

@[expose] public noncomputable section

open OAI OAI.Erdos3
open scoped TensorProduct BigOperators

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open Module NilpotentLieFiltration Finset

/-- The tail of the start step with the flag: a vertical niltest with nonzero top frequency gives a
`LengStart` whose frequency has the flag if that of the niltest has. -/
theorem exists_leng_start_of_vertical' (deg : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {Q : Finset (Unit → ℤ)} {f : (Unit → ℤ) → ℂ} {p : ℝ}
      (V : VerticalNiltest deg p), (∃ z ∈ V.D.filtration.layer deg, V.η z ≠ 0) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ Q, f x * star (V.T.eval x)‖ →
      ∃ S : LengStart deg Q f ((p + C) ^ C), CommKilled V.η → CommKilled S.η := by
  obtain ⟨C, hC, hrebase⟩ := RationalFilteredNilmanifold.exists_controlled_adapted_rebase
  refine ⟨C, hC, ?_⟩
  intro Q f p V hne hcorr
  have hp0 : 0 ≤ p := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  obtain ⟨F, H, hH, hpC, -, hcomp, hfreq⟩ := hrebase V.D hp0 V.complexity.1
  exact ⟨{
    L := V.L
    dim := finrank ℚ V.L
    D := F.model
    omega := F.weight
    hF := F.model_layers
    T := F.rebaseNiltest H hH V.T
    η := V.η
    complexity := hcomp V.T V.complexity
    norm_le := V.norm_le
    eta_height := fun i => hfreq V.η V.eta_height i
    vertical := F.rebaseNiltest_vertical H hH V.T V.η V.vertical
    eta_ne := hne
    corr := (Real.exp_le_exp.mpr (neg_le_neg hpC)).trans hcorr }, fun h => h⟩

/-- **A correlation in the sum form gives the averaged correlation**: from
`N e^{-p} ≤ ‖∑_P F · star E‖` and `P ⊆ [1, N]`, `e^{-p} ≤ ‖𝔼_{P} F · star E‖`. -/
theorem corr_of_sum {N : ℕ} {F : ℤ → ℂ} {p : ℝ} {q : ℕ} {r lo hi : ℤ} (E : (Unit → ℤ) → ℂ)
    (hlo : 1 ≤ lo) (hhi : hi ≤ N) (hN : 0 < N)
    (hΘ : (N : ℝ) * Real.exp (-p) ≤
      ‖∑ n ∈ apInt q r lo hi, F n * star (E fun _ => n)‖) :
    Real.exp (-p) ≤ ‖𝔼 x ∈ apPts q r lo hi, F (x ()) * star (E x)‖ := by
  rw [norm_expect_apPts]
  have hcardN : ((apInt q r lo hi).card : ℝ) ≤ N := by exact_mod_cast card_apInt_le hlo hhi
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hcard0 : 0 < (apInt q r lo hi).card := by
    rcases Nat.eq_zero_or_pos (apInt q r lo hi).card with h | h
    · exfalso
      have hemp : apInt q r lo hi = ∅ := Finset.card_eq_zero.mp h
      rw [hemp] at hΘ
      simp only [Finset.sum_empty, norm_zero] at hΘ
      have : (0 : ℝ) < (N : ℝ) * Real.exp (-p) := by positivity
      linarith
    · exact h
  have hcR : (0 : ℝ) < (apInt q r lo hi).card := by exact_mod_cast hcard0
  rw [le_div_iff₀ hcR]
  calc Real.exp (-p) * (apInt q r lo hi).card ≤ Real.exp (-p) * N :=
        mul_le_mul_of_nonneg_left hcardN (Real.exp_pos _).le
    _ = (N : ℝ) * Real.exp (-p) := mul_comm _ _
    _ ≤ _ := hΘ

/-- **A sum correlation bounds the size of the progression from below.** -/
theorem card_ge_of_sum {F e : ℤ → ℂ} {q : ℕ} {r lo hi : ℤ}
    (hF : ∀ n ∈ apInt q r lo hi, ‖F n‖ ≤ 1) (he : ∀ n, ‖e n‖ ≤ 1) :
    ‖∑ n ∈ apInt q r lo hi, F n * star (e n)‖ ≤ (apInt q r lo hi).card := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ n ∈ apInt q r lo hi, ‖F n * star (e n)‖ ≤ ∑ n ∈ apInt q r lo hi, (1 : ℝ) := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [norm_mul, norm_star]
        calc ‖F n‖ * ‖e n‖ ≤ 1 * 1 := mul_le_mul (hF n hn) (he n) (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
    _ = (apInt q r lo hi).card := by simp

/-- For `N = e^U`, `U ≥ 12` and `0 ≤ x ≤ U / 6`: `16 ≤ N e^{-x}`. -/
theorem sixteen_le_mul_exp {N : ℕ} {U x : ℝ} (hN : (N : ℝ) = Real.exp U) (hU : 12 ≤ U)
    (hx : x ≤ U / 6) : 16 ≤ (N : ℝ) * Real.exp (-x) := by
  rw [hN, ← Real.exp_add]
  have h1 : Real.exp 10 ≤ Real.exp (U + -x) := Real.exp_le_exp.mpr (by linarith)
  have h2 : (2 : ℝ) ^ 10 ≤ Real.exp 10 := by
    have := two_pow_le_exp 10
    simpa using this
  linarith

/-- **After a stay step**: a vertical niltest with the flag on a progression gives a flagged
`LengStart` state of the same degree, or (zero frequency on the top layer) a niltest state of the
next lower degree. -/
theorem vertical_next (s : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {N : ℕ} {F : ℤ → ℂ} {p b : ℝ}, 0 < N → 0 ≤ b → b ≤ p →
      (∀ n ∈ Finset.Icc (1 : ℤ) N, ‖F n‖ ≤ 1) → ∀ (V : VerticalNiltest (s + 1) b)
      {q : ℕ} {r lo hi : ℤ}, APInv N p q r lo hi → CommKilled V.η →
      (N : ℝ) * Real.exp (-p) ≤ ‖∑ n ∈ apInt q r lo hi, F n * star (V.T.eval fun _ => n)‖ →
      LSF N F (s + 1) ((p + K) ^ K) ∨ NS N F s ((p + K) ^ K) := by
  obtain ⟨C₂, hC₂, hvert⟩ := exists_leng_start_of_vertical' (s + 1)
  obtain ⟨C₃, hC₃, hdesc⟩ := exists_topInvariant_descent s
  refine ⟨max C₂ C₃, le_trans hC₂ (le_max_left _ _), ?_⟩
  intro N F p b hN hb0 hbp hF V q r lo hi hAP hkV hs'
  have hp0 : 0 ≤ p := hb0.trans hbp
  have hVe : ∀ n, ‖V.T.eval (fun _ => n)‖ ≤ 1 := fun n =>
    (V.T.norm_le _).trans (by exact_mod_cast V.norm_le)
  have hFP : ∀ n ∈ apInt q r lo hi, ‖F n‖ ≤ 1 := fun n hn => hF n (Finset.mem_Icc.mpr
    ⟨hAP.one_le_lo.trans (mem_apInt.mp hn).1,
      (mem_apInt.mp hn).2.1.trans (by exact_mod_cast hAP.hi_le)⟩)
  have hm₂ : (p + C₂) ^ C₂ ≤ (p + (max C₂ C₃ : ℕ)) ^ (max C₂ C₃) :=
    pow_K_mono hp0 hC₂ (le_max_left _ _)
  have hm₃ : (p + C₃) ^ C₃ ≤ (p + (max C₂ C₃ : ℕ)) ^ (max C₂ C₃) :=
    pow_K_mono hp0 hC₃ (le_max_right _ _)
  have hpC₂ : p ≤ (p + C₂) ^ C₂ := le_pow_K hp0 hC₂
  have hpC₃ : p ≤ (p + C₃) ^ C₃ := le_pow_K hp0 hC₃
  have hcardN : (apInt q r lo hi).card ≤ N := card_apInt_le hAP.one_le_lo hAP.hi_le
  by_cases hne : ∃ z ∈ V.D.filtration.layer (s + 1), V.η z ≠ 0
  · left
    have hcorr := corr_of_sum (F := F) (fun x => V.T.eval x) hAP.one_le_lo hAP.hi_le hN hs'
    obtain ⟨S', hk⟩ := hvert (V.mono hbp) hne hcorr
    have hcard' : (N : ℝ) * Real.exp (-((p + C₂) ^ C₂)) ≤ (apInt q r lo hi).card := by
      calc (N : ℝ) * Real.exp (-((p + C₂) ^ C₂)) ≤ N * Real.exp (-p) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (Nat.cast_nonneg N)
        _ ≤ _ := hs'
        _ ≤ _ := card_ge_of_sum hFP hVe
    refine LSF.mono ⟨q, r, lo, hi, S', hAP.mono hpC₂, hcard', hk hkV⟩ ?_
    linarith
  · right
    push Not at hne
    have hinv : ∀ z ∈ V.D.filtration.realification.subgroup (s + 1), ∀ x,
        V.T.observable (z • x) = V.T.observable x := by
      intro z hz x
      rw [V.vertical z hz x, realifyFunctional_eq_zero_of_mem_subgroup V.D V.η hne z hz]
      simp
    obtain ⟨Nd, -, hc, hn, hev⟩ := hdesc V.D V.T hp0 (V.complexity.mono hbp) hinv
    have hsumeq : ∑ n ∈ apInt q r lo hi, F n * star (Nd.T.eval fun _ => n) =
        ∑ n ∈ apInt q r lo hi, F n * star (V.T.eval fun _ => n) :=
      Finset.sum_congr rfl fun n _ => by rw [hev]
    refine NS.mono ⟨q, r, lo, hi, Nd, hAP.mono hpC₃, hc, ?_, ?_⟩ ?_
    · rw [hn]; exact V.norm_le
    · rw [hsumeq]
      exact le_trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (neg_le_neg hpC₃)) (Nat.cast_nonneg N)) hs'
    · linarith

/-- **One stage from a `LengStart` state.**  A `LengStart` state of degree `s + 1` (`s ≤ 1`) on a
progression goes to a flagged `LengStart` state of degree `s + 1` or to a niltest state of degree
`s`; if the flag `CommKilled S.η` holds, only to the latter. -/
theorem step_core (s : ℕ) (hs : s ≤ 1) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {N : ℕ} {p : ℝ}, 1 ≤ p → Real.log (1 + Real.log N) ≤ p →
      Reg N ((p + K) ^ K) → ∀ {q : ℕ} {r lo hi : ℤ}
      (S : LengStart (s + 1) (apPts q r lo hi) (fun x => normLam N (x ())) p),
      APInv N p q r lo hi → (N : ℝ) * Real.exp (-p) ≤ (apInt q r lo hi).card →
      (LSF N (normLam N) (s + 1) ((p + K) ^ K) ∨ NS N (normLam N) s ((p + K) ^ K)) ∧
      (CommKilled S.η → NS N (normLam N) s ((p + K) ^ K)) := by
  obtain ⟨K₁, hK₁, hcellout⟩ := exists_cell_output s hs
  obtain ⟨Kv, hKv, hvnext⟩ := vertical_next s
  have h2p : PB (fun p : ℝ => 2 * p) := (PB.const 2 (by norm_num)).mul PB.id
  have hB : PB (fun p : ℝ => (2 * p + K₁) ^ K₁) :=
    (PB.step K₁).comp h2p (fun p hp => by linarith)
  have hp₁ : PB (fun p : ℝ => 3 * (2 * p) + 3 * (2 * p + K₁) ^ K₁ + 4) :=
    (((PB.const 3 (by norm_num)).mul h2p).add ((PB.const 3 (by norm_num)).mul hB)).add
      (PB.const 4 (by norm_num))
  have hp₁1 : ∀ p : ℝ, 1 ≤ p → 1 ≤ 3 * (2 * p) + 3 * (2 * p + K₁) ^ K₁ + 4 := fun p hp => by
    have : (0 : ℝ) ≤ (2 * p + K₁) ^ K₁ := by positivity
    linarith
  have hls : PB (fun p : ℝ => (3 * (2 * p) + 3 * (2 * p + K₁) ^ K₁ + 4 + Kv) ^ Kv) :=
    (PB.step Kv).comp hp₁ hp₁1
  have hregb : PB (fun p : ℝ => 4 * p + 3 * (2 * p + K₁) ^ K₁ + 3) :=
    ((((PB.const 4 (by norm_num)).mul PB.id).add ((PB.const 3 (by norm_num)).mul hB)).add
      (PB.const 3 (by norm_num)))
  have hneed : PB (fun p : ℝ =>
      (3 * (2 * p) + 3 * (2 * p + K₁) ^ K₁ + 4 + Kv) ^ Kv +
        (3 * (2 * p) + 3 * (2 * p + K₁) ^ K₁ + 4) + (4 * p + 3 * (2 * p + K₁) ^ K₁ + 3) +
        (2 * p + K₁) ^ K₁ + p) :=
    ((((hls.add hp₁).add hregb).add hB).add PB.id)
  obtain ⟨K, hK, hKn⟩ := hneed
  refine ⟨K, hK, ?_⟩
  intro N p hp hlam hReg q r lo hi S hAP hcard
  have hp0 : 0 ≤ p := by linarith
  have hReg' := hReg
  obtain ⟨hU12, hU6, -, hF⟩ := hReg'
  have hN3 := three_le_of_twelve_le_log hU12
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNe : (N : ℝ) = Real.exp (Real.log N) := (Real.exp_log hNR).symm
  have hneed' := (hKn p hp).2
  set P : ℝ := (p + K) ^ K with hP
  set Bb : ℝ := (2 * p + K₁) ^ K₁ with hBb
  have hBb0 : 0 ≤ Bb := by positivity
  set p₁b : ℝ := 3 * (2 * p) + 3 * Bb + 4 with hp₁b
  set lsb : ℝ := (p₁b + Kv) ^ Kv with hlsb
  have hlsb0 : 0 ≤ lsb := by positivity
  have hp₁b0 : 0 ≤ p₁b := by rw [hp₁b]; linarith
  have hlsbP : lsb ≤ P := by linarith
  have hp₁bP : p₁b ≤ P := by linarith
  have hBbP : Bb ≤ P := by linarith
  have hpP : p ≤ P := by linarith
  -- the cell output at the level `2 p`
  have hp2 : p ≤ 2 * p := by linarith
  have hAP₂ : APInv N (2 * p) q r lo hi := hAP.mono hp2
  have hsum := S.sum_form hcard hNpos
  have hReg₂ : Reg N ((2 * p + K₁) ^ K₁) := hReg.mono (by linarith)
  have hTe : ∀ n, ‖S.T.eval (fun _ => n)‖ ≤ 1 := fun n =>
    (S.T.norm_le _).trans (by exact_mod_cast S.norm_le)
  obtain ⟨A, b, hb0, hb, hA, hcell⟩ := hcellout (S.mono hp2) hAP₂ (by linarith)
    (by linarith) hReg₂ hsum
  have hbp₁ : b ≤ p₁b := by rw [hp₁b]; linarith
  have hreg2 : 16 ≤ (N : ℝ) * Real.exp (-(2 * (2 * p) + 3 * b)) :=
    sixteen_le_mul_exp hNe hU12 (by linarith)
  have hp₁ : 3 * (2 * p) + 3 * b + 4 ≤ p₁b := by rw [hp₁b]; linarith
  -- the niltest state of the drop
  have hdrop : CommKilled S.η → NS N (normLam N) s P := by
    intro hflag
    obtain ⟨q', r', lo', hi', n, hAP', hc, hn, hs'⟩ := drop_step (s := s) hF (p := 2 * p)
      (b := b) (A := A) (by linarith) hb0 hAP₂ (fun x => S.T.eval (fun _ => x)) hTe hsum hA
      hreg2 (flag := CommKilled S.η) hcell hflag
    exact NS.mono ⟨q', r', lo', hi', n, hAP', hc.mono (by linarith), hn, hs'⟩ (by linarith)
  refine ⟨?_, hdrop⟩
  by_cases hflag : CommKilled S.η
  · exact Or.inr (hdrop hflag)
  · obtain ⟨q', r', lo', hi', V, hAP', hkV, hs'⟩ := stay_step (s := s) hF (p := 2 * p)
      (b := b) (A := A) (by linarith) hb0 hAP₂ (fun x => S.T.eval (fun _ => x)) hTe hsum hA
      hreg2 (flag := CommKilled S.η) hcell
    have hv := hvnext hNpos hb0 (show b ≤ 3 * (2 * p) + 3 * b + 4 by linarith) hF V hAP' hkV hs'
    have hle : (3 * (2 * p) + 3 * b + 4 + Kv) ^ Kv ≤ P := by
      have : (3 * (2 * p) + 3 * b + 4 + Kv) ^ Kv ≤ lsb := by
        rw [hlsb]
        exact pow_le_pow_left₀ (by have : (0 : ℝ) ≤ Kv := Nat.cast_nonneg Kv; linarith)
          (by linarith) _
      linarith
    rcases hv with hl | hn
    · exact Or.inl (hl.mono hle)
    · exact Or.inr (hn.mono hle)

/-- A `LengStart` state goes to a flagged `LengStart` state or to a niltest state of lower
degree. -/
theorem ls_step (s : ℕ) (hs : s ≤ 1) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {N : ℕ} {p : ℝ}, 1 ≤ p → Real.log (1 + Real.log N) ≤ p →
      Reg N ((p + K) ^ K) → LS N (normLam N) (s + 1) p →
      LSF N (normLam N) (s + 1) ((p + K) ^ K) ∨ NS N (normLam N) s ((p + K) ^ K) := by
  obtain ⟨K, hK, h⟩ := step_core s hs
  refine ⟨K, hK, fun hp hlam hReg hLS => ?_⟩
  obtain ⟨q, r, lo, hi, S, hAP, hcard⟩ := hLS
  exact (h hp hlam hReg S hAP hcard).1

/-- A flagged `LengStart` state goes to a niltest state of lower degree. -/
theorem lsf_step (s : ℕ) (hs : s ≤ 1) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {N : ℕ} {p : ℝ}, 1 ≤ p → Real.log (1 + Real.log N) ≤ p →
      Reg N ((p + K) ^ K) → LSF N (normLam N) (s + 1) p →
      NS N (normLam N) s ((p + K) ^ K) := by
  obtain ⟨K, hK, h⟩ := step_core s hs
  refine ⟨K, hK, fun hp hlam hReg hLS => ?_⟩
  obtain ⟨q, r, lo, hi, S, hAP, hcard, hk⟩ := hLS
  exact (h hp hlam hReg S hAP hcard).2 hk

/-- **The start step again after a degree drop**: a niltest state of degree `s + 1` goes to a
niltest state of degree `s` (the zero-frequency descent) or to a `LengStart` state of degree
`s + 1`. -/
theorem ns_step (s : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {N : ℕ} {F : ℤ → ℂ} {p : ℝ}, 0 < N → 1 ≤ p →
      (∀ n ∈ Finset.Icc (1 : ℤ) N, ‖F n‖ ≤ 1) → NS N F (s + 1) p →
      NS N F s ((p + K) ^ K) ∨ LS N F (s + 1) ((p + K) ^ K) := by
  obtain ⟨C₁, hC₁, hB0⟩ := exists_leng_start_or_top_invariant
  obtain ⟨C₂, hC₂, hdesc⟩ := exists_topInvariant_descent s
  have h1 : PB (fun p : ℝ => (p + C₁) ^ C₁) := PB.step C₁
  have h2 : PB (fun p : ℝ => ((p + C₁) ^ C₁ + C₂) ^ C₂) :=
    (PB.step C₂).comp h1 (fun p hp => by
      have : (0 : ℝ) ≤ C₁ := Nat.cast_nonneg C₁
      have h3 : (1 : ℝ) ≤ p + C₁ := by linarith
      calc (1 : ℝ) ≤ p + C₁ := h3
        _ ≤ (p + C₁) ^ C₁ := le_self_pow₀ h3 (by omega))
  have hneed : PB (fun p : ℝ => (p + C₁) ^ C₁ + ((p + C₁) ^ C₁ + C₂) ^ C₂ + p) :=
    (h1.add h2).add PB.id
  obtain ⟨K, hK, hKn⟩ := hneed
  refine ⟨K, hK, ?_⟩
  intro N F p hN hp hF hNS
  obtain ⟨q, r, lo, hi, n, hAP, hc, hn, hs⟩ := hNS
  have hp0 : 0 ≤ p := by linarith
  have hneed' := (hKn p hp).2
  set P : ℝ := (p + K) ^ K with hP
  set p₁ : ℝ := (p + C₁) ^ C₁ with hp₁
  set p₂ : ℝ := (p₁ + C₂) ^ C₂ with hp₂
  have hp₁0 : 0 ≤ p₁ := by positivity
  have hp₂0 : 0 ≤ p₂ := by positivity
  have hpp₁ : p ≤ p₁ := le_pow_K hp0 hC₁
  have hfP : ∀ n ∈ apInt q r lo hi, ‖F n‖ ≤ 1 := fun n hn' => hF n (Finset.mem_Icc.mpr
    ⟨hAP.one_le_lo.trans (mem_apInt.mp hn').1,
      (mem_apInt.mp hn').2.1.trans (by exact_mod_cast hAP.hi_le)⟩)
  have hf : ∀ x ∈ apPts q r lo hi, ‖(fun x : Unit → ℤ => F (x ())) x‖ ≤ 1 := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
    exact hfP m hm
  have hTe : ∀ m, ‖n.T.eval (fun _ => m)‖ ≤ 1 := fun m =>
    (n.T.norm_le _).trans (by exact_mod_cast hn)
  have hcard : (N : ℝ) * Real.exp (-p) ≤ (apInt q r lo hi).card :=
    hs.trans (card_ge_of_sum hfP hTe)
  have hcorr := corr_of_sum (F := F) (fun x => n.T.eval x) hAP.one_le_lo hAP.hi_le hN hs
  rcases hB0 n.D (apPts q r lo hi) (fun x => F (x ())) hf n.T hc hn hcorr with hS | hT
  · right
    obtain ⟨S⟩ := hS
    refine LS.mono ⟨q, r, lo, hi, S, hAP.mono hpp₁, le_trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hpp₁)) (Nat.cast_nonneg N))
      hcard⟩ ?_
    linarith
  · left
    obtain ⟨T', hc', hn', hcorr', hinv⟩ := hT
    obtain ⟨Nd, -, hcd, hnd, hev⟩ := hdesc n.D T' hp₁0 hc' hinv
    have hcard0 : (0 : ℝ) < (apInt q r lo hi).card := by
      have : (0 : ℝ) < (N : ℝ) * Real.exp (-p) := by
        have : (0 : ℝ) < N := by exact_mod_cast hN
        positivity
      linarith
    rw [norm_expect_apPts, le_div_iff₀ hcard0] at hcorr'
    set ℓ : ℝ := p₂ + p₁ + p with hℓ
    have hℓP : ℓ ≤ P := by linarith
    refine NS.mono ⟨q, r, lo, hi, Nd, hAP.mono (by linarith), hcd.mono (by linarith), ?_, ?_⟩ hℓP
    · rw [hnd]; exact hn'
    · calc (N : ℝ) * Real.exp (-ℓ) ≤ N * (Real.exp (-p₁) * Real.exp (-p)) :=
            mul_le_mul_of_nonneg_left (by
              rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)) (Nat.cast_nonneg N)
        _ = Real.exp (-p₁) * ((N : ℝ) * Real.exp (-p)) := by ring
        _ ≤ Real.exp (-p₁) * (apInt q r lo hi).card :=
            mul_le_mul_of_nonneg_left hcard (Real.exp_pos _).le
        _ ≤ ‖∑ m ∈ apInt q r lo hi, F m * star (T'.eval fun _ => m)‖ := hcorr'
        _ = ‖∑ m ∈ apInt q r lo hi, F m * star (Nd.T.eval fun _ => m)‖ := by
            congr 1
            exact Finset.sum_congr rfl fun m _ => by rw [hev]

/-- **The terminal condition of the prime number theorem in progressions** at the level `P`: every
progression `⊆ [1, N]` has `‖∑_P normLam N‖ < N e^{-P}`. -/
def TermOK (N : ℕ) (P : ℝ) : Prop :=
  ∀ (q : ℕ) (r lo hi : ℤ), 1 ≤ q → 1 ≤ lo → hi ≤ N →
    ‖∑ x ∈ apInt q r lo hi, normLam N x‖ < N * Real.exp (-P)

/-- **The terminal case**: a niltest state of degree zero contradicts `TermOK`: the niltest is
constant, so the progression correlates with the constant `1`. -/
theorem ns_zero_false {N : ℕ} {P : ℝ} (hNS : NS N (normLam N) 0 P) (hT : TermOK N P) :
    False := by
  obtain ⟨q, r, lo, hi, n, hAP, -, hn, hs⟩ := hNS
  set c : ℂ := n.T.observable (QuotientGroup.mk 1) with hc
  have hev : ∀ x : ℤ, n.T.eval (fun _ => x) = c := fun x =>
    RationalFilteredNilmanifold.Niltest.eval_step_zero n.D n.T _
  have hc1 : ‖c‖ ≤ 1 := by
    rw [← hev 0]
    exact (n.T.norm_le _).trans (by exact_mod_cast hn)
  have h1 : ∑ x ∈ apInt q r lo hi, normLam N x * star (n.T.eval fun _ => x) =
      star c * ∑ x ∈ apInt q r lo hi, normLam N x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hev x, mul_comm]
  have h2 : ‖∑ x ∈ apInt q r lo hi, normLam N x * star (n.T.eval fun _ => x)‖ ≤
      ‖∑ x ∈ apInt q r lo hi, normLam N x‖ := by
    rw [h1, norm_mul, norm_star]
    exact mul_le_of_le_one_left (norm_nonneg _) hc1
  have h3 := hT q r lo hi hAP.one_le_q hAP.one_le_lo hAP.hi_le
  linarith

/-- **No state of the iteration exists** (the unconditional core of the iteration): for the regime
`Reg N P` and the terminal condition `TermOK N P` at the level `P = (p + K)^K`, a state of degree
two (a `LengStart`) or of degree one (a niltest, the zero-frequency start) at the level `p` cannot
exist. Four stages (`ls_step`, `lsf_step`, `ns_step`, `lsf_step`) take a `LengStart` state of degree
two to a niltest state of degree zero, which `ns_zero_false` excludes. -/
theorem no_state : ∃ K : ℕ, 2 ≤ K ∧ ∀ {N : ℕ} {p : ℝ}, 1 ≤ p →
    Real.log (1 + Real.log N) ≤ p → Reg N ((p + K) ^ K) → TermOK N ((p + K) ^ K) →
    (LS N (normLam N) 2 p ∨ NS N (normLam N) 1 p) → False := by
  obtain ⟨Ka, hKa, ha⟩ := ls_step 1 le_rfl
  obtain ⟨Kb, hKb, hb⟩ := lsf_step 1 le_rfl
  obtain ⟨Kc, hKc, hc⟩ := ns_step 0
  obtain ⟨Kd, hKd, hd⟩ := lsf_step 0 (Nat.zero_le 1)
  set K0 : ℕ := max (max Ka Kb) (max Kc Kd) with hK0def
  have hK0 : 2 ≤ K0 := le_trans hKa (le_trans (le_max_left _ _) (le_max_left _ _))
  have hKa' : Ka ≤ K0 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hKb' : Kb ≤ K0 := le_trans (le_max_right _ _) (le_max_left _ _)
  have hKc' : Kc ≤ K0 := le_trans (le_max_left _ _) (le_max_right _ _)
  have hKd' : Kd ≤ K0 := le_trans (le_max_right _ _) (le_max_right _ _)
  set g : ℝ → ℝ := fun p => (p + K0) ^ K0 with hgdef
  have hgge : ∀ x : ℝ, 0 ≤ x → x ≤ g x := fun x hx => le_pow_K hx hK0
  have hg1 : ∀ x : ℝ, 0 ≤ x → 1 ≤ g x := fun x hx => by
    have h2 : (2 : ℝ) ≤ K0 := by exact_mod_cast hK0
    exact one_le_pow₀ (by linarith)
  have hgm : ∀ x y : ℝ, 0 ≤ x → x ≤ y → g x ≤ g y := fun x y hx hxy =>
    pow_le_pow_left₀ (by have : (0 : ℝ) ≤ K0 := Nat.cast_nonneg K0; linarith)
      (by linarith) _
  have hg : PB g := PB.step K0
  have hg2 : PB (fun p => g (g p)) := hg.comp hg (fun p hp => hg1 p (by linarith))
  have hg3 : PB (fun p => g (g (g p))) :=
    hg.comp hg2 (fun p hp => hg1 _ (by have := hg1 p (by linarith); linarith))
  have hg4 : PB (fun p => g (g (g (g p)))) :=
    hg.comp hg3 (fun p hp => hg1 _ (by
      have h1 := hg1 p (by linarith)
      have h2 := hg1 (g p) (by linarith)
      linarith))
  obtain ⟨K, hK, hKgb⟩ := hg4
  refine ⟨K, hK, ?_⟩
  intro N p hp hlam hReg hTerm hstart
  have hp0 : 0 ≤ p := by linarith
  have hN : 0 < N := by
    obtain ⟨hU12, -⟩ := hReg
    have := three_le_of_twelve_le_log hU12
    omega
  have hNorm : ∀ n ∈ Finset.Icc (1 : ℤ) N, ‖normLam N n‖ ≤ 1 := hReg.2.2.2
  set P : ℝ := (p + K) ^ K with hP
  have hP4 : g (g (g (g p))) ≤ P := (hKgb p hp).2
  have e1 : p ≤ g p := hgge p hp0
  have e2 : g p ≤ g (g p) := hgge _ (by linarith)
  have e3 : g (g p) ≤ g (g (g p)) := hgge _ (by linarith)
  have e4 : g (g (g p)) ≤ g (g (g (g p))) := hgge _ (by linarith)
  have hg0 : ∀ x : ℝ, 0 ≤ x → 0 ≤ g x := fun x hx => by have := hg1 x hx; linarith
  -- the common ending: a niltest state of degree one at the level `x` with `g (g x) ≤ P`
  have fromNS1 : ∀ x : ℝ, p ≤ x → g (g x) ≤ P → NS N (normLam N) 1 x → False := by
    intro x hpx hgg hNS
    have hx0 : 0 ≤ x := by linarith
    have hx1 : 1 ≤ x := by linarith
    have hlamx : Real.log (1 + Real.log N) ≤ x := by linarith
    have hcx : (x + Kc) ^ Kc ≤ g x := pow_K_mono hx0 hKc hKc'
    have hxy : g x ≤ g (g x) := hgge _ (hg0 x hx0)
    rcases hc hN hx1 hNorm hNS with h0 | h1
    · exact ns_zero_false (h0.mono (by linarith)) hTerm
    · set y : ℝ := (x + Kc) ^ Kc with hy
      have hy0 : 0 ≤ y := by positivity
      have hy1 : 1 ≤ y := by
        have h2 : (2 : ℝ) ≤ Kc := by exact_mod_cast hKc
        exact one_le_pow₀ (by linarith)
      have hxy' : x ≤ y := le_pow_K hx0 hKc
      have hLSF : LSF N (normLam N) 1 y := by
        obtain ⟨q, r, lo, hi, S, hAP, hcard⟩ := h1
        exact ⟨q, r, lo, hi, S, hAP, hcard, commKilled_of_degree_one S.D.filtration S.η⟩
      have hdy : (y + Kd) ^ Kd ≤ g y := pow_K_mono hy0 hKd hKd'
      have hgy : g y ≤ g (g x) := hgm y (g x) hy0 hcx
      exact ns_zero_false ((hd hy1 (by linarith) (hReg.mono (by linarith)) hLSF).mono
        (by linarith)) hTerm
  rcases hstart with hLS | hNS
  · have hp1 : (p + Ka) ^ Ka ≤ g p := pow_K_mono hp0 hKa hKa'
    rcases ha hp hlam (hReg.mono (by linarith)) hLS with hF | hN1
    · set p₁ : ℝ := (p + Ka) ^ Ka with hp₁
      have hp₁0 : 0 ≤ p₁ := by positivity
      have hpp₁ : p ≤ p₁ := le_pow_K hp0 hKa
      have hp₁1 : 1 ≤ p₁ := by linarith
      have hp₂ : (p₁ + Kb) ^ Kb ≤ g p₁ := pow_K_mono hp₁0 hKb hKb'
      have hgp₁ : g p₁ ≤ g (g p) := hgm p₁ (g p) hp₁0 hp1
      have hNS1 := hb hp₁1 (by linarith) (hReg.mono (by
        have := hgge _ (hg0 p hp0)
        have := hgm (g p₁) (g (g p)) (hg0 p₁ hp₁0) hgp₁
        linarith)) hF
      set p₂ : ℝ := (p₁ + Kb) ^ Kb with hp₂'
      have hp₂0 : 0 ≤ p₂ := by positivity
      have hpp₂ : p ≤ p₂ := by
        have := le_pow_K hp₁0 hKb
        linarith
      have hp₂g : p₂ ≤ g (g p) := by linarith
      exact fromNS1 p₂ hpp₂ (by
        have h5 := hgm p₂ (g (g p)) hp₂0 hp₂g
        have h6 := hgm (g p₂) (g (g (g p))) (hg0 _ hp₂0) h5
        linarith) hNS1
    · set p₁ : ℝ := (p + Ka) ^ Ka with hp₁
      have hp₁0 : 0 ≤ p₁ := by positivity
      have hpp₁ : p ≤ p₁ := le_pow_K hp0 hKa
      exact fromNS1 p₁ hpp₁ (by
        have h5 := hgm p₁ (g p) hp₁0 hp1
        have h6 := hgm (g p₁) (g (g p)) (hg0 _ hp₁0) h5
        linarith) hN1
  · exact fromNS1 p le_rfl (by linarith) hNS

end PrimeCarleson.Proof.Fplus31
