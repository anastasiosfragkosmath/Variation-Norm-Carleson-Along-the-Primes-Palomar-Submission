module

public import PrimeCarleson.Proof.Fplus31.C2.IterationTypeII

/-!
# The iteration, one stage

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). The
stages of the iteration, for `F = normLam N` and a regime `Reg N P`:

* `exists_cell_output`: the type I or type II step (the Vaughan decomposition, `typeI_cell` and
  `typeII_cell`) for a `LengStart` state: the cell approximations of the sub-step at a scale `A`
  with `N ≤ A e^b`;
* `stay_step`, `drop_step`: the pigeonhole `exists_next_ap` with the stay and drop outputs;

`IterationChain.lean` composes these stages:

* `ls_step`, `lsf_step`: a `LengStart` state goes to a flagged `LengStart` state of the same
  degree (stay; `CommKilled` holds on the refiltered sub-model) or to a niltest state of the next
  lower degree (drop, or the zero-frequency descent); with the flag only the latter;
* `ns_step`: The start step again after a degree drop (`exists_leng_start_or_top_invariant`);
* `ns_zero_false`: the terminal case, a degree-zero niltest is constant, against the prime number
  theorem in progressions.
-/

@[expose] public noncomputable section

open OAI OAI.Erdos3
open scoped TensorProduct BigOperators

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open Module NilpotentLieFiltration Finset

/-- **The cell output of the type I or type II step** for a `LengStart` state. -/
theorem exists_cell_output (s : ℕ) (hs : s ≤ 1) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {N : ℕ} {p : ℝ} {Q : Finset (Unit → ℤ)} {f : (Unit → ℤ) → ℂ}
      (S : LengStart (s + 1) Q f p) {q : ℕ} {r lo hi : ℤ}, APInv N p q r lo hi → 1 ≤ p →
      Real.log (1 + Real.log N) ≤ p → Reg N ((p + K) ^ K) →
      (N : ℝ) * Real.exp (-p) ≤
        ‖∑ x ∈ apInt q r lo hi, normLam N x * star (S.T.eval fun _ => x)‖ →
      ∃ A b : ℝ, 0 ≤ b ∧ b ≤ (p + K) ^ K ∧ (N : ℝ) ≤ A * Real.exp b ∧
        ∀ z : ℤ, CellOutput s (fun x => S.T.eval (fun _ => x + z)) (CommKilled S.η) A b := by
  obtain ⟨K₁, hK₁, h₁⟩ := typeI_cell s hs
  obtain ⟨K₂, hK₂, h₂⟩ := typeII_cell s hs
  refine ⟨max K₁ K₂, le_trans hK₁ (le_max_left _ _), ?_⟩
  intro N p Q f S q r lo hi hAP hp hlam hReg hsum
  have hp0 : 0 ≤ p := by linarith
  have hm₁ : (p + K₁) ^ K₁ ≤ (p + (max K₁ K₂ : ℕ)) ^ (max K₁ K₂) :=
    pow_K_mono hp0 hK₁ (le_max_left _ _)
  have hm₂ : (p + K₂) ^ K₂ ≤ (p + (max K₁ K₂ : ℕ)) ^ (max K₁ K₂) :=
    pow_K_mono hp0 hK₂ (le_max_right _ _)
  have hpP : p ≤ (p + (max K₁ K₂ : ℕ)) ^ (max K₁ K₂) :=
    (le_pow_K hp0 hK₁).trans hm₁
  have hdich := c3_dichotomy S hAP hpP hReg hsum (η := 3 * Real.log N * Real.exp (-p)) rfl
  obtain ⟨hU12, hU6, -, -⟩ := hReg
  rcases hdich with hI | hII
  · obtain ⟨A, b, hb0, hb, hA, hcell⟩ := h₁ S hAP hp hlam hU12 (by linarith) rfl hI
    exact ⟨A, b, hb0, hb.trans hm₁, hA, hcell⟩
  · obtain ⟨A, b, hb0, hb, hA, hcell⟩ := h₂ S hAP hp hlam hU12 (by linarith) rfl hII
    exact ⟨A, b, hb0, hb.trans hm₂, hA, hcell⟩

/-- **The stay output of the pigeonhole**: a vertical niltest with the flag on a new progression. -/
theorem stay_step {N : ℕ} {F : ℤ → ℂ} (hF : ∀ n ∈ Finset.Icc (1 : ℤ) N, ‖F n‖ ≤ 1)
    {s : ℕ} {p b A : ℝ} (hp : 0 ≤ p) (hb : 0 ≤ b) {q : ℕ} {r lo hi : ℤ}
    (hAP : APInv N p q r lo hi) (e : ℤ → ℂ) (he : ∀ n, ‖e n‖ ≤ 1)
    (hΘ : (N : ℝ) * Real.exp (-p) ≤ ‖∑ n ∈ apInt q r lo hi, F n * star (e n)‖)
    (hA1 : (N : ℝ) ≤ A * Real.exp b) (hreg : 16 ≤ (N : ℝ) * Real.exp (-(2 * p + 3 * b)))
    {flag : Prop} (hcell : ∀ z : ℤ, CellOutput s (fun x => e (x + z)) flag A b) :
    ∃ (q' : ℕ) (r' lo' hi' : ℤ) (V : VerticalNiltest (s + 1) b),
      APInv N (3 * p + 3 * b + 4) q' r' lo' hi' ∧ CommKilled V.η ∧
      (N : ℝ) * Real.exp (-(3 * p + 3 * b + 4)) ≤
        ‖∑ n ∈ apInt q' r' lo' hi', F n * star (V.T.eval fun _ => n)‖ := by
  obtain ⟨q', r', lo', hi', z, v, hAP', hcorr⟩ := exists_next_ap
    (V := {v : VerticalNiltest (s + 1) b // CommKilled v.η})
    (fun v x => v.1.T.eval (fun _ => x)) F e hF he hp hb hAP hΘ hA1 hreg (fun z => by
      obtain ⟨P, hP, hPb, hy⟩ := (hcell z).1
      refine ⟨P, hP, hPb, fun y hy' => ?_⟩
      obtain ⟨V, hk, hV⟩ := hy y hy'
      exact ⟨⟨V, hk⟩, hV⟩)
  have e1 : ∀ n : ℤ, (v.1.shift (-z)).T.eval (fun _ => n) = v.1.T.eval (fun _ => n - z) :=
    fun n => by rw [VerticalNiltest.eval_shift, sub_eq_add_neg]
  have hsum : ∑ n ∈ apInt q' r' lo' hi', F n * star ((v.1.shift (-z)).T.eval fun _ => n) =
      ∑ n ∈ apInt q' r' lo' hi', F n * star (v.1.T.eval fun _ => n - z) :=
    Finset.sum_congr rfl fun n _ => by rw [e1 n]
  refine ⟨q', r', lo', hi', v.1.shift (-z), hAP', v.2, ?_⟩
  rw [hsum]
  exact hcorr

/-- **The drop output of the pigeonhole**: a niltest of degree `s` on a new progression. -/
theorem drop_step {N : ℕ} {F : ℤ → ℂ} (hF : ∀ n ∈ Finset.Icc (1 : ℤ) N, ‖F n‖ ≤ 1)
    {s : ℕ} {p b A : ℝ} (hp : 0 ≤ p) (hb : 0 ≤ b) {q : ℕ} {r lo hi : ℤ}
    (hAP : APInv N p q r lo hi) (e : ℤ → ℂ) (he : ∀ n, ‖e n‖ ≤ 1)
    (hΘ : (N : ℝ) * Real.exp (-p) ≤ ‖∑ n ∈ apInt q r lo hi, F n * star (e n)‖)
    (hA1 : (N : ℝ) ≤ A * Real.exp b) (hreg : 16 ≤ (N : ℝ) * Real.exp (-(2 * p + 3 * b)))
    {flag : Prop} (hcell : ∀ z : ℤ, CellOutput s (fun x => e (x + z)) flag A b) (hflag : flag) :
    ∃ (q' : ℕ) (r' lo' hi' : ℤ) (n : NiltestData s),
      APInv N (3 * p + 3 * b + 4) q' r' lo' hi' ∧ n.T.ComplexityLE b ∧ n.T.normBound ≤ 1 ∧
      (N : ℝ) * Real.exp (-(3 * p + 3 * b + 4)) ≤
        ‖∑ n' ∈ apInt q' r' lo' hi', F n' * star (n.T.eval fun _ => n')‖ := by
  obtain ⟨q', r', lo', hi', z, v, hAP', hcorr⟩ := exists_next_ap
    (V := {n : NiltestData s // n.T.ComplexityLE b ∧ n.T.normBound ≤ 1})
    (fun v x => v.1.T.eval (fun _ => x)) F e hF he hp hb hAP hΘ hA1 hreg (fun z => by
      obtain ⟨P, hP, hPb, hy⟩ := (hcell z).2 hflag
      refine ⟨P, hP, hPb, fun y hy' => ?_⟩
      obtain ⟨V, hc, hn, hV⟩ := hy y hy'
      exact ⟨⟨V, hc, hn⟩, hV⟩)
  have e1 : ∀ n : ℤ, (v.1.shift (-z)).T.eval (fun _ => n) = v.1.T.eval (fun _ => n - z) :=
    fun n => by rw [NiltestData.eval_shift, sub_eq_add_neg]
  have hsum : ∑ n ∈ apInt q' r' lo' hi', F n * star ((v.1.shift (-z)).T.eval fun _ => n) =
      ∑ n ∈ apInt q' r' lo' hi', F n * star (v.1.T.eval fun _ => n - z) :=
    Finset.sum_congr rfl fun n _ => by rw [e1 n]
  refine ⟨q', r', lo', hi', v.1.shift (-z), hAP', v.2.1, v.2.2, ?_⟩
  rw [hsum]
  exact hcorr

end PrimeCarleson.Proof.Fplus31
