module

public import PrimeCarleson.Proof.Fplus31.C2.IterationCellOutput
public import PrimeCarleson.Proof.Fplus31.C2.IterationStep

/-!
# The iteration, the states

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). For a
function `F : ℤ → ℂ` (bounded by one on `[1, N]`) a state of the iteration is a progression
`P = apInt q r lo hi ⊆ [1, N]` of modulus `q ≤ e^p` and a niltest correlating with `F` on `P`:

* `NS N F s p`: a niltest of degree `s` (`NiltestData`, no frequency), of complexity `p`, with
  `N e^{-p} ≤ ‖∑_P F · star (T.eval)‖`;
* `LS N F s p`: a `LengStart` of degree `s` and complexity `p` on `P` (the vertical frequency `η`
  is nonzero on the top layer), with `|P| ≥ N e^{-p}`; `LSF` adds the flag `CommKilled η`.

The potential is the lexicographic `(degree, flag)`. This file has the monotonicity in `p`, the sum
form of a `LengStart` correlation, the flag at degree one, and `ns_step`, the re-run of the start
step after a degree drop (`exists_leng_start_or_top_invariant`, then the zero-frequency descent).
-/

@[expose] public noncomputable section

open OAI OAI.Erdos3
open scoped TensorProduct BigOperators

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open Module NilpotentLieFiltration Finset

/-- A niltest state of degree `s`. -/
def NS (N : ℕ) (F : ℤ → ℂ) (s : ℕ) (p : ℝ) : Prop :=
  ∃ (q : ℕ) (r lo hi : ℤ) (n : NiltestData s), APInv N p q r lo hi ∧ n.T.ComplexityLE p ∧
    n.T.normBound ≤ 1 ∧
    (N : ℝ) * Real.exp (-p) ≤ ‖∑ x ∈ apInt q r lo hi, F x * star (n.T.eval fun _ => x)‖

/-- A `LengStart` state of degree `s`. -/
def LS (N : ℕ) (F : ℤ → ℂ) (s : ℕ) (p : ℝ) : Prop :=
  ∃ (q : ℕ) (r lo hi : ℤ) (_S : LengStart s (apPts q r lo hi) (fun x => F (x ())) p),
    APInv N p q r lo hi ∧ (N : ℝ) * Real.exp (-p) ≤ (apInt q r lo hi).card

/-- A `LengStart` state with the flag. -/
def LSF (N : ℕ) (F : ℤ → ℂ) (s : ℕ) (p : ℝ) : Prop :=
  ∃ (q : ℕ) (r lo hi : ℤ) (S : LengStart s (apPts q r lo hi) (fun x => F (x ())) p),
    APInv N p q r lo hi ∧ (N : ℝ) * Real.exp (-p) ≤ (apInt q r lo hi).card ∧ CommKilled S.η

/-- `NS` is monotone in `p`. -/
theorem NS.mono {N : ℕ} {F : ℤ → ℂ} {s : ℕ} {p p' : ℝ} (h : NS N F s p) (hp : p ≤ p') :
    NS N F s p' := by
  obtain ⟨q, r, lo, hi, n, hAP, hc, hn, hs⟩ := h
  refine ⟨q, r, lo, hi, n, hAP.mono hp, hc.mono hp, hn, le_trans ?_ hs⟩
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hp)) (Nat.cast_nonneg N)

/-- `LS` is monotone in `p`. -/
theorem LS.mono {N : ℕ} {F : ℤ → ℂ} {s : ℕ} {p p' : ℝ} (h : LS N F s p) (hp : p ≤ p') :
    LS N F s p' := by
  obtain ⟨q, r, lo, hi, S, hAP, hc⟩ := h
  refine ⟨q, r, lo, hi, S.mono hp, hAP.mono hp, le_trans ?_ hc⟩
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hp)) (Nat.cast_nonneg N)

/-- `LSF` is monotone in `p`. -/
theorem LSF.mono {N : ℕ} {F : ℤ → ℂ} {s : ℕ} {p p' : ℝ} (h : LSF N F s p) (hp : p ≤ p') :
    LSF N F s p' := by
  obtain ⟨q, r, lo, hi, S, hAP, hc, hk⟩ := h
  refine ⟨q, r, lo, hi, S.mono hp, hAP.mono hp, le_trans ?_ hc, hk⟩
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hp)) (Nat.cast_nonneg N)

/-- **A `LengStart` correlates on the progression in the sum form**: the average over the points
of the progression is at least `e^{-p}`, so the sum is at least `|P| e^{-p}`. -/
theorem LengStart.sum_form {N : ℕ} {F : ℤ → ℂ} {s : ℕ} {p : ℝ} {q : ℕ} {r lo hi : ℤ}
    (S : LengStart s (apPts q r lo hi) (fun x => F (x ())) p)
    (hc : (N : ℝ) * Real.exp (-p) ≤ (apInt q r lo hi).card) (hN : 0 < N) :
    (N : ℝ) * Real.exp (-(2 * p)) ≤
      ‖∑ x ∈ apInt q r lo hi, F x * star (S.T.eval fun _ => x)‖ := by
  have hcorr := S.corr
  rw [norm_expect_apPts] at hcorr
  have hcard : (0 : ℝ) < (apInt q r lo hi).card := by
    have : (0 : ℝ) < (N : ℝ) * Real.exp (-p) := by positivity
    linarith
  rw [le_div_iff₀ hcard] at hcorr
  have h2 : Real.exp (-(2 * p)) = Real.exp (-p) * Real.exp (-p) := by
    rw [← Real.exp_add]; congr 1; ring
  calc (N : ℝ) * Real.exp (-(2 * p)) = ((N : ℝ) * Real.exp (-p)) * Real.exp (-p) := by
        rw [h2]; ring
    _ ≤ (apInt q r lo hi).card * Real.exp (-p) :=
        mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
    _ = Real.exp (-p) * (apInt q r lo hi).card := mul_comm _ _
    _ ≤ _ := by simpa [apPts] using hcorr

/-- **The flag at degree one** is automatic: the Lie algebra of a model of degree one is
abelian. -/
theorem commKilled_of_degree_one {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L 1) (η : L →ₗ[ℚ] ℚ) : CommKilled η := by
  intro x y
  have hx : x ∈ F.layer 1 := by rw [F.one_eq_top]; exact Submodule.mem_top
  have hy : y ∈ F.layer 1 := by rw [F.one_eq_top]; exact Submodule.mem_top
  have h := F.lie_mem hx hy
  have h2 : F.layer 2 = ⊥ := F.terminal
  rw [h2] at h
  have : ⁅x, y⁆ = 0 := by simpa using h
  rw [this, map_zero]

end PrimeCarleson.Proof.Fplus31
