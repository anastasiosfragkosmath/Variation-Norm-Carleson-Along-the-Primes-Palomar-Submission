module

public import PrimeCarleson.Proof.Paper.P6c.Basic
public import PrimeCarleson.Proof.Paper.P6a.Moments
public import PrimeCarleson.Proof.Paper.P3.TwoSided

/-!
# The `ℓ²` and crude bounds of the maximal operator of one dyadic piece `u ψ_k`

Source: main paper `s:red`, L1525–L1527:

* `sup_L2_piece`: the maximal `U³` estimate of Lemma `e:U3maxmod` at scale `2^k` with the
  smooth cutoff `ψ_k` (`U3maxmod_twoSided`, `P3/TwoSided.lean`):
  `‖sup_λ |∑_n f(x-n) u(n) ψ_k(n) e(λ n)|‖_{ℓ²} ≤ C ‖u‖_{U³([2^k])} ‖f‖_{ℓ²}` for even `u`;
* `crude_sup_piece`: the crude `ℓ^s` bound, `s ≥ 1`, by Young's inequality: the weight `u ψ_k` has
  `ℓ¹` norm `≤ C ‖u‖_{L²([2^k])}` (`|ψ_k| ≲ 2^{-k}`, support in `|n| < 2^k`, `u` even). This is
  the maximal counterpart of `crude_piece_le` of `P6a/Moments.lean`; for the supremum over `λ` no
  restriction `s ≥ r'` is needed.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- **The `ℓ¹` norm of `u ψ_k`** for even `u`: `∑_n |u(n) ψ_k(n)| ≤ 2 ‖ψ‖_∞ ‖u‖_{L²([2^k])}`
(`|ψ_k| ≤ 2^{-k} ‖ψ‖_∞`, `ψ_k` supported in `|n| < 2^k`, `L¹ ≤ L²` on `[2^k]`). -/
theorem psiWeight_l1_le (ψ : PsiData) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (N : ℕ+), (N : ℕ) = 2 ^ k → ∀ u : ℤ → ℂ,
      (∀ n, u (-n) = u n) →
      ∑' n : ℤ, ‖u n * psiKz ψ k n‖ₑ ≤ ENNReal.ofReal (C * lpNormOn 2 (bracket N) u) := by
  obtain ⟨B, hB⟩ := ψ.hasCompactSupport.exists_bound_of_continuous ψ.contDiff.continuous
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine ⟨2 * B, by positivity, fun k N hN u hu => ?_⟩
  set X : ℝ := (2 : ℝ) ^ k with hXdef
  have hX0 : 0 < X := by positivity
  have hNr : ((N : ℕ) : ℝ) = X := by rw [hN]; push_cast; rfl
  set w : ℤ → ℂ := fun n => u n * psiKz ψ k n with hw
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 2 ^ k := ⟨_, rfl⟩
  have hMX : ((M : ℤ) : ℝ) = X := by rw [hM, hXdef]; push_cast; rfl
  set S : Finset ℤ := Finset.Ioo (-(M : ℤ)) (M : ℤ) with hSdef
  have hS : ∀ n ∉ S, w n = 0 := by
    intro n hn
    by_contra h
    have hne : psiKz ψ k n ≠ 0 := fun h0 => h (by simp [hw, h0])
    have h1 := (psiKz_ne_zero ψ hne).2
    have h2 : n.natAbs < M := by rw [hM]; exact_mod_cast h1
    apply hn
    rw [hSdef, Finset.mem_Ioo]
    omega
  have hw0 : w 0 = 0 := by simp [hw, psiKz_zero]
  have hpsi : ∀ n : ℤ, ‖psiKz ψ k n‖ ≤ B / X := by
    intro n
    unfold psiKz psiK
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hX0]
    have hb := hB (n * X⁻¹)
    rw [Real.norm_eq_abs] at hb
    calc X⁻¹ * |ψ.toFun (n * X⁻¹)| ≤ X⁻¹ * B :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = B / X := by ring
  have hwle : ∀ n : ℤ, ‖w n‖ ≤ (B / X) * ‖u n‖ := by
    intro n
    simp only [hw, norm_mul]
    calc ‖u n‖ * ‖psiKz ψ k n‖ ≤ ‖u n‖ * (B / X) :=
          mul_le_mul_of_nonneg_left (hpsi n) (norm_nonneg _)
      _ = B / X * ‖u n‖ := by ring
  have hweven : ∀ n : ℤ, ‖w (-n)‖ = ‖w n‖ := by
    intro n
    simp [hw, hu, psiKz_neg]
  set L : ℝ := lpNormOn 1 (bracket N) u with hL
  have hL1 : ∑ n ∈ bracket N, ‖u n‖ = X * L := by
    have h := lpNormOn_rpow one_pos (bracket N) u
    rw [Real.rpow_one, card_bracket, hNr] at h
    simp only [Real.rpow_one] at h
    rw [hL, h]
    field_simp
  have hsum : ∑ n ∈ S, ‖w n‖ ≤ 2 * (B * L) := by
    rw [← Finset.sum_erase S (f := fun n => ‖w n‖) (a := 0) (by simp [hw0])]
    have h1 := KMTT.sum_le_two_mul_of_even (S := S.erase 0) (N := X) (fun n => ‖w n‖)
      (fun n => norm_nonneg _) hweven (fun n hn => by
        rw [Finset.mem_erase, hSdef, Finset.mem_Ioo] at hn
        obtain ⟨hn0, h1, h2⟩ := hn
        refine ⟨Int.one_le_abs hn0, ?_⟩
        rw [← Int.cast_abs, ← hMX]
        exact_mod_cast (abs_lt.2 ⟨h1, h2⟩).le)
    rw [← hNr, intervalN_pnat] at h1
    refine h1.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    calc ∑ n ∈ bracket N, ‖w n‖ ≤ ∑ n ∈ bracket N, (B / X) * ‖u n‖ :=
          Finset.sum_le_sum fun n _ => hwle n
      _ = (B / X) * ∑ n ∈ bracket N, ‖u n‖ := by rw [Finset.mul_sum]
      _ = B * L := by rw [hL1]; field_simp
  have hts : ∑' n : ℤ, ‖w n‖ₑ = ENNReal.ofReal (∑ n ∈ S, ‖w n‖) := by
    rw [tsum_eq_sum (s := S) (fun n hn => by simp [hS n hn]),
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
    exact Finset.sum_congr rfl fun n _ => by rw [ofReal_norm]
  have hL2 : L ≤ lpNormOn 2 (bracket N) u :=
    lpNormOn_le_two le_rfl (by norm_num) (bracket_nonempty N) u
  rw [hts]
  refine ENNReal.ofReal_le_ofReal (hsum.trans ?_)
  calc 2 * (B * L) ≤ 2 * (B * lpNormOn 2 (bracket N) u) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL2 hB0) (by norm_num)
    _ = 2 * B * lpNormOn 2 (bracket N) u := by ring

/-- **The crude `ℓ^s` bound of a dyadic piece** (maximal counterpart of `crude_piece_le`): for
`k ≥ 0`, `N = 2^k`, even `u` and every `s ≥ 1`,
`‖sup_λ |∑_n f(x-n) u(n) ψ_k(n) e(λ n)|‖_{ℓ^s} ≤ C ‖u‖_{L²([N])} ‖f‖_{ℓ^s}`. -/
theorem crude_sup_piece (ψ : PsiData) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (N : ℕ+), (N : ℕ) = 2 ^ k → ∀ u : ℤ → ℂ,
      (∀ n, u (-n) = u n) → ∀ s : ℝ, 1 ≤ s → ∀ f : ℤ → ℂ,
        eLpNorm (supOp (fun n => u n * psiKz ψ k n) f) (ENNReal.ofReal s) Measure.count ≤
          ENNReal.ofReal (C * lpNormOn 2 (bracket N) u) *
            eLpNorm f (ENNReal.ofReal s) Measure.count := by
  obtain ⟨C, hC0, hC⟩ := psiWeight_l1_le ψ
  exact ⟨C, hC0, fun k N hN u hu s hs f =>
    (eLpNorm_supOp_le hs _ f).trans (mul_le_mul' (hC k N hN u hu) le_rfl)⟩

/-- **The maximal `U³` estimate of a dyadic piece** (`U3maxmod_twoSided` of `P3/TwoSided.lean`): for
`N = 2^k` and even `u`,
`‖sup_λ |∑_n f(x-n) u(n) ψ_k(n) e(λ n)|‖_{ℓ²} ≤ C ‖u‖_{U³([N])} ‖f‖_{ℓ²}`. -/
theorem sup_L2_piece (ψ : PsiData) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (N : ℕ+), (N : ℕ) = 2 ^ k → ∀ u : ℤ → ℂ,
      (∀ n, u (-n) = u n) → ∀ f : ℤ → ℂ,
        eLpNorm (supOp (fun n => u n * psiKz ψ k n) f) (ENNReal.ofReal 2) Measure.count ≤
          ENNReal.ofReal (C * gowersNormInterval 3 N u) *
            eLpNorm f (ENNReal.ofReal 2) Measure.count := by
  obtain ⟨C, hC, h⟩ := U3maxmod_twoSided ψ
  refine ⟨C, hC, fun k N hN u hu f => ?_⟩
  have hN' : N = (2 : ℕ+) ^ k := PNat.eq (by simpa using hN)
  subst hN'
  have h1 := h k u hu f
  have hpt : ∀ x, supOp (fun n => u n * psiKz ψ k n) f x ≤
      ⨆ lam : ℝ, ‖weightedModSum
        (fun n : ℤ => u n * ((psiK ψ.toFun k (n : ℝ) : ℝ) : ℂ)) f lam x‖ₑ := fun x =>
    iSup₂_le fun lam _ => le_iSup (fun lam : ℝ => ‖weightedModSum
      (fun n : ℤ => u n * ((psiK ψ.toFun k (n : ℝ) : ℝ) : ℂ)) f lam x‖ₑ) lam
  simp only [ENNReal.ofReal_ofNat]
  exact (eLpNorm_count_mono_enn hpt 2).trans h1

end PrimeCarleson.Proof.Paper
