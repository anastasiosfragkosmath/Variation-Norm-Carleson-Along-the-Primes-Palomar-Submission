module

public import PrimeCarleson.Proof.Paper.P10.Coef
public import PrimeCarleson.Proof.Paper.P9.Representation

/-!
# Linearization of `C^Q_B` and the decomposition `λ(x) = θ(x)/N + ω(x)`

Source: main paper `p:transferprop`, L2142–L2152.

For finitely supported `f`, `λ ↦ T^{Q,B}_λ f(x)` is a trigonometric polynomial, so the supremum
over `𝕋 = [0, 1)` defining `C^Q_B f(x)` is attained (`exists_maximizer`: the paper's "choose
`λ(x)` with `C^Q_B f(x) ≲ |...|`" holds with constant `1`). Splitting
`λ(x) = θ(x)/N + ω(x)` with `θ(x) = ⌊N λ(x)⌋` gives `ω(x) ∈ [0, 1/N)`
(`exists_selector`); the paper takes `|ω(x)| ≤ 1/(2N)` (a window of the same length `1/N`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

namespace KQSetup

variable (S : KQSetup)

/-- For finitely supported `f`, `T^{Q,B}_λ f(x)` is a finite sum over `supp f`. -/
theorem TQB_eq_sum (Q : ℕ) (B : Finset ℕ) (lam : ℝ) (f : ℤ →₀ ℂ) (x : ℤ) :
    S.TQB Q B lam f x = ∑ k ∈ f.support,
      f k * (blockWeight B (x - k) * S.KQz Q (x - k)) * e (lam * ((x - k : ℤ) : ℝ)) := by
  unfold KQSetup.TQB weightedModSum
  rw [← (Equiv.subLeft x).tsum_eq]
  rw [tsum_eq_sum (s := f.support)]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp [Equiv.subLeft_apply]
  · intro k hk
    simp [Finsupp.notMem_support_iff.1 hk]

theorem continuous_TQB (Q : ℕ) (B : Finset ℕ) (f : ℤ →₀ ℂ) (x : ℤ) :
    Continuous fun lam : ℝ => S.TQB Q B lam f x := by
  simp_rw [S.TQB_eq_sum Q B _ f x]
  exact continuous_finsetSum _ fun k _ =>
    continuous_const.mul (continuous_e.comp (continuous_id.mul continuous_const))

/-- `T^{Q,B}_λ f(x)` is `1`-periodic in `λ`. -/
theorem TQB_add_one (Q : ℕ) (B : Finset ℕ) (lam : ℝ) (f : ℤ →₀ ℂ) (x : ℤ) :
    S.TQB Q B (lam + 1) f x = S.TQB Q B lam f x := by
  have := weightedModSum_add_intCast (fun n => blockWeight B n * S.KQz Q n) f lam 1 x
  unfold KQSetup.TQB
  simpa using this

/-- **Linearization of `C^Q_B`, first part**: the supremum defining `C^Q_B f(x)` is attained
at some `λ(x) ∈ [0, 1)`, `C^Q_B f(x) = |T^{Q,B}_{λ(x)} f(x)|`. -/
theorem exists_maximizer (Q : ℕ) (B : Finset ℕ) (f : ℤ →₀ ℂ) (x : ℤ) :
    ∃ lam ∈ Set.Ico (0 : ℝ) 1, S.CQB Q B (⇑f) x = ‖S.TQB Q B lam f x‖ₑ := by
  have hc : Continuous fun lam : ℝ => ‖S.TQB Q B lam f x‖ := (S.continuous_TQB Q B f x).norm
  obtain ⟨l₀, hl₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 (zero_le_one' ℝ))
    hc.continuousOn
  have hper : ‖S.TQB Q B 1 f x‖ = ‖S.TQB Q B 0 f x‖ := by
    have := S.TQB_add_one Q B 0 f x
    rw [zero_add] at this
    rw [this]
  -- a maximizer in `[0, 1)`
  obtain ⟨l₁, hl₁, hl₁max⟩ : ∃ l₁ ∈ Set.Ico (0 : ℝ) 1, ∀ l ∈ Set.Icc (0 : ℝ) 1,
      ‖S.TQB Q B l f x‖ ≤ ‖S.TQB Q B l₁ f x‖ := by
    by_cases h1 : l₀ = 1
    · refine ⟨0, ⟨le_refl _, zero_lt_one⟩, fun l hl => ?_⟩
      have := hmax hl
      simp only [Set.mem_ofPred_eq, h1] at this
      rw [← hper]
      exact this
    · refine ⟨l₀, ⟨hl₀.1, lt_of_le_of_ne hl₀.2 h1⟩, fun l hl => ?_⟩
      exact hmax hl
  refine ⟨l₁, hl₁, le_antisymm ?_ ?_⟩
  · refine iSup₂_le fun l hl => ?_
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hl₁max l ⟨hl.1, hl.2.le⟩)
  · exact le_iSup₂ (f := fun lam (_ : lam ∈ Set.Ico (0 : ℝ) 1) => ‖S.TQB Q B lam f x‖ₑ) l₁ hl₁

end KQSetup

/-- **Linearization of `C^Q_B`** (L2142–L2152): for every `x` there are `λ(x) ∈ [0, 1)`,
`θ(x) ∈ ℤ` (the class of `⌊N λ(x)⌋` in `ℤ/N`) and `ω(x) ∈ [0, 1/N)` with
`C^Q_B f(x) = |T^{Q,B}_{λ(x)} f(x)|` and `λ(x) = θ(x)/N + ω(x)`. -/
theorem KQSetup.exists_selector (S : KQSetup) (Q : ℕ) (B : Finset ℕ) {N : ℕ} (hN : 0 < N)
    (f : ℤ →₀ ℂ) :
    ∃ (ϑ : ℤ → ℤ) (ω : ℤ → ℝ), (∀ x, 0 ≤ ω x ∧ ω x < 1 / (N : ℝ)) ∧
      ∀ x, S.CQB Q B (⇑f) x = ‖S.TQB Q B ((ϑ x : ℝ) / N + ω x) f x‖ₑ := by
  classical
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  choose lam hlam hCQ using fun x => S.exists_maximizer Q B f x
  refine ⟨fun x => ⌊(N : ℝ) * lam x⌋, fun x => lam x - (⌊(N : ℝ) * lam x⌋ : ℝ) / N, fun x => ?_,
    fun x => ?_⟩
  · have h1 := Int.floor_le ((N : ℝ) * lam x)
    have h2 := Int.lt_floor_add_one ((N : ℝ) * lam x)
    have hω : lam x - (⌊(N : ℝ) * lam x⌋ : ℝ) / N =
        ((N : ℝ) * lam x - ⌊(N : ℝ) * lam x⌋) / N := by
      field_simp
    change 0 ≤ lam x - (⌊(N : ℝ) * lam x⌋ : ℝ) / N ∧
      lam x - (⌊(N : ℝ) * lam x⌋ : ℝ) / N < 1 / N
    rw [hω]
    exact ⟨div_nonneg (by linarith) hNR.le, (div_lt_div_iff_of_pos_right hNR).2 (by linarith)⟩
  · rw [hCQ x]
    congr 3
    ring

end PrimeCarleson.Proof.Paper
