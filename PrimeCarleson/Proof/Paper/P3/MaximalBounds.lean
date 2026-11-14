module

public import PrimeCarleson.Proof.Paper.P3.RecursiveIdentity
public import PrimeCarleson.Proof.Paper.P2.EisnerTao

/-!
# The maximal `U³` estimates in `L⁴` and `L²`

Source: main paper `e:U3maxmod`, L718–L726 and L884, the first two displays of Lemma `e:U3maxmod`.
Paper steps proved here:

* `e:U3lin-target` (`u3lin_target`): for `w` supported in `[N]`, `f` supported in `[-N, 2N]` and
  every selector `θ`, `‖A_θ f‖_{L⁴([-N,2N])} ≤ 20 ‖w‖_{U³([N])} ‖f‖_{U³([-N,2N])}` (fourth roots
  of `four_pow_le_U3`);
* the first display, L720–L722 (`U3maxmod_L4`): with `A_λ f(x) = E_{n ∈ [N]} f(x-n) w(n) e(λ n)`,
  `‖sup_λ |A_λ f|‖_{L⁴([-N,2N])} ≤ 20 ‖w‖_{U³([N])} ‖f‖_{U³([-N,2N])}` for every `w : ℤ → ℂ`
  (only the values on `[N]` enter) and `f` carried by `[-N, 2N]`, by linearization;
* the second display, L724–L726 (`L2_of_L4_via_ET`, `U3maxmod_L2`):
  `‖sup_λ |A_λ f|‖_{L²([-N,2N])} ≤ 40 ‖w‖_{U³([N])} ‖f‖_{L²([-N,2N])}`, from the `L⁴` bound,
  monotonicity of the normalized norms (`L² ≤ L⁴`) and the Eisner-Tao inequality for `s = 3`
  (`p₃ = 2`, `gowersNormOn_three_Icc_le`: `‖f‖_{U³(I)} ≤ 2 ‖f‖_{L²(I)}` on every interval `I`).

The supremum `sup_λ |A_λ f(x)|` over `λ ∈ ℝ` is the real `iSup`
`⨆ lam : ℝ, ‖modAverage N w f lam x‖` (a maximum, `1`-periodicity in `λ`), written as a complex
number to be fed to `lpNormOn`.
-/

@[expose] public noncomputable section

open scoped ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0

/-- `A_λ f` only depends on the values of `w` on `[N]`. -/
theorem modAverage_congr_bracket (N : ℕ+) {w w' : ℤ → ℂ} (h : ∀ n ∈ bracket N, w n = w' n)
    (f : ℤ → ℂ) (lam : ℝ) (x : ℤ) : modAverage N w f lam x = modAverage N w' f lam x := by
  unfold modAverage expect
  congr 1
  exact Finset.sum_congr rfl fun n hn => by simp only [h n hn]

/-- **`e:U3lin-target`** (Source: main paper `e:U3lin-target`, L744–L749, L884): for `w` supported
in `[N]`, `f` supported in `[-N, 2N]` and every selector `θ : ℤ → ℝ`,
`‖A_θ f‖_{L⁴([-N,2N])} ≤ 20 ‖w‖_{U³([N])} ‖f‖_{U³([-N,2N])}`,
`A_θ f(x) = E_{n ∈ [N]} w(n) f(x-n) e(θ(x) n)`. -/
theorem u3lin_target (N : ℕ+) (w f : ℤ → ℂ) (hw : ∀ n, n ∉ bracket N → w n = 0)
    (hf : ∀ y, y ∉ maxWindow N → f y = 0) (θ : ℤ → ℝ) :
    lpNormOn 4 (maxWindow N) (fun x => modAverage N w f (θ x) x) ≤
      20 * gowersNormOn 3 (bracket N) w * gowersNormOn 3 (maxWindow N) f := by
  have h := four_pow_le_U3 N w f hw hf θ
  have hn1 : 0 ≤ gowersNormOn 3 (bracket N) w := gowersNormOn_nonneg _ _ _
  have hn2 : 0 ≤ gowersNormOn 3 (maxWindow N) f := gowersNormOn_nonneg _ _ _
  refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity) ?_
  calc lpNormOn 4 (maxWindow N) (fun x => modAverage N w f (θ x) x) ^ 4
      ≤ 122472 * (gowersNormOn 3 (bracket N) w ^ 4 * gowersNormOn 3 (maxWindow N) f ^ 4) := h
    _ ≤ 20 ^ 4 * (gowersNormOn 3 (bracket N) w ^ 4 * gowersNormOn 3 (maxWindow N) f ^ 4) := by
        refine mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = (20 * gowersNormOn 3 (bracket N) w * gowersNormOn 3 (maxWindow N) f) ^ 4 := by ring

/-- **First display of `e:U3maxmod`** (Source: main paper `e:U3maxmod`, L720–L722, L884): for every
`w : ℤ → ℂ` (only the values on `[N]` enter) and `f` carried by `[-N, 2N]`,
`‖sup_λ |E_{n ∈ [N]} f(x-n) w(n) e(λ n)|‖_{L⁴([-N,2N])} ≤
20 ‖w‖_{U³([N])} ‖f‖_{U³([-N,2N])}`. -/
theorem U3maxmod_L4 (N : ℕ+) (w f : ℤ → ℂ) (hf : ∀ y, y ∉ maxWindow N → f y = 0) :
    lpNormOn 4 (maxWindow N) (fun x => ((⨆ lam : ℝ, ‖modAverage N w f lam x‖ : ℝ) : ℂ)) ≤
      20 * gowersNormOn 3 (bracket N) w * gowersNormOn 3 (maxWindow N) f := by
  classical
  set w' : ℤ → ℂ := fun n => if n ∈ bracket N then w n else 0 with hw'
  have hsupp : ∀ n, n ∉ bracket N → w' n = 0 := fun n hn => by simp [hw', hn]
  have hcong : ∀ n ∈ bracket N, w n = w' n := fun n hn => by simp [hw', hn]
  have hn : gowersNormOn 3 (bracket N) w = gowersNormOn 3 (bracket N) w' :=
    gowersNormOn_congr 3 (bracket N) hcong
  have hmod : ∀ lam x, modAverage N w f lam x = modAverage N w' f lam x :=
    fun lam x => modAverage_congr_bracket N hcong f lam x
  simp_rw [hmod]
  rw [hn]
  exact linearization N w' f _ _ fun θ => u3lin_target N w' f hsupp hf θ

/-- **Second display of `e:U3maxmod` from the first** (Source: main paper `e:U3maxmod`, L723–L726):
the `L⁴` maximal bound with constant `C` implies the `L²` maximal bound with constant `2C`:
monotonicity of normalized norms (`L²([-N,2N]) ≤ L⁴([-N,2N])`) and the Eisner-Tao inequality for
`s = 3` (`p₃ = 2`) on the interval `[-N, 2N]`, `‖f‖_{U³} ≤ 2 ‖f‖_{L²}`. -/
theorem L2_of_L4_via_ET (N : ℕ+) (w f : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (h : lpNormOn 4 (maxWindow N) (fun x => ((⨆ lam : ℝ, ‖modAverage N w f lam x‖ : ℝ) : ℂ)) ≤
      C * gowersNormOn 3 (bracket N) w * gowersNormOn 3 (maxWindow N) f) :
    lpNormOn 2 (maxWindow N) (fun x => ((⨆ lam : ℝ, ‖modAverage N w f lam x‖ : ℝ) : ℂ)) ≤
      2 * C * gowersNormOn 3 (bracket N) w * lpNormOn 2 (maxWindow N) f := by
  have hET : gowersNormOn 3 (maxWindow N) f ≤ 2 * lpNormOn 2 (maxWindow N) f :=
    gowersNormOn_three_Icc_le (a := -(N : ℤ)) (b := 2 * (N : ℤ)) (by omega) f
  have hn1 : 0 ≤ gowersNormOn 3 (bracket N) w := gowersNormOn_nonneg _ _ _
  calc _ ≤ lpNormOn 4 (maxWindow N) (fun x => ((⨆ lam : ℝ, ‖modAverage N w f lam x‖ : ℝ) : ℂ)) :=
        lpNormOn_two_le_four _ _
    _ ≤ C * gowersNormOn 3 (bracket N) w * gowersNormOn 3 (maxWindow N) f := h
    _ ≤ C * gowersNormOn 3 (bracket N) w * (2 * lpNormOn 2 (maxWindow N) f) :=
        mul_le_mul_of_nonneg_left hET (by positivity)
    _ = 2 * C * gowersNormOn 3 (bracket N) w * lpNormOn 2 (maxWindow N) f := by ring

/-- **Second display of `e:U3maxmod`** (Source: main paper `e:U3maxmod`, L724–L726): for every
`w : ℤ → ℂ` and `f` carried by `[-N, 2N]`,
`‖sup_λ |E_{n ∈ [N]} f(x-n) w(n) e(λ n)|‖_{L²([-N,2N])} ≤
40 ‖w‖_{U³([N])} ‖f‖_{L²([-N,2N])}`. -/
theorem U3maxmod_L2 (N : ℕ+) (w f : ℤ → ℂ) (hf : ∀ y, y ∉ maxWindow N → f y = 0) :
    lpNormOn 2 (maxWindow N) (fun x => ((⨆ lam : ℝ, ‖modAverage N w f lam x‖ : ℝ) : ℂ)) ≤
      40 * gowersNormOn 3 (bracket N) w * lpNormOn 2 (maxWindow N) f := by
  have := L2_of_L4_via_ET N w f 20 (by norm_num) (U3maxmod_L4 N w f hf)
  linarith

end PrimeCarleson.Proof.Paper
