module

public import PrimeCarleson.Proof.Paper.Defs.Gowers
public import PrimeCarleson.Proof.Paper.Defs.Modulated
public import PrimeCarleson.Proof.Paper.Defs.Norms
public import PrimeCarleson.Proof.Common.FourierZ

/-!
# Basic API for the `U³` maximal estimates

`sources/Variational_Carleson.tex` L718-L898 (Lemma `e:U3maxmod`). This file collects the
elementary facts shared by the other files of `Paper/P3/`:

* the window `[-N, 2N]` (`maxWindow`) of the lemma, of cardinality `3N + 1`, an interval
  `Icc a (a + L - 1)` with `a = -N`, `L = 3N + 1` (so that the normalizations of
  `P2/Normalization.lean` apply to it), and `[N] = Icc 1 (1 + N - 1)`;
* the normalized `L^p` norms `lpNormOn` in the forms `L² ≤ L⁴`, monotonicity under
  pointwise domination, the identities `‖f‖_{L^p(X)}^p = |X|⁻¹ ∑ |f|^p` for `p = 2, 4`;
* the supremum over `λ`: for a continuous `1`-periodic family `Φ : ℝ → ℂ` the supremum of
  `|Φ(λ)|` is attained (`exists_forall_norm_le_of_periodic`), so that the maximal function
  `sup_λ |A_λ f(x)|` is a maximum over `λ ∈ [0, 1]` and can be linearized by a selector (the
  linearization of Lemma `e:U3maxmod`, L733–L743, in `VanDerCorput.lean`);
* the shift covariance `A_λ (Mod_θ w) = A_{λ+θ} w` (`modAverage_modZ`), which gives that the
  maximal function of the modulated weight equals that of `w`.
-/

@[expose] public noncomputable section

open scoped ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0

/-! ### The window `[-N, 2N]` -/

/-- The window `[-N, 2N] = {-N, …, 2N}` of `e:U3maxmod` (L720-L731) for `N : ℕ+`. -/
def maxWindow (N : ℕ+) : Finset ℤ := Finset.Icc (-(N : ℤ)) (2 * (N : ℤ))

/-- Membership in the window `[-N, 2N]`. -/
theorem mem_maxWindow {N : ℕ+} {x : ℤ} : x ∈ maxWindow N ↔ -(N : ℤ) ≤ x ∧ x ≤ 2 * (N : ℤ) := by
  simp [maxWindow]

/-- `|[-N, 2N]| = 3N + 1`. -/
theorem card_maxWindow (N : ℕ+) : (maxWindow N).card = 3 * (N : ℕ) + 1 := by
  rw [maxWindow, Int.card_Icc]
  omega

/-- The window `[-N, 2N]` is nonempty. -/
theorem maxWindow_nonempty (N : ℕ+) : (maxWindow N).Nonempty :=
  ⟨0, mem_maxWindow.2 ⟨by omega, by omega⟩⟩

/-- `[N] ⊆ [-N, 2N]`. -/
theorem bracket_subset_maxWindow (N : ℕ+) : bracket N ⊆ maxWindow N := fun n hn => by
  rw [mem_bracket] at hn
  exact mem_maxWindow.2 ⟨by omega, by omega⟩

/-- The window is the interval `Icc a (a + L - 1)` with `a = -N`, `L = 3N + 1`, the shape to
which `gowersNorm_indicator_pow_le` and `pow_le_gowersNorm_indicator_pow` apply. -/
theorem maxWindow_eq_Icc (N : ℕ+) :
    maxWindow N = Finset.Icc (-(N : ℤ)) (-(N : ℤ) + ((3 * (N : ℕ) + 1 : ℕ) : ℤ) - 1) := by
  rw [maxWindow]
  congr 1
  push_cast
  ring

/-- `[N]` is the interval `Icc a (a + L - 1)` with `a = 1`, `L = N`. -/
theorem bracket_eq_Icc (N : ℕ+) :
    bracket N = Finset.Icc (1 : ℤ) (1 + (((N : ℕ) : ℕ) : ℤ) - 1) := by
  rw [bracket]
  congr 1
  ring

/-! ### Normalized `L^p` norms -/

/-- `‖f‖_{L²(X)}² = |X|⁻¹ ∑_{x ∈ X} |f(x)|²`. -/
theorem lpNormOn_two_sq (X : Finset ℤ) (f : ℤ → ℂ) :
    lpNormOn 2 X f ^ 2 = (X.card : ℝ)⁻¹ * ∑ x ∈ X, ‖f x‖ ^ 2 := by
  have h := lpNormOn_rpow (p := 2) (by norm_num) X f
  simpa [Real.rpow_two] using h

/-- `‖f‖_{L⁴(X)}⁴ = |X|⁻¹ ∑_{x ∈ X} |f(x)|⁴`. -/
theorem lpNormOn_four_pow (X : Finset ℤ) (f : ℤ → ℂ) :
    lpNormOn 4 X f ^ 4 = (X.card : ℝ)⁻¹ * ∑ x ∈ X, ‖f x‖ ^ 4 := by
  have h := lpNormOn_rpow (p := 4) (by norm_num) X f
  have h1 : ∀ (y : ℝ), y ^ (4 : ℝ) = y ^ 4 := fun y => by
    rw [← Real.rpow_natCast]; norm_num
  simpa [h1] using h

/-- The norm `‖f‖_{L^p(X)}` only depends on the absolute values `|f(x)|`, `x ∈ X`, and is
monotone in them (`p > 0`). -/
theorem lpNormOn_mono {p : ℝ} (hp : 0 < p) (X : Finset ℤ) {f g : ℤ → ℂ}
    (h : ∀ x ∈ X, ‖f x‖ ≤ ‖g x‖) : lpNormOn p X f ≤ lpNormOn p X g := by
  unfold lpNormOn
  refine Real.rpow_le_rpow (mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)) ?_ (by positivity)
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x hx =>
    Real.rpow_le_rpow (norm_nonneg _) (h x hx) hp.le) (inv_nonneg.2 (Nat.cast_nonneg _))

/-- `‖f‖_{L²(X)} ≤ ‖f‖_{L⁴(X)}` (monotonicity of normalized norms). -/
theorem lpNormOn_two_le_four (X : Finset ℤ) (f : ℤ → ℂ) : lpNormOn 2 X f ≤ lpNormOn 4 X f := by
  rcases X.eq_empty_or_nonempty with rfl | hX
  · simp [lpNormOn]
  have hc : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (lpNormOn_nonneg _ _ _) ?_
  have h2 : (lpNormOn 2 X f ^ 2) ^ 2 = (lpNormOn 2 X f) ^ 4 := by ring
  rw [← h2, lpNormOn_two_sq, lpNormOn_four_pow]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq X (fun x => ‖f x‖ ^ 2) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul] at hcs
  have : ∀ x, (‖f x‖ ^ 2) ^ 2 = ‖f x‖ ^ 4 := fun x => by ring
  simp only [this] at hcs
  rw [mul_pow]
  calc ((X.card : ℝ)⁻¹) ^ 2 * (∑ x ∈ X, ‖f x‖ ^ 2) ^ 2
      ≤ ((X.card : ℝ)⁻¹) ^ 2 * ((∑ x ∈ X, ‖f x‖ ^ 4) * X.card) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = (X.card : ℝ)⁻¹ * ∑ x ∈ X, ‖f x‖ ^ 4 := by field_simp

/-! ### The supremum over `λ` -/

/-- A continuous `1`-periodic family `Φ : ℝ → ℂ` attains the supremum of `|Φ(λ)|`. -/
theorem exists_forall_norm_le_of_periodic {Φ : ℝ → ℂ} (hc : Continuous Φ)
    (hp : Function.Periodic Φ 1) : ∃ m : ℝ, ∀ lam : ℝ, ‖Φ lam‖ ≤ ‖Φ m‖ := by
  obtain ⟨m, -, hm⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMaxOn
    ⟨0, Set.mem_Icc.2 ⟨le_rfl, zero_le_one⟩⟩ hc.norm.continuousOn
  refine ⟨m, fun lam => ?_⟩
  have h1 : Φ (Int.fract lam) = Φ lam := by
    have := hp.sub_int_mul_eq (x := lam) ⌊lam⌋
    rw [mul_one] at this
    rw [Int.fract]
    exact this
  rw [← h1]
  exact hm (Set.mem_Icc.2 ⟨Int.fract_nonneg lam, (Int.fract_lt_one lam).le⟩)

/-- The supremum of `|Φ(λ)|` is the maximum `|Φ(m)|` for a continuous `1`-periodic family. -/
theorem iSup_norm_eq_of_periodic {Φ : ℝ → ℂ} (hc : Continuous Φ) (hp : Function.Periodic Φ 1) :
    ∃ m : ℝ, (⨆ lam : ℝ, ‖Φ lam‖) = ‖Φ m‖ ∧ ∀ lam, ‖Φ lam‖ ≤ ‖Φ m‖ := by
  obtain ⟨m, hm⟩ := exists_forall_norm_le_of_periodic hc hp
  have hb : BddAbove (Set.range fun lam : ℝ => ‖Φ lam‖) := ⟨‖Φ m‖, by
    rintro _ ⟨lam, rfl⟩
    exact hm lam⟩
  exact ⟨m, le_antisymm (ciSup_le hm) (le_ciSup (f := fun lam : ℝ => ‖Φ lam‖) hb m), hm⟩

/-! ### The modulated averages as continuous periodic families -/

/-- The modulated sum with weight carried by the finite set `S` is continuous in `λ`. -/
theorem continuous_weightedModSum (c f : ℤ → ℂ) (x : ℤ) (S : Finset ℤ)
    (hS : ∀ n, n ∉ S → c n = 0) : Continuous fun lam : ℝ => weightedModSum c f lam x := by
  have h : (fun lam : ℝ => weightedModSum c f lam x) =
      fun lam => ∑ n ∈ S, f (x - n) * c n * e (lam * n) :=
    funext fun lam => weightedModSum_eq_sum c f lam x S hS
  rw [h]
  exact continuous_finsetSum _ fun n _ =>
    continuous_const.mul (Common.continuous_e.comp (continuous_id.mul continuous_const))

/-- The modulated average `A_λ f(x)` is continuous in `λ`. -/
theorem continuous_modAverage_lam (N : ℕ+) (w f : ℤ → ℂ) (x : ℤ) :
    Continuous fun lam : ℝ => modAverage N w f lam x := by
  have h : (fun lam : ℝ => modAverage N w f lam x) = fun lam =>
      (N : ℂ)⁻¹ * weightedModSum (fun n => if n ∈ bracket N then w n else 0) f lam x :=
    funext fun lam => modAverage_eq_weightedModSum N w f lam x
  rw [h]
  exact continuous_const.mul (continuous_weightedModSum _ f x (bracket N) fun n hn => by simp [hn])

/-- The modulated average is `1`-periodic in `λ`. -/
theorem periodic_modAverage_lam (N : ℕ+) (w f : ℤ → ℂ) (x : ℤ) :
    Function.Periodic (fun lam : ℝ => modAverage N w f lam x) 1 := by
  intro lam
  simp only [modAverage_eq_weightedModSum]
  have := weightedModSum_add_intCast (fun n => if n ∈ bracket N then w n else 0) f lam 1 x
  simpa using congrArg (fun z => (N : ℂ)⁻¹ * z) this

/-- The weighted modulated sum is `1`-periodic in `λ`. -/
theorem periodic_weightedModSum (c f : ℤ → ℂ) (x : ℤ) :
    Function.Periodic (fun lam : ℝ => weightedModSum c f lam x) 1 := by
  intro lam
  simpa using weightedModSum_add_intCast c f lam 1 x

/-- **Shift covariance**: the average of the modulated weight `Mod_θ w` at frequency `λ` is the
average of `w` at frequency `λ + θ` (`e(θ n) e(λ n) = e((λ + θ) n)`). -/
theorem modAverage_modZ (N : ℕ+) (θ : ℝ) (w f : ℤ → ℂ) (lam : ℝ) (x : ℤ) :
    modAverage N (modZ θ w) f lam x = modAverage N w f (lam + θ) x := by
  unfold modAverage expect
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [modZ]
  have : e ((lam + θ) * n) = e (θ * n) * e (lam * n) := by
    rw [← e_add]; congr 1; ring
  rw [this]
  ring

/-- The maximal function of the modulated weight equals that of `w`: the supremum over all
`λ ∈ ℝ` is invariant under the shift `λ ↦ λ + θ`. -/
theorem iSup_norm_modAverage_modZ (N : ℕ+) (θ : ℝ) (w f : ℤ → ℂ) (x : ℤ) :
    (⨆ lam : ℝ, ‖modAverage N (modZ θ w) f lam x‖) = ⨆ lam : ℝ, ‖modAverage N w f lam x‖ := by
  simp_rw [modAverage_modZ]
  exact (Equiv.addRight θ).iSup_comp (g := fun lam => ‖modAverage N w f lam x‖)

end PrimeCarleson.Proof.Paper
