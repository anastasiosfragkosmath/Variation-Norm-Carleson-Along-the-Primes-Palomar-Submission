module

public import PrimeCarleson.Proof.Paper.P5.KQProps
public import PrimeCarleson.Proof.Paper.P5.Blocks
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The radius `δ₀` of the cutoff and the support of `K̂_Q`

Source: main paper `p:transferprop`, L2224–L2227; main paper `p:global-shell-var`, L1974–L1982 and
L2028–L2029; main paper `e:KQ`, L1199–L1201.

The multiplier `K̂_Q(β) = φ̂(N(Q) β) ∑_{k ≥ k₀} ψ̂(2^k β)` vanishes for `|β| > δ / N(Q)`
(`KQhat_eq_zero`). Which `δ` do the consumers allow? There are two constraints, both of the form
"`δ / N(Q)` is small compared with a quantity attached to `Q`", for every dyadic `Q = 2^j`:

* **(C1) `SupportBlock`** (Source: main paper `p:transferprop`, L2224–L2227): the support of `K̂_Q`
  lies in `{‖β‖ ≤ (100 𝒬_B)⁻¹}` for every block, i.e. `100 δ 𝒬_B ≤ N(Q)`; since
  `𝒬_B ≤ exp(100 log Q Q^κ)` (`lcmQ_le_exp`), it is implied by
  `100 δ exp(100 Q^κ log Q) ≤ N(Q) = exp(Q^{1/D₀ - ε/10})`. For large `Q` this holds with room
  to spare (`N(Q) ≫_A 𝒬_B^A`), the paper's "N(Q) ≫ N^A"; for the finitely
  many small `Q` it is the constraint "φ̂ supported in a sufficiently small neighbourhood of 0";
* **(C2) `SupportScale c`** (Source: main paper `p:global-shell-var`, L1974–L1982): the
  support of `K̂_Q` lies in a neighbourhood of `0` of size `c Q^{-2}` (the interval `J` of length
  `c Q^{-2}` must absorb `supp K̂_Q`), i.e. `δ Q² ≤ c N(Q)`, `c` the absolute constant of
  `p:global-shell-var`.

Both are conditions on `(D₀, ε, δ)` only and hold for all `δ ≤ δ₀(D₀, ε, c)`
(`exists_delta0`): `δ₀ = 1 / max(1, sup_j 100 exp(100 Q^κ log Q)/N(Q), sup_j Q²/(c N(Q)))`, a
positive number because the suprema are finite (both ratios tend to `0`). (C1) alone also gives
the length bound `≤ 1/10` for `l:varcarZ`, the support in `(-1/2, 1/2]`, and the same for the
rescaled kernels `K_{Q,d}`, `d ≤ Q`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Asymptotics
open scoped ENNReal Real

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Paper.P5

/-! ### The asymptotics -/

theorem tendsto_rpow_sub_log {κ γ : ℝ} (hκ : 0 ≤ κ) (hκγ : κ < γ) (a b : ℝ) :
    Tendsto (fun x : ℝ => x ^ γ - a * x ^ κ * Real.log x - b) atTop atTop := by
  have hs : 0 < γ - κ := sub_pos.2 hκγ
  have hγ0 : 0 < γ := by linarith
  have hlit := (isLittleO_log_rpow_atTop hs).def (c := 1 / (2 * (|a| + 1))) (by positivity)
  have hx : Tendsto (fun x : ℝ => x ^ γ) atTop atTop := tendsto_rpow_atTop hγ0
  have hbig : ∀ᶠ x : ℝ in atTop, 4 * b ≤ x ^ γ := hx.eventually_ge_atTop _
  have hpos : ∀ᶠ x : ℝ in atTop, 1 ≤ x := eventually_ge_atTop 1
  refine tendsto_atTop_mono' atTop ?_ (hx.atTop_div_const (by norm_num : (0 : ℝ) < 4))
  filter_upwards [hlit, hbig, hpos] with x h1 h2 h3
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg h3
  have hxs : 0 ≤ x ^ (γ - κ) := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog, abs_of_nonneg hxs] at h1
  have h4 : x ^ κ * x ^ (γ - κ) = x ^ γ := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have hxκ : 0 ≤ x ^ κ := by positivity
  have h5 : |a| * (x ^ κ * Real.log x) ≤ |a| * (x ^ κ * (1 / (2 * (|a| + 1)) * x ^ (γ - κ))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hxκ) (abs_nonneg a)
  have h6 : |a| * (x ^ κ * (1 / (2 * (|a| + 1)) * x ^ (γ - κ))) =
      |a| / (2 * (|a| + 1)) * x ^ γ := by
    rw [← h4]
    ring
  have h7 : |a| / (2 * (|a| + 1)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg a]
  have h8 : |a| / (2 * (|a| + 1)) * x ^ γ ≤ 1 / 2 * x ^ γ :=
    mul_le_mul_of_nonneg_right h7 (by positivity)
  have h9 : a * x ^ κ * Real.log x ≤ |a| * (x ^ κ * Real.log x) := by
    calc a * x ^ κ * Real.log x = a * (x ^ κ * Real.log x) := by ring
      _ ≤ |a| * (x ^ κ * Real.log x) :=
        mul_le_mul_of_nonneg_right (le_abs_self a) (by positivity)
  linarith

namespace KQParams

variable (P : KQParams)

/-- **(C1)** `100 δ exp(100 Q^κ log Q) ≤ N(Q)` for every `Q = 2^j`. -/
def SupportBlock (δ : ℝ) : Prop :=
  ∀ j : ℕ, 100 * δ * Real.exp (100 * ((2 : ℝ) ^ j) ^ P.kappa * Real.log ((2 : ℝ) ^ j)) ≤
    P.NQ (2 ^ j)

/-- **(C2)** `δ Q² ≤ c N(Q)` for every `Q = 2^j`. -/
def SupportScale (δ c : ℝ) : Prop :=
  ∀ j : ℕ, δ * ((2 : ℝ) ^ j) ^ 2 ≤ c * P.NQ (2 ^ j)

theorem NQ_two_pow (j : ℕ) : P.NQ (2 ^ j) = Real.exp (((2 : ℝ) ^ j) ^ P.gamma) := by
  unfold NQ
  push_cast
  rfl

theorem tendsto_two_pow : Tendsto (fun j : ℕ => (2 : ℝ) ^ j) atTop atTop :=
  tendsto_pow_atTop_atTop_of_one_lt (by norm_num)

/-- **The radius `δ₀`**: for every `c > 0` there is `δ₀ > 0` such that every `0 < δ ≤ δ₀`
satisfies (C1) and (C2). -/
theorem exists_delta0 {c : ℝ} (hc : 0 < c) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → P.SupportBlock δ ∧ P.SupportScale δ c := by
  -- the two ratios tend to zero
  have hr1 : Tendsto (fun j : ℕ => 100 * Real.exp (100 * ((2 : ℝ) ^ j) ^ P.kappa *
      Real.log ((2 : ℝ) ^ j)) / P.NQ (2 ^ j)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_sub_log P.kappa_pos.le P.kappa_lt_gamma 100 (Real.log 100)).comp
      tendsto_two_pow
    have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h
    refine h2.congr fun j => ?_
    simp only [Function.comp, NQ_two_pow]
    set Q : ℝ := (2 : ℝ) ^ j
    rw [show -(Q ^ P.gamma - 100 * Q ^ P.kappa * Real.log Q - Real.log 100) =
      100 * Q ^ P.kappa * Real.log Q + Real.log 100 - Q ^ P.gamma by ring,
      Real.exp_sub, Real.exp_add, Real.exp_log (by norm_num)]
    ring
  have hr2 : Tendsto (fun j : ℕ => ((2 : ℝ) ^ j) ^ 2 / (c * P.NQ (2 ^ j))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_sub_log (le_refl (0 : ℝ)) P.gamma_pos 2 (-Real.log c)).comp
      tendsto_two_pow
    have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h
    refine h2.congr fun j => ?_
    simp only [Function.comp, NQ_two_pow, Real.rpow_zero, mul_one]
    have hQ : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    set Q : ℝ := (2 : ℝ) ^ j
    have e2 : Real.exp (2 * Real.log Q) = Q ^ 2 := by
      rw [two_mul, Real.exp_add, Real.exp_log hQ]
      ring
    rw [show -(Q ^ P.gamma - 2 * Real.log Q - -Real.log c) =
      2 * Real.log Q - Real.log c - Q ^ P.gamma by ring,
      Real.exp_sub, Real.exp_sub, e2, Real.exp_log hc]
    field_simp
  obtain ⟨M1, hM1⟩ := hr1.bddAbove_range
  obtain ⟨M2, hM2⟩ := hr2.bddAbove_range
  set M : ℝ := max (max M1 M2) 1 with hM
  have hM0 : 0 < M := lt_max_of_lt_right one_pos
  refine ⟨1 / M, by positivity, fun δ hδ hδM => ⟨fun j => ?_, fun j => ?_⟩⟩
  · have h1 : 100 * Real.exp (100 * ((2 : ℝ) ^ j) ^ P.kappa * Real.log ((2 : ℝ) ^ j)) /
        P.NQ (2 ^ j) ≤ M := (hM1 ⟨j, rfl⟩).trans ((le_max_left _ _).trans (le_max_left _ _))
    have hN := P.NQ_pos (2 ^ j)
    rw [div_le_iff₀ hN] at h1
    have : δ * M ≤ 1 := by
      rw [le_div_iff₀ hM0] at hδM
      exact hδM
    calc 100 * δ * Real.exp (100 * ((2 : ℝ) ^ j) ^ P.kappa * Real.log ((2 : ℝ) ^ j))
        = δ * (100 * Real.exp (100 * ((2 : ℝ) ^ j) ^ P.kappa * Real.log ((2 : ℝ) ^ j))) := by
          ring
      _ ≤ δ * (M * P.NQ (2 ^ j)) := mul_le_mul_of_nonneg_left h1 hδ.le
      _ = (δ * M) * P.NQ (2 ^ j) := by ring
      _ ≤ 1 * P.NQ (2 ^ j) := mul_le_mul_of_nonneg_right this hN.le
      _ = P.NQ (2 ^ j) := one_mul _
  · have h1 : ((2 : ℝ) ^ j) ^ 2 / (c * P.NQ (2 ^ j)) ≤ M :=
      (hM2 ⟨j, rfl⟩).trans ((le_max_right _ _).trans (le_max_left _ _))
    have hN := P.NQ_pos (2 ^ j)
    rw [div_le_iff₀ (by positivity)] at h1
    have : δ * M ≤ 1 := by
      rw [le_div_iff₀ hM0] at hδM
      exact hδM
    calc δ * ((2 : ℝ) ^ j) ^ 2 ≤ δ * (M * (c * P.NQ (2 ^ j))) :=
          mul_le_mul_of_nonneg_left h1 hδ.le
      _ = (δ * M) * (c * P.NQ (2 ^ j)) := by ring
      _ ≤ 1 * (c * P.NQ (2 ^ j)) := mul_le_mul_of_nonneg_right this (by positivity)
      _ = c * P.NQ (2 ^ j) := one_mul _

end KQParams

end PrimeCarleson.Proof.Paper

/-! ### The support of `K̂_Q` under (C1), (C2) -/

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Paper.P5

namespace KQSetup

variable (S : KQSetup)

/-- The `1`-periodization `∑_{m ∈ ℤ} K̂_Q(β + m)` of the multiplier (the multiplier on `𝕋`); it
equals `K̂_Q(β - round β)` because the support of `K̂_Q` is far smaller than `1/2`. -/
def KQhatPer (Q : ℕ) (β : ℝ) : ℂ := ∑' m : ℤ, S.KQhat Q (β + m)

theorem exp_ge_two_pow (P : KQParams) (j : ℕ) :
    (2 : ℝ) ^ j ≤ Real.exp (100 * ((2 : ℝ) ^ j) ^ P.kappa * Real.log ((2 : ℝ) ^ j)) := by
  have hQ1 : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hlog : 0 ≤ Real.log ((2 : ℝ) ^ j) := Real.log_nonneg hQ1
  have hκ : 1 ≤ ((2 : ℝ) ^ j) ^ P.kappa := Real.one_le_rpow hQ1 P.kappa_pos.le
  calc (2 : ℝ) ^ j = Real.exp (Real.log ((2 : ℝ) ^ j)) := (Real.exp_log (by positivity)).symm
    _ ≤ _ := Real.exp_le_exp.2 (by nlinarith)

/-- Under (C1), `δ / N(Q) ≤ 1 / (100 Q)` for every `Q = 2^j`. -/
theorem delta_div_NQ_le (hS : S.P.SupportBlock S.δ) (j : ℕ) :
    S.δ / S.P.NQ (2 ^ j) ≤ 1 / (100 * (2 : ℝ) ^ j) := by
  have hN := S.P.NQ_pos (2 ^ j)
  have h1 := hS j
  have h2 := exp_ge_two_pow S.P j
  rw [div_le_div_iff₀ hN (by positivity)]
  have : 100 * S.δ * (2 : ℝ) ^ j ≤ 100 * S.δ * Real.exp (100 * ((2 : ℝ) ^ j) ^ S.P.kappa *
      Real.log ((2 : ℝ) ^ j)) :=
    mul_le_mul_of_nonneg_left h2 (by have := S.δ_pos; positivity)
  linarith

/-- Under (C1) the support of `K̂_Q` lies in `[-1/(100Q), 1/(100Q)]`, in particular in an interval
of length `≤ 1/10` (the hypothesis of `l:varcarZ`). -/
theorem support_KQhat_subset_of_block (hS : S.P.SupportBlock S.δ) (j : ℕ) :
    Function.support (S.KQhat (2 ^ j)) ⊆
      Set.Icc (-(1 / (100 * (2 : ℝ) ^ j))) (1 / (100 * (2 : ℝ) ^ j)) := by
  refine (S.support_KQhat_subset (2 ^ j)).trans ?_
  have := S.delta_div_NQ_le hS j
  intro β hβ
  rw [Set.mem_Icc] at hβ ⊢
  constructor <;> linarith [hβ.1, hβ.2]

/-- Under (C2) the support of `K̂_Q` lies in `[-c Q^{-2}, c Q^{-2}]` (Source: main paper
`p:global-shell-var`, L2028–L2029: "a neighbourhood of `0` of size `≲ c Q^{-2}`"). -/
theorem support_KQhat_subset_of_scale {c : ℝ} (hS : S.P.SupportScale S.δ c) (j : ℕ) :
    Function.support (S.KQhat (2 ^ j)) ⊆
      Set.Icc (-(c / ((2 : ℝ) ^ j) ^ 2)) (c / ((2 : ℝ) ^ j) ^ 2) := by
  refine (S.support_KQhat_subset (2 ^ j)).trans ?_
  have hN := S.P.NQ_pos (2 ^ j)
  have h1 : S.δ / S.P.NQ (2 ^ j) ≤ c / ((2 : ℝ) ^ j) ^ 2 := by
    rw [div_le_div_iff₀ hN (by positivity)]
    linarith [hS j]
  intro β hβ
  rw [Set.mem_Icc] at hβ ⊢
  constructor <;> linarith [hβ.1, hβ.2]

/-- **The Fourier support of `K̂_Q`** (Source: main paper `p:transferprop`, L2224–L2227): under
(C1), for every block `B ⊆ sqfreeSet j` with `|B| ≤ 100 Q^κ`, `K̂_Q` is supported in
`{|β| ≤ (100 𝒬_B)⁻¹}`, and its periodization in `{‖β‖_𝕋 ≤ (100 𝒬_B)⁻¹}`. -/
theorem support_of_KQhat (hS : S.P.SupportBlock S.δ) {j : ℕ} {B : Finset ℕ}
    (hB : B ⊆ sqfreeSet j) (hcard : (B.card : ℝ) ≤ 100 * ((2 : ℝ) ^ j) ^ S.P.kappa) :
    (∀ β : ℝ, (100 * (lcmQ B : ℝ))⁻¹ < |β| → S.KQhat (2 ^ j) β = 0) ∧
    (∀ β : ℝ, (100 * (lcmQ B : ℝ))⁻¹ < torusNorm β → S.KQhatPer (2 ^ j) β = 0) := by
  have hpos : 0 < lcmQ B :=
    lcmQ_pos fun q hq => Nat.pos_of_ne_zero (mem_sqfreeSet.1 (hB hq)).2.2.ne_zero
  have hQB : (0 : ℝ) < lcmQ B := by exact_mod_cast hpos
  have hN := S.P.NQ_pos (2 ^ j)
  have hle : S.δ / S.P.NQ (2 ^ j) ≤ (100 * (lcmQ B : ℝ))⁻¹ := by
    rw [div_le_iff₀ hN, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
    have h1 := hS j
    have h2 := lcmQ_le_exp hB hcard
    have h3 : 100 * S.δ * (lcmQ B : ℝ) ≤ 100 * S.δ * Real.exp (100 * ((2 : ℝ) ^ j) ^ S.P.kappa *
        Real.log ((2 : ℝ) ^ j)) :=
      mul_le_mul_of_nonneg_left h2 (by have := S.δ_pos; positivity)
    linarith
  have h0 : ∀ β : ℝ, (100 * (lcmQ B : ℝ))⁻¹ < |β| → S.KQhat (2 ^ j) β = 0 := fun β hβ =>
    S.KQhat_eq_zero _ (lt_of_le_of_lt hle hβ)
  refine ⟨h0, fun β hβ => ?_⟩
  unfold KQhatPer
  have hm : ∀ m : ℤ, S.KQhat (2 ^ j) (β + m) = 0 := fun m =>
    h0 _ (lt_of_lt_of_le hβ (by
      have := torusNorm_le_abs_sub β (-m)
      simpa [sub_neg_eq_add] using this))
  simp [hm]

/-- Under (C1), for `1 ≤ d ≤ Q = 2^j` the multiplier `ξ ↦ K̂_Q(ξ/d)` of `K_{Q,d}` is supported in
`[-1/100, 1/100] ⊆ (-1/2, 1/2]`, the hypothesis of the `multiplierOpDis` /
`msw_transference_variation`. -/
theorem support_KQdhat_subset_Ioc (hS : S.P.SupportBlock S.δ) {j d : ℕ} (hd : 1 ≤ d)
    (hdQ : d ≤ 2 ^ j) : Function.support (S.KQdhat (2 ^ j) d) ⊆ Set.Ioc (-1 / 2) (1 / 2) := by
  intro ξ hξ
  by_contra hcon
  apply hξ
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hdQ' : (d : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast hdQ
  have h1 := S.delta_div_NQ_le hS j
  have h2 : (d : ℝ) * (S.δ / S.P.NQ (2 ^ j)) ≤ 1 / 100 := by
    calc (d : ℝ) * (S.δ / S.P.NQ (2 ^ j)) ≤ (2 : ℝ) ^ j * (1 / (100 * (2 : ℝ) ^ j)) :=
          mul_le_mul hdQ' h1 (by have := S.δ_pos; have := S.P.NQ_pos (2 ^ j); positivity)
            (by positivity)
      _ = 1 / 100 := by field_simp
  refine S.KQdhat_eq_zero hd _ ?_
  rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hcon
  rcases hcon with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-- **Uniform bounded variation and small support of `K̂_Q`** (Source: main paper
`p:global-shell-var`, L2028–L2029): `K̂_Q` has total variation and sup norm bounded by a constant
`C` depending only on `ψ` and `φ` (uniformly in `Q`, `D₀`, `ε`), is supported in an interval of
length `≤ 1/10` (the hypothesis of `l:varcarZ`) under (C1) and in `[-c Q^{-2}, c Q^{-2}]` under
(C2). -/
theorem KQ_multiplier_properties (hS : S.P.SupportBlock S.δ) {c : ℝ}
    (hc : S.P.SupportScale S.δ c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ,
      (∀ β, ‖S.KQhat (2 ^ j) β‖ ≤ C) ∧
      eVariationOn (S.KQhat (2 ^ j)) Set.univ ≤ ENNReal.ofReal C ∧
      Function.support (S.KQhat (2 ^ j)) ⊆ Set.Icc (-(1 / 20)) (1 / 20) ∧
      Function.support (S.KQhat (2 ^ j)) ⊆
        Set.Icc (-(c / ((2 : ℝ) ^ j) ^ 2)) (c / ((2 : ℝ) ^ j) ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := S.KQhat_bv
  refine ⟨C, hC0, fun j => ⟨(hC S.P _).1, (hC S.P _).2, ?_, S.support_KQhat_subset_of_scale hc j⟩⟩
  refine (S.support_KQhat_subset_of_block hS j).trans ?_
  have h1 : (1 : ℝ) / (100 * (2 : ℝ) ^ j) ≤ 1 / 20 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    linarith
  intro β hβ
  rw [Set.mem_Icc] at hβ ⊢
  constructor <;> linarith [hβ.1, hβ.2]

/-- **Uniform bounded variation of the rescaled multipliers** (Source: main paper `s:red`,
L1694–L1695): the multipliers `ξ ↦ K̂_Q(ξ/d)` of the rescaled kernels `K_{Q,d}(m) = d K_Q(d m)`,
`1 ≤ d ≤ Q`, are supported in `(-1/2, 1/2]` and have sup norm and total variation at most
`C = C(ψ, φ)`, uniformly in `Q = 2^j` and `d ≤ Q`; and `K_{Q,d}(m) = ∫ K̂_Q(ξ/d) e(mξ) dξ`. -/
theorem KQd_uniform_BV (hS : S.P.SupportBlock S.δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j d : ℕ, 1 ≤ d → d ≤ 2 ^ j →
      (∀ ξ, ‖S.KQdhat (2 ^ j) d ξ‖ ≤ C) ∧
      eVariationOn (S.KQdhat (2 ^ j) d) Set.univ ≤ ENNReal.ofReal C ∧
      Function.support (S.KQdhat (2 ^ j) d) ⊆ Set.Ioc (-1 / 2) (1 / 2) ∧
      ∀ m : ℤ, S.KQd (2 ^ j) d m = ∫ ξ, S.KQdhat (2 ^ j) d ξ * e (m * ξ) := by
  obtain ⟨C, hC0, hC⟩ := S.KQdhat_bv
  exact ⟨C, hC0, fun j d hd hdQ => ⟨(hC S.P _ _ hd).1, (hC S.P _ _ hd).2,
    S.support_KQdhat_subset_Ioc hS hd hdQ, fun m => S.KQd_eq_integral hd _ m⟩⟩

end KQSetup

end PrimeCarleson.Proof.Paper
