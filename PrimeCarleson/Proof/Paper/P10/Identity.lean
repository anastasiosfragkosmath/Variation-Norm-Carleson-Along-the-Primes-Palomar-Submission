module

public import PrimeCarleson.Proof.Paper.P10.Statistics
public import PrimeCarleson.Proof.Paper.P10.Linearization
public import PrimeCarleson.Proof.Paper.P9.VarCarInput

/-!
# The key identity

Source: main paper `e:keyidentity`, L2256–L2259; main paper `p:transferprop`, L2220–L2237 (the
densities) and L2224–L2227 (the Fourier support of `K_Q`, used here).

Fix `N = 𝒬_B` and a window `u`: `ω ∈ [u, u + 1/(2N)]`. The multiplier `K̂_Q` vanishes for
`|β| > w = 1/(100 N)` (Source: main paper `p:transferprop`, L2224–L2227; `P5/`), so for such `ω` the
multiplier `m_ω(β) = K̂_Q(β - ω)` is supported in `I_u = [u - w, u + 1/(2N) + w]`, an interval of
length `13/(25 N) < 1/N`. The pieces of `f` are the densities
`F̂_R(β) = 1_{I_u}(β) f̂(β + R/N)` (`winDens`), `R ∈ ℤ/N` (the paper's `ρ(Nβ) f̂(β + R/N)`, with
a sharp cutoff `1_{I_u}` in place of the smooth `ρ`: since `|I_u| < 1/N`, the translates
`I_u + R/N` are disjoint mod `1`, see `Decomposition.lean`).

* `keyidentity` (`e:keyidentity`): for `λ = ϑ(x)/N + ω`,
  `T^{Q,B}_λ f(x) = ∑_{R ∈ ℤ/N} g_R(x) (m_ω^v * F_R)(x)`, i.e. `aSum` of `P9/Variable.lean` for the
  coefficients `g_R(x) = b(R - ϑ(x)) e_N(R x)` (`gcoefR`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

/-! ### The window data -/

/-- Left end of the interval `I_u = [u - 1/(100 N), u + 1/(2N) + 1/(100 N)]`. -/
def winLo (N : ℕ) (u : ℝ) : ℝ := u - 1 / (100 * N)

/-- Right end of the interval `I_u`. -/
def winHi (N : ℕ) (u : ℝ) : ℝ := u + 1 / (2 * N) + 1 / (100 * N)

/-- The scale `c = |I_u|/100 = 13/(2500 N)` of the cutoffs `φ_I`. -/
def winScale (N : ℕ) : ℝ := 13 / (2500 * N)

/-- The coordinate chart `[u - 1/4, u + 3/4]` containing `I_u + [-4c, 4c]`. -/
def winChart (u : ℝ) : ℝ := u - 1 / 4

theorem winHi_sub_winLo {N : ℕ} (hN : 0 < N) (u : ℝ) : winHi N u - winLo N u = 13 / (25 * N) := by
  have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold winHi winLo
  field_simp
  ring

theorem winScale_pos {N : ℕ} (hN : 0 < N) : 0 < winScale N := by
  unfold winScale
  have : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

/-- `I_u` has length `< 1/N`, so the translates `I_u + R/N` are disjoint. -/
theorem winHi_sub_winLo_lt {N : ℕ} (hN : 0 < N) (u : ℝ) : winHi N u - winLo N u < 1 / N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [winHi_sub_winLo hN, div_lt_div_iff₀ (by positivity) hNR]
  nlinarith

/-- **The cutoffs of the window** (Source: main paper `p:transferprop`, L2164–L2170; existence): the
cutoffs `χ_I, φ_I` for the window interval `I_u` with scale `c = |I_u|/100`, in the chart
`[u - 1/4, u + 3/4]`. -/
theorem window_cutoff {N : ℕ} (hN : 0 < N) (u : ℝ) :
    Nonempty (CutoffData (winChart u) (winLo N u) (winHi N u) (winScale N)) := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlen := winHi_sub_winLo hN u
  refine CutoffData.nonempty (winScale_pos hN) ?_ ?_ ?_
  · rw [hlen]
    unfold winScale
    rw [show (100 : ℝ) * (13 / (2500 * N)) = 13 / (25 * N) by field_simp; ring]
  · unfold winChart winLo winScale
    have h1 : 1 / (100 * (N : ℝ)) ≤ 1 / 100 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have h2 : 4 * (13 / (2500 * (N : ℝ))) ≤ 4 * (13 / 2500) := by
      have : 13 / (2500 * (N : ℝ)) ≤ 13 / 2500 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    linarith
  · unfold winChart winHi winScale
    have h1 : 1 / (2 * (N : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have h2 : 1 / (100 * (N : ℝ)) ≤ 1 / 100 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have h3 : 4 * (13 / (2500 * (N : ℝ))) ≤ 4 * (13 / 2500) := by
      have : 13 / (2500 * (N : ℝ)) ≤ 13 / 2500 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    linarith

/-! ### The densities `F̂_R` and the multiplier support -/

/-- `F̂_R(β) = 1_{I_u}(β) f̂(β + R/N)` for `R ∈ ℤ/N` (Source: main paper `p:transferprop`,
L2220–L2237). -/
def winDens (N : ℕ) (u : ℝ) (f : ℤ →₀ ℂ) (R : Fin N) (β : ℝ) : ℂ :=
  if β ∈ Set.Icc (winLo N u) (winHi N u) then fourierZ f (β + ((R : ℕ) : ℝ) / N) else 0

theorem winDens_eq_zero {N : ℕ} {u : ℝ} {f : ℤ →₀ ℂ} (R : Fin N) {β : ℝ}
    (hβ : β ∉ Set.Icc (winLo N u) (winHi N u)) : winDens N u f R β = 0 := by
  unfold winDens
  rw [ite_eq_right hβ]

theorem measurable_winDens (N : ℕ) (u : ℝ) (f : ℤ →₀ ℂ) (R : Fin N) :
    Measurable (winDens N u f R) := by
  unfold winDens
  refine Measurable.ite measurableSet_Icc ?_ measurable_const
  exact (continuous_fourierZ f).measurable.comp (measurable_id.add_const _)

theorem norm_winDens_le (N : ℕ) (u : ℝ) (f : ℤ →₀ ℂ) (R : Fin N) (β : ℝ) :
    ‖winDens N u f R β‖ ≤ f.sum (fun _ c => ‖c‖) := by
  unfold winDens
  split_ifs
  · exact norm_fourierZ_le f _
  · simp only [norm_zero]
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem chartL2_winDens (N : ℕ) (u : ℝ) (f : ℤ →₀ ℂ) (R : Fin N) (θ : ℝ) :
    ChartL2 θ (winDens N u f R) :=
  ChartL2.of_bound (measurable_winDens N u f R).aestronglyMeasurable
    (M := f.sum (fun _ c => ‖c‖)) fun β _ => norm_winDens_le N u f R β

/-- If `K̂_Q` vanishes off `|β| ≤ 1/(100N)` and `ω ∈ [u, u + 1/(2N)]`, then `K̂_Q(· - ω)` vanishes
off `I_u`. -/
theorem KQmult_eq_zero_of_not_mem (S : KQSetup) {Q N : ℕ}
    (hsupp : ∀ β : ℝ, 1 / (100 * (N : ℝ)) < |β| → S.KQhat Q β = 0) {u ω : ℝ} (h1 : u ≤ ω)
    (h2 : ω ≤ u + 1 / (2 * N)) {β : ℝ} (hβ : β ∉ Set.Icc (winLo N u) (winHi N u)) :
    S.KQmult Q ω β = 0 := by
  unfold KQSetup.KQmult
  apply hsupp
  by_contra hle
  push Not at hle
  rw [abs_le] at hle
  apply hβ
  unfold winLo winHi
  constructor <;> linarith [hle.1, hle.2]

/-- **The kernel of `K_λ`** (generalization of `KQSetup.invFZ_KQmult`): if `K̂_Q` vanishes off
`|β| ≤ w`, the chart contains `[λ - w, λ + w]`, then `invFZ θ (K̂_Q(· - λ)) (z) = e(λ z) K_Q(z)`. -/
theorem KQSetup.invFZ_KQmult' (S : KQSetup) (Q : ℕ) {θ lam w : ℝ}
    (hsupp : ∀ β : ℝ, w < |β| → S.KQhat Q β = 0) (hlo : θ < lam - w) (hhi : lam + w < θ + 1)
    (z : ℤ) : invFZ θ (S.KQmult Q lam) z = e (lam * z) * S.KQz Q z := by
  unfold invFZ KQSetup.KQmult KQSetup.KQz KQSetup.KQ
  rw [intervalIntegral.integral_of_le (by linarith)]
  have h1 : ∫ β in Set.Ioc θ (θ + 1), S.KQhat Q (β - lam) * e ((z : ℝ) * β) =
      ∫ β, S.KQhat Q (β - lam) * e ((z : ℝ) * β) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun β hβ => ?_
    rw [hsupp _ ?_, zero_mul]
    by_contra hle
    push Not at hle
    apply hβ
    rw [abs_le] at hle
    constructor <;> linarith [hle.1, hle.2]
  rw [h1]
  have h2 : ∀ β : ℝ, S.KQhat Q (β - lam) * e ((z : ℝ) * β) =
      e (lam * z) * (S.KQhat Q (β - lam) * e ((z : ℝ) * (β - lam))) := by
    intro β
    have : e ((z : ℝ) * β) = e (lam * z) * e ((z : ℝ) * (β - lam)) := by
      rw [← e_add]; congr 1; ring
    rw [this]; ring
  simp_rw [h2]
  rw [integral_const_mul]
  congr 1
  exact integral_sub_right_eq_self (fun ξ => S.KQhat Q ξ * e ((z : ℝ) * ξ)) lam

/-! ### The key identity -/

section KeyIdentity

variable (S : KQSetup)

/-- One piece of the key identity: for `γ = R/N`,
`e(γ x) (m_ω^v * F_R)(x) = ∑_{k ∈ supp f} f(k) K_Q(x - k) e((ω + γ)(x - k))`. -/
theorem exp_mul_kseq_winDens {Q N : ℕ} (hN : 0 < N)
    (hsupp : ∀ β : ℝ, 1 / (100 * (N : ℝ)) < |β| → S.KQhat Q β = 0) {u ω : ℝ} (h1 : u ≤ ω)
    (h2 : ω ≤ u + 1 / (2 * N)) (hN1 : (1 : ℝ) ≤ N) (f : ℤ →₀ ℂ) (R : Fin N) (x : ℤ) :
    e ((((R : ℕ) : ℝ) / N) * x) *
        KSeq (winChart u) (fun t β => S.KQmult Q t β) (winDens N u f) ω R x =
      ∑ k ∈ f.support, f k * S.KQz Q (x - k) *
        e ((ω + ((R : ℕ) : ℝ) / N) * ((x - k : ℤ) : ℝ)) := by
  set γ : ℝ := ((R : ℕ) : ℝ) / N with hγ
  have hw : 1 / (100 * (N : ℝ)) ≤ 1 / 100 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hw2 : 1 / (2 * (N : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h1' : (fun β => S.KQmult Q ω β * winDens N u f R β) =
      fun β => S.KQmult Q ω β * fourierZ (modF f γ) β := by
    funext β
    by_cases hβ : β ∈ Set.Icc (winLo N u) (winHi N u)
    · rw [fourierZ_modF]
      simp only [winDens, hβ, ite_true, hγ]
    · rw [KQmult_eq_zero_of_not_mem S hsupp h1 h2 hβ]
      simp
  unfold KSeq
  rw [h1', ← invFZ_conv_fourierZ (S.chartL2_KQmult Q ω (winChart u)) (modF f γ) x]
  rw [Finset.sum_subset (s₁ := (modF f γ).support) (s₂ := f.support) (fun k hk => by
      simp only [Finsupp.mem_support_iff, modF, Finsupp.onFinset_apply] at hk ⊢
      intro h; exact hk (by simp [h])) (fun k _ hk => by
      simp [Finsupp.notMem_support_iff.1 hk])]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [S.invFZ_KQmult' Q hsupp (w := 1 / (100 * (N : ℝ))) (lam := ω) (θ := winChart u)
    (by unfold winChart; linarith) (by unfold winChart; linarith)]
  simp only [modF, Finsupp.onFinset_apply]
  have : e (γ * (x : ℝ)) * e (-(γ * (k : ℝ))) * e (ω * ((x - k : ℤ) : ℝ)) =
      e ((ω + γ) * ((x - k : ℤ) : ℝ)) := by
    rw [← e_add, ← e_add]; congr 1; push_cast; ring
  rw [← this]
  ring

/-- **`e:keyidentity`** (L2256-L2277): for `λ = ϑ(x)/N + ω` with `ω ∈ [u, u + 1/(2N)]`,
`∑_n f(x-n) w_{Q,B}(n) K_Q(n) e(λ n) = ∑_{R ∈ ℤ/N} g_R(x) (m_ω^v * F_R)(x)`. -/
theorem keyidentity {Q : ℕ} {B : Finset ℕ} (hB : ∀ q ∈ B, 0 < q)
    (hsupp : ∀ β : ℝ, 1 / (100 * (lcmQ B : ℝ)) < |β| → S.KQhat Q β = 0) {u ω : ℝ}
    (h1 : u ≤ ω) (h2 : ω ≤ u + 1 / (2 * (lcmQ B : ℝ))) (f : ℤ →₀ ℂ) (x : ℤ) (ϑ : ℤ → ℤ) :
    S.TQB Q B ((ϑ x : ℝ) / (lcmQ B : ℝ) + ω) f x =
      aSum (winChart u) (gcoefR B ϑ) (fun t β => S.KQmult Q t β) (winDens (lcmQ B) u f) ω x := by
  classical
  have hN : 0 < lcmQ B := lcmQ_pos hB
  have hNR : (1 : ℝ) ≤ lcmQ B := by exact_mod_cast hN
  have hN0 : (lcmQ B : ℝ) ≠ 0 := by positivity
  set N := lcmQ B with hNdef
  -- the right side as a sum over `R`
  have hRHS : aSum (winChart u) (gcoefR B ϑ) (fun t β => S.KQmult Q t β) (winDens N u f) ω x =
      ∑ R ∈ Finset.range N, bcoef B ((R : ℤ) - ϑ x) * ∑ k ∈ f.support,
        f k * S.KQz Q (x - k) * e ((ω + (R : ℝ) / N) * ((x - k : ℤ) : ℝ)) := by
    unfold aSum
    rw [← Fin.sum_univ_eq_sum_range (fun R : ℕ => bcoef B ((R : ℤ) - ϑ x) * ∑ k ∈ f.support,
        f k * S.KQz Q (x - k) * e ((ω + (R : ℝ) / N) * ((x - k : ℤ) : ℝ))) N]
    refine Finset.sum_congr rfl fun R _ => ?_
    rw [← exp_mul_kseq_winDens S hN hsupp h1 h2 hNR f R x]
    simp only [gcoefR]
    have : e ((x : ℝ) * (R : ℕ) / (N : ℝ)) = e ((((R : ℕ) : ℝ) / N) * x) := by
      congr 1; ring
    rw [this]
    ring
  rw [hRHS, S.TQB_eq_sum]
  -- expand `w_{Q,B}` and regroup
  set P : ℤ → ℂ := fun D => bcoef B D * ∑ k ∈ f.support, f k * S.KQz Q (x - k) *
      e (((ϑ x : ℝ) / N + ω + (D : ℝ) / N) * ((x - k : ℤ) : ℝ)) with hP
  have hPper : Function.Periodic P (N : ℤ) := by
    intro D
    simp only [hP]
    rw [bcoef_add_period B D]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    have : (((ϑ x : ℝ) / N + ω + ((D + (N : ℤ) : ℤ) : ℝ) / N) * ((x - k : ℤ) : ℝ)) =
        ((ϑ x : ℝ) / N + ω + (D : ℝ) / N) * ((x - k : ℤ) : ℝ) + ((x - k : ℤ) : ℝ) := by
      push_cast
      field_simp
      ring
    rw [this, e_add, e_intCast, mul_one]
  have hshift := sum_range_add_of_periodic hPper (-(ϑ x))
  have hL : ∑ k ∈ f.support, f k * (blockWeight B (x - k) * S.KQz Q (x - k)) *
      e (((ϑ x : ℝ) / N + ω) * ((x - k : ℤ) : ℝ)) =
      ∑ D ∈ Finset.range N, P (D : ℤ) := by
    simp only [hP]
    have h1 : ∀ k ∈ f.support, f k * (blockWeight B (x - k) * S.KQz Q (x - k)) *
        e (((ϑ x : ℝ) / N + ω) * ((x - k : ℤ) : ℝ)) =
        ∑ D ∈ Finset.range N, bnat B D * (f k * S.KQz Q (x - k) *
          e (((ϑ x : ℝ) / N + ω + (D : ℝ) / N) * ((x - k : ℤ) : ℝ))) := by
      intro k _
      rw [blockWeight_eq_sum_bnat hB, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun D _ => ?_
      have : e (((ϑ x : ℝ) / N + ω + (D : ℝ) / N) * ((x - k : ℤ) : ℝ)) =
          e (((ϑ x : ℝ) / N + ω) * ((x - k : ℤ) : ℝ)) * e (((x - k : ℤ) : ℝ) * D / N) := by
        rw [← e_add]; congr 1; ring
      rw [this]
      ring
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun D hD => ?_
    rw [bcoef_natCast B (Finset.mem_range.1 hD), Finset.mul_sum]
    simp only [Int.cast_natCast]
  rw [hL, ← hshift]
  refine Finset.sum_congr rfl fun R _ => ?_
  simp only [hP]
  rw [sub_eq_add_neg]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  push_cast
  ring

end KeyIdentity

end PrimeCarleson.Proof.Paper
