module

public import PrimeCarleson.Proof.Paper.P5.Cutoff
public import PrimeCarleson.Proof.Paper.Defs.Psi
public import PrimeCarleson.Proof.Paper.Defs.Weights
public import PrimeCarleson.Proof.Paper.Defs.Modulated
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The kernel `K_Q`, the operators `T^Q_λ`, `V^{Q,r}`, `C^Q`, `C^Q_B`

Source: main paper, L1188–L1220 (`e:KQ`, `e:CQvar`), L1943–L1952 and L2098–L2101.

## Parameters

`KQParams` packages `D₀`, `ε` of L1188-L1190 (`κ = 1/D₀ - ε`, `0 < ε ≤ κ/100`, L2084-L2088); the
paper's "`D₀` sufficiently large, `ε` sufficiently small depending on `(p, r)`" is the free
choice of the structure (`KQParams.exists_ge`). `N(Q) = exp(Q^{1/D₀ - ε/10})` is `NQ`.

## The multiplier first

As for the `multiplierOpDis`, the kernel is defined from its multiplier
`K̂_Q(β) = φ̂(N(Q) β) ∑_{k ≥ ⌈Q^{1/D₀}⌉} ψ̂(2^k β)` (`KQhat`), on `ℝ`:
`K_Q(x) = ∫ K̂_Q(ξ) e(xξ) dξ` (`KQ`), `K_Q(n) = KQz n` on `ℤ`. This is the `ℝ` convolution form
(the support claim at L2224 needs it): `K̂_Q` is supported in `[-δ/N(Q), δ/N(Q)]`
(`KQhat_eq_zero`), a tiny neighbourhood of `0` inside `(-1/2, 1/2]`. The paper's convolution
`K_Q = φ_{N(Q)} * ∑_{k ≥ k₀} ψ_k` has exactly this Fourier transform (`φ̂_N = φ̂(N ·)`,
`(ψ_k)^ = ψ̂(2^k ·)`, `psiK_hat`); the identity itself is not proved here.

## Operators

`TQ` (`T^Q_λ f(x) = ∑_n f(x-n) w_Q(n) K_Q(n) e(λ n)`, the shared `weightedModSum` with
`w = w_Q K_Q`), `VQr` (`V^{Q,r} f(x) = V^r(T^Q_λ f(x) : λ ∈ 𝕋)`, `𝕋 = [0, 1)`), `CQ`
(`C^Q f(x) = sup_{λ ∈ 𝕋} |T^Q_λ f(x)|`), `TQB`, `CQB` (`w_{Q,B}` in place of `w_Q`), for
`f : ℤ → ℂ` (finitely supported in every use); `ℝ≥0∞`-valued as the `carlesonMax`.

The cutoff data `ψ : PsiData`, `φ : PhiData δ` are fixed once: `KQSetup`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-! ### The parameters `D₀`, `ε` -/

/-- The parameters of `K_Q` (L1188-L1190, L2083-L2088): `D₀ > 0`, `ε > 0`, `κ = 1/D₀ - ε` and
`ε ≤ κ/100` (e:epskappa), which forces `κ ≥ 100 ε > 0`. -/
structure KQParams where
  /-- `D₀`. -/
  D₀ : ℝ
  /-- `ε`. -/
  ε : ℝ
  /-- `D₀ > 0`. -/
  D₀_pos : 0 < D₀
  /-- `ε > 0`. -/
  ε_pos : 0 < ε
  /-- `ε ≤ κ/100` (e:epskappa). -/
  eps_le_kappa : ε ≤ (1 / D₀ - ε) / 100

namespace KQParams

variable (P : KQParams)

/-- `κ = 1/D₀ - ε` (e:kappa, L2083-L2086). -/
def kappa : ℝ := 1 / P.D₀ - P.ε

/-- The exponent `1/D₀ - ε/10` of `N(Q)`. -/
def gamma : ℝ := 1 / P.D₀ - P.ε / 10

/-- `N(Q) = exp(Q^{1/D₀ - ε/10})` (L1199-L1203). -/
def NQ (Q : ℕ) : ℝ := Real.exp ((Q : ℝ) ^ P.gamma)

/-- The least `k` with `Q^{1/D₀} ≤ k` (the range `Q^{1/D₀} ≤ k` of (e:KQ), `k : ℕ`). -/
def kmin (Q : ℕ) : ℕ := ⌈(Q : ℝ) ^ (1 / P.D₀)⌉₊

theorem hundred_eps_le_kappa : 100 * P.ε ≤ P.kappa := by
  have := P.eps_le_kappa
  unfold kappa
  linarith

theorem kappa_pos : 0 < P.kappa := by
  have := P.hundred_eps_le_kappa
  have := P.ε_pos
  linarith

theorem kappa_lt_gamma : P.kappa < P.gamma := by
  have := P.ε_pos
  unfold kappa gamma
  linarith

theorem gamma_pos : 0 < P.gamma := P.kappa_pos.trans P.kappa_lt_gamma

/-- `γ < 1/D₀`. -/
theorem gamma_lt_inv : P.gamma < 1 / P.D₀ := by
  have := P.ε_pos
  unfold gamma
  linarith

/-- `ε ≤ κ/100` is `ε ≤ 1/(101 D₀)`. -/
theorem eps_le_iff {D₀ ε : ℝ} (hD : 0 < D₀) :
    ε ≤ (1 / D₀ - ε) / 100 ↔ ε ≤ 1 / (101 * D₀) := by
  have hD' : D₀ ≠ 0 := hD.ne'
  rw [show 1 / (101 * D₀) = (1 / D₀) / 101 by field_simp]
  constructor <;> intro h <;> linarith

theorem NQ_pos (Q : ℕ) : 0 < P.NQ Q := Real.exp_pos _

theorem rpow_le_kmin (Q : ℕ) : (Q : ℝ) ^ (1 / P.D₀) ≤ P.kmin Q := Nat.le_ceil _

theorem one_le_kmin {Q : ℕ} (hQ : 1 ≤ Q) : 1 ≤ P.kmin Q := by
  unfold kmin
  refine Nat.one_le_iff_ne_zero.2 ?_
  rw [Ne, Nat.ceil_eq_zero, not_le]
  exact Real.rpow_pos_of_pos (by exact_mod_cast hQ) _

/-- Admissible parameters exist with `D₀` arbitrarily large: `ε = 1/(101 D₀)`. -/
theorem exists_ge (D₁ : ℝ) : ∃ P : KQParams, D₁ ≤ P.D₀ ∧ P.ε = 1 / (101 * P.D₀) := by
  refine ⟨⟨max D₁ 1, 1 / (101 * max D₁ 1), lt_max_of_lt_right one_pos, by positivity,
    (eps_le_iff (lt_max_of_lt_right one_pos)).2 le_rfl⟩, le_max_left _ _, rfl⟩

end KQParams

/-! ### The data of `K_Q` and the multiplier -/

/-- The Fourier transform `ψ̂(u) = ∫ ψ(t) e(-tu) dt` of the real function `ψ`. -/
def psiHat (ψ : PsiData) (u : ℝ) : ℂ := 𝓕 (fun t : ℝ => ((ψ.toFun t : ℝ) : ℂ)) u

/-- The tail `∑_{k ≥ k₀} ψ̂(2^k β)`. -/
def psiTail (ψ : PsiData) (k₀ : ℕ) (β : ℝ) : ℂ := ∑' i : ℕ, psiHat ψ (2 ^ (k₀ + i) * β)

/-- The fixed data of `K_Q` (L1188-L1203): the dyadic piece `ψ`, the cutoff `φ` with
`φ̂ = 1` on `[-δ/2, δ/2]` and `supp φ̂ ⊆ [-δ, δ]` (`0 < δ`), and the parameters `D₀`, `ε`. -/
structure KQSetup where
  /-- The dyadic decomposition `ψ`. -/
  ψ : PsiData
  /-- The radius `δ` of the support of `φ̂`. -/
  δ : ℝ
  /-- `δ > 0`. -/
  δ_pos : 0 < δ
  /-- The cutoff `φ`. -/
  φ : PhiData δ
  /-- The parameters `D₀`, `ε`. -/
  P : KQParams

namespace KQSetup

variable (S : KQSetup)

/-- The multiplier `K̂_Q(β) = φ̂(N(Q) β) ∑_{k ≥ ⌈Q^{1/D₀}⌉} ψ̂(2^k β)` (Source: main paper `e:KQ`,
L1193–L1203). -/
def KQhat (Q : ℕ) (β : ℝ) : ℂ :=
  S.φ.hat (S.P.NQ Q * β) * psiTail S.ψ (S.P.kmin Q) β

/-- The kernel `K_Q(x) = ∫ K̂_Q(ξ) e(xξ) dξ` on `ℝ`. -/
def KQ (Q : ℕ) (x : ℝ) : ℂ := ∫ ξ, S.KQhat Q ξ * e (x * ξ)

/-- The kernel `K_Q(n)`, `n ∈ ℤ`. -/
def KQz (Q : ℕ) (n : ℤ) : ℂ := S.KQ Q n

/-- The multiplier of the rescaled kernel `K_{Q,d}(m) = d K_Q(d m)` (L1694), `ξ ↦ K̂_Q(ξ / d)`. -/
def KQdhat (Q d : ℕ) (ξ : ℝ) : ℂ := S.KQhat Q (ξ / d)

/-- The rescaled kernel `K_{Q,d}(m) = d K_Q(d m)` (L1694-L1695). -/
def KQd (Q d : ℕ) (m : ℤ) : ℂ := (d : ℂ) * S.KQz Q ((d : ℤ) * m)

/-- `K_{Q,d}(m) = ∫ K̂_Q(ξ / d) e(mξ) dξ`: the multiplier of `K_{Q,d}` is `KQdhat`. -/
theorem KQd_eq_integral {d : ℕ} (hd : 1 ≤ d) (Q : ℕ) (m : ℤ) :
    S.KQd Q d m = ∫ ξ, S.KQdhat Q d ξ * e (m * ξ) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  unfold KQd KQz KQ KQdhat
  have h := Measure.integral_comp_div (fun y : ℝ => S.KQhat Q y * e (((((d : ℤ) * m : ℤ)) : ℝ) * y))
    (d : ℝ)
  rw [abs_of_pos hd0] at h
  have h2 : ∀ ξ : ℝ, S.KQhat Q (ξ / d) * e ((((d : ℤ) * m : ℤ) : ℝ) * (ξ / d)) =
      S.KQhat Q (ξ / d) * e (m * ξ) := by
    intro ξ
    congr 2
    push_cast
    field_simp
  simp only [h2] at h
  rw [h, Complex.real_smul]
  push_cast
  ring

/-- The multiplier vanishes for `|β| > δ / N(Q)`. -/
theorem KQhat_eq_zero (Q : ℕ) {β : ℝ} (hβ : S.δ / S.P.NQ Q < |β|) : S.KQhat Q β = 0 := by
  unfold KQhat
  have hN := S.P.NQ_pos Q
  rw [S.φ.hat_eq_zero, zero_mul]
  rw [div_lt_iff₀ hN] at hβ
  rw [abs_mul, abs_of_pos hN]
  linarith

/-! ### The operators `T^Q_λ`, `V^{Q,r}`, `C^Q`, `C^Q_B` -/

/-- `T^Q_λ f(x) = ∑_n f(x - n) w_Q(n) K_Q(n) e(λ n)` (Source: main paper, L1943–L1947), a sum over
`ℤ` (finite for finitely supported `f`). -/
def TQ (Q : ℕ) (lam : ℝ) (f : ℤ → ℂ) (x : ℤ) : ℂ :=
  weightedModSum (fun n => wQ Q n * S.KQz Q n) f lam x

/-- `T^{Q,B}_λ f(x) = ∑_n f(x - n) w_{Q,B}(n) K_Q(n) e(λ n)` (the operator inside `C^Q_B`). -/
def TQB (Q : ℕ) (B : Finset ℕ) (lam : ℝ) (f : ℤ → ℂ) (x : ℤ) : ℂ :=
  weightedModSum (fun n => blockWeight B n * S.KQz Q n) f lam x

/-- `V^{Q,r} f(x) = V^r(T^Q_λ f(x) : λ ∈ 𝕋)` (Source: main paper `e:CQvar`, L1204–L1212),
`𝕋 = [0, 1)`. -/
def VQr (r : ℝ) (Q : ℕ) (f : ℤ → ℂ) (x : ℤ) : ℝ≥0∞ :=
  pointwiseVariation r (fun lam y => S.TQ Q lam f y) x

/-- `C^Q f(x) = sup_{λ ∈ 𝕋} |T^Q_λ f(x)|` (Source: main paper, L1213–L1220). -/
def CQ (Q : ℕ) (f : ℤ → ℂ) (x : ℤ) : ℝ≥0∞ :=
  ⨆ lam ∈ Set.Ico (0 : ℝ) 1, ‖S.TQ Q lam f x‖ₑ

/-- `C^Q_B f(x) = sup_{λ ∈ 𝕋} |∑_n f(x-n) w_{Q,B}(n) K_Q(n) e(λ n)|` (Source: main paper,
L2098–L2101). -/
def CQB (Q : ℕ) (B : Finset ℕ) (f : ℤ → ℂ) (x : ℤ) : ℝ≥0∞ :=
  ⨆ lam ∈ Set.Ico (0 : ℝ) 1, ‖S.TQB Q B lam f x‖ₑ

end KQSetup

/-! ### The cutoff `M(k)` and `w_{≤ M(k)}` (Source: main paper `p:red-var`, L1275–L1281) -/

/-- `M(k) := exp(k^{1/10})`. -/
def cutoffM (k : ℕ) : ℝ := Real.exp ((k : ℝ) ^ ((1 : ℝ) / 10))

/-- `w_{≤ M(k)} := ∑_{L ≤ M(k), L dyadic} w_L`, the Heath-Brown model at `T = M(k)`. -/
def wLeM (k : ℕ) (n : ℤ) : ℂ := heathBrownModel (cutoffM k) n

/-- `w_{≤ M(k)} = ∑_{j : 2^j ≤ M(k)} w_{2^j}`. -/
theorem wLeM_eq_sum (k : ℕ) (n : ℤ) :
    wLeM k n = ∑ j ∈ (Finset.range (⌊cutoffM k⌋₊ + 1)).filter (fun j => (2 : ℝ) ^ j ≤ cutoffM k),
      wQ (2 ^ j) n :=
  heathBrownModel_eq_sum_wQ _ n

end PrimeCarleson.Proof.Paper
