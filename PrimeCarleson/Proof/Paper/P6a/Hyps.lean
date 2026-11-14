module

public import PrimeCarleson.Proof.Paper.P6a.Basic
public import PrimeCarleson.Proof.Paper.Defs.Norms
public import PrimeCarleson.Proof.Paper.Defs.Gowers
public import PrimeCarleson.Frozen.HeathBrownModel
public import PrimeCarleson.Frozen.GowersNormInterval
public import Mathlib.Analysis.BoundedVariation

/-!
# Statements of the inputs from other parts of the formalization

Inputs of the proof of `p:red-var` (Source: main paper, L1244–L1519) that are taken as hypotheses
here. Each is a `Prop` whose statement is exactly that of the paper step; the theorems of `P6a/`
that need it take it as an explicit hypothesis.

* `FplusProp31`: `[F+, Proposition 3.1]`, the theorem
  `PrimeCarleson.vonMangoldt_sub_heathBrown_U3` (Source: [F+] `p:logsavings`, L1056–L1062; consumed
  by the cutoff bridge of `Cutoff.lean`);
* `LocalU3VarRed ψ r`: the step `e:local-U3-var-red` (proved in `P4b/`; Source: main paper
  `e:local-U3-var-red`, L1288–L1303): the `ℓ²` bound for `V^r(∑_n f(x-n) u(n) ψ_k(n) e(λ n) : λ)` in
  terms of `‖u‖_{U³([2^k])}` and `‖u‖_{L²([2^k])}`. As printed `u` is arbitrary, which is false (the
  norms of `u` see only `n ∈ [2^k]` while `ψ_k` is two-sided); the weights used (`w - w_{≤ M(k)}`,
  `w_Q`) are even, so `u` is assumed even (the consumers' only use);
* `VarCarZ r`: the step `l:varcarZ` (proved in `P7/`, L1762–L1812): the `ℓ²` bound
  `‖V^r(∑_n f(x-n) e(λ n) k(n) : λ)‖_{ℓ²} ≲ c₀ r/(r-2) ‖f‖_{ℓ²}` when `k̂` is supported in an
  interval of length `≤ 1/10` and has total variation `≤ c₀`; the kernel is
  `k(n) = ∫ k̂(ξ) e(nξ) dξ` (`k̂ = m` a function on `ℝ` vanishing off the interval, so that the
  total variation over `ℝ` counts the jumps at the endpoints).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- **`[F+, Proposition 3.1]`** (Source: [F+] `p:logsavings`, L1056–L1062; the statement of the
theorem `PrimeCarleson.vonMangoldt_sub_heathBrown_U3`): with `Q_N = exp((log N)^{1/10})`, for
every `A ≥ 1` there is `C_A` with `‖Λ - Λ_{≤ Q_N}‖_{U³[N]} ≤ C_A (log N)^{-A}` for `N ≥ 2`. -/
def FplusProp31 : Prop :=
  ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, ∀ N : ℕ+, 2 ≤ N →
    gowersNormInterval 3 N
        (fun n => ((ArithmeticFunction.vonMangoldt n.toNat : ℝ) : ℂ) -
          heathBrownModel (Real.exp (Real.log N ^ ((1 : ℝ) / 10))) n) ≤
      C * Real.log N ^ (-A)

/-- **The step `e:local-U3-var-red`** (Source: main paper `e:local-U3-var-red`, L1288–L1303), for
the even weights `u` (the form the consumers use; see the module docstring): for `k ≥ 1`, `N = 2^k`,
every even `u : ℤ → ℂ` and every finitely supported `f`, `‖V^r(∑_n f(x-n) u(n) ψ_k(n) e(λ n) :
λ)‖_{ℓ²} ≤ C k^{2/r} ‖u‖_{U³([N])}^{1-2/r} ‖u‖_{L²([N])}^{2/r} ‖f‖_{ℓ²}`, with `C` depending only on
`r` (and the fixed `ψ`). -/
def LocalU3VarRed (ψ : PsiData) (r : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (N : ℕ+), 1 ≤ k → (N : ℕ) = 2 ^ k → ∀ u : ℤ → ℂ,
    (∀ n, u (-n) = u n) → ∀ f : ℤ →₀ ℂ,
      eLpNorm (varOp r (fun n => u n * psiKz ψ k n) (⇑f)) (ENNReal.ofReal 2) Measure.count ≤
        ENNReal.ofReal (C * (k : ℝ) ^ (2 / r) * gowersNormInterval 3 N u ^ (1 - 2 / r) *
            lpNormOn 2 (bracket N) u ^ (2 / r)) *
          eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count

/-- **The step `l:varcarZ`** (Source: main paper `l:varcarZ`, L1762–L1812): for `k̂ = m : ℝ → ℂ`
vanishing off an interval `[a, a + 1/10]` and of total variation `≤ c₀` (over `ℝ`), the kernel
`k(n) = ∫ m(ξ) e(nξ) dξ` satisfies `‖V^r(∑_n f(x-n) e(λ n) k(n) : λ)‖_{ℓ²} ≤ C c₀ r/(r-2) ‖f‖_{ℓ²}`,
`C` absolute. -/
def VarCarZ (r : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℝ → ℂ) (a : ℝ), (∀ ξ, m ξ ≠ 0 → a ≤ ξ ∧ ξ ≤ a + 1 / 10) →
    ∀ c₀ : ℝ, 0 ≤ c₀ → eVariationOn m Set.univ ≤ ENNReal.ofReal c₀ → ∀ f : ℤ →₀ ℂ,
      eLpNorm (varOp r (fun n : ℤ => ∫ ξ : ℝ, m ξ * e ((n : ℝ) * ξ)) (⇑f))
          (ENNReal.ofReal 2) Measure.count ≤
        ENNReal.ofReal (C * c₀ * (r / (r - 2))) * eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count

end PrimeCarleson.Proof.Paper
