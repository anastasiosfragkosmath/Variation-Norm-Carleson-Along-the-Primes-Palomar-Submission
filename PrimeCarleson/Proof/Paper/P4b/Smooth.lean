module

public import PrimeCarleson.Proof.Paper.P4b.SmoothV2
public import PrimeCarleson.Proof.Paper.P4b.Interpolation
public import PrimeCarleson.Proof.Paper.P6a.Hyps

/-!
# The smooth two-sided `U³`-variation bound at scale `2^k`

Source: main paper `e:local-U3-var-red`, L1288–L1303 (the smooth-cutoff form of Corollary
`c:U3modvariation`); consumers: `e:minor-var-L2-red`, `e:highQ-var-L2-red`.

For `ψ : PsiData`, `r ≥ 2`, `k ≥ 1`, an **even** weight `u : ℤ → ℂ` and finitely supported `f`,

`‖V^r(∑_n f(x-n) u(n) ψ_k(n) e(λ n) : λ ∈ 𝕋)‖_{ℓ²(ℤ)} ≤
C k^{2/r} ‖u‖_{U³([2^k])}^{1-2/r} ‖u‖_{L²([2^k])}^{2/r} ‖f‖_{ℓ²(ℤ)}`,

`C = C(r, ψ)`. The proof interpolates (`eLpNorm_pointwiseVariation_le_of_bounds`, the mechanism of
`c:U3modvariation`, see `Interpolation.lean`) the `V²` bound `smooth_V2` (`K k ‖u‖_{L²([2^k])}`,
from `l:crudeV2lambda` by the reflection `f ↦ f(-·)`) with the smooth maximal `U³` bound
`U3maxmod_twoSided` (`C₃ ‖u‖_{U³([2^k])}`, `P3/TwoSided.lean`): `C = K^{2/r} (2 C₃)^{1-2/r}`. The
paper's "by (e:U3varlambda) and convexity" (sharp to smooth cutoff) is replaced by this direct
argument: the sharp `V²` endpoint already holds for arbitrary weights, and the smooth maximal
estimate is proved in `P3/`.

**Evenness of `u`**: as printed the paper's statement has no hypothesis on `u`, which is false
(`‖u‖_{U³([2^k])}` and `‖u‖_{L²([2^k])}` see only `u` on `[2^k]`, while `ψ_k` is two-sided: for
`u = 1_{n < 0}` the right side vanishes and the left side does not). The weights used,
`w - w_{≤ M(k)}` and `w_Q`, are even (`resWeight_neg`, `wQ_neg`).

`localU3VarRed_holds` is the statement of the `Prop` `LocalU3VarRed ψ r` of `P6a/Hyps.lean`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- **The smooth two-sided `U³`-variation bound at scale `2^k`** (Source: main paper
`e:local-U3-var-red`, L1288–L1303; `u` even):
for `ψ : PsiData` and `r ≥ 2` there is `C` such that for all `k ≥ 1`, every even `u : ℤ → ℂ` and
every finitely supported `f : ℤ → ℂ`,
`‖V^r(∑_n f(x-n) u(n) ψ_k(n) e(λ n) : λ ∈ 𝕋)‖_{ℓ²(ℤ)} ≤
C k^{2/r} ‖u‖_{U³([2^k])}^{1-2/r} ‖u‖_{L²([2^k])}^{2/r} ‖f‖_{ℓ²(ℤ)}`. -/
theorem U3modvariation_smooth_cutoff (ψ : PsiData) {r : ℝ} (hr : 2 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ), 1 ≤ k → ∀ u : ℤ → ℂ, (∀ n, u (-n) = u n) →
      ∀ f : ℤ → ℂ, (Function.support f).Finite →
        eLpNorm (pointwiseVariation r (fun lam x =>
            weightedModSum (fun n : ℤ => u n * psiKz ψ k n) f lam x)) 2 Measure.count ≤
          ENNReal.ofReal (C * (k : ℝ) ^ (2 / r) *
              gowersNormOn 3 (bracket ((2 : ℕ+) ^ k)) u ^ (1 - 2 / r) *
              lpNormOn 2 (bracket ((2 : ℕ+) ^ k)) u ^ (2 / r)) *
            eLpNorm f 2 Measure.count := by
  obtain ⟨K, hK, hV2⟩ := smooth_V2 ψ
  obtain ⟨C₃, hC₃, hmax⟩ := U3maxmod_twoSided ψ
  have hθ : 0 ≤ 1 - 2 / r := sub_nonneg.2 ((div_le_one (by linarith)).2 hr)
  refine ⟨K ^ (2 / r) * (2 * C₃) ^ (1 - 2 / r), by positivity, fun k hk u heven f hf => ?_⟩
  have hL : 0 ≤ lpNormOn 2 (bracket ((2 : ℕ+) ^ k)) u := lpNormOn_nonneg _ _ _
  have hG : 0 ≤ gowersNormOn 3 (bracket ((2 : ℕ+) ^ k)) u := gowersNormOn_nonneg _ _ _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h := eLpNorm_pointwiseVariation_le_of_bounds hr
    (fun lam x => weightedModSum (fun n : ℤ => u n * psiKz ψ k n) f lam x)
    (P := K * (k : ℝ) * lpNormOn 2 (bracket ((2 : ℕ+) ^ k)) u)
    (Q := C₃ * gowersNormOn 3 (bracket ((2 : ℕ+) ^ k)) u) (by positivity) (by positivity)
    (F := eLpNorm f 2 Measure.count) (hV2 k hk u heven f hf) (hmax k u heven f)
  refine h.trans (le_of_eq ?_)
  congr 2
  have e1 : (K * (k : ℝ) * lpNormOn 2 (bracket ((2 : ℕ+) ^ k)) u) ^ (2 / r) =
      K ^ (2 / r) * (k : ℝ) ^ (2 / r) * lpNormOn 2 (bracket ((2 : ℕ+) ^ k)) u ^ (2 / r) := by
    rw [Real.mul_rpow (by positivity) hL, Real.mul_rpow hK hk0]
  have e2 : (2 * (C₃ * gowersNormOn 3 (bracket ((2 : ℕ+) ^ k)) u)) ^ (1 - 2 / r) =
      (2 * C₃) ^ (1 - 2 / r) * gowersNormOn 3 (bracket ((2 : ℕ+) ^ k)) u ^ (1 - 2 / r) := by
    rw [← mul_assoc, Real.mul_rpow (by positivity) hG]
  rw [e1, e2]
  ring

/-- **The smooth two-sided `U³`-variation bound at scale `2^k`**, for `f : ℤ →₀ ℂ`, in the form of
`LocalU3VarRed`. -/
theorem localU3VarRed_of_two_le (ψ : PsiData) {r : ℝ} (hr : 2 ≤ r) : LocalU3VarRed ψ r := by
  obtain ⟨C, hC, h⟩ := U3modvariation_smooth_cutoff ψ hr
  refine ⟨C, hC, fun k N hk hN u heven f => ?_⟩
  have hN' : N = (2 : ℕ+) ^ k := PNat.eq (by simpa using hN)
  subst hN'
  have hfin : (Function.support (⇑f)).Finite := by
    refine f.support.finite_toSet.subset fun x hx => ?_
    simpa using hx
  have := h k hk u heven (⇑f) hfin
  simp only [ENNReal.ofReal_ofNat]
  exact this

/-- **`e:local-U3-var-red`** (Source: main paper `e:local-U3-var-red`, L1288–L1302; `u` even): for
`ψ : PsiData` and `r > 2`, the `Prop` `LocalU3VarRed ψ r` of
`P6a/Hyps.lean`: there is `C ≥ 0` such that for `k ≥ 1`, `N = 2^k`, every even `u : ℤ → ℂ` and
every finitely supported `f`,
`‖V^r(∑_n f(x-n) u(n) ψ_k(n) e(λ n) : λ)‖_{ℓ²} ≤ C k^{2/r} ‖u‖_{U³([N])}^{1-2/r}
‖u‖_{L²([N])}^{2/r} ‖f‖_{ℓ²}`. -/
theorem localU3VarRed_holds (ψ : PsiData) {r : ℝ} (hr : 2 < r) : LocalU3VarRed ψ r :=
  localU3VarRed_of_two_le ψ hr.le

end PrimeCarleson.Proof.Paper
