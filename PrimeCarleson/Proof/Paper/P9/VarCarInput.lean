module

public import PrimeCarleson.Proof.Paper.P9.Truncation
public import PrimeCarleson.Proof.Paper.P9.Representation

/-!
# The input `l:varcarZ` (taken as a hypothesis) and the variational hypothesis `(V_s)` for `K_λ`

`sources/Variational_Carleson.tex` L1771-L1776 (statement of `l:varcarZ`), L2028-L2029.

**The input.** `LVarCarZ s C` is *exactly* the statement of `l:varcarZ` in the form used
here (with a constant depending on `s` only): for every measurable `k̂ : ℝ → ℂ` supported in an
interval of length `1/10` (`k̂` the multiplier of the kernel `k(n) = ∫ k̂(ξ) e(nξ) dξ`) with total
variation at most `c₀`, every finitely supported `f` and every finite `T ⊂ [0, 1)`:

`‖V^s(∑_n f(x - n) e(λ n) k(n) : λ ∈ T)‖_{ℓ²_x} ≤ C c₀ ‖f‖_{ℓ²}`;

the constant `C = C_s` depends on the exponent `s > 2` only. `P7/` proves
`∀ s > 2, ∃ C, LVarCarZ s C` (`lVarCarZ_of_oplus`); every consumer here takes it as a hypothesis.

`KQSetup.variation_hyp` turns it into the hypothesis `(V_s)` of `p:variable` for the multipliers
`m_λ = K̂_Q(· - λ)`, `λ ∈ T`, in the density form on the chart (`ℓ²` pieces `f` with `f̂` on `I`),
through the identification `(K_λ * f)(x) = ∑_n f(x - n) e(λ n) K_Q(n) = invFZ θ (m_λ f̂)(x)`
(`KQSetup.invFZ_KQmult`, `invFZ_conv_fourierZ`) and Lemma T (`variable_truncation`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

/-- **The statement of `l:varcarZ`** (taken as a hypothesis, see the module docstring): the
variation estimate for maximally modulated bounded-variation multipliers on `ℤ`, exponent `s`,
constant `C`. (Source: main paper `l:varcarZ`, L1771–L1776; the kernel is `k(n) = ∫ k̂(ξ) e(nξ) dξ`,
`k̂` supported in an interval of length `≤ 1/10` with total variation `≤ c₀`.) -/
def LVarCarZ (s C : ℝ) : Prop :=
  ∀ (khat : ℝ → ℂ) (c₀ u : ℝ), Measurable khat →
    (∀ ξ, khat ξ ≠ 0 → ξ ∈ Set.Icc u (u + 1 / 10)) →
    eVariationOn khat Set.univ ≤ ENNReal.ofReal c₀ →
    ∀ (f : ℤ →₀ ℂ) (T : Set ℝ), T.Finite → T ⊆ Set.Ico 0 1 →
      (∑' x : ℤ, rVariationOn s T (fun lam => ∑' n : ℤ, f (x - n) * e (lam * (n : ℝ)) *
        ∫ ξ, khat ξ * e ((n : ℝ) * ξ)) ^ 2) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (C * c₀) * l2enorm (⇑f)

/-- `∑_n f(x - n) F(n) = ∑_{k ∈ supp f} f(k) F(x - k)` for finitely supported `f`. -/
theorem tsum_conv_eq_sum (f : ℤ →₀ ℂ) (F : ℤ → ℂ) (x : ℤ) :
    ∑' n : ℤ, f (x - n) * F n = ∑ k ∈ f.support, f k * F (x - k) := by
  rw [← (Equiv.subLeft x).tsum_eq]
  rw [tsum_eq_sum (s := f.support)]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp [Equiv.subLeft_apply]
  · intro k hk
    simp [Finsupp.notMem_support_iff.1 hk]

/-- **The variational hypothesis `(V_s)` for `K_λ`** (from `l:varcarZ` and Lemma T):
if `LVarCarZ s Cv` holds, `K̂_Q` has total variation `≤ C₀` and support in `[-1/20, 1/20]`, then for
every finite `T ⊂ [0, 1)` whose `δ/N(Q)`-neighbourhood lies in the chart `(θ, θ + 1)`, every
density `H ∈ L²(θ, θ + 1]`,
`‖V^s(K_λ * f : λ ∈ T)‖_{ℓ²} ≤ Cv C₀ ‖f‖_{ℓ²}`, `f = invFZ θ H`, `(K_λ * f)^ = K̂_Q(· - λ) H`. -/
theorem KQSetup.variation_hyp (S : KQSetup) {Q : ℕ} {s Cv C₀ : ℝ} (hv : LVarCarZ s Cv)
    (hs : 1 ≤ s) (_hC₀ : 0 ≤ C₀) (_hCv : 0 ≤ Cv)
    (hbv : eVariationOn (S.KQhat Q) Set.univ ≤ ENNReal.ofReal C₀)
    (hsup : Function.support (S.KQhat Q) ⊆ Set.Icc (-(1 / 20)) (1 / 20))
    (hKb : ∀ β, ‖S.KQhat Q β‖ ≤ C₀)
    {θ : ℝ} {T : Set ℝ} (hT : T.Finite) (hT01 : T ⊆ Set.Ico 0 1)
    (hchart : ∀ t ∈ T, θ < t - S.δ / S.P.NQ Q ∧ t + S.δ / S.P.NQ Q < θ + 1)
    {H : ℝ → ℂ} (hH : ChartL2 θ H) :
    (∑' x : ℤ, rVariationOn s T
      (fun t => invFZ θ (fun β => S.KQmult Q t β * H β) x) ^ 2) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Cv * C₀) * l2enorm (invFZ θ H) := by
  refine variable_truncation (M := fun _ => C₀) hT (fun t _ => S.measurable_KQmult Q t)
    (fun t _ β => ?_) hs ?_ hH
  · simpa [KQSetup.KQmult] using hKb (β - t)
  · intro f
    have hpt : ∀ t ∈ T, ∀ x : ℤ, invFZ θ (fun β => S.KQmult Q t β * fourierZ f β) x =
        ∑' n : ℤ, f (x - n) * e (t * (n : ℝ)) * ∫ ξ, S.KQhat Q ξ * e ((n : ℝ) * ξ) := by
      intro t ht x
      rw [← invFZ_conv_fourierZ (S.chartL2_KQmult Q t θ) f x]
      have h1 : ∀ n : ℤ, f (x - n) * e (t * (n : ℝ)) * ∫ ξ, S.KQhat Q ξ * e ((n : ℝ) * ξ) =
          f (x - n) * (e (t * (n : ℝ)) * S.KQz Q n) := fun n => by
        simp only [KQSetup.KQz, KQSetup.KQ]; ring
      simp_rw [h1]
      rw [tsum_conv_eq_sum f (fun n => e (t * (n : ℝ)) * S.KQz Q n) x]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [S.invFZ_KQmult Q (hchart t ht).1 (hchart t ht).2]
    have hcongr : ∀ x : ℤ, rVariationOn s T
        (fun t => invFZ θ (fun β => S.KQmult Q t β * fourierZ f β) x) =
        rVariationOn s T (fun lam => ∑' n : ℤ, f (x - n) * e (lam * (n : ℝ)) *
          ∫ ξ, S.KQhat Q ξ * e ((n : ℝ) * ξ)) := fun x =>
      rVariationOn_congr fun t ht => hpt t ht x
    simp_rw [hcongr]
    exact hv (S.KQhat Q) C₀ (-(1 / 20)) (S.measurable_KQhat Q)
      (fun ξ hξ => by
        have := hsup (Function.mem_support.2 hξ)
        constructor <;> linarith [this.1, this.2]) hbv f T hT hT01

end PrimeCarleson.Proof.Paper
