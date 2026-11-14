module

public import PrimeCarleson.Proof.Paper.P6b.Mobius
public import PrimeCarleson.Proof.Paper.P6a.Covering

/-!
# The change of variables `λ ↦ dλ` and the pointwise bound `e:mobius-var-pointwise`

Source: main paper `l:red-var-l2`, L1621–L1672; main paper `e:mobius-var-pointwise`, L1673–L1692.
For the `1`-periodic family `a_λ(x) = ∑_m f(x - dm) K_{Q,d}(m) e(λ m)` (`dilSum K̂_{Q,d} d f x λ`)
the covering `λ ↦ dλ` of `𝕋` is `d`-to-one and `V^r(a_{dλ}) ≤ 3 d^{1/r} V^r(a_λ)`
(`var_covering_loss_strong`, `P6a/Covering.lean`): the second term of the printed
`e:var-covering-loss` is not needed, so the supremum term of `e:mobius-var-pointwise` is absent from
`mobius_var_pointwise`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Common

/-- **The change of variables `λ ↦ dλ`** (Source: main paper `l:red-var-l2`, L1621–L1672): for
`r ≥ 1` and `d ≥ 1`,
`V^r(∑_m f(x - dm) K(m) e(dλ m) : λ) ≤ 3 d^{1/r} V^r(∑_m f(x - dm) K(m) e(λ m) : λ)`, `λ ∈ [0, 1)`
(any multiplier `k̂` with `K(m) = ∫ k̂(ξ) e(mξ) dξ`). -/
theorem dilation_change_of_variables {r : ℝ} (hr : 1 ≤ r) (khat : ℝ → ℂ) {d : ℕ} (hd : 1 ≤ d)
    (f : ℤ →₀ ℂ) (x : ℤ) :
    rVariationOn r (Set.Ico 0 1) (fun lam => dilSum khat (d : ℤ) f x ((d : ℝ) * lam)) ≤
      ENNReal.ofReal (3 * (d : ℝ) ^ (1 / r)) *
        rVariationOn r (Set.Ico 0 1) (fun lam => dilSum khat (d : ℤ) f x lam) :=
  var_covering_loss_strong hr (dilSum_periodic khat (d : ℤ) f x) hd

/-- **`e:mobius-var-pointwise`** (L1673–L1692), in the stronger form without the supremum term: for
`r ≥ 1`,
`V^{Q,r} f(x) ≤ ∑_{Q/2 < q ≤ Q} φ(q)⁻¹ ∑_{d ∣ q} 3 d^{1/r}
  V^r(∑_m f(x - dm) K_{Q,d}(m) e(λ m) : λ)`. -/
theorem mobius_var_pointwise (S : KQSetup) {r : ℝ} (hr : 1 ≤ r) (Q : ℕ) (f : ℤ →₀ ℂ) (x : ℤ) :
    S.VQr r Q (⇑f) x ≤ ∑ q ∈ Finset.Ioc (Q / 2) Q, ENNReal.ofReal (1 / (Nat.totient q : ℝ)) *
      ∑ d ∈ q.divisors, ENNReal.ofReal (3 * (d : ℝ) ^ (1 / r)) *
        rVariationOn r (Set.Ico 0 1) (fun lam => dilSum (S.KQdhat Q d) (d : ℤ) f x lam) := by
  refine (VQr_le_mobius S hr Q f x).trans (Finset.sum_le_sum fun q _ => ?_)
  refine mul_le_mul_right (Finset.sum_le_sum fun d hd => ?_) _
  exact dilation_change_of_variables hr _ (Nat.pos_of_mem_divisors hd) f x

end PrimeCarleson.Proof.Paper
