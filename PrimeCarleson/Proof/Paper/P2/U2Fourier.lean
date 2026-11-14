module

public import PrimeCarleson.Proof.Paper.Defs.Gowers
public import PrimeCarleson.Proof.Common.FourierZ
public import PrimeCarleson.Proof.Common.GowersCauchySchwarz

/-!
# The `U²` norm is the `L⁴(𝕋)` norm of the Fourier transform

Display `e:U2-ell4` (Source: main paper `e;U2-ell4`, L669–L672):
for a finitely supported `f : ℤ → ℂ`,
`‖f‖_{U²(ℤ)}⁴ = ∫_𝕋 |f̂(β)|⁴ dβ`, with `f̂(β) = ∑_n f(n) e(-nβ)` (`Common.fourierZ`).

Proof. The additive quadruples `x, x + h₁, x + h₂, x + h₁ + h₂` of the `U²` sum
`∑_{x,h₁,h₂} f(x) conj f(x + h₁) conj f(x + h₂) f(x + h₁ + h₂)` are exactly the solutions of
`a + b = c + d`; hence the `U²` sum is `∑_n |(f ⋆ f)(n)|²` (`tsum_multDiff_two`, a re-indexing
`(x, h) ↦ (2x + h₀ + h₁, x, x + h₀)` of `ℤ × (Fin 2 → ℤ)` with `ℤ³`). By Plancherel
(`Common.sum_norm_sq_eq_integral`) and `(f ⋆ f)^ = f̂²` (`Common.fourierZ_convZ`) this is
`∫_𝕋 |f̂|⁴`.
-/

@[expose] public noncomputable section

open scoped ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0

/-- The re-indexing `(x, h₀, h₁) ↦ (n, a, c) = (2x + h₀ + h₁, x, x + h₀)` of the parameters of the
`U²` sum by the quadruples `(a, n - a, c, n - c)` with equal sums. -/
private def u2Equiv : ℤ × (Fin 2 → ℤ) ≃ ℤ × ℤ × ℤ where
  toFun p := (2 * p.1 + p.2 0 + p.2 1, p.1, p.1 + p.2 0)
  invFun q := (q.2.1, ![q.2.2 - q.2.1, q.1 - q.2.2 - q.2.1])
  left_inv := by
    rintro ⟨x, h⟩
    refine Prod.ext rfl (funext fun i => ?_)
    fin_cases i
    · simp
    · simp; ring
  right_inv := by
    rintro ⟨n, a, c⟩
    ext
    · simp; ring
    · simp
    · simp

/-- The summand of the energy `∑_n |(f ⋆ f)(n)|²`, indexed by `(n, a, c)`:
`f(a) f(n - a) conj f(c) conj f(n - c)`. -/
private def u2Term (f : ℤ → ℂ) (q : ℤ × ℤ × ℤ) : ℂ :=
  f q.2.1 * f (q.1 - q.2.1) * conj (f q.2.2 * f (q.1 - q.2.2))

/-- The iterated difference `Δ_{h₀,h₁} f(x) = f(x) conj f(x + h₀) conj f(x + h₁) f(x + h₀ + h₁)`
(for the recursion `Δ_{h₀,h₁} = Δ_{h₁} Δ_{h₀}`). -/
theorem multDiff_two_apply (h : Fin 2 → ℤ) (f : ℤ → ℂ) (x : ℤ) :
    multDiff 2 h f x =
      f x * conj (f (x + h 0)) * conj (f (x + h 1) * conj (f (x + h 1 + h 0))) := by
  rfl

private theorem u2Term_equiv (f : ℤ → ℂ) (p : ℤ × (Fin 2 → ℤ)) :
    u2Term f (u2Equiv p) = multDiff 2 p.2 f p.1 := by
  obtain ⟨x, h⟩ := p
  rw [multDiff_two_apply]
  simp only [u2Term, u2Equiv, Equiv.coe_fn_mk]
  have e1 : 2 * x + h 0 + h 1 - x = x + h 1 + h 0 := by ring
  have e2 : 2 * x + h 0 + h 1 - (x + h 0) = x + h 1 := by ring
  rw [e1, e2]
  simp only [map_mul, Complex.conj_conj]
  ring

/-- The support of the energy summand is finite. -/
private theorem u2Term_support_finite (f : ℤ →₀ ℂ) :
    (Function.support (u2Term (⇑f))).Finite := by
  classical
  set S : Finset ℤ := f.support with hS
  have hfin : (↑((S ×ˢ S ×ˢ S).image
      (fun m : ℤ × ℤ × ℤ => (m.2.1 + m.1, m.2.1, m.2.2))) : Set (ℤ × ℤ × ℤ)).Finite :=
    Finset.finite_toSet _
  refine hfin.subset fun q hq => ?_
  have hq' : u2Term (⇑f) q ≠ 0 := hq
  simp only [u2Term, ne_eq, mul_eq_zero, map_eq_zero, not_or] at hq'
  obtain ⟨⟨ha, hna⟩, hc, _⟩ := hq'
  obtain ⟨n, a, c⟩ := q
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product,
    Prod.mk.injEq, Prod.exists]
  refine ⟨n - a, a, c, ⟨?_, ?_, ?_⟩, ?_, rfl, rfl⟩
  · simpa [hS] using hna
  · simpa [hS] using ha
  · simpa [hS] using hc
  · ring

/-- For fixed `n`, the double sum over `(a, c)` factors: it is `(f ⋆ f)(n) conj (f ⋆ f)(n)`. -/
private theorem tsum_u2Term_fixed (f : ℤ →₀ ℂ) (n : ℤ) :
    ∑' p : ℤ × ℤ, u2Term (⇑f) (n, p) =
      Common.convZ f f n * conj (Common.convZ f f n) := by
  classical
  have hsum : ∑' p : ℤ × ℤ, u2Term (⇑f) (n, p) = ∑ p ∈ f.support ×ˢ f.support,
      u2Term (⇑f) (n, p) := by
    refine tsum_eq_sum fun p hp => ?_
    simp only [Finset.mem_product, Finsupp.mem_support_iff, not_and_or, not_not] at hp
    rcases hp with hp | hp
    · simp [u2Term, hp]
    · simp [u2Term, hp]
  rw [hsum, Finset.sum_product, Common.convZ_apply, Finsupp.sum, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  simp [u2Term, map_mul]

/-- **The `U²` sum is the energy `∑_n |(f ⋆ f)(n)|²`**: the sum `∑_{x,h₁,h₂} Δ_{h₁,h₂} f(x)`
defining `‖f‖_{U²(ℤ)}⁴` equals `∑_n |(f ⋆ f)(n)|²`. -/
theorem tsum_multDiff_two (f : ℤ →₀ ℂ) :
    ∑' p : ℤ × (Fin 2 → ℤ), multDiff 2 p.2 f p.1 =
      ∑' n : ℤ, Common.convZ f f n * conj (Common.convZ f f n) := by
  have h1 : ∑' p : ℤ × (Fin 2 → ℤ), multDiff 2 p.2 f p.1 = ∑' q, u2Term (⇑f) q := by
    rw [← u2Equiv.tsum_eq (u2Term (⇑f))]
    exact tsum_congr fun p => (u2Term_equiv _ p).symm
  rw [h1, Common.GowersCS.tsum_equiv_prod (Equiv.refl (ℤ × ℤ × ℤ)) (u2Term (⇑f))
    (u2Term_support_finite f)]
  exact tsum_congr fun n => tsum_u2Term_fixed f n

/-- The `U²` norm as the energy: `‖f‖_{U²(ℤ)}⁴ = ∑_n |(f ⋆ f)(n)|²` (the convolution
`(f ⋆ f)(n) = ∑_k f(k) f(n - k)`). -/
theorem gowersNorm_two_pow_four_eq_sum (f : ℤ →₀ ℂ) :
    gowersNorm 2 f ^ 4 = ∑ n ∈ (Common.convZ f f).support, ‖Common.convZ f f n‖ ^ 2 := by
  have h0 : ((gowersNorm 2 f : ℝ) : ℂ) ^ 2 ^ 2 =
      ∑' p : ℤ × (Fin 2 → ℤ), multDiff 2 p.2 f p.1 := gowersNorm_pow_eq_tsum 2 f
  rw [tsum_multDiff_two] at h0
  have hF : ∑' n : ℤ, Common.convZ f f n * conj (Common.convZ f f n) =
      ((∑ n ∈ (Common.convZ f f).support, ‖Common.convZ f f n‖ ^ 2 : ℝ) : ℂ) := by
    rw [tsum_eq_sum (s := (Common.convZ f f).support)]
    · push_cast
      exact Finset.sum_congr rfl fun n _ => Complex.mul_conj' _
    · intro n hn
      simp [Finsupp.notMem_support_iff.1 hn]
  rw [hF] at h0
  have h5 : (((gowersNorm 2 f : ℝ) : ℂ)) ^ 2 ^ 2 = ((gowersNorm 2 f ^ 4 : ℝ) : ℂ) := by
    push_cast
    norm_num
  rw [h5] at h0
  exact_mod_cast h0

/-- **`e;U2-ell4`** (Source: main paper, L669–L672): for finitely supported `f : ℤ → ℂ`,
`‖f‖_{U²(ℤ)}⁴ = ∫_𝕋 |f̂(β)|⁴ dβ`, where `f̂(β) = ∑_n f(n) e(-nβ)` (`Common.fourierZ`) and
`𝕋 = [0, 1)` (the integral over `(0, 1)`). -/
theorem gowersNorm_two_pow_four_eq_integral (f : ℤ →₀ ℂ) :
    gowersNorm 2 f ^ 4 = ∫ ξ in (0 : ℝ)..1, ‖Common.fourierZ f ξ‖ ^ 4 := by
  rw [gowersNorm_two_pow_four_eq_sum, Common.sum_norm_sq_eq_integral]
  refine intervalIntegral.integral_congr fun ξ _ => ?_
  simp only [Common.fourierZ_convZ, norm_mul]
  ring

/-- **The `U²` norm is definite**: `‖f‖_{U²(ℤ)} = 0` forces `f = 0` (the case `s = 2` of
"higher orders are norms", L663-L667 and `[F+]` L517). -/
theorem eq_zero_of_gowersNorm_two_eq_zero {f : ℤ →₀ ℂ} (h : gowersNorm 2 f = 0) : f = 0 := by
  have h4 : gowersNorm 2 f ^ 4 = 0 := by rw [h]; norm_num
  rw [gowersNorm_two_pow_four_eq_sum] at h4
  have hz : ∀ n ∈ (Common.convZ f f).support, ‖Common.convZ f f n‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun n _ => sq_nonneg _).1 h4
  have hF : Common.convZ f f = 0 := by
    ext n
    by_cases hn : n ∈ (Common.convZ f f).support
    · simpa using hz n hn
    · simpa using Finsupp.notMem_support_iff.1 hn
  have hf2 : ∀ ξ : ℝ, Common.fourierZ f ξ = 0 := fun ξ => by
    have := Common.fourierZ_convZ f f ξ
    rw [hF] at this
    simp only [Common.fourierZ, Finsupp.sum_zero_index] at this
    exact mul_self_eq_zero.1 this.symm
  ext n
  rw [Common.fourierZ_inversion f n]
  simp [hf2]

end PrimeCarleson.Proof.Paper
