module

public import PrimeCarleson.Proof.Goal0.Basic
public import PrimeCarleson.Frozen.MultiplierOpDis
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Fourier analysis on `ℤ` and `ℤ / K`

Fourier series of finitely supported sequences `f : ℤ →₀ ℂ` and cyclic Plancherel, in the
convention `e(t) = exp(2πit)` of `sources/Variational_Carleson.tex` (the Plancherel identities
recalled at L669-L672 and L823-L827, and Fourier inversion on `ℤ`), together with the discrete
multiplier operator of [MSW] §2 (`PrimeCarleson.multiplierOpDis`) as a Fourier integral:

* `fourierZ f ξ = ∑ₙ f(n) e(-nξ)`, `convZ f g`: the Fourier series and the convolution of
  finitely supported sequences;
* `integral_e_intCast_mul`: `∫ₐ^{a+1} e(kξ) dξ = 1_{k = 0}` for `k ∈ ℤ`;
* `fourierZ_periodic`, `continuous_fourierZ`, `fourierZ_inversion`;
* `sum_mul_conj_eq_integral_shift` (Parseval) and `sum_norm_sq_eq_integral_shift` (Plancherel)
  over an arbitrary interval of length one, and `sum_norm_sq_eq_integral` (Plancherel over
  `[0, 1]`);
* `convZ_apply`, `fourierZ_convZ`: `(f ⋆ g)^ = f̂ ĝ`;
* `multiplierOpDis_eq_integral`: `T_dis f(n) = ∫_{-1/2}^{1/2} m(ξ) f̂(ξ) e(nξ) dξ` when `m`
  is bounded, measurable, supported in `(-1/2, 1/2]`;
* `sum_norm_sq_cyclic`: cyclic Plancherel `∑_{s<K} |∑_{l<K} B_l e(sl/K)|² = K ∑_{l<K} |B_l|²`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Common

open PrimeCarleson PrimeCarleson.Proof.Goal0

/-- Fourier series of a finitely supported sequence: `f̂(ξ) = ∑_n f(n) e(-n ξ)`. -/
def fourierZ (f : ℤ →₀ ℂ) (ξ : ℝ) : ℂ := f.sum fun n c => c * e (-((n : ℝ) * ξ))

/-- Convolution of finitely supported sequences. -/
def convZ (f g : ℤ →₀ ℂ) : ℤ →₀ ℂ :=
  (f.sum fun k c => g.sum fun l d => Finsupp.single (k + l) (c * d))

/-- `e` is continuous. -/
theorem continuous_e : Continuous e := by
  unfold e
  fun_prop

/-- `e t = exp (2πi t)`, by definition. -/
theorem e_eq_exp_mul (t : ℝ) : e t = Complex.exp ((2 * Real.pi * Complex.I * (t : ℂ))) := rfl

/-- Orthogonality of the characters `e(kξ)` over any interval of length one. -/
theorem integral_e_intCast_mul (a : ℝ) (k : ℤ) :
    ∫ ξ in a..a + 1, e ((k : ℝ) * ξ) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp [hk, e_zero]
  · rw [ite_eq_right_iff.2 (fun h => absurd h hk)]
    have hc : (2 * Real.pi * Complex.I * (k : ℂ)) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero, hk]
    have h1 : ∀ ξ : ℝ,
        e ((k : ℝ) * ξ) = Complex.exp ((2 * Real.pi * Complex.I * (k : ℂ)) * ξ) := by
      intro ξ
      rw [e_eq_exp_mul]
      congr 1
      push_cast
      ring
    simp_rw [h1]
    rw [integral_exp_mul_complex hc]
    have h2 : Complex.exp ((2 * Real.pi * Complex.I * (k : ℂ)) * ((a + 1 : ℝ) : ℂ)) =
        Complex.exp ((2 * Real.pi * Complex.I * (k : ℂ)) * (a : ℂ)) := by
      have := e_add_intCast ((k : ℝ) * a) k
      rw [e_eq_exp_mul, e_eq_exp_mul] at this
      have e1 : (2 * Real.pi * Complex.I * (k : ℂ)) * ((a + 1 : ℝ) : ℂ) =
          2 * Real.pi * Complex.I * (((k : ℝ) * a + k : ℝ) : ℂ) := by push_cast; ring
      have e2 : (2 * Real.pi * Complex.I * (k : ℂ)) * (a : ℂ) =
          2 * Real.pi * Complex.I * (((k : ℝ) * a : ℝ) : ℂ) := by push_cast; ring
      rw [e1, e2]
      exact this
    rw [h2, sub_self, zero_div]

/-- `fourierZ` as a sum over any finite set containing the support. -/
theorem fourierZ_eq_sum_of_support_subset (f : ℤ →₀ ℂ) {S : Finset ℤ} (hS : f.support ⊆ S)
    (ξ : ℝ) : fourierZ f ξ = ∑ n ∈ S, f n * e (-((n : ℝ) * ξ)) :=
  Finsupp.sum_of_support_subset f hS _ (fun n _ => by simp)

/-- The Fourier series of a finitely supported sequence is `1`-periodic. -/
theorem fourierZ_periodic (f : ℤ →₀ ℂ) : Function.Periodic (fourierZ f) 1 := by
  intro x
  unfold fourierZ
  refine Finset.sum_congr rfl fun n _ => ?_
  change f n * e (-((n : ℝ) * (x + 1))) = f n * e (-((n : ℝ) * x))
  congr 1
  have := e_add_intCast (-((n : ℝ) * x)) (-n)
  rw [← this]
  congr 1
  push_cast
  ring

/-- The Fourier series of a finitely supported sequence is continuous. -/
theorem continuous_fourierZ (f : ℤ →₀ ℂ) : Continuous (fourierZ f) := by
  unfold fourierZ Finsupp.sum
  exact continuous_finsetSum _ fun n _ =>
    continuous_const.mul (continuous_e.comp (by fun_prop))

/-- Pairing of two trigonometric polynomials over any interval of length one. -/
theorem integral_sum_mul_conj_sum (S : Finset ℤ) (A B : ℤ → ℂ) (a : ℝ) :
    ∫ ξ in a..a + 1, (∑ n ∈ S, A n * e (-((n : ℝ) * ξ))) *
        conj (∑ m ∈ S, B m * e (-((m : ℝ) * ξ))) = ∑ n ∈ S, A n * conj (B n) := by
  have h1 : ∀ ξ : ℝ, (∑ n ∈ S, A n * e (-((n : ℝ) * ξ))) *
      conj (∑ m ∈ S, B m * e (-((m : ℝ) * ξ))) =
        ∑ n ∈ S, ∑ m ∈ S, (A n * conj (B m)) * e (((m - n : ℤ) : ℝ) * ξ) := by
    intro ξ
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, ← e_neg, neg_neg]
    have : e (((m - n : ℤ) : ℝ) * ξ) = e (m * ξ) * e (-(n * ξ)) := by
      rw [← e_add]
      congr 1
      push_cast
      ring
    rw [this]
    ring
  simp_rw [h1]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [intervalIntegral.integral_finsetSum]
    · simp_rw [intervalIntegral.integral_const_mul, integral_e_intCast_mul]
      simp [sub_eq_zero, hn]
    · intro m _
      exact (continuous_const.mul (continuous_e.comp (by fun_prop))).intervalIntegrable _ _
  · intro n _
    exact (continuous_finsetSum _ fun m _ =>
      continuous_const.mul (continuous_e.comp (by fun_prop))).intervalIntegrable _ _


/-- `f̂(ξ) e(nξ)` as a sum of characters of frequency `n - k`. -/
theorem fourierZ_mul_e (f : ℤ →₀ ℂ) (n : ℤ) (ξ : ℝ) :
    fourierZ f ξ * e ((n : ℝ) * ξ) = f.sum fun k c => c * e (((n - k : ℤ) : ℝ) * ξ) := by
  unfold fourierZ Finsupp.sum
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_assoc, ← e_add]
  congr 2
  push_cast
  ring

/-- Fourier inversion. -/
theorem fourierZ_inversion (f : ℤ →₀ ℂ) (n : ℤ) :
    f n = ∫ ξ in (0 : ℝ)..1, fourierZ f ξ * e ((n : ℝ) * ξ) := by
  simp_rw [fourierZ_mul_e]
  unfold Finsupp.sum
  rw [intervalIntegral.integral_finsetSum]
  · have h0 : (0 : ℝ) + 1 = 1 := by norm_num
    have : ∀ k ∈ f.support, ∫ ξ in (0 : ℝ)..1, f k * e (((n - k : ℤ) : ℝ) * ξ) =
        if k = n then f k else 0 := by
      intro k _
      rw [intervalIntegral.integral_const_mul, ← h0, integral_e_intCast_mul]
      by_cases hk : k = n
      · simp [hk]
      · simp [hk, sub_eq_zero, Ne.symm hk]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
    by_cases hn : n ∈ f.support
    · simp [hn]
    · simp [hn, Finsupp.notMem_support_iff.1 hn]
  · intro k _
    exact (continuous_const.mul (continuous_e.comp (by fun_prop))).intervalIntegrable _ _

/-- Parseval on any interval of length one. -/
theorem sum_mul_conj_eq_integral_shift (f g : ℤ →₀ ℂ) (a : ℝ) :
    (f.support ∪ g.support).sum (fun n => f n * conj (g n)) =
      ∫ ξ in a..a + 1, fourierZ f ξ * conj (fourierZ g ξ) := by
  have hf := fourierZ_eq_sum_of_support_subset f
    (Finset.subset_union_left : f.support ⊆ f.support ∪ g.support)
  have hg := fourierZ_eq_sum_of_support_subset g
    (Finset.subset_union_right : g.support ⊆ f.support ∪ g.support)
  simp_rw [hf, hg]
  exact (integral_sum_mul_conj_sum _ f g a).symm

/-- Plancherel on any interval of length one. -/
theorem sum_norm_sq_eq_integral_shift (f : ℤ →₀ ℂ) (a : ℝ) :
    f.support.sum (fun n => ‖f n‖ ^ 2) = ∫ ξ in a..a + 1, ‖fourierZ f ξ‖ ^ 2 := by
  apply Complex.ofReal_injective
  have h := sum_mul_conj_eq_integral_shift f f a
  rw [Finset.union_self] at h
  rw [← intervalIntegral.integral_ofReal, Complex.ofReal_sum]
  simp only [Complex.ofReal_pow, ← Complex.mul_conj']
  exact h

/-- Plancherel. -/
theorem sum_norm_sq_eq_integral (f : ℤ →₀ ℂ) :
    f.support.sum (fun n => ‖f n‖ ^ 2) = ∫ ξ in (0 : ℝ)..1, ‖fourierZ f ξ‖ ^ 2 := by
  have := sum_norm_sq_eq_integral_shift f 0
  rwa [zero_add] at this

/-- The convolution of finitely supported sequences, evaluated at a point. -/
theorem convZ_apply (f g : ℤ →₀ ℂ) (n : ℤ) : convZ f g n = f.sum fun k c => c * g (n - k) := by
  unfold convZ
  rw [Finsupp.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  change (g.sum fun l d => Finsupp.single (k + l) (f k * d)) n = f k * g (n - k)
  rw [Finsupp.sum_apply, Finsupp.sum]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_eq_single (n - k)]
  · simp
  · intro l _ hl
    rw [ite_eq_right_iff]
    intro h
    omega
  · intro hn
    simp [Finsupp.notMem_support_iff.1 hn]

/-- `fourierZ` as an additive homomorphism. -/
private def fourierZHom (ξ : ℝ) : (ℤ →₀ ℂ) →+ ℂ :=
  Finsupp.liftAddHom fun n => AddMonoidHom.mulRight (e (-((n : ℝ) * ξ)))

/-- `fourierZHom` is `fourierZ`. -/
private theorem fourierZHom_apply (ξ : ℝ) (f : ℤ →₀ ℂ) : fourierZHom ξ f = fourierZ f ξ := by
  simp [fourierZHom, fourierZ]

/-- The Fourier series of a convolution is the product of the Fourier series. -/
theorem fourierZ_convZ (f g : ℤ →₀ ℂ) (ξ : ℝ) :
    fourierZ (convZ f g) ξ = fourierZ f ξ * fourierZ g ξ := by
  have hR : fourierZ f ξ * fourierZ g ξ = f.sum fun k c => g.sum fun l d =>
      (c * e (-((k : ℝ) * ξ))) * (d * e (-((l : ℝ) * ξ))) := by
    unfold fourierZ
    rw [Finsupp.sum, Finsupp.sum, Finset.sum_mul_sum]
    rfl
  rw [← fourierZHom_apply, convZ, map_finsuppSum, hR]
  refine Finsupp.sum_congr fun k _ => ?_
  rw [map_finsuppSum]
  refine Finsupp.sum_congr fun l _ => ?_
  simp only [fourierZHom, Finsupp.liftAddHom_apply_single, AddMonoidHom.mulRight_apply]
  rw [mul_mul_mul_comm, ← e_add]
  congr 2
  push_cast
  ring


/-- A bounded a.e. strongly measurable function is interval integrable. -/
theorem intervalIntegrable_of_bound {E : Type*} [NormedAddCommGroup E] {g : ℝ → E}
    (hg : AEStronglyMeasurable g volume) {C : ℝ} (hC : ∀ ξ, ‖g ξ‖ ≤ C) (a b : ℝ) :
    IntervalIntegrable g volume a b := by
  rw [intervalIntegrable_iff]
  exact Measure.integrableOn_of_bounded (M := C) measure_Ioc_lt_top.ne hg
    (ae_of_all _ fun ξ => hC ξ)

/-- A bounded measurable multiplier times a character is interval integrable. -/
theorem intervalIntegrable_mul_e {m : ℝ → ℂ} (hm : Measurable m) {M : ℝ}
    (hM : ∀ ξ, ‖m ξ‖ ≤ M) (j : ℤ) (a b : ℝ) :
    IntervalIntegrable (fun ξ : ℝ => m ξ * e ((j : ℝ) * ξ)) volume a b :=
  intervalIntegrable_of_bound (g := fun ξ : ℝ => m ξ * e ((j : ℝ) * ξ))
    (hm.mul (continuous_e.comp (by fun_prop)).measurable).aestronglyMeasurable
    (fun ξ => by rw [norm_mul, norm_e, mul_one]; exact hM ξ) a b

/-- The discrete multiplier operator as a Fourier integral (m supported in one period). -/
theorem multiplierOpDis_eq_integral {m : ℝ → ℂ} (hm : Measurable m) (hb : ∃ M, ∀ ξ, ‖m ξ‖ ≤ M)
    (hs : Function.support m ⊆ Set.Ioc (-1 / 2) (1 / 2)) (f : ℤ →₀ ℂ) (n : ℤ) :
    multiplierOpDis m f n = ∫ ξ in (-1 / 2 : ℝ)..(1 / 2), m ξ * fourierZ f ξ * e ((n : ℝ) * ξ) := by
  obtain ⟨M, hM⟩ := hb
  have hint : ∀ j : ℤ, ∫ ξ, m ξ * e ((j : ℝ) * ξ) =
      ∫ ξ in (-1 / 2 : ℝ)..(1 / 2), m ξ * e ((j : ℝ) * ξ) := by
    intro j
    rw [intervalIntegral.integral_of_le (by norm_num)]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
    intro ξ hξ
    have : m ξ = 0 := by
      by_contra h
      exact hξ (hs h)
    simp [this]
  have h2 : ∀ ξ : ℝ, m ξ * fourierZ f ξ * e ((n : ℝ) * ξ) =
      ∑ k ∈ f.support, f k * (m ξ * e (((n - k : ℤ) : ℝ) * ξ)) := by
    intro ξ
    rw [mul_assoc, fourierZ_mul_e, Finsupp.sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  unfold multiplierOpDis
  simp_rw [hint, h2]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [intervalIntegral.integral_const_mul]
  · intro k _
    exact (intervalIntegrable_mul_e hm hM _ _ _).const_mul _


/-- `‖f̂(ξ)‖ ≤ ∑ₙ ‖f(n)‖`. -/
theorem norm_fourierZ_le (f : ℤ →₀ ℂ) (ξ : ℝ) : ‖fourierZ f ξ‖ ≤ f.sum fun _ c => ‖c‖ := by
  unfold fourierZ Finsupp.sum
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul, norm_e, mul_one]

/-- Cyclic Plancherel. -/
theorem sum_norm_sq_cyclic {K : ℕ} (hK : 0 < K) (B : ℕ → ℂ) :
    ∑ s ∈ Finset.range K, ‖∑ l ∈ Finset.range K, B l * e ((s : ℝ) * l / K)‖ ^ 2 =
      K * ∑ l ∈ Finset.range K, ‖B l‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.mul_conj']
  have h1 : ∀ s : ℕ, (∑ l ∈ Finset.range K, B l * e ((s : ℝ) * l / K)) *
      conj (∑ l ∈ Finset.range K, B l * e ((s : ℝ) * l / K)) =
        ∑ l ∈ Finset.range K, ∑ l' ∈ Finset.range K,
          (B l * conj (B l')) * e ((s : ℝ) * (((l : ℤ) - l' : ℤ) : ℝ) / K) := by
    intro s
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
    rw [map_mul, ← e_neg]
    have : e ((s : ℝ) * (((l : ℤ) - l' : ℤ) : ℝ) / K) =
        e ((s : ℝ) * l / K) * e (-((s : ℝ) * l' / K)) := by
      rw [← e_add]
      congr 1
      push_cast
      ring
    rw [this]
    ring
  simp_rw [h1]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_range_e_mul_div hK]
  have hl' := Finset.mem_range.1 hl
  rw [Finset.sum_eq_single l]
  · simp only [sub_self, dvd_zero, ite_true]
    ring
  · intro l' hl'' hne
    rw [ite_eq_right_iff.2, mul_zero]
    intro hdvd
    exfalso
    have hl'' := Finset.mem_range.1 hl''
    have := Int.eq_zero_of_abs_lt_dvd hdvd (by rw [abs_lt]; omega)
    omega
  · intro h
    exact absurd hl h

end PrimeCarleson.Proof.Common
