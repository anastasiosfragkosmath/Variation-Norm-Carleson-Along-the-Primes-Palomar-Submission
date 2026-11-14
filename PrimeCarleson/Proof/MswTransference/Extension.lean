module

public import PrimeCarleson.Proof.MswTransference.Cutoff
public import PrimeCarleson.Frozen.MultiplierOp
public import PrimeCarleson.Frozen.MultiplierOpDis
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The multiplier operator on extensions of finitely supported sequences

Fourier-side identities for the Magyar–Stein–Wainger transference
`PrimeCarleson.msw_transference_variation`. Let `m` be bounded, measurable and supported in
`(-1/2, 1/2]`, and let `F = extend f = ∑ₖ f(k) Φ(· - k)` with the cutoff `Φ` of
`PrimeCarleson.Proof.MswTransference.cutoff`. Since `Φ̂ = 1` on `[-1/2, 1/2]`,
`m F̂ = g` with `g(ξ) = m(ξ) ∑ₖ f(k) e(-kξ)`, so `T F(x) = ∫ g(ξ) e(ξx) dξ`. Hence

* `multiplierOp_extend_intCast`: `T F` restricted to `ℤ` is the discrete operator `T_dis f`;
* `continuous_multiplierOp_extend`: `T F` is continuous;
* `integrable_multiplierOp_extend_mul`, `multiplierOp_extend_eq_integral`: `T F = T F ⋆ Φ`,
  because the Fourier transform of `T F` is `g`, supported where `Φ̂ = 1`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal SchwartzMap

set_option autoImplicit false

namespace PrimeCarleson.Proof.MswTransference

section Character

theorem norm_e (t : ℝ) : ‖e t‖ = 1 := by
  rw [← fourierChar_eq_e]
  exact Circle.norm_coe _

theorem e_add (a b : ℝ) : e (a + b) = e a * e b := by
  rw [e, e, e, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem continuous_e : Continuous e := by
  unfold e
  fun_prop

end Character

section Translate

/-- The Fourier transform of a translate of the cutoff on `[-1/2, 1/2]`. -/
theorem integral_cutoff_sub_mul_e (a : ℝ) {ξ : ℝ} (hξ : |ξ| ≤ 1 / 2) :
    ∫ y, cutoff (y - a) * e (-(y * ξ)) = e (-(a * ξ)) := by
  calc ∫ y, cutoff (y - a) * e (-(y * ξ))
      = ∫ y, cutoff (y - a) * e (-((y - a) * ξ)) * e (-(a * ξ)) := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        dsimp only
        rw [mul_assoc, ← e_add]
        congr 2
        ring
    _ = ∫ y, cutoff y * e (-(y * ξ)) * e (-(a * ξ)) :=
        integral_sub_right_eq_self (μ := volume)
          (fun y : ℝ => cutoff y * e (-(y * ξ)) * e (-(a * ξ))) a
    _ = e (-(a * ξ)) := by rw [integral_mul_const, cutoff_fourier_eq_one hξ, one_mul]

theorem integrable_cutoff_sub_mul_e (a ξ : ℝ) :
    Integrable (fun y => cutoff (y - a) * e (-(y * ξ))) :=
  (cutoff.integrable.comp_sub_right a).mul_bdd
    (continuous_e.comp (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun y => (norm_e _).le)

/-- The Fourier transform of `extend f` on `[-1/2, 1/2]`. -/
theorem integral_extend_mul_e (f : ℤ →₀ ℂ) {ξ : ℝ} (hξ : |ξ| ≤ 1 / 2) :
    ∫ y, extend f y * e (-(y * ξ)) = f.sum fun k c => c * e (-(k * ξ)) := by
  simp only [extend_apply, Finsupp.sum, Finset.sum_mul]
  rw [integral_finsetSum _ fun k _ => ?_]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp only [mul_assoc]
    rw [integral_const_mul, integral_cutoff_sub_mul_e _ hξ]
  · simp only [mul_assoc]
    exact (integrable_cutoff_sub_mul_e _ _).const_mul _

end Translate

section Symbol

/-- The trigonometric polynomial `∑ₖ f(k) e(-kξ)`. -/
def trigPoly (f : ℤ →₀ ℂ) (ξ : ℝ) : ℂ :=
  f.sum fun k c => c * e (-(k * ξ))

theorem continuous_trigPoly (f : ℤ →₀ ℂ) : Continuous (trigPoly f) := by
  unfold trigPoly Finsupp.sum
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_e.comp (by fun_prop))

theorem norm_trigPoly_le (f : ℤ →₀ ℂ) (ξ : ℝ) :
    ‖trigPoly f ξ‖ ≤ ∑ k ∈ f.support, ‖f k‖ := by
  unfold trigPoly Finsupp.sum
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
  rw [norm_mul, norm_e, mul_one]

theorem integrable_of_support_subset_Ioc {m : ℝ → ℂ} (hm : Measurable m)
    (hb : ∃ M : ℝ, ∀ ξ, ‖m ξ‖ ≤ M) (hs : Function.support m ⊆ Set.Ioc (-1 / 2) (1 / 2)) :
    Integrable m := by
  obtain ⟨M, hM⟩ := hb
  rw [← integrableOn_iff_integrable_of_support_subset hs]
  exact Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hm.aestronglyMeasurable
    (Eventually.of_forall hM)

theorem abs_le_of_mem_support {m : ℝ → ℂ}
    (hs : Function.support m ⊆ Set.Ioc (-1 / 2) (1 / 2)) {ξ : ℝ} (hξ : m ξ ≠ 0) :
    |ξ| ≤ 1 / 2 := by
  obtain ⟨h1, h2⟩ := hs hξ
  rw [abs_le]
  constructor <;> linarith

theorem mul_integral_extend_mul_e {m : ℝ → ℂ}
    (hs : Function.support m ⊆ Set.Ioc (-1 / 2) (1 / 2)) (f : ℤ →₀ ℂ) (ξ : ℝ) :
    m ξ * (∫ y, extend f y * e (-(y * ξ))) = m ξ * trigPoly f ξ := by
  by_cases hξ : m ξ = 0
  · simp [hξ]
  · rw [integral_extend_mul_e f (abs_le_of_mem_support hs hξ), trigPoly]

theorem multiplierOp_extend_eq {m : ℝ → ℂ}
    (hs : Function.support m ⊆ Set.Ioc (-1 / 2) (1 / 2)) (f : ℤ →₀ ℂ) (x : ℝ) :
    multiplierOp m (extend f) x = ∫ ξ, m ξ * trigPoly f ξ * e (ξ * x) := by
  unfold multiplierOp
  simp only [mul_integral_extend_mul_e hs]

theorem integrable_mul_trigPoly {m : ℝ → ℂ} (hm : Measurable m)
    (hb : ∃ M : ℝ, ∀ ξ, ‖m ξ‖ ≤ M) (hs : Function.support m ⊆ Set.Ioc (-1 / 2) (1 / 2))
    (f : ℤ →₀ ℂ) : Integrable fun ξ => m ξ * trigPoly f ξ :=
  (integrable_of_support_subset_Ioc hm hb hs).mul_bdd
    (continuous_trigPoly f).aestronglyMeasurable
    (Eventually.of_forall (norm_trigPoly_le f))

theorem measurable_mul_trigPoly {m : ℝ → ℂ} (hm : Measurable m) (f : ℤ →₀ ℂ) :
    Measurable fun ξ => m ξ * trigPoly f ξ :=
  hm.mul (continuous_trigPoly f).measurable

theorem norm_multiplierOp_extend_le {m : ℝ → ℂ}
    (hs : Function.support m ⊆ Set.Ioc (-1 / 2) (1 / 2)) (f : ℤ →₀ ℂ) (x : ℝ) :
    ‖multiplierOp m (extend f) x‖ ≤ ∫ ξ, ‖m ξ * trigPoly f ξ‖ := by
  rw [multiplierOp_extend_eq hs]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [norm_mul, norm_e, mul_one]

end Symbol

section Multiplier

variable {m : ℝ → ℂ} (hm : Measurable m) (hb : ∃ M : ℝ, ∀ ξ, ‖m ξ‖ ≤ M)
  (hs : Function.support m ⊆ Set.Ioc (-1 / 2) (1 / 2))
include hm hb hs

theorem multiplierOp_extend_intCast (f : ℤ →₀ ℂ) (n : ℤ) :
    multiplierOp m (extend f) n = multiplierOpDis m f n := by
  have hmi := integrable_of_support_subset_Ioc hm hb hs
  rw [multiplierOp_extend_eq hs, multiplierOpDis, Finsupp.sum]
  have h : ∀ ξ : ℝ, m ξ * trigPoly f ξ * e (ξ * n) =
      ∑ k ∈ f.support, f k * (m ξ * e (((n - k : ℤ) : ℝ) * ξ)) := by
    intro ξ
    rw [trigPoly, Finsupp.sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show ((n - k : ℤ) : ℝ) * ξ = -(k * ξ) + ξ * n by push_cast; ring, e_add]
    ring
  simp only [h]
  rw [integral_finsetSum _ fun k _ => ?_]
  · simp only [integral_const_mul]
  · exact (hmi.mul_bdd (continuous_e.comp (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun ξ => (norm_e _).le)).const_mul _

theorem continuous_multiplierOp_extend (f : ℤ →₀ ℂ) :
    Continuous (multiplierOp m (extend f)) := by
  have hg := integrable_mul_trigPoly hm hb hs f
  have h : multiplierOp m (extend f) = fun x => ∫ ξ, m ξ * trigPoly f ξ * e (ξ * x) :=
    funext (multiplierOp_extend_eq hs f)
  rw [h]
  refine continuous_of_dominated (bound := fun ξ => ‖m ξ * trigPoly f ξ‖) (fun x => ?_)
    (fun x => Eventually.of_forall fun ξ => ?_) hg.norm
    (Eventually.of_forall fun ξ => ?_)
  · exact hg.aestronglyMeasurable.mul (continuous_e.comp (by fun_prop)).aestronglyMeasurable
  · rw [norm_mul, norm_e, mul_one]
  · exact continuous_const.mul (continuous_e.comp (by fun_prop))

theorem integrable_multiplierOp_extend_mul (f : ℤ →₀ ℂ) (x : ℝ) :
    Integrable (fun y => multiplierOp m (extend f) y * cutoff (x - y)) :=
  (cutoff.integrable.comp_sub_left x).bdd_mul
    (continuous_multiplierOp_extend hm hb hs f).aestronglyMeasurable
    (Eventually.of_forall (norm_multiplierOp_extend_le hs f))

theorem multiplierOp_extend_eq_integral (f : ℤ →₀ ℂ) (x : ℝ) :
    multiplierOp m (extend f) x = ∫ y, multiplierOp m (extend f) y * cutoff (x - y) := by
  set g : ℝ → ℂ := fun ξ => m ξ * trigPoly f ξ with hg_def
  have hg : Integrable g := integrable_mul_trigPoly hm hb hs f
  have hgm : Measurable g := measurable_mul_trigPoly hm f
  have hprod : Integrable (Function.uncurry fun y ξ => g ξ * e (ξ * y) * cutoff (x - y))
      (volume.prod volume) := by
    refine Integrable.mono' ((cutoff.integrable.comp_sub_left x).norm.mul_prod hg.norm) ?_
      (Eventually.of_forall fun p => ?_)
    · exact ((hgm.comp measurable_snd).mul
        (continuous_e.comp (by fun_prop)).measurable).mul
        (cutoff.continuous.comp (by fun_prop)).measurable |>.aestronglyMeasurable
    · change ‖g p.2 * e (p.2 * p.1) * cutoff (x - p.1)‖ ≤ ‖cutoff (x - p.1)‖ * ‖g p.2‖
      rw [norm_mul, norm_mul, norm_e, mul_one, mul_comm]
  have hy : ∀ y, multiplierOp m (extend f) y * cutoff (x - y) =
      ∫ ξ, g ξ * e (ξ * y) * cutoff (x - y) := by
    intro y
    rw [multiplierOp_extend_eq hs, integral_mul_const]
  have hξ : ∀ ξ, ∫ y, g ξ * e (ξ * y) * cutoff (x - y) = g ξ * e (ξ * x) := by
    intro ξ
    by_cases h0 : m ξ = 0
    · simp [hg_def, h0]
    calc ∫ y, g ξ * e (ξ * y) * cutoff (x - y)
        = ∫ y, g ξ * (cutoff (x - y) * e (-((x - y) * ξ))) * e (ξ * x) := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          dsimp only
          rw [show ξ * y = -((x - y) * ξ) + ξ * x by ring, e_add]
          ring
      _ = ∫ u, g ξ * (cutoff u * e (-(u * ξ))) * e (ξ * x) :=
          integral_sub_left_eq_self
            (fun u : ℝ => g ξ * (cutoff u * e (-(u * ξ))) * e (ξ * x)) volume x
      _ = g ξ * e (ξ * x) := by
          rw [integral_mul_const, integral_const_mul,
            cutoff_fourier_eq_one (abs_le_of_mem_support hs h0), mul_one]
  rw [integral_congr_ae (Eventually.of_forall hy), integral_integral_swap hprod,
    integral_congr_ae (Eventually.of_forall hξ), multiplierOp_extend_eq hs]

end Multiplier

end PrimeCarleson.Proof.MswTransference
