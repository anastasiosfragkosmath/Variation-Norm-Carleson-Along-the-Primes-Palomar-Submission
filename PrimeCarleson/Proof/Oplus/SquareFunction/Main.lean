module

public import PrimeCarleson.Proof.Oplus.SquareFunction.VarEst
public import PrimeCarleson.Proof.Oplus.Defs.Psi

/-!
# `varestpsi` at `p = 2`: final statements

Let `ψ` be a Schwartz function with `∫ ψ = 1`, `ψ_k = 2^{-k} ψ(2^{-k} ·)` (`schwartzScale`) and
`A_k f = ψ_k * f` (`schwartzAvg`).

* `varestpsi_two` (Source: [O+] `varestpsi`, L2011–L2016, at `p = 2`):
  `‖V^r_{k∈ℤ}(A_k f)‖_{L²} ≤ K' ‖f‖_{L²}` for `r > 2`;
* `varestpsi_two_eLpNorm`: the same in terms of `eLpNorm`.

The functions `f` are only assumed to lie in `L²` (`MemLp f 2 volume`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal SchwartzMap

open PrimeCarleson PrimeCarleson.Proof.Lepingle

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- The family `x ↦ V^r_k(b_k(x))` is measurable when every `b_k` is. -/
theorem measurable_rVariationOn_family (r : ℝ) {b : ℤ → ℝ → ℂ} (hb : ∀ m, Measurable (b m)) :
    Measurable fun x => rVariationOn r (Set.range ((↑) : ℤ → ℝ)) (fun t => b ⌊t⌋ x) := by
  have : (fun x => rVariationOn r (Set.range ((↑) : ℤ → ℝ)) (fun t => b ⌊t⌋ x)) =
      fun x => ⨆ (J : ℕ) (k : Fin (J + 1) → ℤ) (_ : StrictMono k),
        (∑ i : Fin J, ‖b (k i.castSucc) x - b (k i.succ) x‖ₑ ^ r) ^ (1 / r) := by
    funext x
    have h := rVariationOn_intCast_image_eq r Set.univ (fun m => b m x)
    rw [Set.image_univ] at h
    rw [h]
    simp only [Set.mem_univ, iSup_pos, implies_true]
  rw [this]
  refine Measurable.iSup fun J => Measurable.iSup fun k => Measurable.iSup fun _ => ?_
  refine Measurable.pow_const (Finset.measurable_sum _ fun i _ => ?_) _
  exact (((hb _).sub (hb _)).enorm).pow_const _

/-- **`varestpsi` at `p = 2`** ([O+] L2011-L2016): for `r > 2` there is a constant `K` (depending on
`r` and `ψ`) with `‖V^r_{k∈ℤ}(A_k f)‖_{L²(ℝ)} ≤ K ‖f‖_{L²(ℝ)}`, where
`V^r_k(A_k f(x)) = rVariationOn r (range ((↑) : ℤ → ℝ)) (t ↦ A_{⌊t⌋} f(x))` is the supremum
over finite increasing chains of integers. -/
theorem varestpsi_two (ψ : 𝓢(ℝ, ℂ)) (hψ : ∫ t, ψ t = 1) {r : ℝ} (hr : 2 < r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : ℝ → ℂ, MemLp f 2 volume →
      (∫⁻ x, rVariationOn r (Set.range ((↑) : ℤ → ℝ)) (fun t => schwartzAvg ψ ⌊t⌋ f x) ^
          (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤
        ENNReal.ofReal K * (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
  obtain ⟨C, -, hC⟩ := exists_deriv_decay ψ
  have hfin := squareFunctionConst_lt_top ψ C
  have hK : ENNReal.ofReal (672 * 2 * (2 / (2 - 1)) * (r / (r - 2))) +
      2 * squareFunctionConst ψ C ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top (by simp) hfin.ne⟩
  refine ⟨(ENNReal.ofReal (672 * 2 * (2 / (2 - 1)) * (r / (r - 2))) +
    2 * squareFunctionConst ψ C).toReal, ENNReal.toReal_nonneg, fun f hf => ?_⟩
  rw [ENNReal.ofReal_toReal hK]
  set f₀ : ℝ → ℂ := hf.aestronglyMeasurable.mk f with hf₀
  have hae : f =ᵐ[volume] f₀ := hf.aestronglyMeasurable.ae_eq_mk
  have hf₀m : Measurable f₀ := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hf₀L : MemLp f₀ 2 volume := hf.ae_eq hae
  have h1 : ∀ k x, schwartzAvg ψ k f x = schwartzAvg ψ k f₀ x := fun k x =>
    schwartzAvg_congr_ae ψ k hae x
  have h3 : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) = ∫⁻ x, ‖f₀ x‖ₑ ^ (2 : ℝ) :=
    lintegral_congr_ae (hae.mono fun x hx => by simp only [hx])
  have e : (fun x => rVariationOn r (Set.range ((↑) : ℤ → ℝ))
      (fun t => schwartzAvg ψ ⌊t⌋ f x) ^ (2 : ℝ)) = fun x => rVariationOn r
        (Set.range ((↑) : ℤ → ℝ)) (fun t => schwartzAvg ψ ⌊t⌋ f₀ x) ^ (2 : ℝ) := by
    funext x
    congr 2
    funext t
    exact h1 _ x
  rw [e, h3]
  exact varestpsi_two_of_measurable hψ hC hr hf₀m hf₀L

/-- `varestpsi` for `p = 2`, in terms of `eLpNorm`. -/
theorem varestpsi_two_eLpNorm (ψ : 𝓢(ℝ, ℂ)) (hψ : ∫ t, ψ t = 1) {r : ℝ} (hr : 2 < r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : ℝ → ℂ, MemLp f 2 volume →
      eLpNorm (fun x => rVariationOn r (Set.range ((↑) : ℤ → ℝ))
          (fun t => schwartzAvg ψ ⌊t⌋ f x)) 2 volume ≤
        ENNReal.ofReal K * eLpNorm f 2 volume := by
  obtain ⟨K, hK0, hK⟩ := varestpsi_two ψ hψ hr
  refine ⟨K, hK0, fun f hf => ?_⟩
  have hmeas : Measurable fun x => rVariationOn r (Set.range ((↑) : ℤ → ℝ))
      (fun t => schwartzAvg ψ ⌊t⌋ f x) := by
    set f₀ : ℝ → ℂ := hf.aestronglyMeasurable.mk f with hf₀
    have hae : f =ᵐ[volume] f₀ := hf.aestronglyMeasurable.ae_eq_mk
    have hf₀m : Measurable f₀ := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
    have h1 : ∀ k x, schwartzAvg ψ k f x = schwartzAvg ψ k f₀ x := fun k x =>
      schwartzAvg_congr_ae ψ k hae x
    have e : (fun x => rVariationOn r (Set.range ((↑) : ℤ → ℝ))
        (fun t => schwartzAvg ψ ⌊t⌋ f x)) = fun x => rVariationOn r
          (Set.range ((↑) : ℤ → ℝ)) (fun t => schwartzAvg ψ ⌊t⌋ f₀ x) := by
      funext x
      congr 1
      funext t
      exact h1 _ x
    rw [e]
    exact measurable_rVariationOn_family r (b := fun k x => schwartzAvg ψ k f₀ x)
      (fun k => measurable_schwartzAvg ψ k hf₀m)
  have h := hK f hf
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      hmeas.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  simpa using h

end PrimeCarleson.Proof.Oplus
