module

public import OAI.NumberTheory.DirichletL.LogarithmicControl
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.BorelCaratheodory

/-!
# A Landau-type bound for the logarithmic derivative on a zero-free disc

Part of the prime number theorem in progressions on the classical zero-free region
(`PNTSW/Main.lean`). The classical zero-free region has width `c / log (q (|t| + 3))`, so the
logarithmic derivative has to be controlled on a disc whose radius is that width, not at scale one.

* `logDeriv_bound_of_disc`: if `F` is holomorphic and zero-free on `ball c R`, `‖F‖ ≤ e^M` there,
  and `F c = exp m` with `‖m‖ ≤ A`, then `‖F'/F‖ ≤ (112 M + 120 A) / R` on `closedBall c (3R/4)`.

The proof takes a holomorphic logarithm `g` of `F` with `g c = m`
(`OAI.SevenEighths.LogarithmicControl.exists_holomorphic_log_normalized`, a Mathlib-only file),
bounds `g` on `closedBall c (7R/8)` by the Borel-Carathéodory theorem of Mathlib, and bounds `g'`
by a Cauchy estimate on circles of radius `R/8`.
-/

@[expose] public noncomputable section

open Metric Complex

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31.PNTSW

/-- **Landau-type bound.**  `‖F'/F‖ ≤ (112 M + 120 A) / R` on `closedBall c (3R/4)` for `F`
holomorphic and zero-free on `ball c R`, bounded by `e^M` there, with a logarithm `m` of `F c`
of norm at most `A`. -/
theorem logDeriv_bound_of_disc {F : ℂ → ℂ} {c m : ℂ} {R M A : ℝ} (hR : 0 < R) (hM : 0 < M)
    (hA : 0 ≤ A) (hF : DifferentiableOn ℂ F (ball c R)) (h0 : ∀ z ∈ ball c R, F z ≠ 0)
    (hb : ∀ z ∈ ball c R, ‖F z‖ ≤ Real.exp M) (hm : Complex.exp m = F c) (hmA : ‖m‖ ≤ A)
    {z : ℂ} (hz : z ∈ closedBall c (3 * R / 4)) :
    ‖deriv F z / F z‖ ≤ (112 * M + 120 * A) / R := by
  obtain ⟨g, hg, hge, hgc⟩ :=
    OAI.SevenEighths.LogarithmicControl.exists_holomorphic_log_normalized hR hF h0 hm
  have hRe : ∀ w ∈ ball c R, (g w).re ≤ M := by
    intro w hw
    have h1 : ‖Complex.exp (g w)‖ = Real.exp (g w).re := Complex.norm_exp _
    have h2 : Complex.exp (g w) = F w := hge hw
    rw [h2] at h1
    have := hb w hw
    rw [h1] at this
    exact Real.exp_le_exp.mp this
  have hgc' : ‖g c‖ ≤ A := by rw [hgc]; exact hmA
  have hbc : ∀ w ∈ closedBall c (7 * R / 8), ‖g w‖ ≤ 14 * M + 15 * A := by
    intro w hw
    have := OAI.SevenEighths.LogarithmicControl.borel_caratheodory_closedBall (g := g) (c := c)
      (r := 7 * R / 8) (R := R) (M := M) (A := A) (by positivity) (by linarith) hM hA hg hRe hgc'
      hw
    refine this.trans (le_of_eq ?_)
    field_simp
    ring
  have hzR : ‖z - c‖ ≤ 3 * R / 4 := by simpa [mem_closedBall, dist_eq_norm] using hz
  have hsub : closedBall z (R / 8) ⊆ closedBall c (7 * R / 8) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw ⊢
    have : ‖w - c‖ ≤ ‖w - z‖ + ‖z - c‖ := by
      have := norm_add_le (w - z) (z - c)
      simpa using this
    linarith
  have hsub' : closedBall z (R / 8) ⊆ ball c R := fun w hw =>
    closedBall_subset_ball (by linarith : 7 * R / 8 < R) (hsub hw)
  have hdc : DiffContOnCl ℂ g (ball z (R / 8)) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ (by positivity : R / 8 ≠ 0)]
    exact hg.mono hsub'
  have hcau := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z) (R := R / 8)
    (C := 14 * M + 15 * A) (f := g) (by positivity) hdc (fun w hw =>
      hbc w (hsub (sphere_subset_closedBall hw)))
  have hzmem : z ∈ ball c R := by
    exact closedBall_subset_ball (by linarith : 7 * R / 8 < R)
      (hsub (mem_closedBall_self (by positivity)))
  rw [OAI.SevenEighths.LogarithmicControl.logarithmic_derivative_eq isOpen_ball hg hge hzmem]
  refine hcau.trans (le_of_eq ?_)
  field_simp
  ring

end PrimeCarleson.Proof.Fplus31.PNTSW
