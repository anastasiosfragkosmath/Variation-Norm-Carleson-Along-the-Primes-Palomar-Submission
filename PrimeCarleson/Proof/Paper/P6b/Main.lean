module

public import PrimeCarleson.Proof.Paper.P6b.Adapter
public import PrimeCarleson.Proof.Paper.P6b.Interp
public import PrimeCarleson.Proof.Paper.P6b.Saving
public import PrimeCarleson.Proof.Paper.P6a.Main

/-!
# The power saving `e:red-var` for the shell operators `V^{Q,r}`

Source: main paper `l:red-var-l2`, L1546–L1564; main paper `s:red`, L1530–L1543, L1717–L1760 and the
steps proved in the other files of `P6b/`. `red_var_premise` proves, for the setup `S` of `K_Q`,
exactly the premise of the theorem `red_var_param` of `Main/RedVar.lean` (the hypothesis `e:red-var`
of Proposition `p:red-var`):
`∃ c > 0, ∃ C, ∀ Q = 2^j, ‖V^{Q,r} f‖_{ℓ^p} ≤ C Q^{-c} ‖f‖_{ℓ^p}`.

It is conditional on

* `hO : OplusVariationBound` (the `[O+]` statement, through `c:disc` and `l:varcarZ`);
* `hC : CQL2Saving S`, the `ℓ²` saving `‖C^Q f‖₂ ≲ Q^{-ε/2} ‖f‖₂` of the maximal operator
  (Source: main paper `s:number`, L1742–L1745; proved in `P10/BlockSum.lean`);
* the two smallness conditions on the cutoff `φ` of `S`: `SupportBlock` and `SupportScale (1/16)`
  (the radius `δ₀`);
* the numerical condition `hrange` of the paper (`e:interp-var-l2-condition`, L1554): for
  `p ≠ 2`, exponents `s > r'`, `θ ∈ (0, 1)` with `1/p = θ/2 + (1-θ)/s` and `α ∈ (0, 1 - 2/r)`
  with `(1-θ)/r < θ ε α/2`. For `p = 2` there is no condition. This is the paper's restriction
  of the range of `p` ("the range of exponents in the variational formulation is somewhat
  restricted, and dependent on interpolation", L1530): it depends on `ε = S.P.ε ≤ 1/(101 D₀)`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- **The premise `e:red-var` of `p:red-var`, from the `ℓ²` saving** (Source: main paper
`l:red-var-l2`, L1546–L1564; main paper `s:red`, L1530–L1543 and L1754–L1760; see the module
docstring for the hypotheses): for `r > 2`, with the numerical condition `hrange` (void for
`p = 2`), `∃ c > 0, ∃ C, ‖V^{Q,r} f‖_{ℓ^p} ≤ C Q^{-c} ‖f‖_{ℓ^p}` for every dyadic `Q = 2^j` and
finitely supported `f`. -/
theorem red_var_premise (hO : OplusVariationBound) (S : KQSetup) (hS : S.P.SupportBlock S.δ)
    (hSc : S.P.SupportScale S.δ (1 / 16)) (hC : CQL2Saving S) {r p : ℝ} (hr : 2 < r)
    (hrange : p = 2 ∨ ∃ s θ α : ℝ, r / (r - 1) < s ∧ 0 < θ ∧ θ < 1 ∧
      1 / p = θ / 2 + (1 - θ) / s ∧ 0 < α ∧ α < 1 - 2 / r ∧
      (1 - θ) / r < θ * (S.P.ε * α / 2)) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ (j : ℕ) (f : ℤ →₀ ℂ),
      eLpNorm (S.VQr r (2 ^ j) (⇑f)) (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ (-c)) *
          eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  have hε := S.P.ε_pos
  have hr0 : 0 < r := by linarith
  by_cases hp2 : p = 2
  · -- `p = 2`: the `ℓ²` saving itself, with `α = (1 - 2/r)/2`
    subst hp2
    have h2r : 0 < 2 / r := by positivity
    have hlt : 2 / r < 1 := by rw [div_lt_one hr0]; exact hr
    have hα0 : 0 < (1 - 2 / r) / 2 := by linarith
    have hα1 : (1 - 2 / r) / 2 < 1 - 2 / r := by linarith
    obtain ⟨C, -, hC'⟩ := var_l2_power_saving hO S hS hSc hC hr hα0 hα1
      (δ := S.P.ε * ((1 - 2 / r) / 2) / 4) (by positivity)
    refine ⟨S.P.ε * ((1 - 2 / r) / 2) / 4, by positivity, C, fun j f => ?_⟩
    have := hC' j f
    have e1 : S.P.ε * ((1 - 2 / r) / 2) / 4 - S.P.ε * ((1 - 2 / r) / 2) / 2 =
        -(S.P.ε * ((1 - 2 / r) / 2) / 4) := by ring
    rwa [e1] at this
  · obtain ⟨s, θ, α, hs, hθ0, hθ1, hp, hα0, hα1, hcond⟩ := hrange.resolve_left hp2
    set δ : ℝ := (θ * (S.P.ε * α / 2) - (1 - θ) / r) / (2 * θ) with hδ
    have hδ0 : 0 < δ := div_pos (by linarith) (by positivity)
    obtain ⟨C, -, hC'⟩ := var_l2_power_saving hO S hS hSc hC hr hα0 hα1 hδ0
    set σ : ℝ := S.P.ε * α / 2 - δ with hσ
    have h2 : ∀ (j : ℕ) (f : ℤ →₀ ℂ),
        eLpNorm (S.VQr r (2 ^ j) (⇑f)) (ENNReal.ofReal 2) Measure.count ≤
          ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ (-σ)) *
            eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count := by
      intro j f
      have := hC' j f
      have e1 : δ - S.P.ε * α / 2 = -σ := by rw [hσ]; ring
      rwa [e1] at this
    have hcond' : (1 - θ) / r < θ * σ := by
      have : θ * σ = θ * (S.P.ε * α / 2) - θ * δ := by rw [hσ]; ring
      have h3 : θ * δ = (θ * (S.P.ε * α / 2) - (1 - θ) / r) / 2 := by
        rw [hδ]; field_simp
      linarith
    obtain ⟨c, hc, -, C', -, hC''⟩ := red_var_l2 hO S hS hr hs hθ0 hθ1 hp hp2 h2 hcond'
    exact ⟨c, hc, C', hC''⟩

end PrimeCarleson.Proof.Paper
