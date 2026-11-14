module

public import PrimeCarleson.Proof.Paper.P5.BV

/-!
# Properties of the multiplier `K̂_Q`

`sources/Variational_Carleson.tex` L1694-L1695, L2028-L2029 (Source: main paper `s:red`,
L1694–L1695; main paper `p:global-shell-var`, L2028–L2029).

* `KQhat_bv`: there is a constant `C`, depending on `ψ` and `φ` only (not on `Q`, `D₀`, `ε`,
  `δ`), with `|K̂_Q| ≤ C` and total variation `V(K̂_Q) ≤ C` for every `Q` (the uniform bounded
  variation of the multiplier of `K_Q`);
* `eVariationOn_KQdhat`: the rescaled kernels `K_{Q,d}(m) = d K_Q(d m)` have multiplier
  `K̂_Q(ξ/d)` with the same total variation, so the bound is uniform in `Q` and `d ≥ 1`;
* `measurable_KQhat`, `integrable_KQhat`: `K̂_Q` is measurable, bounded and compactly supported,
  hence integrable, so `K_Q(x) = ∫ K̂_Q(ξ) e(xξ) dξ` is the Fourier transform of an `L¹` function;
* `KQhat_eq_zero`, `KQdhat_eq_zero`: the supports.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal FourierTransform SchwartzMap Real

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Paper.P5

namespace KQSetup

variable (S : KQSetup)

/-- **Uniform bounded variation of `K̂_Q`** (Source: main paper `p:global-shell-var`, L2028–L2029,
and `s:red`, L1694–L1695 for `d = 1`): the sup norm and the total variation of `K̂_Q` are at most
`C`, a constant depending only on `ψ` and `φ`, for every `Q` and every choice of `D₀`, `ε`. -/
theorem KQhat_bv : ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : KQParams) (Q : ℕ),
    (∀ β, ‖({ S with P := P } : KQSetup).KQhat Q β‖ ≤ C) ∧
    eVariationOn (({ S with P := P } : KQSetup).KQhat Q) Set.univ ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC0, hC⟩ := exists_bv_bound S.ψ S.φ.toSchwartz
  exact ⟨C, hC0, fun P Q => hC (P.NQ Q) (P.NQ_pos Q) (P.kmin Q)⟩

/-- `ψ`-tail is measurable. -/
theorem measurable_psiTail' (k₀ : ℕ) : Measurable (psiTail S.ψ k₀) := by
  refine measurable_of_tendsto_metrizable (f := fun n => Spart S.ψ k₀ (k₀ + n)) (fun n => ?_)
    (tendsto_pi_nhds.2 (tendsto_Spart_psiTail S.ψ k₀))
  refine Continuous.measurable (continuous_iff_continuousAt.2 fun x => ?_)
  exact (hasDerivAt_Spart S.ψ (Nat.le_add_right k₀ n) x).continuousAt

/-- `K̂_Q` is measurable. -/
theorem measurable_KQhat (Q : ℕ) : Measurable (S.KQhat Q) := by
  unfold KQhat
  refine Measurable.mul ?_ (measurable_psiTail' S _)
  exact ((𝓕 S.φ.toSchwartz).continuous.comp (continuous_const.mul continuous_id)).measurable

/-- `K̂_Q` vanishes outside `[-δ/N(Q), δ/N(Q)]`. -/
theorem support_KQhat_subset (Q : ℕ) :
    Function.support (S.KQhat Q) ⊆ Set.Icc (-(S.δ / S.P.NQ Q)) (S.δ / S.P.NQ Q) := by
  intro β hβ
  by_contra h
  apply hβ
  refine S.KQhat_eq_zero Q ?_
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at h
  rcases h with h | h
  · rw [abs_of_neg (by linarith [div_pos S.δ_pos (S.P.NQ_pos Q)])]; linarith
  · rwa [abs_of_pos (by linarith [div_pos S.δ_pos (S.P.NQ_pos Q)])]

/-- `K̂_Q` is integrable. -/
theorem integrable_KQhat (Q : ℕ) : Integrable (S.KQhat Q) := by
  obtain ⟨C, hC0, hC⟩ := S.KQhat_bv
  have hbd : ∀ β, ‖S.KQhat Q β‖ ≤ C := fun β => (hC S.P Q).1 β
  refine (integrableOn_iff_integrable_of_support_subset (S.support_KQhat_subset Q)).1 ?_
  exact Measure.integrableOn_of_bounded (measure_Icc_lt_top.ne)
    (S.measurable_KQhat Q).aestronglyMeasurable (ae_of_all _ hbd)

/-- The multiplier `ξ ↦ K̂_Q(ξ/d)` of `K_{Q,d}` has the same total variation as `K̂_Q`. -/
theorem eVariationOn_KQdhat {d : ℕ} (hd : 1 ≤ d) (Q : ℕ) :
    eVariationOn (S.KQdhat Q d) Set.univ = eVariationOn (S.KQhat Q) Set.univ := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 := eVariationOn.comp_eq_of_monotoneOn (S.KQhat Q) (fun ξ : ℝ => ξ / d)
    (t := Set.univ) (fun a _ b _ hab => div_le_div_of_nonneg_right hab hd0.le)
  have h2 : (fun ξ : ℝ => ξ / d) '' Set.univ = Set.univ := by
    ext y
    simp only [Set.image_univ, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨y * d, by field_simp⟩
  rw [h2] at h1
  exact h1

/-- **Uniform bounded variation of the multiplier of `K_{Q,d}`** (Source: main paper `s:red`,
L1694–L1695): for every `d ≥ 1`, the sup norm and the total variation of `ξ ↦ K̂_Q(ξ/d)` are at most
`C`, with `C` depending only on `ψ` and `φ` (uniformly in `Q`, `d`, `D₀`, `ε`). -/
theorem KQdhat_bv : ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : KQParams) (Q d : ℕ), 1 ≤ d →
    (∀ ξ, ‖({ S with P := P } : KQSetup).KQdhat Q d ξ‖ ≤ C) ∧
    eVariationOn (({ S with P := P } : KQSetup).KQdhat Q d) Set.univ ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC0, hC⟩ := S.KQhat_bv
  refine ⟨C, hC0, fun P Q d hd => ⟨fun ξ => (hC P Q).1 _, ?_⟩⟩
  rw [({ S with P := P } : KQSetup).eVariationOn_KQdhat hd Q]
  exact (hC P Q).2

/-- `K̂_Q(ξ/d) = 0` for `|ξ| > d δ / N(Q)`. -/
theorem KQdhat_eq_zero {d : ℕ} (hd : 1 ≤ d) (Q : ℕ) {ξ : ℝ}
    (hξ : d * (S.δ / S.P.NQ Q) < |ξ|) : S.KQdhat Q d ξ = 0 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  refine S.KQhat_eq_zero Q ?_
  rw [abs_div, abs_of_pos hd0, lt_div_iff₀ hd0]
  linarith

end KQSetup

end PrimeCarleson.Proof.Paper
