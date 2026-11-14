module

public import PrimeCarleson.Proof.Oplus.ModelBound.All
public import PrimeCarleson.Proof.Oplus.Theorem.CutoffSeq

/-!
# The linearized theorem: `‖𝒮'[f]‖_{L^p} ≤ C ‖f‖_{L^p}` for Schwartz `f` ([O+] L905-L926)

Source: [O+] `linearizedtheorem`, L905–L921; [O+] `linearizedtheorem`, L921–L926 (in the amended
form used here), L905-L926 and L1026-L1096.

For `r > 2`, `r' < p < 2r/(r-2)`, linearizing data `L` (`K`, `Ξ`, `ξ_k`, `a_k`) with `Ξ` free of
dyadic end points, and every Schwartz function `f`,
`‖𝒮'[f]‖_{L^p} ≤ C ‖f‖_{L^p}` with `C = 10 C_{p,r}` independent of `K`, `Ξ` and the data.

* `linearized_of_compact`: the case `f̂` compactly supported in `ℝ ∖ Ξ`: the wave-packet
  representation `𝒮''_{𝔓_n}[f] → 𝒮'[f]` pointwise along an exhausting sequence of finite families
  of tiles (`tendsto_waveOp_nat`) gives, by Fatou (`eLpNorm_op_le_liminf_waveOp`),
  `‖𝒮'[f]‖_p ≤ liminf ‖𝒮''_{𝔓_n}[f]‖_p ≤ 10 C_{p,r} ‖f‖_p` (`waveOp_strong_type`, Minkowski over
  the ten classes `ρ ∈ R`);
* `linearized_theorem`: every Schwartz `f`: cut `f̂` off near `Ξ` and at infinity
  (`exists_fourier_cutoff_seq`), `|𝒮'[f - g_n](x)| ≤ K ‖f̂ - ĝ_n‖_{L¹} → 0` for every `x`
  (`Linearization.norm_op_sub_op_le`), `‖g_n‖_p → ‖f‖_p`, and Fatou once more.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped FourierTransform SchwartzMap ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

/-- Tiles are exhausted by an increasing sequence of finite families. -/
theorem exists_exhaustion_tile :
    ∃ 𝔓 : ℕ → Finset Tile, Monotone 𝔓 ∧ ∀ P : Tile, ∃ n, P ∈ 𝔓 n := by
  classical
  have : Nonempty Tile := ⟨⟨⟨0, 0⟩, ⟨-1, 0⟩, by simp⟩⟩
  obtain ⟨f, hf⟩ := exists_surjective_nat Tile
  refine ⟨fun n => (Finset.range n).image f,
    fun m n hmn => Finset.image_subset_image (Finset.range_mono hmn), fun P => ?_⟩
  obtain ⟨m, rfl⟩ := hf P
  exact ⟨m + 1, Finset.mem_image.2 ⟨m, Finset.mem_range.2 (Nat.lt_succ_self m), rfl⟩⟩

/-- **The linearized bound for `f̂` compactly supported away from `Ξ`**: from the strong bound for
the finite-family operators and Fatou along an exhausting sequence of finite families. -/
theorem linearized_of_compact {r p C : ℝ}
    (hC : ∀ (L : Linearization r), AvoidsDyadicEndpoints (L.Ξ : Set ℝ) →
      ∀ (𝔓 : Finset Tile) {f : ℝ → ℂ}, MemLp f (ENNReal.ofReal p) volume →
      eLpNorm (waveOp L 𝔓 f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume)
    (L : Linearization r) (hΞ : AvoidsDyadicEndpoints (L.Ξ : Set ℝ)) (f : 𝓢(ℝ, ℂ))
    (hc : HasCompactSupport (𝓕 (⇑f))) (hs : ∀ ζ ∈ L.Ξ, ζ ∉ tsupport (𝓕 (⇑f))) :
    eLpNorm (L.op f) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) volume := by
  obtain ⟨𝔓, hmono, hcov⟩ := exists_exhaustion_tile
  refine (eLpNorm_op_le_liminf_waveOp L hΞ f hc hs 𝔓 hmono hcov _).trans ?_
  calc Filter.liminf (fun n => eLpNorm (waveOp L (𝔓 n) ⇑f) (ENNReal.ofReal p) volume) atTop
      ≤ Filter.liminf (fun _ : ℕ => ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) volume)
          atTop :=
        Filter.liminf_le_liminf (Eventually.of_forall fun n => hC L hΞ (𝔓 n)
          (f.memLp (ENNReal.ofReal p) volume))
    _ = _ := Filter.liminf_const _

/-- **The linearized theorem** ([O+] L905-L926): for `r > 2` and `r' < p < 2r/(r-2)` there is
`C > 0` such that `‖𝒮'[f]‖_{L^p} ≤ C ‖f‖_{L^p}` for every Schwartz function `f` and all linearizing
data `K`, `Ξ` (free of dyadic end points), `ξ_k`, `a_k`. -/
theorem linearized_theorem {r p : ℝ} (hr : 2 < r) (hp1 : Real.conjExponent r < p)
    (hp2 : p < 2 * r / (r - 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : Linearization r), AvoidsDyadicEndpoints (L.Ξ : Set ℝ) →
      ∀ f : 𝓢(ℝ, ℂ), eLpNorm (L.op f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC0, hC⟩ := waveOp_strong_type hr hp1 hp2
  have hr1 : 1 < r := by linarith
  have hp : 1 < p := lt_trans (one_lt_conjExponent hr1) hp1
  have hp1' : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  refine ⟨C, hC0, fun L hΞ f => ?_⟩
  obtain ⟨g, hgc, hgs, hg1, hgp⟩ := exists_fourier_cutoff_seq L.Ξ f
  -- pointwise convergence of `𝒮'[g_n] → 𝒮'[f]`
  have hlim : ∀ x, Tendsto (fun n => L.op (g n) x) atTop (𝓝 (L.op f x)) := by
    intro x
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (by simpa using hg1.const_mul (L.K : ℝ) : Tendsto (fun n => (L.K : ℝ) *
        ∫ η, ‖𝓕 (⇑f) η - 𝓕 (⇑(g n)) η‖) atTop (𝓝 0))
    rw [norm_sub_rev]
    exact L.norm_op_sub_op_le hr1 f (g n) x
  -- Fatou
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := ENNReal.ofReal p) (μ := volume)
    (fun n => (L.measurable_op (g n)).aestronglyMeasurable) (L.op f)
    (L.measurable_op f).aestronglyMeasurable (Eventually.of_forall hlim)
  refine hfatou.trans ?_
  -- the bounds for `g_n`
  have hbd : ∀ n, eLpNorm (L.op (g n)) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal C * (eLpNorm (⇑f) (ENNReal.ofReal p) volume +
        eLpNorm (⇑(g n) - ⇑f) (ENNReal.ofReal p) volume) := by
    intro n
    refine (linearized_of_compact hC L hΞ (g n) (hgc n) (hgs n)).trans ?_
    gcongr
    calc eLpNorm (⇑(g n)) (ENNReal.ofReal p) volume
        = eLpNorm (⇑f + (⇑(g n) - ⇑f)) (ENNReal.ofReal p) volume := by
          congr 1; ext x; simp
      _ ≤ _ := eLpNorm_add_le hp1'
  have htend : Tendsto (fun n => ENNReal.ofReal C * (eLpNorm (⇑f) (ENNReal.ofReal p) volume +
      eLpNorm (⇑(g n) - ⇑f) (ENNReal.ofReal p) volume)) atTop
      (𝓝 (ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) volume)) := by
    have h1 := (tendsto_const_nhds (x := eLpNorm (⇑f) (ENNReal.ofReal p) volume)).add (hgp p hp)
    rw [add_zero] at h1
    exact ENNReal.Tendsto.const_mul h1 (Or.inr ENNReal.ofReal_ne_top)
  calc Filter.liminf (fun n => eLpNorm (L.op (g n)) (ENNReal.ofReal p) volume) atTop
      ≤ Filter.liminf (fun n => ENNReal.ofReal C * (eLpNorm (⇑f) (ENNReal.ofReal p) volume +
          eLpNorm (⇑(g n) - ⇑f) (ENNReal.ofReal p) volume)) atTop :=
        Filter.liminf_le_liminf (Eventually.of_forall hbd)
    _ = _ := htend.liminf_eq

end PrimeCarleson.Proof.Oplus
