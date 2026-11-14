module

public import PrimeCarleson.Proof.Paper.P3.TwoSided
public import PrimeCarleson.Proof.Common.Variation

/-!
# Reflection invariance of the variation over `𝕋`

For the two-sided weights `u ψ_k` (Source: main paper `e:local-U3-var-red`, L1288–L1303) the
negative-`n` part of the modulated sum is the positive-`n` part of the reflected function:
`T^{cm}_λ f(x) = -T^{cp}_{-λ} f̃(-x)` (`weightedModSum_cm_eq` of `P3/TwoSided.lean`),
`cm(n) = -cp(-n)`, `f̃(y) = f(-y)`. The maximal function does not see `λ ↦ -λ`; the variation over
`𝕋 = [0, 1)` does, because `-𝕋 = (-1, 0]`. For a continuous `1`-periodic `g` we show
`V^r(g(-·) : [0, 1)) ≤ V^r(g : [0, 1))` (`rVariationOn_Ico_comp_neg_le`):
`g(-λ) = g(1 - λ)` by periodicity, `λ ↦ 1 - λ` reverses chains (`Fin.rev`) and maps `[0, 1)` onto
`(0, 1]`, and a chain in `(0, 1]` is a limit of chains in `[0, 1)` (`rVariationOn_Ioc_le_Ico`,
continuity of `g`). `rVariationOn_weightedModSum_cm_le` is the application to the modulated
sums.
-/

@[expose] public noncomputable section

open Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.MswTransference

/-- For a continuous `g`, the `r`-variation over `(0, 1]` is at most the `r`-variation over
`[0, 1)`: a chain in `(0, 1]` is the limit of the chains `(1 - ε) t_i` in `[0, 1)`. -/
theorem rVariationOn_Ioc_le_Ico {r : ℝ} {g : ℝ → ℂ} (hg : Continuous g) :
    rVariationOn r (Set.Ioc 0 1) g ≤ rVariationOn r (Set.Ico 0 1) g := by
  refine rVariationOn_le fun J t hm hS => ?_
  let u : ℝ → Fin (J + 1) → ℝ := fun ε j => (1 - ε) * t j
  let L : ℝ → ℝ≥0∞ := fun ε =>
    (∑ i : Fin J, ‖g (u ε i.castSucc) - g (u ε i.succ)‖ₑ ^ r) ^ (1 / r)
  have hbound : ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → L ε ≤ rVariationOn r (Set.Ico 0 1) g := by
    intro ε hε
    have hpos : 0 < 1 - ε := by linarith [hε.2]
    have hs : StrictMono (u ε) := fun j k hjk => by
      simp only [u]
      exact mul_lt_mul_of_pos_left (hm hjk) hpos
    refine le_rVariationOn (r := r) (S := Set.Ico 0 1) (a := g) hs fun j => ?_
    have h1 := hS j
    simp only [u]
    refine ⟨mul_nonneg hpos.le h1.1.le, ?_⟩
    nlinarith [h1.2, hε.1]
  have hcont : Continuous L := by
    refine ENNReal.continuous_rpow_const.comp (continuous_finsetSum _ fun i _ => ?_)
    refine ENNReal.continuous_rpow_const.comp ?_
    have hu : ∀ j : Fin (J + 1), Continuous fun ε : ℝ => u ε j := fun j => by
      simp only [u]
      fun_prop
    exact ((hg.comp (hu _)).sub (hg.comp (hu _))).enorm
  have hlim : Tendsto L (𝓝[>] 0) (𝓝 (L 0)) := (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have h0 : L 0 ≤ rVariationOn r (Set.Ico 0 1) g :=
    le_of_tendsto hlim (Filter.mem_of_superset (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1))
      fun ε hε => hbound ε hε)
  simpa [L, u] using h0

/-- **Reflection of the variation over `𝕋`**: for a continuous `1`-periodic `g`,
`V^r(λ ↦ g(-λ) : [0, 1)) ≤ V^r(g : [0, 1))`. -/
theorem rVariationOn_Ico_comp_neg_le {r : ℝ} {g : ℝ → ℂ} (hg : Continuous g)
    (hper : ∀ t, g (t + 1) = g t) :
    rVariationOn r (Set.Ico 0 1) (fun t => g (-t)) ≤ rVariationOn r (Set.Ico 0 1) g := by
  refine le_trans ?_ (rVariationOn_Ioc_le_Ico hg)
  refine rVariationOn_le fun J t hm hS => ?_
  let s : Fin (J + 1) → ℝ := fun j => 1 - t (Fin.rev j)
  have hs : StrictMono s := fun j k hjk => by
    simp only [s]
    have := hm (Fin.rev_lt_rev.2 hjk)
    linarith
  have hmem : ∀ j, s j ∈ Set.Ioc (0 : ℝ) 1 := fun j => by
    have h1 := hS (Fin.rev j)
    simp only [s]
    exact ⟨by linarith [h1.2], by linarith [h1.1]⟩
  have hneg : ∀ y, g (-y) = g (1 - y) := fun y => by
    rw [← hper (-y)]
    ring_nf
  have key := le_rVariationOn (r := r) (S := Set.Ioc 0 1) (a := g) hs hmem
  refine le_trans (le_of_eq ?_) key
  congr 1
  simp only [hneg]
  rw [← Equiv.sum_comp (Fin.revPerm (n := J))
    (fun i : Fin J => ‖g (s i.castSucc) - g (s i.succ)‖ₑ ^ r)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.revPerm_apply, Fin.rev_castSucc, Fin.rev_succ, s, Fin.rev_rev]
  rw [enorm_sub_rev]

/-- **The reflected piece of a two-sided modulated sum**: for `cp` carried by the finite set `S`,
`cm(n) = -cp(-n)` and `f̃(y) = f(-y)`,
`V^r(λ ↦ T^{cm}_λ f(x) : [0, 1)) ≤ V^r(λ ↦ T^{cp}_λ f̃(-x) : [0, 1))` (`0 < r`). -/
theorem rVariationOn_weightedModSum_cm_le {r : ℝ} (hr : 0 < r) (cp f : ℤ → ℂ) (S : Finset ℤ)
    (hS : ∀ n, n ∉ S → cp n = 0) (x : ℤ) :
    rVariationOn r (Set.Ico 0 1) (fun lam => weightedModSum (fun n => -(cp (-n))) f lam x) ≤
      rVariationOn r (Set.Ico 0 1) (fun lam => weightedModSum cp (fun y => f (-y)) lam (-x)) := by
  set g : ℝ → ℂ := fun mu => weightedModSum cp (fun y => f (-y)) mu (-x) with hg
  have hcont : Continuous g := continuous_weightedModSum cp (fun y => f (-y)) (-x) S hS
  have hper : ∀ t, g (t + 1) = g t := fun t => by
    have := weightedModSum_add_intCast cp (fun y => f (-y)) t 1 (-x)
    simpa [hg] using this
  have heq : (fun lam => weightedModSum (fun n => -(cp (-n))) f lam x) =
      (-1 : ℂ) • fun lam => g (-lam) := by
    funext lam
    simp [weightedModSum_cm_eq, hg]
  rw [heq, Common.rVariationOn_const_smul hr]
  simpa using rVariationOn_Ico_comp_neg_le (r := r) hcont hper

end PrimeCarleson.Proof.Paper
