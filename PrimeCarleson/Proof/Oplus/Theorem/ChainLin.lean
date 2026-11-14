module

public import PrimeCarleson.Proof.Oplus.Theorem.Chains
public import PrimeCarleson.Proof.Oplus.Theorem.Dual

/-!
# The chain supremum over a finite set `Ξ` is a linearized operator ([O+] L897-L921)

Source: [O+], L897–L903 (in the amended form used here), L897-L921: for a finite set `Ξ`, the
supremum `G^Ξ_{J+1}(x)` of `(∑_{l=1}^{J+1} |𝒮[f](ξ_l, x) - 𝒮[f](ξ_{l-1}, x)|^r)^{1/r}` over the
strictly increasing chains `ξ_0 < ⋯ < ξ_{J+1}` in `Ξ` equals `|𝒮'[f](x)|` for suitable linearizing
data (`exists_linearization_chainSup`): the first maximizing chain `x ↦ ξ(x)` is measurable (the
finitely many chains are compared through the continuous functions `x ↦ ‖incr‖_r`;
`exists_measurable_argmax`)
and `a_k` is the Hölder dual `dualCoeff`. If `Ξ` has no chain, `G^Ξ_{J+1} = 0`.

`lintegral_chainSup_le`: if the linearized bound `‖𝒮'[f]‖_p ≤ C‖f‖_p` holds for the linearizing
data with `Ξ` free of dyadic end points, then `G^Ξ_{J+1}` is measurable and
`∫ (G^Ξ_{J+1})^p ≤ (C ‖f‖_p)^p`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped FourierTransform SchwartzMap ENNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson PrimeCarleson.Proof.Common

/-- The increments `𝒮[f](t_{i+1}, x) - 𝒮[f](t_i, x)` of a chain with `J + 1` steps. -/
def incr (f : 𝓢(ℝ, ℂ)) {J : ℕ} (t : Fin (J + 1 + 1) → ℝ) (x : ℝ) : Fin (J + 1) → ℂ :=
  fun i => partialFourierIntegral f (t i.succ) x - partialFourierIntegral f (t i.castSucc) x

/-- `chainVar` is the `ℓ^r` norm of the increments, as an extended real. -/
theorem chainVar_eq_ofReal {r : ℝ} (hr : 0 < r) (f : 𝓢(ℝ, ℂ)) {J : ℕ} (t : Fin (J + 1 + 1) → ℝ)
    (x : ℝ) : chainVar r f t x = ENNReal.ofReal (lrNorm r (incr f t x)) := by
  unfold chainVar lrNorm incr
  have hX : 0 ≤ ∑ i : Fin (J + 1), ‖partialFourierIntegral f (t i.succ) x -
      partialFourierIntegral f (t i.castSucc) x‖ ^ r :=
    Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _
  rw [← ENNReal.ofReal_rpow_of_nonneg hX (by positivity),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [enorm_sub_rev, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr.le]

/-- Every strictly increasing chain in a finite set is one of finitely many, listed as `c`. -/
theorem exists_chain_enumeration (Ξ : Finset ℝ) (J : ℕ)
    (h : ∃ t : Fin (J + 1 + 1) → ℝ, StrictMono t ∧ ∀ i, t i ∈ Ξ) :
    ∃ (N : ℕ) (c : Fin (N + 1) → Fin (J + 1 + 1) → ℝ), (∀ j, StrictMono (c j)) ∧
      (∀ j i, c j i ∈ Ξ) ∧
      ∀ t : Fin (J + 1 + 1) → ℝ, StrictMono t → (∀ i, t i ∈ Ξ) → ∃ j, c j = t := by
  classical
  set Cset : Set (Fin (J + 1 + 1) → ℝ) := {t | StrictMono t ∧ ∀ i, t i ∈ Ξ} with hC
  have hfin : Cset.Finite := by
    refine (Set.Finite.pi (t := fun _ : Fin (J + 1 + 1) => (↑Ξ : Set ℝ))
      (fun _ => Ξ.finite_toSet)).subset ?_
    intro t ht i _
    exact Finset.mem_coe.2 (ht.2 i)
  have : Finite Cset := hfin.to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin Cset
  obtain ⟨t₀, ht₀⟩ := h
  have hn : n ≠ 0 := by
    rintro rfl
    exact (e ⟨t₀, ht₀⟩).elim0
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  refine ⟨N, fun j => (e.symm j).1, fun j => (e.symm j).2.1, fun j i => (e.symm j).2.2 i,
    fun t ht hS => ?_⟩
  exact ⟨e ⟨t, ht, hS⟩, by simp⟩

/-- `x ↦ ‖incr(x)‖_r` is continuous (continuity of `𝒮[f]`). -/
theorem continuous_lrNorm_incr {r : ℝ} (hr : 0 < r) (f : 𝓢(ℝ, ℂ)) {J : ℕ}
    (t : Fin (J + 1 + 1) → ℝ) : Continuous fun x => lrNorm r (incr f t x) := by
  unfold lrNorm incr
  have hS : ∀ ξ : ℝ, Continuous fun x : ℝ => partialFourierIntegral f ξ x := fun ξ =>
    (continuous_partialFourierIntegral_prod f).comp (continuous_const.prodMk continuous_id)
  refine Continuous.rpow_const (continuous_finsetSum _ fun i _ => ?_)
    (fun _ => Or.inr (by positivity))
  exact ((hS _).sub (hS _)).norm.rpow_const (fun _ => Or.inr hr.le)

/-- **The chain supremum over a finite set is a linearized operator** ([O+] L897-L921). -/
theorem exists_linearization_chainSup {r : ℝ} (hr : 2 < r) (f : 𝓢(ℝ, ℂ)) (Ξ : Finset ℝ) (J : ℕ) :
    (∀ x, chainSup r f (J + 1) (↑Ξ : Set ℝ) x = 0) ∨
      ∃ L : Linearization r, L.Ξ = Ξ ∧
        ∀ x, chainSup r f (J + 1) (↑Ξ : Set ℝ) x = ‖L.op f x‖ₑ := by
  have hr0 : 0 < r := by linarith
  by_cases h : ∃ t : Fin (J + 1 + 1) → ℝ, StrictMono t ∧ ∀ i, t i ∈ Ξ
  swap
  · left
    intro x
    refine le_antisymm (iSup_le fun t => iSup_le fun ht => iSup_le fun hS => ?_) bot_le
    exact absurd ⟨t, ht, fun i => Finset.mem_coe.1 (hS i)⟩ h
  right
  obtain ⟨N, c, hc1, hc2, hc3⟩ := exists_chain_enumeration Ξ J h
  obtain ⟨s, hs_max, hs_meas⟩ := exists_measurable_argmax
    (fun (j : Fin (N + 1)) x => lrNorm r (incr f (c j) x))
    (fun j => (continuous_lrNorm_incr hr0 f (c j)).measurable)
  -- the data
  set D : ℝ → Fin (J + 1) → ℂ := fun x => incr f (c (s x)) x with hD
  have hS : Continuous fun p : ℝ × ℝ => partialFourierIntegral f p.1 p.2 :=
    continuous_partialFourierIntegral_prod f
  have hDmeas : ∀ i, Measurable fun x => D x i := by
    intro i
    refine Measurable.sub ?_ ?_
    · exact hS.measurable.comp ((hs_meas fun j => c j i.succ).prodMk measurable_id)
    · exact hS.measurable.comp ((hs_meas fun j => c j i.castSucc).prodMk measurable_id)
  have hNmeas : Measurable fun x => lrNorm r (D x) := by
    unfold lrNorm
    refine Measurable.pow_const (Finset.measurable_sum _ fun i _ => ?_) _
    exact (hDmeas i).norm.pow_const _
  have hamea : ∀ k : Fin (J + 1), Measurable fun x => dualCoeff r (D x) k := by
    intro k
    unfold dualCoeff
    refine Measurable.ite (hNmeas (measurableSet_singleton (0 : ℝ))) measurable_const ?_
    refine Measurable.mul (Measurable.mul ?_ ?_) ?_
    · exact Complex.continuous_conj.measurable.comp (hDmeas k)
    · exact Complex.measurable_ofReal.comp ((hDmeas k).norm.pow_const _)
    · exact Complex.measurable_ofReal.comp (hNmeas.pow_const _)
  set L : Linearization r :=
    { K := J + 1
      Ξ := Ξ
      ξ := fun k x => c (s x) k
      a := fun k x => dualCoeff r (D x) k
      measurable_ξ := fun k => hs_meas fun j => c j k
      strictMono_ξ := fun x => hc1 (s x)
      ξ_mem := fun k x => hc2 (s x) k
      measurable_a := hamea
      sum_norm_rpow := fun x => sum_norm_dualCoeff_rpow hr (D x) } with hL
  refine ⟨L, rfl, fun x => ?_⟩
  have hopf : L.op f x = (lrNorm r (D x) : ℂ) := sum_mul_dualCoeff hr (D x)
  rw [hopf, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (lrNorm_nonneg r (D x))]
  refine le_antisymm (iSup_le fun t => iSup_le fun ht => iSup_le fun hSt => ?_) ?_
  · obtain ⟨j, rfl⟩ := hc3 t ht (fun i => Finset.mem_coe.1 (hSt i))
    rw [chainVar_eq_ofReal hr0]
    exact ENNReal.ofReal_le_ofReal (hs_max x j)
  · have := le_chainSup r f (hc1 (s x)) (fun i => Finset.mem_coe.2 (hc2 (s x) i)) x
    rwa [chainVar_eq_ofReal hr0] at this

end PrimeCarleson.Proof.Oplus
