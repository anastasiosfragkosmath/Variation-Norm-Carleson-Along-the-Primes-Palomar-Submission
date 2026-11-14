module

public import PrimeCarleson.Proof.Oplus.TreeSmall.DensityBound

/-!
# The tree sum, the Hölder bound (csvar) and the `L²` norm of a tree sum ([O+] L2258-L2442)

[O+]:

* `treeSum ch f L E T x = ∑_{P ∈ T} ⟨f, φ_P⟩ φ_P(x) a_P(x) 1_E(x)`, the sum estimated by the
  proposition `treeestimate` ([O+] L2031-L2044);
* `csvar` (Source: [O+] `csvar`, L2258–L2274, display `(csvar)` L2260-L2272): for every `x`,
  `|∑_{P ∈ T : |I| ≥ C''|J|} ⟨f, φ_P⟩ φ_P(x) a_P(x)| ≤
  (∑_{k : ξ_{k-1}(x) ∈ Ω_J} |a_k(x)|^{r'})^{1/r'}
  (∑_{k : ξ_{k-1}(x) ∈ Ω_J} |∑_{P ∈ T : |I| ≥ C''|J|, ξ_{k-1}(x) ∈ ω_l, ξ_k(x) ∈ ω_h}
  ⟨f, φ_P⟩ φ_P(x)|^r)^{1/r}`, Hölder's inequality in the index `k` after regrouping the sum over
  `P` by the index `k` of `a_P(x) = a_k(x)`. It holds for every finite family of multitiles (no
  tree hypothesis);
* `tailSum_eq_ofReal` converts the `ℝ≥0∞`-valued tail sum into the real sum over the `k` with
  `ξ_{k-1}(x) ∈ Ω`;
* `l2_norm_tree_sum` (Source: [O+] `treeestimatelargeintervals`, L2426–L2442):
  `‖∑_{P ∈ T} ⟨f, φ_P⟩ φ_P‖²_{L²} ≲ ∑_{P ∈ T} |⟨f, φ_P⟩|² ≤ ene² |I_T|` for an
  `l`-overlapping tree `T` with energy at most `ene` (the first inequality is the orthogonality
  of `Estimates/UnivBound.lean`, the second the definition of the energy).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- The tree sum `∑_{P ∈ T} ⟨f, φ_P⟩ φ_P(x) a_P(x) 1_E(x)` (L2031-L2037). -/
def treeSum {ρ : Idx} {r : ℝ} (ch : ProfileChoice) (f : ℝ → ℂ) (L : Linearization r)
    (E : Set ℝ) (T : Finset (Multitile ρ)) (x : ℝ) : ℂ :=
  ∑ P ∈ T, P.coeff ch f * P.wavePacket ch x * P.aP L x * E.indicator (fun _ => (1 : ℂ)) x

section Csvar

variable {ρ : Idx}

/-- `‖a‖ₑ^p = ofReal(‖a‖^p)` for `p ≥ 0`. -/
theorem enorm_rpow_eq_ofReal {a : ℂ} {p : ℝ} (hp : 0 ≤ p) :
    ‖a‖ₑ ^ p = ENNReal.ofReal (‖a‖ ^ p) := by
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg a) hp, ofReal_norm]

open Classical in
/-- The tail sum is the (real) sum of `|a_k(x)|^{r'}` over the `k` with `ξ_{k-1}(x) ∈ Ω`. -/
theorem Linearization.tailSum_eq_ofReal {r : ℝ} (hr : 1 < r) (L : Linearization r) (Ω : Set ℝ)
    (x : ℝ) : L.tailSum Ω x = ENNReal.ofReal (∑ k ∈ Finset.univ.filter
      (fun k : Fin L.K => L.ξ k.castSucc x ∈ Ω), ‖L.a k x‖ ^ Real.conjExponent r) := by
  have hr' : 0 ≤ Real.conjExponent r := by
    unfold Real.conjExponent
    exact (div_pos (by linarith) (by linarith)).le
  unfold Linearization.tailSum
  rw [Finset.sum_filter, ENNReal.ofReal_sum_of_nonneg (fun k _ => by split_ifs <;> positivity)]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : L.ξ k.castSucc x ∈ Ω
  · simp only [h, Set.indicator_of_mem, mul_one, ite_true]
    exact enorm_rpow_eq_ofReal hr'
  · simp [h]

open Classical in
/-- Regrouping the sum over `P` by the index `k` of `a_P(x) = a_k(x)` (L2261-L2265). -/
theorem sum_mul_aP_eq {r : ℝ} (ch : ProfileChoice) (f : ℝ → ℂ) (L : Linearization r)
    (x : ℝ) (T' : Finset (Multitile ρ)) :
    ∑ P ∈ T', P.coeff ch f * P.wavePacket ch x * P.aP L x =
      ∑ k : Fin L.K, L.a k x * ∑ P ∈ T'.filter (fun P =>
        L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh), P.coeff ch f * P.wavePacket ch x := by
  simp only [Multitile.aP, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun P _ => ?_
  split_ifs <;> simp [mul_comm]

open Classical in
/-- **`csvar`** ([O+] L2258-L2274): Hölder's inequality in the index `k`. For every finite family
`𝒯.T` of multitiles, every `x`, `C` and `J`, with `Ω_J = ⋃_{P ∈ T : |I| ≥ C|J|} ω_l`,
`|∑_{P : |I| ≥ C|J|} ⟨f, φ_P⟩ φ_P(x) a_P(x)| ≤
(∑_{k : ξ_{k-1}(x) ∈ Ω_J} |a_k(x)|^{r'})^{1/r'}
(∑_{k : ξ_{k-1}(x) ∈ Ω_J}
|∑_{P : |I| ≥ C|J|, ξ_{k-1}(x) ∈ ω_l, ξ_k(x) ∈ ω_h} ⟨f, φ_P⟩ φ_P(x)|^r)^{1/r}`. -/
theorem csvar {r : ℝ} (hr : 1 < r) (ch : ProfileChoice) (f : ℝ → ℂ) (L : Linearization r)
    (𝒯 : MultitileTree ρ) (C : ℝ) (J : Dyadic) (x : ℝ) :
    ‖∑ P ∈ 𝒯.T.filter (fun P => C * J.length ≤ P.I.length),
        P.coeff ch f * P.wavePacket ch x * P.aP L x‖ ≤
      (∑ k ∈ Finset.univ.filter (fun k : Fin L.K => L.ξ k.castSucc x ∈ 𝒯.OmegaJ C J),
          ‖L.a k x‖ ^ Real.conjExponent r) ^ (1 / Real.conjExponent r) *
      (∑ k ∈ Finset.univ.filter (fun k : Fin L.K => L.ξ k.castSucc x ∈ 𝒯.OmegaJ C J),
          ‖∑ P ∈ 𝒯.T.filter (fun P => C * J.length ≤ P.I.length ∧
              L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh),
            P.coeff ch f * P.wavePacket ch x‖ ^ r) ^ (1 / r) := by
  -- only the `k` with `ξ_{k-1}(x) ∈ Ω_J` contribute
  have hrestr : ∑ k : Fin L.K, L.a k x * ∑ P ∈
        (𝒯.T.filter (fun P => C * J.length ≤ P.I.length)).filter
        (fun P => L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh),
          P.coeff ch f * P.wavePacket ch x =
      ∑ k ∈ Finset.univ.filter (fun k : Fin L.K => L.ξ k.castSucc x ∈ 𝒯.OmegaJ C J),
        L.a k x * ∑ P ∈ (𝒯.T.filter (fun P => C * J.length ≤ P.I.length)).filter
          (fun P => L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh),
            P.coeff ch f * P.wavePacket ch x := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun k _ hk => ?_
    have hempty : (𝒯.T.filter (fun P => C * J.length ≤ P.I.length)).filter
        (fun P => L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun P hP hcond => ?_
      have hPm := Finset.mem_filter.1 hP
      exact hk (Finset.mem_filter.2 ⟨Finset.mem_univ _, P, hPm.1, hPm.2, hcond.1⟩)
    rw [hempty]
    simp
  have hfilt : ∀ k : Fin L.K, (𝒯.T.filter (fun P => C * J.length ≤ P.I.length)).filter
      (fun P => L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh) =
      𝒯.T.filter (fun P => C * J.length ≤ P.I.length ∧
        L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh) := by
    intro k
    rw [Finset.filter_filter]
  rw [sum_mul_aP_eq, hrestr]
  simp only [hfilt]
  -- Hölder
  set K' : Finset (Fin L.K) :=
    Finset.univ.filter (fun k : Fin L.K => L.ξ k.castSucc x ∈ 𝒯.OmegaJ C J) with hK'
  have hH := Real.HolderConjugate.conjExponent hr
  calc ‖∑ k ∈ K', L.a k x * ∑ P ∈ 𝒯.T.filter (fun P => C * J.length ≤ P.I.length ∧
          L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh), P.coeff ch f * P.wavePacket ch x‖
      ≤ ∑ k ∈ K', ‖L.a k x‖ * ‖∑ P ∈ 𝒯.T.filter (fun P => C * J.length ≤ P.I.length ∧
          L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh), P.coeff ch f * P.wavePacket ch x‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [norm_mul]
    _ ≤ _ := Real.inner_le_Lp_mul_Lq_of_nonneg K' hH.symm
          (fun k _ => norm_nonneg _) (fun k _ => norm_nonneg _)

end Csvar

section L2

variable {ρ : Idx} [Fact ρ.IsOneOrTwo]

/-- **`treeestimatelargeintervals`** ([O+] L2426-L2442). There is a constant
`K` such that for every `l`-overlapping tree `T ⊂ S` of `ρ`-multitiles satisfying the separation
assumptions, with `energy(S) ≤ ene`:
`‖∑_{P ∈ T} ⟨f, φ_P⟩ φ_P‖²_{L²} ≤ K ∑_{P ∈ T} |⟨f, φ_P⟩|² ≤ K ene² |I_T|`. -/
theorem l2_norm_tree_sum :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ},
      AdmissibleConstants C₁ C₂ C₃ → ρ.IsStd → ∀ (ch : ProfileChoice) (f : ℝ → ℂ)
      {S : Set (Multitile ρ)} {ene : ℝ}, 0 ≤ ene →
      energy C₁ C₂ M ch f S ≤ ENNReal.ofReal ene → ∀ (𝒯 : MultitileTree ρ),
      𝒯.IsTree C₁ C₂ M → 𝒯.IsOverlapping C₂ → Separated C₁ C₂ C₃ (𝒯.T : Set (Multitile ρ)) →
      (𝒯.T : Set (Multitile ρ)) ⊆ S →
        ∫ x, ‖∑ P ∈ 𝒯.T, P.coeff ch f • P.wavePacket ch x‖ ^ 2 ≤
            K * ∑ P ∈ 𝒯.T, ‖P.coeff ch f‖ ^ 2 ∧
          ∑ P ∈ 𝒯.T, ‖P.coeff ch f‖ ^ 2 ≤ ene ^ 2 * 𝒯.I.length ∧
          ∫ x, ‖∑ P ∈ 𝒯.T, P.coeff ch f • P.wavePacket ch x‖ ^ 2 ≤ K * (ene ^ 2 * 𝒯.I.length) := by
  obtain ⟨K, hK0, hK⟩ := exists_tree_orthogonality_coeff
  refine ⟨K, hK0, fun {ρ} _ {C₁ C₂ C₃} {M} hC hρ ch f {S} {ene} hene hen 𝒯 hT hov hsep hsub => ?_⟩
  have h1 := hK hC hρ ch 𝒯 hT hov hsep f
  have h2 := sum_norm_sq_coeff_le_of_energy_le hene hen hT hov hsub
  exact ⟨h1, h2, h1.trans (mul_le_mul_of_nonneg_left h2 hK0)⟩

end L2

end PrimeCarleson.Proof.Oplus
