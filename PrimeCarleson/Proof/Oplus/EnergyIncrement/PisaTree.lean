module

public import PrimeCarleson.Proof.Oplus.EnergyIncrement.PisaThird

/-!
# `threeterms` and `pisatree` ([O+] L1438-L1445, L1799-L1895)

Source: [O+] `threeterms`, L1807–L1809; [O+] `pisatree`, L1438–L1445 (L1799-L1895): "For each
`T ∈ 𝒯` let `S ≡ S(T)` be the corresponding `l`-overlapping tree from the
selection algorithm and recall `∑_{T ∈ 𝒯} |I_T| (e/2)² ≤ ∑_{P ∈ ⋃_{T ∈ 𝒯} S} |⟨f, φ_P⟩|²`. Since
`𝔓 = ⋃_{T' ∈ 𝒯'} T'`, the right side above is dominated by (threeterms) [the three sums over the
multitiles of `T' ∩ ⋃ S` with `ξ_{T'} ∈ C₂ ω_l`, `ξ_{T'} ≥ inf C₃ ω_u`, `sup C₂ ω_l ≤ ξ_{T'} <
inf C₃ ω_u`]". The three sums are bounded by `e² |I_{T'}|`, `e² |I_{T'}|`, `2 e² |I_{T'}|`
(`pisatree_first_term`, `pisatree_second_term`, `pisatree_third_term`), so
`(e/2)² ∑_T |I_T| ≤ 4 e² ∑_{T'} |I_{T'}|`: `∑_T |I_T| ≤ 16 ∑_{T'} |I_{T'}|` (`pisatree`).
The hypotheses are `C₂ = 2` (L1875) and that the cover consists of trees (so `ξ_{T'} ∈ ω_m(P)`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

section PisaTree

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ} {ch : ProfileChoice} {f : ℝ → ℂ}
  {e : ℝ} {𝔓 : Finset (Multitile ρ)} {n : ℕ} {S T : ℕ → MultitileTree ρ}

open Classical in
/-- **`threeterms`** ([O+] L1801-L1809): `∑_j |I_{S_j}| (e/2)² ≤ ∑_{P ∈ U} |⟨f, φ_P⟩|² ≤
∑_{T'} (∑_{P ∈ T' ∩ U, ξ_{T'} ∈ C₂ ω_l} + ∑_{P ∈ T' ∩ U, ξ_{T'} ≥ inf C₃ ω_u} +
∑_{P ∈ T' ∩ U, sup C₂ ω_l ≤ ξ_{T'} < inf C₃ ω_u}) |⟨f, φ_P⟩|²`, `U = ⋃_j S_j`, for every cover
`𝔓 ⊂ ⋃_{T' ∈ 𝒯'} T'` by trees. -/
theorem threeterms (hC : AdmissibleConstants C₁ C₂ C₃)
    (sel : IsSelection C₁ C₂ M ch f e 𝔓 n S T) (𝒯' : Finset (MultitileTree ρ))
    (hT' : ∀ T' ∈ 𝒯', T'.IsTree C₁ C₂ M)
    (hcov : (𝔓 : Set (Multitile ρ)) ⊆ ⋃ T' ∈ 𝒯', (T'.T : Set (Multitile ρ))) :
    e ^ 2 / 4 * ∑ j ∈ Finset.range n, (S j).I.length ≤
        ∑ P ∈ (Finset.range n).biUnion (fun j => (S j).T), ‖P.coeff ch f‖ ^ 2 ∧
      ∑ P ∈ (Finset.range n).biUnion (fun j => (S j).T), ‖P.coeff ch f‖ ^ 2 ≤
        ∑ T' ∈ 𝒯',
          (∑ P ∈ T'.T.filter (fun P => P ∈ (Finset.range n).biUnion (fun j => (S j).T) ∧
              Multitile.Case1 C₂ T'.ξ P), ‖P.coeff ch f‖ ^ 2 +
            ∑ P ∈ T'.T.filter (fun P => P ∈ (Finset.range n).biUnion (fun j => (S j).T) ∧
              Multitile.Case2 C₃ T'.ξ P), ‖P.coeff ch f‖ ^ 2 +
            ∑ P ∈ T'.T.filter (fun P => P ∈ (Finset.range n).biUnion (fun j => (S j).T) ∧
              Multitile.Case3 C₂ C₃ T'.ξ P), ‖P.coeff ch f‖ ^ 2) := by
  have hC₂ : 0 < C₂ := by linarith [hC.one_le, hC.lt₁]
  have hC₂1 : 1 < C₂ := lt_of_le_of_lt hC.one_le hC.lt₁
  set U := (Finset.range n).biUnion (fun j => (S j).T) with hU
  have hdisj : (↑(Finset.range n) : Set ℕ).PairwiseDisjoint (fun j => (S j).T) :=
    fun j hj k hk hne => sel.disjoint_range j (Finset.mem_range.1 hj) k (Finset.mem_range.1 hk) hne
  refine ⟨?_, ?_⟩
  · rw [hU, Finset.sum_biUnion hdisj, Finset.mul_sum]
    exact Finset.sum_le_sum fun j hj => (sel.large j (Finset.mem_range.1 hj)).large
  · have hUsub : ∀ P ∈ U, P ∈ 𝔓 := by
      intro P hP
      obtain ⟨j, hj, hPj⟩ := Finset.mem_biUnion.1 hP
      exact sel.mem_of_mem_S (Finset.mem_range.1 hj) hPj
    -- each `P ∈ U` lies in some `T'`
    calc ∑ P ∈ U, ‖P.coeff ch f‖ ^ 2
        ≤ ∑ P ∈ U, ∑ T' ∈ 𝒯', (if P ∈ T'.T then ‖P.coeff ch f‖ ^ 2 else 0) := by
          refine Finset.sum_le_sum fun P hP => ?_
          have := hcov (Finset.mem_coe.2 (hUsub P hP))
          obtain ⟨T', hT'mem, hPT'⟩ := Set.mem_iUnion₂.1 this
          have := Finset.single_le_sum (f := fun T' : MultitileTree ρ =>
            if P ∈ T'.T then ‖P.coeff ch f‖ ^ 2 else 0) (s := 𝒯')
            (fun T' _ => by split_ifs <;> positivity) hT'mem
          simpa [Finset.mem_coe.1 hPT'] using this
      _ = ∑ T' ∈ 𝒯', ∑ P ∈ U, (if P ∈ T'.T then ‖P.coeff ch f‖ ^ 2 else 0) :=
          Finset.sum_comm
      _ ≤ _ := by
          refine Finset.sum_le_sum fun T' hT'mem => ?_
          set Z := U.filter (fun P => P ∈ T'.T) with hZdef
          have hZ : ∀ (Q : Multitile ρ → Prop) [DecidablePred Q],
              T'.T.filter (fun P => P ∈ U ∧ Q P) = Z.filter Q := by
            intro Q _
            ext P
            simp only [Finset.mem_filter, hZdef]
            tauto
          rw [hZ, hZ, hZ]
          calc ∑ P ∈ U, (if P ∈ T'.T then ‖P.coeff ch f‖ ^ 2 else 0)
              = ∑ P ∈ Z, ‖P.coeff ch f‖ ^ 2 := (Finset.sum_filter _ _).symm
            _ ≤ ∑ P ∈ Z, ((if Multitile.Case1 C₂ T'.ξ P then ‖P.coeff ch f‖ ^ 2 else 0) +
                  (if Multitile.Case2 C₃ T'.ξ P then ‖P.coeff ch f‖ ^ 2 else 0) +
                  (if Multitile.Case3 C₂ C₃ T'.ξ P then ‖P.coeff ch f‖ ^ 2 else 0)) := by
                refine Finset.sum_le_sum fun P hP => ?_
                have hPT : P ∈ T'.T := (Finset.mem_filter.1 hP).2
                have hξ := (hT' T' hT'mem).freq P hPT (T'.mem_ωT_self hC₂1)
                have h1 : 0 ≤ ‖P.coeff ch f‖ ^ 2 := by positivity
                rcases case_cover hC₂ (C₃ := C₃) hξ with h | h | h
                · have : (if Multitile.Case1 C₂ T'.ξ P then ‖P.coeff ch f‖ ^ 2 else 0) =
                      ‖P.coeff ch f‖ ^ 2 := by simp [h]
                  have h2 : 0 ≤ (if Multitile.Case2 C₃ T'.ξ P then ‖P.coeff ch f‖ ^ 2 else 0) := by
                    split_ifs <;> simp [h1]
                  have h3 : 0 ≤ (if Multitile.Case3 C₂ C₃ T'.ξ P then ‖P.coeff ch f‖ ^ 2
                      else 0) := by split_ifs <;> simp [h1]
                  linarith
                · have : (if Multitile.Case2 C₃ T'.ξ P then ‖P.coeff ch f‖ ^ 2 else 0) =
                      ‖P.coeff ch f‖ ^ 2 := by simp [h]
                  have h2 : 0 ≤ (if Multitile.Case1 C₂ T'.ξ P then ‖P.coeff ch f‖ ^ 2 else 0) := by
                    split_ifs <;> simp [h1]
                  have h3 : 0 ≤ (if Multitile.Case3 C₂ C₃ T'.ξ P then ‖P.coeff ch f‖ ^ 2
                      else 0) := by split_ifs <;> simp [h1]
                  linarith
                · have : (if Multitile.Case3 C₂ C₃ T'.ξ P then ‖P.coeff ch f‖ ^ 2 else 0) =
                      ‖P.coeff ch f‖ ^ 2 := by simp [h]
                  have h2 : 0 ≤ (if Multitile.Case1 C₂ T'.ξ P then ‖P.coeff ch f‖ ^ 2 else 0) := by
                    split_ifs <;> simp [h1]
                  have h3 : 0 ≤ (if Multitile.Case2 C₃ T'.ξ P then ‖P.coeff ch f‖ ^ 2
                      else 0) := by split_ifs <;> simp [h1]
                  linarith
            _ = ∑ P ∈ Z.filter (Multitile.Case1 C₂ T'.ξ), ‖P.coeff ch f‖ ^ 2 +
                  ∑ P ∈ Z.filter (Multitile.Case2 C₃ T'.ξ), ‖P.coeff ch f‖ ^ 2 +
                  ∑ P ∈ Z.filter (Multitile.Case3 C₂ C₃ T'.ξ), ‖P.coeff ch f‖ ^ 2 := by
                rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
                exact congrArg₂ (· + ·) (congrArg₂ (· + ·) (Finset.sum_filter _ _).symm
                  (Finset.sum_filter _ _).symm) (Finset.sum_filter _ _).symm

open Classical in
/-- **`pisatree`** ([O+] L1438-L1445, L1799-L1895): if `𝔓 ⊂ ⋃_{T' ∈ 𝒯'} T'` for trees `T' ⊂ 𝔓`
(`C₂ = 2`, `𝔓` in the square `[-2^M, 2^M]²`, `energy(𝔓) ≤ e`), then
`∑_{j < n} |I_{S_j}| ≤ 16 ∑_{T' ∈ 𝒯'} |I_{T'}|`. -/
theorem pisatree_sum (hC : AdmissibleConstants C₁ C₂ C₃) (hC₂ : C₂ = 2) (hρ : ρ.IsStd)
    (hsep : Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ))) (hsq : ∀ P ∈ 𝔓, P.InSquare M)
    (he : 0 < e) (hen : energy C₁ C₂ M ch f (𝔓 : Set (Multitile ρ)) ≤ ENNReal.ofReal e)
    (sel : IsSelection C₁ C₂ M ch f e 𝔓 n S T) (𝒯' : Finset (MultitileTree ρ))
    (hT' : ∀ T' ∈ 𝒯', T'.IsTree C₁ C₂ M) (hsub : ∀ T' ∈ 𝒯', (T'.T : Set (Multitile ρ)) ⊆ 𝔓)
    (hcov : (𝔓 : Set (Multitile ρ)) ⊆ ⋃ T' ∈ 𝒯', (T'.T : Set (Multitile ρ))) :
    ∑ j ∈ Finset.range n, (S j).I.length ≤ 16 * ∑ T' ∈ 𝒯', T'.I.length := by
  obtain ⟨h1, h2⟩ := threeterms hC sel 𝒯' hT' hcov
  have h3 : ∑ P ∈ (Finset.range n).biUnion (fun j => (S j).T), ‖P.coeff ch f‖ ^ 2 ≤
      ∑ T' ∈ 𝒯', 4 * (e ^ 2 * T'.I.length) := by
    refine h2.trans (Finset.sum_le_sum fun T' hT'mem => ?_)
    have a1 := pisatree_first_term (U := (Finset.range n).biUnion (fun j => (S j).T)) he.le hen
      (hT' T' hT'mem) (hsub T' hT'mem)
    have a2 := pisatree_second_term hC hC₂ hρ hsep hsq he.le hen sel (hT' T' hT'mem)
      (hsub T' hT'mem)
    have a3 := pisatree_third_term hC hC₂ hρ hsep hsq he.le hen sel (hT' T' hT'mem)
      (hsub T' hT'mem)
    linarith
  have he2 : 0 < e ^ 2 := by positivity
  have h4 : e ^ 2 / 4 * ∑ j ∈ Finset.range n, (S j).I.length ≤
      e ^ 2 / 4 * (16 * ∑ T' ∈ 𝒯', T'.I.length) := by
    calc e ^ 2 / 4 * ∑ j ∈ Finset.range n, (S j).I.length ≤ _ := h1
      _ ≤ _ := h3
      _ = e ^ 2 / 4 * (16 * ∑ T' ∈ 𝒯', T'.I.length) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]; ring
  exact le_of_mul_le_mul_left h4 (by positivity)

end PisaTree

end PrimeCarleson.Proof.Oplus
