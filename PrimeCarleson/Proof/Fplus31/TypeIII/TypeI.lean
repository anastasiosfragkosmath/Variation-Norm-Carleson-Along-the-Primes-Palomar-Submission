module

public import PrimeCarleson.Proof.Fplus31.TypeIII.Reindex
public import PrimeCarleson.Proof.Fplus31.TypeIII.Blocks

/-!
# Type I correlation: many `ℓ` with a large dilated sum (Leng23 Proposition 5.1, first bullet)

Part of the Vaughan decomposition in the proof of [F+] Proposition 3.1 (Leng23
`p:type1type2correlation`, `Final_Version.tex` L1096-L1104; the hypothesis `hI` of the type I step).
If a type I sum `∑_{d ≤ D} a_d ∑_{n ≤ N', d ∣ n} f(n)` with bounded coefficients `|a_d| ≤ A`
correlates with a bounded function `f` at the level `ξ`, then for one dyadic block `(L/2, L]`,
`L ≤ D`, at least `δ L` values `ℓ` have `‖∑_{n ≤ N', ℓ ∣ n} f n‖ ≥ δ N/L`, with
`δ = ξ / (4 N A (⌊log₂ D⌋ + 1))`.

No Cauchy–Schwarz is needed here: the type I coefficients of Vaughan's identity are bounded by
`O(log N)` (not merely divisor-bounded), so the triangle inequality, the trivial bound
`|∑_{n ≤ N', ℓ ∣ n} f n| ≤ N/ℓ` and a pigeonhole over the dyadic blocks suffice.

* `typeI_extract`: the statement above.
-/

@[expose] public noncomputable section

open Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- **Type I extraction** (Leng23 Proposition 5.1, first bullet). -/
theorem typeI_extract (f : ℕ → ℂ) (N D : ℕ) (hD : 1 ≤ D) (hDN : D ^ 3 ≤ N ^ 2)
    (hf : ∀ n ∈ Icc 1 N, ‖f n‖ ≤ 1) (a : ℕ → ℂ) {A : ℝ} (hA0 : 0 < A)
    (hA : ∀ d ∈ Icc 1 D, ‖a d‖ ≤ A) {N' : ℕ} (hN' : N' ≤ N) {ξ : ℝ} (hξ : 0 < ξ)
    (h : ξ ≤ ‖∑ d ∈ Icc 1 D, a d * dvdSum f d N'‖) :
    ∃ L : ℕ, 1 ≤ L ∧ L ≤ D ∧ ∃ Ls : Finset ℕ, Ls ⊆ dyadicBlock L ∧
      ξ / (4 * N * A * ((Nat.log 2 D + 1 : ℕ) : ℝ)) * L ≤ Ls.card ∧
      ∀ ℓ ∈ Ls, ξ / (4 * N * A * ((Nat.log 2 D + 1 : ℕ) : ℝ)) * (N / L) ≤ ‖dvdSum f ℓ N'‖ := by
  have hN1 : 1 ≤ N := by
    by_contra hN0
    have : N = 0 := by omega
    subst this
    have : 1 ≤ D ^ 3 := Nat.one_le_pow _ _ hD
    simp at hDN
    omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  set J : ℝ := ((Nat.log 2 D + 1 : ℕ) : ℝ) with hJ
  have hJpos : 0 < J := by positivity
  set g : ℕ → ℝ := fun d => ‖dvdSum f d N'‖ with hg
  have hfN' : ∀ n ∈ Icc 1 N', ‖f n‖ ≤ 1 := fun n hn =>
    hf n (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans hN'⟩)
  have hgle : ∀ d, g d ≤ (N : ℝ) / d := fun d =>
    (norm_dvdSum_le f d N' hfN').trans (div_le_div_of_nonneg_right (by exact_mod_cast hN') (by
      positivity))
  -- the weighted sum
  have h1 : ξ / A ≤ ∑ d ∈ Icc 1 D, g d := by
    rw [div_le_iff₀ hA0]
    calc ξ ≤ ‖∑ d ∈ Icc 1 D, a d * dvdSum f d N'‖ := h
      _ ≤ ∑ d ∈ Icc 1 D, ‖a d * dvdSum f d N'‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ Icc 1 D, A * g d := by
          refine Finset.sum_le_sum fun d hd => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hA d hd) (norm_nonneg _)
      _ = (∑ d ∈ Icc 1 D, g d) * A := by rw [← Finset.mul_sum, mul_comm]
  obtain ⟨i, hiJ, hi⟩ := exists_block_sum_ge D g h1
  set L := blockTop D i with hL
  set Bl := blockSet D i with hBl
  set ξ' : ℝ := ξ / A / J with hξ'
  have hξ'pos : 0 < ξ' := by positivity
  have hdy : Bl ⊆ dyadicBlock L := blockSet_subset_dyadic D i
  -- nonempty block
  have hne : Bl.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Finset.sum_empty] at hi
    linarith
  obtain ⟨d₀, hd₀⟩ := hne
  have hL1 : 1 ≤ L := by
    have h1' := (Finset.mem_Icc.mp (blockSet_subset D i hd₀)).1
    have h2' := mem_dyadicBlock.mp (hdy hd₀)
    have : (d₀ : ℝ) ≤ L := h2'.2
    have : d₀ ≤ L := by exact_mod_cast this
    omega
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
  refine ⟨L, hL1, blockTop_le D i, ?_⟩
  set thr : ℝ := ξ' / (2 * L) with hthr
  set Ls := Bl.filter (fun d => thr ≤ g d) with hLs
  refine ⟨Ls, (Finset.filter_subset _ _).trans hdy, ?_, ?_⟩
  · -- counting
    have hcardBl : (Bl.card : ℝ) ≤ L := by
      exact_mod_cast (Finset.card_le_card hdy).trans (card_dyadicBlock_le L)
    have hsplit := Finset.sum_filter_add_sum_filter_not Bl (fun d => thr ≤ g d) g
    have hsmall : ∑ d ∈ Bl.filter (fun d => ¬ thr ≤ g d), g d ≤ ξ' / 2 := by
      calc ∑ d ∈ Bl.filter (fun d => ¬ thr ≤ g d), g d
          ≤ ∑ _d ∈ Bl.filter (fun d => ¬ thr ≤ g d), thr := by
            refine Finset.sum_le_sum fun d hd => ?_
            exact (not_le.mp (Finset.mem_filter.mp hd).2).le
        _ ≤ ∑ _d ∈ Bl, thr := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun _ _ _ => by positivity
        _ = Bl.card * thr := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ L * thr := mul_le_mul_of_nonneg_right hcardBl (by positivity)
        _ = ξ' / 2 := by rw [hthr]; field_simp
    have hbig : ξ' / 2 ≤ ∑ d ∈ Ls, g d := by linarith
    have hLsle : ∑ d ∈ Ls, g d ≤ Ls.card * (2 * N / L) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun d hd => ?_
      have hdBl : d ∈ Bl := (Finset.mem_filter.mp hd).1
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (blockSet_subset D i hdBl)).1
      have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
      have hdL : (L : ℝ) / 2 < d := (mem_dyadicBlock.mp (hdy hdBl)).1
      calc g d ≤ (N : ℝ) / d := hgle d
        _ ≤ 2 * N / L := by
            rw [div_le_div_iff₀ hdpos hLpos]
            nlinarith
    have : ξ' / 2 ≤ Ls.card * (2 * N / L) := hbig.trans hLsle
    have e : ξ / (4 * N * A * J) * L = (ξ' / 2) / (2 * N / L) := by
      rw [hξ']
      field_simp
      ring
    rw [e, div_le_iff₀ (by positivity)]
    exact this
  · intro ℓ hℓ
    have hge : thr ≤ g ℓ := (Finset.mem_filter.mp hℓ).2
    calc ξ / (4 * N * A * J) * (N / L) = ξ / (4 * A * J * L) := by
          field_simp
      _ ≤ ξ / (2 * A * J * L) :=
          div_le_div_of_nonneg_left hξ.le (by positivity)
            (by nlinarith [mul_pos (mul_pos hA0 hJpos) hLpos])
      _ = thr := by
          rw [hthr, hξ']
          field_simp
      _ ≤ g ℓ := hge

end PrimeCarleson.Proof.Fplus31
