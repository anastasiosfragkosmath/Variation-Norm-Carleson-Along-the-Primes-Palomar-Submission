module

public import PrimeCarleson.Proof.Paper.P10.Decomposition
public import PrimeCarleson.Proof.Paper.P10.Exponents

/-!
# Application of `p:variable` (Theorem B(c)) to the families `g_R`, `F_R`

Source: main paper `p:transferprop`, L2260–L2264.

For a window `u` (`ω(x) ∈ [u, u + 1/(2N)]`) and a finite set `X ⊂ ℤ`, the selector theorem
`variable_selector` of `P9/VariableMain.lean` (with `r = 4`, `2 < s < 4`, base point `t₀ = u`) gives
`(∑_{x ∈ X} |T^{Q,B}_{λ(x)} f(x)|²)^{1/2} ≤ ‖χ_I‖ (A₁ C₀ + E C A₁^{1-γ} B₁^γ) (∑_R ‖F_R‖²)^{1/2}`
for `λ(x) = ϑ(x)/N + ω(x)`; here `‖χ_I‖ = chiNorm` of the cutoff data of the window, `(A₁, B₁)` are
the statistics of `l:A1B1` and the sum of the pieces is bounded by `‖f‖` (`famNorm_winDens_le`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

theorem two_mul_winScale_mul_lt_one {N : ℕ} (hN : 0 < N) : 2 * winScale N * (N : ℝ) < 1 := by
  unfold winScale
  have : (0 : ℝ) < N := by exact_mod_cast hN
  rw [show 2 * (13 / (2500 * (N : ℝ))) * N = 13 / 1250 by field_simp; ring]
  norm_num

/-- **Application of `p:variable` to `g_R`, `F_R`** (Source: main paper `p:transferprop`,
L2260–L2264; Theorem B(c) with `r = 4`, `t₀ = u`):
Let `B ⊆ sqfreeSet j` be a block with `|B| ≤ 100 Q^κ` (`Q = 2^j`, `κ = S.P.kappa`) and
`N = 𝒬_B`, `(C1)` `SupportBlock`, `l:varcarZ` at the exponent `s ∈ (2, 4)` (`LVarCarZ s Cv`),
`C₀` a bound for `sup |K̂_Q|` and `V(K̂_Q)`, `D` the cutoff data of the window `[u, u + 1/(2N)]`
and `A₁, B₁` with `A₁² ≥ 2 𝔪_B²/c`, `B₁² ≥ (2/c) ∑_{q ∈ B} 1/φ(q)` (`c = 13/(2500 N)`). Then for
every finite `X ⊂ ℤ`, selectors `ϑ : ℤ → ℤ`, `ω` with `ω(x) ∈ [u, u + 1/(2N)] ∩ (-∞, 1)`,
`x ∈ X`, and finitely supported `f`,
`(∑_{x ∈ X} |T^{Q,B}_{ϑ(x)/N + ω(x)} f(x)|²)^{1/2} ≤
  ‖χ_I‖ (A₁ C₀ + E(4, s) Cv C₀ A₁^{1-γ} B₁^γ) ‖f‖_{ℓ²}`. -/
theorem apply_variable (S : KQSetup) (hS : S.P.SupportBlock S.δ) {j : ℕ} {B : Finset ℕ}
    (hBsub : B ⊆ sqfreeSet j) (hcard : (B.card : ℝ) ≤ 100 * ((2 : ℝ) ^ j) ^ S.P.kappa)
    {u : ℝ} (hu0 : 0 ≤ u) {s Cv : ℝ} (hs : 2 < s) (hs4 : s < 4) (hCv : 0 ≤ Cv)
    (hv : LVarCarZ s Cv) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hKb : ∀ β : ℝ, ‖S.KQhat (2 ^ j) β‖ ≤ C₀)
    (hbv : eVariationOn (S.KQhat (2 ^ j)) Set.univ ≤ ENNReal.ofReal C₀)
    (D : CutoffData (winChart u) (winLo (lcmQ B) u) (winHi (lcmQ B) u) (winScale (lcmQ B)))
    {A₁ B₁ : ℝ} (hA₁ : 0 ≤ A₁) (hB₁ : 0 ≤ B₁)
    (hA₁' : 2 / winScale (lcmQ B) * mB B ^ 2 ≤ A₁ ^ 2)
    (hB₁' : 2 / winScale (lcmQ B) * ∑ q ∈ B, ((Nat.totient q : ℝ))⁻¹ ≤ B₁ ^ 2)
    (f : ℤ →₀ ℂ) (X : Finset ℤ) (ϑ : ℤ → ℤ) (ω : ℤ → ℝ)
    (hω : ∀ x ∈ X, u ≤ ω x ∧ ω x ≤ u + 1 / (2 * (lcmQ B : ℝ)) ∧ ω x < 1)
    (hu1 : u < 1) (hu2 : u ≤ u + 1 / (2 * (lcmQ B : ℝ))) :
    (∑ x ∈ X, ‖S.TQB (2 ^ j) B ((ϑ x : ℝ) / (lcmQ B : ℝ) + ω x) f x‖ₑ ^ 2) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (D.chiNorm * (A₁ * C₀ + entropyConst 4 s * (Cv * C₀) *
        A₁ ^ (1 - entropyGamma 4 s) * B₁ ^ entropyGamma 4 s)) * l2enorm (⇑f) := by
  classical
  have hB : ∀ q ∈ B, 0 < q := fun q hq =>
    Nat.pos_of_ne_zero (mem_sqfreeSet.1 (hBsub hq)).2.2.ne_zero
  have hN : 0 < lcmQ B := lcmQ_pos hB
  have hNR : (1 : ℝ) ≤ lcmQ B := by exact_mod_cast hN
  have hsuppN := (S.support_of_KQhat hS hBsub hcard).1
  have hsupp : ∀ β : ℝ, 1 / (100 * (lcmQ B : ℝ)) < |β| → S.KQhat (2 ^ j) β = 0 := by
    intro β hβ
    apply hsuppN
    rwa [← one_div]
  have hδ : S.δ / S.P.NQ (2 ^ j) ≤ 1 / 100 := by
    refine (S.delta_div_NQ_le hS j).trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    linarith
  have hℓ : 1 / (2 * (lcmQ B : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  -- the finite set of parameters
  set T : Set ℝ := insert u (ω '' (X : Set ℤ)) with hT
  have hTfin : T.Finite := Set.Finite.insert u (X.finite_toSet.image ω)
  have hTmem : ∀ x ∈ X, ω x ∈ T := fun x hx => Or.inr ⟨x, hx, rfl⟩
  have hT01 : T ⊆ Set.Ico 0 1 := by
    intro t ht
    rcases ht with rfl | ⟨x, hx, rfl⟩
    · exact ⟨hu0, hu1⟩
    · exact ⟨hu0.trans (hω x hx).1, (hω x hx).2.2⟩
  have hTchart : ∀ t ∈ T, winChart u < t - S.δ / S.P.NQ (2 ^ j) ∧
      t + S.δ / S.P.NQ (2 ^ j) < winChart u + 1 := by
    intro t ht
    have h1 : u ≤ t ∧ t ≤ u + 1 / (2 * (lcmQ B : ℝ)) := by
      rcases ht with rfl | ⟨x, hx, rfl⟩
      · exact ⟨le_rfl, hu2⟩
      · exact ⟨(hω x hx).1, (hω x hx).2.1⟩
    unfold winChart
    constructor <;> linarith [h1.1, h1.2]
  have hadm : VarAdmissible (winChart u) (winLo (lcmQ B) u) (winHi (lcmQ B) u) T
      (fun t β => S.KQmult (2 ^ j) t β) (winDens (lcmQ B) u f) := by
    refine ⟨fun t _ => S.measurable_KQmult _ t, fun t _ => ⟨C₀, fun β _ => ?_⟩,
      fun R => chartL2_winDens _ u f R _, fun R β hβ => winDens_eq_zero R hβ⟩
    simpa [KQSetup.KQmult] using hKb (β - t)
  have hVs : ∀ H' : ℝ → ℂ, ChartL2 (winChart u) H' →
      (∀ β, β ∉ Set.Icc (winLo (lcmQ B) u) (winHi (lcmQ B) u) → H' β = 0) →
      (∑' x : ℤ, rVariationOn s T (fun t => invFZ (winChart u)
        (fun β => (fun t β => S.KQmult (2 ^ j) t β) t β * H' β) x) ^ 2) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (Cv * C₀) * l2enorm (invFZ (winChart u) H') := by
    intro H' hH' _
    exact mt_variational_bound S hS (by linarith) hCv hv hC₀ j hKb hbv hTfin hT01 hTchart hH'
  have hsel := variable_selector D (gcoefR B ϑ) hadm (t₀ := u) (Or.inl rfl) hs hs4 hTfin hA₁ hB₁
    (fun x w => A1_bound D hB (two_mul_winScale_mul_lt_one hN) ϑ hA₁' x w)
    (fun x => B1_bound D hB ϑ hB₁' x) (mul_nonneg hCv hC₀) hVs hC₀
    (fun β _ => by simpa [KQSetup.KQmult] using hKb (β - u)) X ω hTmem
  have hfam := famNorm_winDens_le hN u f
  have hcongr : ∑ x ∈ X, ‖S.TQB (2 ^ j) B ((ϑ x : ℝ) / (lcmQ B : ℝ) + ω x) f x‖ₑ ^ 2 =
      ∑ x ∈ X, ‖aSum (winChart u) (gcoefR B ϑ) (fun t β => S.KQmult (2 ^ j) t β)
        (winDens (lcmQ B) u f) (ω x) x‖ₑ ^ 2 := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [keyidentity S hB hsupp (hω x hx).1 (hω x hx).2.1 f x ϑ]
  rw [hcongr]
  exact hsel.trans (mul_le_mul_right hfam _)

end PrimeCarleson.Proof.Paper
