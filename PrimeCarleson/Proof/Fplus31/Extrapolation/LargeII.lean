module

public import PrimeCarleson.Proof.Fplus31.Extrapolation.ReconstructII
public import PrimeCarleson.Proof.Fplus31.Extrapolation.Characters2
public import PrimeCarleson.Proof.Fplus31.Extrapolation.Large

/-!
# The large-`L` case of the extrapolation step, type II

Part of the abstract extrapolation, type II variant (the extrapolation step of the iteration of
`C2/CMain.lean`, proof of [F+] Proposition 3.1). `large_caseII`: the pairs `(ℓ, ℓ') ∈ Γ₁` sharing
one subalgebra `W` of `g × g` and one grid size `m`, with data for `(δ_{qℓ} X, δ_{qℓ'} X)`, give a
datum for `X` itself relative to `K⁰ = (W + D × D)⁰`, with the heights parameter, the slow constant
and the grid size at most `e^{C B⁴}`. The pivot functionals of `K = W + D × D` (exactly as in type
I) give approximate integrality of all their halves (`character_family₂`); the kernel pivot of the
halves (`exists_kerData`) and `reconstruct_kernel` give the factorization.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- An integer within `x` in absolute value is at most `⌊x⌋₊` in absolute value. -/
theorem abs_le_floor (n : ℤ) {x : ℝ} (h : |(n : ℝ)| ≤ x) : |n| ≤ ((⌊x⌋₊ : ℕ) : ℤ) := by
  rw [Int.abs_eq_natAbs]
  have h2 : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  have : n.natAbs ≤ ⌊x⌋₊ := Nat.le_floor (by rw [h2]; exact h)
  exact_mod_cast this

omit [Fintype ι₁] [Fintype ι₂] in
/-- The product of two groups has structure constants of the same height. -/
theorem prod_c_height {a : Step2Algebra ι₁ ι₂} {p : ℝ} (hp : 0 ≤ p)
    (hc : ∀ i j k, ratLogHeight (a.c i j k) ≤ p) (i j : ι₁ ⊕ ι₁) (k : ι₂ ⊕ ι₂) :
    ratLogHeight (a.prod.c i j k) ≤ p := by
  rcases i with i | i <;> rcases j with j | j <;> rcases k with k | k <;>
    simp only [Step2Algebra.prod, Sum.elim_inl, Sum.elim_inr, ratLogHeight_zero] <;>
    first | exact hc _ _ _ | exact hp

section Functionals

variable {a : Step2Algebra ι₁ ι₂}

/-- **The pivot functionals of `K = W + D × D`.**  The functionals of the pivot structure of the
layers of `K` (integer, of size at most `e^{2 p³}`), killing the middle factor of every datum of
`W` and the structure constants, and describing `K⁰` as the common kernel of their halves. -/
theorem typeII_functionals {p : ℝ} (hp : 1 ≤ p)
    (hd : ((Fintype.card (ι₁ ⊕ ι₁) + Fintype.card (ι₂ ⊕ ι₂) : ℕ) : ℝ) ≤ p)
    (hc : ∀ i j k, ratLogHeight (a.c i j k) ≤ p) (W : GradedSubalg a.prod) (hW : W.Gen p) :
    ∃ (Z₁ : Finset (ι₁ ⊕ ι₁)) (θ₁ : ι₁ ⊕ ι₁ → ι₁ ⊕ ι₁ → ℤ) (Z₂ : Finset (ι₂ ⊕ ι₂))
      (θ₂ : ι₂ ⊕ ι₂ → ι₂ ⊕ ι₂ → ℤ),
      (∀ j i, |(θ₁ j i : ℝ)| ≤ Real.exp (2 * p ^ 3)) ∧
      (∀ j i, |(θ₂ j i : ℝ)| ≤ Real.exp (2 * p ^ 3)) ∧
      (∀ j ∈ Z₂, ∀ i i', ∑ k, (θ₂ j k : ℚ) * a.prod.c i i' k = 0) ∧
      (∀ j ∈ Z₁, ∀ P : SymbolGroup a.prod, (P.fst, P.snd) ∈ realSpan W.toSubmodule →
        fnl (θ₁ j) P.fst = 0) ∧
      (∀ j ∈ Z₂, ∀ P : SymbolGroup a.prod, (P.fst, P.snd) ∈ realSpan W.toSubmodule →
        fnl (θ₂ j) P.snd = 0) ∧
      (∀ k : ι₁ → ℚ, k ∈ W.plusDerived.commonKernel.layer₁ ↔
        ∀ b : {j // j ∈ Z₁} ⊕ {j // j ∈ Z₁},
          ∑ i, ((Sum.elim (fun j i => θ₁ j.1 (.inl i)) (fun j i => θ₁ j.1 (.inr i)) b i : ℤ) : ℚ) *
            k i = 0) ∧
      (∀ k : ι₂ → ℚ, k ∈ W.plusDerived.commonKernel.layer₂ ↔
        ∀ b : {j // j ∈ Z₂} ⊕ {j // j ∈ Z₂},
          ∑ i, ((Sum.elim (fun j i => θ₂ j.1 (.inl i)) (fun j i => θ₂ j.1 (.inr i)) b i : ℤ) : ℚ) *
            k i = 0) := by
  classical
  have hp0 : 0 ≤ p := by linarith
  have hKgen := W.gen_plusDerived hp0 hW (prod_c_height hp0 hc)
  obtain ⟨v₀, hv₀, hh₀⟩ := hW
  obtain ⟨v', hv', hh'⟩ := hKgen
  have hn₁' : (Fintype.card (ι₁ ⊕ ι₁) : ℝ) ≤ p := by
    have : (Fintype.card (ι₁ ⊕ ι₁) : ℝ) ≤
        ((Fintype.card (ι₁ ⊕ ι₁) + Fintype.card (ι₂ ⊕ ι₂) : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (ι₂ ⊕ ι₂))]
    linarith
  have hn₂' : (Fintype.card (ι₂ ⊕ ι₂) : ℝ) ≤ p := by
    have : (Fintype.card (ι₂ ⊕ ι₂) : ℝ) ≤
        ((Fintype.card (ι₁ ⊕ ι₁) + Fintype.card (ι₂ ⊕ ι₂) : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (ι₁ ⊕ ι₁))]
    linarith
  obtain ⟨Z₁, Δ₁, θ₁, z₁, hΔ₁, hΔ₁b, hθ₁b, hdiag₁, hkill₁, hspan₁, hspanQ₁⟩ :=
    exists_pivot hp hn₁' (fun r i => (v' r).1 i) (fun r i => (hh' r).1 i)
  obtain ⟨Z₂, Δ₂, θ₂, z₂, hΔ₂, hΔ₂b, hθ₂b, hdiag₂, hkill₂, hspan₂, hspanQ₂⟩ :=
    exists_pivot hp hn₂' (fun r i => (v' r).2 i) (fun r i => (hh' r).2 i)
  have hlayerK := GradedSubalg.layer_eq_span hv'
  have hmem₀ : ∀ r, v₀ r ∈ W.toSubmodule := fun r => by
    rw [← hv₀]
    exact Submodule.subset_span ⟨r, rfl⟩
  refine ⟨Z₁, θ₁, Z₂, θ₂, hθ₁b, hθ₂b, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj i i'
    have hD : (fun k => a.prod.c i i' k) ∈ derived a.prod := by
      rw [derived_eq_span]
      exact Submodule.subset_span ⟨(i, i'), rfl⟩
    have hmem : (fun k => a.prod.c i i' k) ∈ W.plusDerived.layer₂ :=
      GradedSubalg.mem_layer₂.mpr (W.mem_plusDerived_of_derived hD)
    rw [hlayerK.2] at hmem
    exact kill_of_span (θ₂ j) (hkill₂ j hj) hmem
  · intro j hj P hP
    refine fnl_fst_realSpan hv₀ (θ₁ j) (fun r => ?_) hP
    have hmem : (v₀ r).1 ∈ W.plusDerived.layer₁ :=
      GradedSubalg.mem_layer₁.mpr (W.le_plusDerived (W.fst_mem (v₀ r) (hmem₀ r)))
    rw [hlayerK.1] at hmem
    exact kill_of_span (θ₁ j) (hkill₁ j hj) hmem
  · intro j hj P hP
    refine fnl_snd_realSpan hv₀ (θ₂ j) (fun r => ?_) hP
    have hmem : (v₀ r).2 ∈ W.plusDerived.layer₂ :=
      GradedSubalg.mem_layer₂.mpr (W.le_plusDerived (W.snd_mem (v₀ r) (hmem₀ r)))
    rw [hlayerK.2] at hmem
    exact kill_of_span (θ₂ j) (hkill₂ j hj) hmem
  · intro k
    rw [commonKernel_layer₁_iff hv' Z₁ θ₁ hkill₁ hspanQ₁ k]
    constructor
    · intro h b
      rcases b with j | j
      · exact (h j.1 j.2).1
      · exact (h j.1 j.2).2
    · intro h j hj
      exact ⟨h (Sum.inl ⟨j, hj⟩), h (Sum.inr ⟨j, hj⟩)⟩
  · intro k
    rw [commonKernel_layer₂_iff hv' Z₂ θ₂ hkill₂ hspanQ₂ k]
    constructor
    · intro h b
      rcases b with j | j
      · exact (h j.1 j.2).1
      · exact (h j.1 j.2).2
    · intro h j hj
      exact ⟨h (Sum.inl ⟨j, hj⟩), h (Sum.inr ⟨j, hj⟩)⟩

end Functionals

section Kernel

variable {a : Step2Algebra ι₁ ι₂} [DecidableEq ι₁] [DecidableEq ι₂]

/-- **The datum relative to `K⁰` from the kernel data.**  See the module documentation. -/
theorem datum_from_kernel {K : GradedSubalg a.prod} {κ₁ κ₂ : Type*} {rows₁ : κ₁ → ι₁ → ℤ}
    {rows₂ : κ₂ → ι₂ → ℤ} (D₁ : KerData rows₁) (D₂ : KerData rows₂)
    (hD : derived a ≤ K.commonKernel.layer₂)
    (hrk₁ : ∀ k : ι₁ → ℚ, k ∈ K.commonKernel.layer₁ ↔ ∀ b, ∑ i, (rows₁ b i : ℚ) * k i = 0)
    (hrk₂ : ∀ k : ι₂ → ℚ, k ∈ K.commonKernel.layer₂ ↔ ∀ b, ∑ i, (rows₂ b i : ℚ) * k i = 0)
    {p' M' A' Hψ τ₁ τ₂ : ℝ} (hp' : 0 ≤ p') (hHψ : 0 ≤ Hψ) (hHψp : Hψ ≤ Real.exp p')
    (hψ₁ : ∀ j i, |(D₁.ψ j i : ℝ)| ≤ Hψ) (hψ₂ : ∀ j i, |(D₂.ψ j i : ℝ)| ≤ Hψ)
    (X : SymbolGroup a) (N₁ N₂ : ℕ) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (Y₁ : ι₁ → ℤ) (Y₂ : ι₂ → ℤ)
    (hτ₁ : 0 ≤ τ₁) (hτ₂ : 0 ≤ τ₂)
    (hY₁ : ∀ j, j ∉ D₁.Z → |(N₁ : ℝ) * (∑ i, (D₁.cols j i : ℝ) * X.fst i) - Y₁ j| ≤ τ₁)
    (hY₂ : ∀ j, j ∉ D₂.Z → |(N₂ : ℝ) * (∑ i, (D₂.cols j i : ℝ) * X.snd i) - Y₂ j| ≤ τ₂)
    (hslow₁ : Fintype.card ι₁ * (τ₁ * Hψ) ≤ M' / A')
    (hslow₂ : Fintype.card ι₂ * (τ₂ * Hψ) ≤ M' / A' ^ 2)
    (hgrid : ((N₁ * D₁.Δ * (N₂ * D₂.Δ) : ℕ) : ℝ) ≤ M') :
    ∃ m' : ℕ, (m' : ℝ) ≤ M' ∧ Datum p' K.commonKernel A' M' m' X := by
  obtain ⟨E', P', R', hprod', hE₁', hE₂', hR₁', hR₂', hP₁', hP₂'⟩ :=
    reconstruct_kernel X D₁ D₂ N₁ N₂ hN₁ hN₂ Y₁ Y₂ hτ₁ hτ₂ hHψ hψ₁ hψ₂ hY₁ hY₂
  have hgen := commonKernel_gen hp' D₁ D₂ hrk₁ hrk₂ (fun j i => (hψ₁ j i).trans hHψp)
    (fun j i => (hψ₂ j i).trans hHψp)
  have hspanK₁ := inl_mem_realSpan (S := K.commonKernel.toSubmodule)
    (g := fun j : D₁.Z => fun i => (D₁.ψ j i : ℚ)) (fun j => psi_mem_layer₁ D₁ hrk₁ j) hP₁'
  have hfam : (fun (n : D₂.Z ⊕ (ι₁ × ι₁)) (k : ι₂) =>
      (((Sum.elim (fun (j : D₂.Z) (k : ι₂) => (D₂.ψ j k : ℚ))
        (fun (ij : ι₁ × ι₁) (k : ι₂) => a.c ij.1 ij.2 k) n) k : ℚ) : ℝ)) =
      Sum.elim (fun j : D₂.Z => fun k => (D₂.ψ j k : ℝ))
        (fun ij : ι₁ × ι₁ => fun k => (a.c ij.1 ij.2 k : ℝ)) := by
    funext n
    rcases n with j | ij <;> rfl
  have hspanK₂ := inr_mem_realSpan (S := K.commonKernel.toSubmodule)
    (g := Sum.elim (fun j : D₂.Z => fun k => (D₂.ψ j k : ℚ))
      (fun ij : ι₁ × ι₁ => fun k => (a.c ij.1 ij.2 k : ℚ)))
    (by
      intro n
      rcases n with j | ij
      · exact psi_mem_layer₂ D₂ hrk₂ j
      · refine (GradedSubalg.mem_layer₂ (W := K.commonKernel)).mp (hD ?_)
        rw [derived_eq_span]
        exact Submodule.subset_span ⟨ij, rfl⟩)
    (by rw [hfam]; exact hP₂')
  refine ⟨N₁ * D₁.Δ * (N₂ * D₂.Δ), hgrid, hgen,
    Nat.mul_pos (Nat.mul_pos hN₁ D₁.Δ_pos) (Nat.mul_pos hN₂ D₂.Δ_pos), E', P', R', hprod',
    fun i => (hE₁' i).trans hslow₁, fun k => (hE₂' k).trans hslow₂, hR₁', hR₂', ?_⟩
  have h3 := Submodule.add_mem _ hspanK₁ hspanK₂
  simpa using h3

end Kernel

section Bounds

/-- The size of the reconstructed slow factor: `p e^{3 p⁴} Q V Ξ ≤ e^{C B⁴}`. -/
theorem typeII_slow_bound {p lam w Cc Q V cv : ℝ} (hcv : 1 ≤ cv) (hp : 1 ≤ p) (hlam : 0 ≤ lam)
    (hCc : 14 * cv + 40 ≤ Cc) (hw : w = cv * (1 + lam + 5 * p ^ 3))
    (hQ : Q ≤ Real.exp (p * w)) (hQ0 : 0 ≤ Q) (hV : V ≤ Real.exp w) (hV0 : 0 ≤ V) :
    p * Real.exp (3 * p ^ 4) * Q * V * Real.exp (3 * p + 2 * p ^ 3) ≤
      Real.exp (Cc * (p + lam) ^ 4) := by
  have hE1 := arith_E1 hcv hp hlam rfl
  rw [← hw] at hE1
  obtain ⟨hB1, hpB, -, hB3, hB4, -, -, -⟩ := arith_facts hp hlam (B := p + lam) rfl
  have hB40 : 0 ≤ (p + lam) ^ 4 := by positivity
  have hp4B : p ^ 4 ≤ (p + lam) ^ 4 := pow_le_pow_left₀ (by linarith) hpB 4
  have hp4 : p ≤ (p + lam) ^ 4 := hpB.trans (hB3.trans hB4)
  have hpe : p ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  calc p * Real.exp (3 * p ^ 4) * Q * V * Real.exp (3 * p + 2 * p ^ 3)
      ≤ Real.exp p * Real.exp (3 * p ^ 4) * Real.exp (p * w) * Real.exp w *
        Real.exp (3 * p + 2 * p ^ 3) := by
        gcongr
    _ = Real.exp (p + 3 * p ^ 4 + ((p + 1) * w + 3 * p + 2 * p ^ 3)) := by
        simp only [← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (Cc * (p + lam) ^ 4) := by
        apply Real.exp_le_exp.mpr
        have : (14 * cv + 9) * (p + lam) ^ 4 ≤ Cc * (p + lam) ^ 4 :=
          mul_le_mul_of_nonneg_right (by linarith) hB40
        linarith

/-- The size of the grid: `Q q m Δ₁ (Q q² m Δ₂) ≤ e^{C B⁴}`. -/
theorem typeII_grid_bound {p lam w Cc Q cv q m D₁ D₂ : ℝ} (hcv : 1 ≤ cv) (hp : 1 ≤ p)
    (hlam : 0 ≤ lam) (hCc : 14 * cv + 40 ≤ Cc) (hw : w = cv * (1 + lam + 5 * p ^ 3))
    (hQ : Q ≤ Real.exp (p * w)) (hQ0 : 0 ≤ Q) (hq : q ≤ Real.exp p) (hq0 : 0 ≤ q)
    (hm : m ≤ Real.exp p) (hm0 : 0 ≤ m) (hD₁ : D₁ ≤ Real.exp (3 * p ^ 4)) (hD₁0 : 0 ≤ D₁)
    (hD₂ : D₂ ≤ Real.exp (3 * p ^ 4)) (hD₂0 : 0 ≤ D₂) :
    Q * q * m * D₁ * (Q * q ^ 2 * m * D₂) ≤ Real.exp (Cc * (p + lam) ^ 4) := by
  have hE2 := arith_E2 hcv hp hlam rfl
  rw [← hw] at hE2
  obtain ⟨hB1, hpB, -, -, -, -, -, -⟩ := arith_facts hp hlam (B := p + lam) rfl
  have hB40 : 0 ≤ (p + lam) ^ 4 := by positivity
  have hp4B : p ^ 4 ≤ (p + lam) ^ 4 := pow_le_pow_left₀ (by linarith) hpB 4
  have hq2 : q ^ 2 ≤ Real.exp p * Real.exp p := by
    rw [sq]
    exact mul_le_mul hq hq hq0 (Real.exp_nonneg _)
  have hN₁r : Q * q * m ≤ Real.exp (p * w) * Real.exp p * Real.exp p :=
    mul_le_mul (mul_le_mul hQ hq hq0 (Real.exp_nonneg _)) hm hm0 (by positivity)
  have hN₂r : Q * q ^ 2 * m ≤ Real.exp (p * w) * (Real.exp p * Real.exp p) * Real.exp p :=
    mul_le_mul (mul_le_mul hQ hq2 (by positivity) (Real.exp_nonneg _)) hm hm0 (by positivity)
  calc Q * q * m * D₁ * (Q * q ^ 2 * m * D₂)
      ≤ (Real.exp (p * w) * Real.exp p * Real.exp p) * Real.exp (3 * p ^ 4) *
        ((Real.exp (p * w) * (Real.exp p * Real.exp p) * Real.exp p) * Real.exp (3 * p ^ 4)) := by
        gcongr
    _ = Real.exp (2 * p * w + 5 * p + 6 * p ^ 4) := by
        simp only [← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (Cc * (p + lam) ^ 4) := by
        apply Real.exp_le_exp.mpr
        have : (14 * cv + 15) * (p + lam) ^ 4 ≤ Cc * (p + lam) ^ 4 :=
          mul_le_mul_of_nonneg_right (by linarith) hB40
        have hp3 : 0 ≤ 4 * p ^ 3 := by positivity
        linarith

end Bounds

section Second

variable {a : Step2Algebra ι₁ ι₂}

/-- **The factorization relative to `K⁰` from the approximate integrality of the halves of the
pivot functionals** (second half of `large_caseII`). -/
theorem typeII_second {p A L V Ξ M' p' : ℝ} (hp : 1 ≤ p) (hn₁ : (Fintype.card ι₁ : ℝ) ≤ p)
    (hn₂ : (Fintype.card ι₂ : ℝ) ≤ p) (hApos : 0 < A) (hLpos : 0 < L) (hV0 : 0 ≤ V)
    (hΞ0 : 0 < Ξ) (hM0 : 0 ≤ M') (hp'0 : 0 ≤ p') (h3p4 : 3 * p ^ 4 ≤ p')
    (X : SymbolGroup a) (W : GradedSubalg a.prod) (q m Q : ℕ) (hQpos : 0 < Q) (hq1 : 1 ≤ q)
    (hm0 : 0 < m) (hQVΞ : p * Real.exp (3 * p ^ 4) * (Q : ℝ) * V * Ξ ≤ M')
    (hgridb : ∀ D₁ D₂ : ℝ, 0 ≤ D₁ → 0 ≤ D₂ → D₁ ≤ Real.exp (3 * p ^ 4) →
      D₂ ≤ Real.exp (3 * p ^ 4) →
      (Q : ℝ) * q * m * D₁ * ((Q : ℝ) * (q : ℝ) ^ 2 * m * D₂) ≤ M')
    (Z₁ : Finset (ι₁ ⊕ ι₁)) (θ₁ : ι₁ ⊕ ι₁ → ι₁ ⊕ ι₁ → ℤ) (Z₂ : Finset (ι₂ ⊕ ι₂))
    (θ₂ : ι₂ ⊕ ι₂ → ι₂ ⊕ ι₂ → ℤ) (hθ₁b : ∀ j i, |(θ₁ j i : ℝ)| ≤ Real.exp (2 * p ^ 3))
    (hθ₂b : ∀ j i, |(θ₂ j i : ℝ)| ≤ Real.exp (2 * p ^ 3))
    (hrk₁ : ∀ k : ι₁ → ℚ, k ∈ W.plusDerived.commonKernel.layer₁ ↔
      ∀ b : {j // j ∈ Z₁} ⊕ {j // j ∈ Z₁},
        ∑ i, ((Sum.elim (fun j i => θ₁ j.1 (.inl i)) (fun j i => θ₁ j.1 (.inr i)) b i : ℤ) : ℚ) *
          k i = 0)
    (hrk₂ : ∀ k : ι₂ → ℚ, k ∈ W.plusDerived.commonKernel.layer₂ ↔
      ∀ b : {j // j ∈ Z₂} ⊕ {j // j ∈ Z₂},
        ∑ i, ((Sum.elim (fun j i => θ₂ j.1 (.inl i)) (fun j i => θ₂ j.1 (.inr i)) b i : ℤ) : ℚ) *
          k i = 0)
    (hfam₁ : ∀ j ∈ Z₁,
      (∃ y : ℤ, |(Q : ℝ) * ((q : ℝ) * m * fnl (fun i => θ₁ j (.inl i)) X.fst) - y| ≤
        Q * (V * (Ξ / A) / L)) ∧
      (∃ y : ℤ, |(Q : ℝ) * ((q : ℝ) * m * fnl (fun i => θ₁ j (.inr i)) X.fst) - y| ≤
        Q * (V * (Ξ / A) / L)))
    (hfam₂ : ∀ j ∈ Z₂,
      (∃ y : ℤ, |(Q : ℝ) * ((q : ℝ) ^ 2 * m * fnl (fun i => θ₂ j (.inl i)) X.snd) - y| ≤
        Q * (V * (Ξ / A ^ 2) / L ^ 2)) ∧
      (∃ y : ℤ, |(Q : ℝ) * ((q : ℝ) ^ 2 * m * fnl (fun i => θ₂ j (.inr i)) X.snd) - y| ≤
        Q * (V * (Ξ / A ^ 2) / L ^ 2))) :
    ∃ m' : ℕ, (m' : ℝ) ≤ M' ∧ Datum p' W.plusDerived.commonKernel (A * L / 2) M' m' X := by
  classical
  -- the kernel pivots of the rows
  have hH1 : 1 ≤ ⌊Real.exp (2 * p ^ 3)⌋₊ :=
    Nat.le_floor (by simpa using Real.one_le_exp (by positivity : (0 : ℝ) ≤ 2 * p ^ 3))
  have hHfl : ((⌊Real.exp (2 * p ^ 3)⌋₊ : ℕ) : ℝ) ≤ Real.exp (2 * p ^ 3) :=
    Nat.floor_le (Real.exp_nonneg _)
  let rows₁ : {j // j ∈ Z₁} ⊕ {j // j ∈ Z₁} → ι₁ → ℤ :=
    Sum.elim (fun j i => θ₁ j.1 (.inl i)) (fun j i => θ₁ j.1 (.inr i))
  let rows₂ : {j // j ∈ Z₂} ⊕ {j // j ∈ Z₂} → ι₂ → ℤ :=
    Sum.elim (fun j i => θ₂ j.1 (.inl i)) (fun j i => θ₂ j.1 (.inr i))
  have hrows₁ : ∀ b i, |rows₁ b i| ≤ ((⌊Real.exp (2 * p ^ 3)⌋₊ : ℕ) : ℤ) := by
    intro b i
    rcases b with j | j
    · exact abs_le_floor _ (hθ₁b j.1 (.inl i))
    · exact abs_le_floor _ (hθ₁b j.1 (.inr i))
  have hrows₂ : ∀ b i, |rows₂ b i| ≤ ((⌊Real.exp (2 * p ^ 3)⌋₊ : ℕ) : ℤ) := by
    intro b i
    rcases b with j | j
    · exact abs_le_floor _ (hθ₂b j.1 (.inl i))
    · exact abs_le_floor _ (hθ₂b j.1 (.inr i))
  obtain ⟨D₁, hD₁Δ, hD₁ψ⟩ := exists_kerData rows₁ _ hH1 hrows₁
  obtain ⟨D₂, hD₂Δ, hD₂ψ⟩ := exists_kerData rows₂ _ hH1 hrows₂
  have hfac₁ : ((Fintype.card ι₁).factorial : ℝ) *
      ((⌊Real.exp (2 * p ^ 3)⌋₊ : ℕ) : ℝ) ^ Fintype.card ι₁ ≤ Real.exp (3 * p ^ 4) :=
    factorial_mul_pow_le_exp hp hn₁ (Nat.cast_nonneg _) hHfl
  have hfac₂ : ((Fintype.card ι₂).factorial : ℝ) *
      ((⌊Real.exp (2 * p ^ 3)⌋₊ : ℕ) : ℝ) ^ Fintype.card ι₂ ≤ Real.exp (3 * p ^ 4) :=
    factorial_mul_pow_le_exp hp hn₂ (Nat.cast_nonneg _) hHfl
  have hψ₁ : ∀ j i, |(D₁.ψ j i : ℝ)| ≤ Real.exp (3 * p ^ 4) := by
    intro j i
    refine le_trans ?_ hfac₁
    exact_mod_cast hD₁ψ j i
  have hψ₂ : ∀ j i, |(D₂.ψ j i : ℝ)| ≤ Real.exp (3 * p ^ 4) := by
    intro j i
    refine le_trans ?_ hfac₂
    exact_mod_cast hD₂ψ j i
  have hΔD₁ : (D₁.Δ : ℝ) ≤ Real.exp (3 * p ^ 4) := by
    refine le_trans ?_ hfac₁
    exact_mod_cast hD₁Δ
  have hΔD₂ : (D₂.Δ : ℝ) ≤ Real.exp (3 * p ^ 4) := by
    refine le_trans ?_ hfac₂
    exact_mod_cast hD₂Δ
  -- the approximate integrality of the rows
  have hN₁ : 0 < Q * q * m := Nat.mul_pos (Nat.mul_pos hQpos hq1) hm0
  have hN₂ : 0 < Q * q ^ 2 * m := Nat.mul_pos (Nat.mul_pos hQpos (pow_pos hq1 2)) hm0
  have happ₁ : ∀ b, ∃ y : ℤ, |((Q * q * m : ℕ) : ℝ) * (∑ i, (rows₁ b i : ℝ) * X.fst i) - y| ≤
      (Q : ℝ) * (V * (Ξ / A) / L) := by
    intro b
    have e : ∀ f : ℝ, ((Q * q * m : ℕ) : ℝ) * f = (Q : ℝ) * ((q : ℝ) * m * f) := by
      intro f
      push_cast
      ring
    rcases b with j | j
    · obtain ⟨y, hy⟩ := (hfam₁ j.1 j.2).1
      exact ⟨y, by rw [show (∑ i, (rows₁ (Sum.inl j) i : ℝ) * X.fst i) =
        fnl (fun i => θ₁ j.1 (.inl i)) X.fst from rfl, e]; exact hy⟩
    · obtain ⟨y, hy⟩ := (hfam₁ j.1 j.2).2
      exact ⟨y, by rw [show (∑ i, (rows₁ (Sum.inr j) i : ℝ) * X.fst i) =
        fnl (fun i => θ₁ j.1 (.inr i)) X.fst from rfl, e]; exact hy⟩
  have happ₂ : ∀ b, ∃ y : ℤ, |((Q * q ^ 2 * m : ℕ) : ℝ) * (∑ i, (rows₂ b i : ℝ) * X.snd i) - y| ≤
      (Q : ℝ) * (V * (Ξ / A ^ 2) /
        (L : ℝ) ^ 2) := by
    intro b
    have e : ∀ f : ℝ, ((Q * q ^ 2 * m : ℕ) : ℝ) * f = (Q : ℝ) * (((q : ℝ) ^ 2) * m * f) := by
      intro f
      push_cast
      ring
    rcases b with j | j
    · obtain ⟨y, hy⟩ := (hfam₂ j.1 j.2).1
      exact ⟨y, by rw [show (∑ i, (rows₂ (Sum.inl j) i : ℝ) * X.snd i) =
        fnl (fun i => θ₂ j.1 (.inl i)) X.snd from rfl, e]; exact hy⟩
    · obtain ⟨y, hy⟩ := (hfam₂ j.1 j.2).2
      exact ⟨y, by rw [show (∑ i, (rows₂ (Sum.inr j) i : ℝ) * X.snd i) =
        fnl (fun i => θ₂ j.1 (.inr i)) X.snd from rfl, e]; exact hy⟩
  have hφ₁ : ∀ j, j ∉ D₁.Z → ∃ y : ℤ, |((Q * q * m : ℕ) : ℝ) *
      (∑ i, (D₁.cols j i : ℝ) * X.fst i) - y| ≤
      (Q : ℝ) * (V * (Ξ / A) / L) := by
    intro j hj
    obtain ⟨b, hb⟩ := D₁.colsk j hj
    obtain ⟨y, hy⟩ := happ₁ b
    exact ⟨y, by rw [hb]; exact hy⟩
  have hφ₂ : ∀ j, j ∉ D₂.Z → ∃ y : ℤ, |((Q * q ^ 2 * m : ℕ) : ℝ) *
      (∑ i, (D₂.cols j i : ℝ) * X.snd i) - y| ≤
      (Q : ℝ) * (V * (Ξ / A ^ 2) /
        (L : ℝ) ^ 2) := by
    intro j hj
    obtain ⟨b, hb⟩ := D₂.colsk j hj
    obtain ⟨y, hy⟩ := happ₂ b
    exact ⟨y, by rw [hb]; exact hy⟩
  choose! Y₁ hY₁ using hφ₁
  choose! Y₂ hY₂ using hφ₂
  have hτ₁ : 0 ≤ (Q : ℝ) * (V * (Ξ / A) / L) := by
    positivity
  have hτ₂ : 0 ≤ (Q : ℝ) * (V *
      (Ξ / A ^ 2) / (L : ℝ) ^ 2) := by
    positivity
  have hHψ0 : 0 ≤ Real.exp (3 * p ^ 4) := (Real.exp_pos _).le
  have hsl := slow_algebra (Q := p * Real.exp (3 * p ^ 4) * (Q : ℝ))
    (V := V) (Ξ := Ξ) (A := A) (L := L)
    (M' := M') hApos hLpos hM0 hQVΞ
  have hgridb' := hgridb _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _) hΔD₁ hΔD₂
  have hslow₁ : (Fintype.card ι₁ : ℝ) * ((Q : ℝ) * (V *
      (Ξ / A) / L) * Real.exp (3 * p ^ 4)) ≤
      M' / (A * L / 2) := by
    refine le_trans ?_ hsl.1
    calc (Fintype.card ι₁ : ℝ) * ((Q : ℝ) * (V *
        (Ξ / A) / L) * Real.exp (3 * p ^ 4))
        ≤ p * ((Q : ℝ) * (V * (Ξ / A) / L) *
          Real.exp (3 * p ^ 4)) := mul_le_mul_of_nonneg_right hn₁ (by positivity)
      _ = _ := by ring
  have hslow₂ : (Fintype.card ι₂ : ℝ) * ((Q : ℝ) * (V *
      (Ξ / A ^ 2) / (L : ℝ) ^ 2) * Real.exp (3 * p ^ 4)) ≤
      M' / (A * L / 2) ^ 2 := by
    refine le_trans ?_ hsl.2
    calc (Fintype.card ι₂ : ℝ) * ((Q : ℝ) * (V *
        (Ξ / A ^ 2) / (L : ℝ) ^ 2) * Real.exp (3 * p ^ 4))
        ≤ p * ((Q : ℝ) * (V * (Ξ / A ^ 2) /
          (L : ℝ) ^ 2) * Real.exp (3 * p ^ 4)) := mul_le_mul_of_nonneg_right hn₂ (by positivity)
      _ = _ := by ring
  have hgrid : ((Q * q * m * D₁.Δ * (Q * q ^ 2 * m * D₂.Δ) : ℕ) : ℝ) ≤
      M' := by
    push_cast
    exact hgridb'
  exact datum_from_kernel (K := W.plusDerived) D₁ D₂ (GradedSubalg.derived_le_commonKernel W) hrk₁
    hrk₂ hp'0 hHψ0 (Real.exp_le_exp.mpr h3p4) hψ₁ hψ₂ X (Q * q * m) (Q * q ^ 2 * m) hN₁ hN₂ Y₁
    Y₂ hτ₁ hτ₂ hY₁ hY₂ hslow₁ hslow₂ hgrid

end Second

section Large

variable {a : Step2Algebra ι₁ ι₂}

/-- **The large-`L` case, type II.**  See the module documentation. -/
theorem large_caseII {CV : ℕ} (hCV : 1 ≤ CV) (hV : Vino2Spec CV)
    {p lam Cc δ A : ℝ} (hp : 1 ≤ p) (hlam : 0 ≤ lam)
    (hd : ((Fintype.card (ι₁ ⊕ ι₁) + Fintype.card (ι₂ ⊕ ι₂) : ℕ) : ℝ) ≤ p)
    (hc : ∀ i j k, ratLogHeight (a.c i j k) ≤ p) (hCc : 14 * (CV : ℝ) + 40 ≤ Cc)
    (hδ : δ = Real.exp (-(lam + 5 * p ^ 3)))
    (hA : Real.exp (Cc * (p + lam) ^ 3) ≤ A) {q : ℕ} (hq1 : 1 ≤ q) (hq : (q : ℝ) ≤ Real.exp p)
    {L : ℕ} (hL1 : 1 ≤ L) (hLV : (CV : ℝ) * (δ ^ CV)⁻¹ ≤ L) {Γ₁ : Finset (ℕ × ℕ)}
    (hΓ₁ : ∀ pr ∈ Γ₁, (L : ℝ) / 2 < pr.1 ∧ (pr.1 : ℝ) ≤ L ∧ (L : ℝ) / 2 < pr.2 ∧
      (pr.2 : ℝ) ≤ L)
    (hcard : δ * (L : ℝ) ^ 2 ≤ Γ₁.card) (X : SymbolGroup a) (W : GradedSubalg a.prod)
    (hW : W.Gen p) {m : ℕ} (hm0 : 0 < m) (hm : (m : ℝ) ≤ Real.exp p)
    (hdat : ∀ pr ∈ Γ₁, ∃ E P R : SymbolGroup a.prod,
      E * P * R = SymbolGroup.biDil ((q : ℝ) * pr.1) ((q : ℝ) * pr.2) X ∧
      (∀ i, |E.fst i| ≤ Real.exp p / A) ∧ (∀ k, |E.snd k| ≤ Real.exp p / A ^ 2) ∧
      (∀ i, ∃ z : ℤ, (z : ℝ) = (m : ℝ) * R.fst i) ∧
      (∀ k, ∃ z : ℤ, (z : ℝ) = (m : ℝ) * R.snd k) ∧ (P.fst, P.snd) ∈ realSpan W.toSubmodule) :
    ∃ m' : ℕ, (m' : ℝ) ≤ Real.exp (Cc * (p + lam) ^ 4) ∧
      Datum (Cc * (p + lam) ^ 4) W.plusDerived.commonKernel (A * L / 2)
        (Real.exp (Cc * (p + lam) ^ 4)) m' X := by
  classical
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨Z₁, θ₁, Z₂, θ₂, hθ₁b, hθ₂b, hbr, hP₁, hP₂, hrk₁, hrk₂⟩ :=
    typeII_functionals hp hd hc W hW
  -- the arithmetic
  obtain ⟨hB1, hpB, hlB, hB3, hB4, hp3B, h7, h8⟩ := arith_facts hp hlam rfl
  set B := p + lam with hB
  have hcv1 : (1 : ℝ) ≤ CV := by exact_mod_cast hCV
  have hCcpos : 0 ≤ Cc := by linarith
  have hu0 : 0 ≤ lam + 5 * p ^ 3 := by positivity
  have hδ0 : 0 < δ := by rw [hδ]; exact Real.exp_pos _
  have hδ1 : δ ≤ 1 := by
    rw [hδ]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hδC' : δ ^ CV = Real.exp (-(CV * (lam + 5 * p ^ 3))) := by
    rw [hδ, ← Real.exp_nat_mul]
    congr 1
    ring
  set w : ℝ := CV * (1 + lam + 5 * p ^ 3) with hw
  have hw0 : 0 ≤ w := by positivity
  have hVw : (CV : ℝ) * (δ ^ CV)⁻¹ ≤ Real.exp w := by
    have hδC : (δ ^ CV)⁻¹ = Real.exp (CV * (lam + 5 * p ^ 3)) := by
      rw [hδ, ← Real.exp_nat_mul, ← Real.exp_neg]
      congr 1
      ring
    rw [hδC]
    have h1 : (CV : ℝ) ≤ Real.exp CV := by linarith [Real.add_one_le_exp (CV : ℝ)]
    calc (CV : ℝ) * Real.exp (CV * (lam + 5 * p ^ 3))
        ≤ Real.exp CV * Real.exp (CV * (lam + 5 * p ^ 3)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
      _ = Real.exp w := by
          rw [← Real.exp_add, hw]
          congr 1
          ring
  have hA1 : 1 ≤ A := le_trans (Real.one_le_exp (by positivity)) hA
  have hApos : 0 < A := by linarith
  have hn₁' : (Fintype.card (ι₁ ⊕ ι₁) : ℝ) ≤ p := by
    have : (Fintype.card (ι₁ ⊕ ι₁) : ℝ) ≤
        ((Fintype.card (ι₁ ⊕ ι₁) + Fintype.card (ι₂ ⊕ ι₂) : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (ι₂ ⊕ ι₂))]
    linarith
  have hn₂' : (Fintype.card (ι₂ ⊕ ι₂) : ℝ) ≤ p := by
    have : (Fintype.card (ι₂ ⊕ ι₂) : ℝ) ≤
        ((Fintype.card (ι₁ ⊕ ι₁) + Fintype.card (ι₂ ⊕ ι₂) : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (ι₁ ⊕ ι₁))]
    linarith
  have hn₁ : (Fintype.card ι₁ : ℝ) ≤ p := by
    have : Fintype.card ι₁ ≤ Fintype.card (ι₁ ⊕ ι₁) := by
      rw [Fintype.card_sum]; omega
    have h2 : (Fintype.card ι₁ : ℝ) ≤ Fintype.card (ι₁ ⊕ ι₁) := by exact_mod_cast this
    linarith
  have hn₂ : (Fintype.card ι₂ : ℝ) ≤ p := by
    have : Fintype.card ι₂ ≤ Fintype.card (ι₂ ⊕ ι₂) := by
      rw [Fintype.card_sum]; omega
    have h2 : (Fintype.card ι₂ : ℝ) ≤ Fintype.card (ι₂ ⊕ ι₂) := by exact_mod_cast this
    linarith
  -- the error budgets
  have hΞ0 : 0 < Real.exp (3 * p + 2 * p ^ 3) := Real.exp_pos _
  have hHθ0 : 0 ≤ Real.exp (2 * p ^ 3) := (Real.exp_pos _).le
  have hε₁ : (m : ℝ) * (Fintype.card (ι₁ ⊕ ι₁) * (Real.exp (2 * p ^ 3) * (Real.exp p / A))) ≤
      Real.exp (3 * p + 2 * p ^ 3) / A :=
    bound_mnHM hApos hm (Nat.cast_nonneg _) hn₁' hHθ0 le_rfl
  have hε₂ : (m : ℝ) * (Fintype.card (ι₂ ⊕ ι₂) * (Real.exp (2 * p ^ 3) *
      (Real.exp p / A ^ 2))) ≤ Real.exp (3 * p + 2 * p ^ 3) / A ^ 2 :=
    bound_mnHM (by positivity) hm (Nat.cast_nonneg _) hn₂' hHθ0 le_rfl
  have hK : (CV : ℝ) + 3 * p + 2 * p ^ 3 + CV * (lam + 5 * p ^ 3) ≤ Cc * B ^ 3 :=
    (arith_E3 hcv1 hp hlam hB).trans
      (mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (by linarith) 3))
  have hε₁' : Real.exp (3 * p + 2 * p ^ 3) / A ≤ δ ^ CV / CV := by
    have hCVpos : (0 : ℝ) < CV := by linarith
    rw [div_le_div_iff₀ hApos hCVpos, hδC']
    have h1 : Real.exp (3 * p + 2 * p ^ 3) * CV ≤
        Real.exp (3 * p + 2 * p ^ 3) * Real.exp CV :=
      mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (CV : ℝ)]) hΞ0.le
    calc Real.exp (3 * p + 2 * p ^ 3) * CV ≤ Real.exp (3 * p + 2 * p ^ 3) * Real.exp CV := h1
      _ = Real.exp (-(CV * (lam + 5 * p ^ 3))) * Real.exp (CV + 3 * p + 2 * p ^ 3 +
            CV * (lam + 5 * p ^ 3)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
      _ ≤ Real.exp (-(CV * (lam + 5 * p ^ 3))) * A := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          exact (Real.exp_le_exp.mpr hK).trans hA
  have hε₂' : Real.exp (3 * p + 2 * p ^ 3) / A ^ 2 ≤ δ ^ CV / CV := by
    refine le_trans ?_ hε₁'
    apply div_le_div_of_nonneg_left hΞ0.le hApos
    exact le_self_pow₀ hA1 (by norm_num)
  -- the data of the pairs
  have hdat' : ∀ pr, ∃ E P R : SymbolGroup a.prod, pr ∈ Γ₁ →
      (E * P * R = SymbolGroup.biDil ((q : ℝ) * pr.1) ((q : ℝ) * pr.2) X ∧
      (∀ i, |E.fst i| ≤ Real.exp p / A) ∧ (∀ k, |E.snd k| ≤ Real.exp p / A ^ 2) ∧
      (∀ i, ∃ z : ℤ, (z : ℝ) = (m : ℝ) * R.fst i) ∧
      (∀ k, ∃ z : ℤ, (z : ℝ) = (m : ℝ) * R.snd k) ∧ (P.fst, P.snd) ∈ realSpan W.toSubmodule) := by
    intro pr
    by_cases hpr : pr ∈ Γ₁
    · obtain ⟨E, P, R, h⟩ := hdat pr hpr
      exact ⟨E, P, R, fun _ => h⟩
    · exact ⟨1, 1, 1, fun h => absurd h hpr⟩
  choose Ef Pf Rf hEPR using hdat'
  obtain ⟨Q, hQpos, hQle, hfam₁, hfam₂⟩ := character_family₂ hV X q m hδ0 hδ1 hHθ0
    (Real.exp_pos p).le hApos hLV hε₁ hε₁' hε₂ hε₂' hΓ₁ hcard Ef Pf Rf
    (fun pr hpr => (hEPR pr hpr).1) (fun pr hpr => (hEPR pr hpr).2.1)
    (fun pr hpr => (hEPR pr hpr).2.2.1) (fun pr hpr => (hEPR pr hpr).2.2.2.1)
    (fun pr hpr => (hEPR pr hpr).2.2.2.2.1) Z₁ θ₁ hθ₁b Z₂ θ₂ hθ₂b hbr
    (fun pr hpr j hj => hP₁ j hj (Pf pr) (hEPR pr hpr).2.2.2.2.2)
    (fun pr hpr j hj => hP₂ j hj (Pf pr) (hEPR pr hpr).2.2.2.2.2)
  have hV0 : (0 : ℝ) ≤ (CV : ℝ) * (δ ^ CV)⁻¹ := by positivity
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
  have hkZ : ((Z₁.card + Z₂.card : ℕ) : ℝ) ≤ p := by
    have h1 : Z₁.card ≤ Fintype.card (ι₁ ⊕ ι₁) := Finset.card_le_univ _
    have h2 : Z₂.card ≤ Fintype.card (ι₂ ⊕ ι₂) := Finset.card_le_univ _
    have h3 : ((Z₁.card + Z₂.card : ℕ) : ℝ) ≤
        ((Fintype.card (ι₁ ⊕ ι₁) + Fintype.card (ι₂ ⊕ ι₂) : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add h1 h2
    linarith
  have hQexp : (Q : ℝ) ≤ Real.exp (p * w) := by
    calc (Q : ℝ) ≤ ((CV : ℝ) * (δ ^ CV)⁻¹) ^ (Z₁.card + Z₂.card) := hQle
      _ ≤ (Real.exp w) ^ (Z₁.card + Z₂.card) := pow_le_pow_left₀ hV0 hVw _
      _ = Real.exp ((Z₁.card + Z₂.card : ℕ) * w) := (Real.exp_nat_mul w _).symm
      _ ≤ Real.exp (p * w) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hkZ hw0)
  have hp'0 : 0 ≤ Cc * B ^ 4 := by positivity
  have h3p4 : 3 * p ^ 4 ≤ Cc * B ^ 4 := by
    have h1 : p ^ 4 ≤ B ^ 4 := pow_le_pow_left₀ (by linarith) hpB 4
    calc 3 * p ^ 4 ≤ 3 * B ^ 4 := by linarith
      _ ≤ Cc * B ^ 4 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hQVΞ := typeII_slow_bound hcv1 hp hlam hCc hw hQexp (Nat.cast_nonneg Q) hVw hV0
  have hgridb : ∀ D₁ D₂ : ℝ, 0 ≤ D₁ → 0 ≤ D₂ → D₁ ≤ Real.exp (3 * p ^ 4) →
      D₂ ≤ Real.exp (3 * p ^ 4) →
      (Q : ℝ) * q * m * D₁ * ((Q : ℝ) * (q : ℝ) ^ 2 * m * D₂) ≤ Real.exp (Cc * B ^ 4) :=
    fun D₁ D₂ h1 h2 h3 h4 => typeII_grid_bound hcv1 hp hlam hCc hw hQexp (Nat.cast_nonneg Q) hq
      (Nat.cast_nonneg q) hm (Nat.cast_nonneg m) h3 h1 h4 h2
  exact typeII_second hp hn₁ hn₂ hApos hLpos hV0 hΞ0 (Real.exp_pos _).le hp'0 h3p4 X W q m Q
    hQpos hq1 hm0 hQVΞ hgridb Z₁ θ₁ Z₂ θ₂ hθ₁b hθ₂b hrk₁ hrk₂ hfam₁ hfam₂

end Large

end PrimeCarleson.Proof.Fplus31
