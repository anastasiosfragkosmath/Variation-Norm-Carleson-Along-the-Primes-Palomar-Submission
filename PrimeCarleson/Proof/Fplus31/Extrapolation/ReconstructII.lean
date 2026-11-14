module

public import PrimeCarleson.Proof.Fplus31.Extrapolation.Kernel
public import PrimeCarleson.Proof.Fplus31.Extrapolation.Lift

/-!
# The type II reconstruction and the generators of `K⁰` (the extrapolation step, type II)

Part of the abstract extrapolation, type II variant (the extrapolation step of the iteration of
`C2/CMain.lean`, proof of [F+] Proposition 3.1).

* `reconstruct_kernel`: the group-level version of `KerData.kernel_decomp`.  If the independent
  rows of the two layers are approximately integral on `X`, then `X = E P R` with `E` slow, `R`
  in a grid, and `P = (Σ_j c_j ψ¹_j, Σ_j c'_j ψ²_j + Σ_{i,i'} c''_{ii'} β(b_i, b_{i'}))`;
* `commonKernel_gen`: `K⁰` is spanned by `dim g` vectors of coordinate log-height at most `p'`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] {a : Step2Algebra ι₁ ι₂}

omit [Fintype ι₂] in
/-- The real bracket lies in the real span of the structure-constant vectors. -/
theorem br_mem_span_c (u v : ι₁ → ℝ) :
    a.br u v ∈ Submodule.span ℝ (Set.range fun (ij : ι₁ × ι₁) k => (a.c ij.1 ij.2 k : ℝ)) := by
  have : a.br u v = ∑ ij : ι₁ × ι₁, (u ij.1 * v ij.2) • (fun k => (a.c ij.1 ij.2 k : ℝ)) := by
    ext k
    simp [Step2Algebra.br_apply, Fintype.sum_prod_type]
  rw [this]
  exact Submodule.sum_mem _ fun ij _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨ij, rfl⟩)

section Reconstruct

variable [DecidableEq ι₁] [DecidableEq ι₂]

/-- **The type II reconstruction.**  See the module documentation. -/
theorem reconstruct_kernel (X : SymbolGroup a) {κ₁ κ₂ : Type*} {rows₁ : κ₁ → ι₁ → ℤ}
    {rows₂ : κ₂ → ι₂ → ℤ} (D₁ : KerData rows₁) (D₂ : KerData rows₂) (N₁ N₂ : ℕ) (hN₁ : 0 < N₁)
    (hN₂ : 0 < N₂) (Y₁ : ι₁ → ℤ) (Y₂ : ι₂ → ℤ) {τ₁ τ₂ Hψ : ℝ} (hτ₁ : 0 ≤ τ₁) (hτ₂ : 0 ≤ τ₂)
    (hHψ : 0 ≤ Hψ) (hH₁ : ∀ j i, |(D₁.ψ j i : ℝ)| ≤ Hψ) (hH₂ : ∀ j i, |(D₂.ψ j i : ℝ)| ≤ Hψ)
    (hφ₁ : ∀ j, j ∉ D₁.Z → |(N₁ : ℝ) * (∑ i, (D₁.cols j i : ℝ) * X.fst i) - Y₁ j| ≤ τ₁)
    (hφ₂ : ∀ j, j ∉ D₂.Z → |(N₂ : ℝ) * (∑ i, (D₂.cols j i : ℝ) * X.snd i) - Y₂ j| ≤ τ₂) :
    ∃ E P R : SymbolGroup a, E * P * R = X ∧ (∀ i, |E.fst i| ≤ Fintype.card ι₁ * (τ₁ * Hψ)) ∧
      (∀ k, |E.snd k| ≤ Fintype.card ι₂ * (τ₂ * Hψ)) ∧
      (∀ i, ∃ w : ℤ, (w : ℝ) = ((N₁ * D₁.Δ * (N₂ * D₂.Δ) : ℕ) : ℝ) * R.fst i) ∧
      (∀ k, ∃ w : ℤ, (w : ℝ) = ((N₁ * D₁.Δ * (N₂ * D₂.Δ) : ℕ) : ℝ) * R.snd k) ∧
      P.fst ∈ Submodule.span ℝ (Set.range fun j : D₁.Z => fun i => (D₁.ψ j i : ℝ)) ∧
      P.snd ∈ Submodule.span ℝ (Set.range (Sum.elim
        (fun j : D₂.Z => fun k => (D₂.ψ j k : ℝ))
        (fun ij : ι₁ × ι₁ => fun k => (a.c ij.1 ij.2 k : ℝ)))) := by
  obtain ⟨e₁, r₁, p₁, hX₁, he₁, hr₁, hp₁⟩ := D₁.kernel_decomp X.fst N₁ hN₁ Y₁ hτ₁ hHψ hH₁ hφ₁
  obtain ⟨e₂, r₂, p₂, hX₂, he₂, hr₂, hp₂⟩ := D₂.kernel_decomp X.snd N₂ hN₂ Y₂ hτ₂ hHψ hH₂ hφ₂
  let E : SymbolGroup a := ⟨e₁, e₂⟩
  let R : SymbolGroup a := ⟨r₁, r₂⟩
  refine ⟨E, E⁻¹ * X * R⁻¹, R, by group, he₁, he₂, ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨w, hw⟩ := hr₁ i
    refine ⟨w * (N₂ * D₂.Δ : ℕ), ?_⟩
    push_cast at hw ⊢
    rw [hw]
    ring
  · intro k
    obtain ⟨w, hw⟩ := hr₂ k
    refine ⟨w * (N₁ * D₁.Δ : ℕ), ?_⟩
    push_cast at hw ⊢
    rw [hw]
    ring
  · have hP : (E⁻¹ * X * R⁻¹).fst = p₁ := by
      simp only [SymbolGroup.mul_fst, SymbolGroup.inv_fst]
      change -e₁ + X.fst + -r₁ = p₁
      rw [hX₁]
      abel
    rw [hP]
    exact hp₁
  · have hP : (E⁻¹ * X * R⁻¹).snd = p₂ + ((-(1 / 2 : ℝ)) • a.br e₁ X.fst +
        (-(1 / 2 : ℝ)) • a.br (X.fst - e₁) r₁) := by
      simp only [E, R, SymbolGroup.mul_snd, SymbolGroup.mul_fst, SymbolGroup.inv_fst,
        SymbolGroup.inv_snd, Step2Algebra.br_neg_left, Step2Algebra.br_neg_right, smul_neg,
        neg_add_eq_sub]
      rw [hX₂]
      module
    rw [hP]
    refine Submodule.add_mem _ ?_ (Submodule.add_mem _ ?_ ?_)
    · refine Submodule.span_mono ?_ hp₂
      rintro _ ⟨j, rfl⟩
      exact ⟨Sum.inl j, rfl⟩
    · refine Submodule.smul_mem _ _ (Submodule.span_mono ?_ (br_mem_span_c (a := a) e₁ X.fst))
      rintro _ ⟨ij, rfl⟩
      exact ⟨Sum.inr ij, rfl⟩
    · refine Submodule.smul_mem _ _ (Submodule.span_mono ?_
        (br_mem_span_c (a := a) (X.fst - e₁) r₁))
      rintro _ ⟨ij, rfl⟩
      exact ⟨Sum.inr ij, rfl⟩

end Reconstruct

/-- An integer of absolute value at most `e^{p'}` has log-height at most `p'`. -/
theorem ratLogHeight_intCast_le (z : ℤ) {p' : ℝ} (hp' : 0 ≤ p') (hz : |(z : ℝ)| ≤ Real.exp p') :
    ratLogHeight (z : ℚ) ≤ p' := by
  apply ratLogHeight_le_of_le
  · simpa [Rat.num_intCast, Nat.cast_natAbs] using hz
  · simpa using Real.one_le_exp hp'

section Gen

variable [DecidableEq ι₁] [DecidableEq ι₂]

/-- **`K⁰` is spanned by `dim g` vectors of log-height at most `p'`.** -/
theorem commonKernel_gen {p' : ℝ} (hp' : 0 ≤ p') {K : GradedSubalg a.prod} {κ₁ κ₂ : Type*}
    {rows₁ : κ₁ → ι₁ → ℤ} {rows₂ : κ₂ → ι₂ → ℤ} (D₁ : KerData rows₁) (D₂ : KerData rows₂)
    (h₁ : ∀ k : ι₁ → ℚ, k ∈ K.commonKernel.layer₁ ↔ ∀ b, ∑ i, (rows₁ b i : ℚ) * k i = 0)
    (h₂ : ∀ k : ι₂ → ℚ, k ∈ K.commonKernel.layer₂ ↔ ∀ b, ∑ i, (rows₂ b i : ℚ) * k i = 0)
    (hψ₁ : ∀ j i, |(D₁.ψ j i : ℝ)| ≤ Real.exp p') (hψ₂ : ∀ j i, |(D₂.ψ j i : ℝ)| ≤ Real.exp p') :
    K.commonKernel.Gen p' := by
  let g : D₁.Z ⊕ D₂.Z → (ι₁ → ℚ) × (ι₂ → ℚ) := Sum.elim
    (fun j => (fun i => (D₁.ψ j i : ℚ), (0 : ι₂ → ℚ)))
    (fun j => ((0 : ι₁ → ℚ), fun k => (D₂.ψ j k : ℚ)))
  have hd : Module.finrank ℚ ((ι₁ → ℚ) × (ι₂ → ℚ)) = Fintype.card ι₁ + Fintype.card ι₂ := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]
  obtain ⟨v', hv', hmem⟩ := exists_fin_family g _ hd
  refine ⟨v', ?_, ?_⟩
  · rw [hv']
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨n, rfl⟩
      rcases n with j | j
      · change (fun i => (D₁.ψ j i : ℚ), (0 : ι₂ → ℚ)) ∈ K.commonKernel.toSubmodule
        refine (GradedSubalg.mem_layer₁ (W := K.commonKernel)).mp ((h₁ _).mpr fun b => ?_)
        have := D₁.kill j j.2 b
        have h5 : ((∑ i, D₁.ψ j i * rows₁ b i : ℤ) : ℚ) = 0 := by rw [this]; simp
        push_cast at h5
        rw [← h5]
        exact Finset.sum_congr rfl fun i _ => by ring
      · change ((0 : ι₁ → ℚ), fun k => (D₂.ψ j k : ℚ)) ∈ K.commonKernel.toSubmodule
        refine (GradedSubalg.mem_layer₂ (W := K.commonKernel)).mp ((h₂ _).mpr fun b => ?_)
        have := D₂.kill j j.2 b
        have h5 : ((∑ i, D₂.ψ j i * rows₂ b i : ℤ) : ℚ) = 0 := by rw [this]; simp
        push_cast at h5
        rw [← h5]
        exact Finset.sum_congr rfl fun i _ => by ring
    · intro w hw
      have hw1 : w.1 ∈ K.commonKernel.layer₁ := K.commonKernel.fst_mem w hw
      have hw2 : w.2 ∈ K.commonKernel.layer₂ := K.commonKernel.snd_mem w hw
      have hs1 := D₁.span_of_ker w.1 ((h₁ _).mp hw1)
      have hs2 := D₂.span_of_ker w.2 ((h₂ _).mp hw2)
      have hl : ∀ x ∈ Submodule.span ℚ (Set.range fun j : D₁.Z => fun i => (D₁.ψ j i : ℚ)),
          (x, (0 : ι₂ → ℚ)) ∈ Submodule.span ℚ (Set.range g) := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨j, rfl⟩ := hx
          exact Submodule.subset_span ⟨Sum.inl j, rfl⟩
        | zero =>
          rw [Prod.mk_zero_zero]
          exact Submodule.zero_mem _
        | add x y _ _ hx hy =>
          have := Submodule.add_mem _ hx hy
          simpa using this
        | smul t x _ hx =>
          have := Submodule.smul_mem _ t hx
          simpa using this
      have hr : ∀ x ∈ Submodule.span ℚ (Set.range fun j : D₂.Z => fun i => (D₂.ψ j i : ℚ)),
          ((0 : ι₁ → ℚ), x) ∈ Submodule.span ℚ (Set.range g) := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨j, rfl⟩ := hx
          exact Submodule.subset_span ⟨Sum.inr j, rfl⟩
        | zero =>
          rw [Prod.mk_zero_zero]
          exact Submodule.zero_mem _
        | add x y _ _ hx hy =>
          have := Submodule.add_mem _ hx hy
          simpa using this
        | smul t x _ hx =>
          have := Submodule.smul_mem _ t hx
          simpa using this
      have := Submodule.add_mem _ (hl _ hs1) (hr _ hs2)
      simpa using this
  · intro r
    rcases hmem r with h0 | ⟨n, hn⟩
    · rw [h0]
      simp [ratLogHeight_zero, hp']
    · rw [hn]
      rcases n with j | j
      · exact ⟨fun i => ratLogHeight_intCast_le _ hp' (hψ₁ j i), fun k => by
          simp [g, ratLogHeight_zero, hp']⟩
      · exact ⟨fun i => by simp [g, ratLogHeight_zero, hp'],
          fun k => ratLogHeight_intCast_le _ hp' (hψ₂ j k)⟩

end Gen

section PsiMem

variable [DecidableEq ι₁] [DecidableEq ι₂]

omit [Fintype ι₂] [DecidableEq ι₂] in
/-- The kernel vectors of layer one lie in `K⁰`. -/
theorem psi_mem_layer₁ {K : GradedSubalg a.prod} {κ₁ : Type*} {rows₁ : κ₁ → ι₁ → ℤ}
    (D₁ : KerData rows₁)
    (h₁ : ∀ k : ι₁ → ℚ, k ∈ K.commonKernel.layer₁ ↔ ∀ b, ∑ i, (rows₁ b i : ℚ) * k i = 0)
    (j : D₁.Z) :
    ((fun i => (D₁.ψ j i : ℚ)), (0 : ι₂ → ℚ)) ∈ K.commonKernel.toSubmodule := by
  refine (GradedSubalg.mem_layer₁ (W := K.commonKernel)).mp ((h₁ _).mpr fun b => ?_)
  have := D₁.kill j j.2 b
  have h5 : ((∑ i, D₁.ψ j i * rows₁ b i : ℤ) : ℚ) = 0 := by rw [this]; simp
  push_cast at h5
  rw [← h5]
  exact Finset.sum_congr rfl fun i _ => by ring

omit [DecidableEq ι₁] in
/-- The kernel vectors of layer two lie in `K⁰`. -/
theorem psi_mem_layer₂ {K : GradedSubalg a.prod} {κ₂ : Type*} {rows₂ : κ₂ → ι₂ → ℤ}
    (D₂ : KerData rows₂)
    (h₂ : ∀ k : ι₂ → ℚ, k ∈ K.commonKernel.layer₂ ↔ ∀ b, ∑ i, (rows₂ b i : ℚ) * k i = 0)
    (j : D₂.Z) :
    ((0 : ι₁ → ℚ), fun k => (D₂.ψ j k : ℚ)) ∈ K.commonKernel.toSubmodule := by
  refine (GradedSubalg.mem_layer₂ (W := K.commonKernel)).mp ((h₂ _).mpr fun b => ?_)
  have := D₂.kill j j.2 b
  have h5 : ((∑ i, D₂.ψ j i * rows₂ b i : ℤ) : ℚ) = 0 := by rw [this]; simp
  push_cast at h5
  rw [← h5]
  exact Finset.sum_congr rfl fun i _ => by ring

end PsiMem

end PrimeCarleson.Proof.Fplus31
