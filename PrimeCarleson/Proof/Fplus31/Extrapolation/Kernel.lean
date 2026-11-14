module

public import PrimeCarleson.Proof.Fplus31.Extrapolation.Product
public import PrimeCarleson.Proof.Fplus31.Extrapolation.Pivot
public import PrimeCarleson.Proof.Fplus31.Extrapolation.Reconstruct

/-!
# The kernel pivot and the decomposition relative to `K⁰` (the extrapolation step, type II)

Part of the abstract extrapolation, type II variant (the extrapolation step of the iteration of
`C2/CMain.lean`, proof of [F+] Proposition 3.1). In the type II argument the approximate integrality
is known for the *rows* `θ⁰_j, θ¹_j` of a system `Φ` of integer functionals on the single copy `g`,
and one wants a factorization of `X` with the middle factor in `K⁰ = ker Φ` (the common kernel of
the rows).

`KerData rows` is the output of `exists_pivot_int` applied to the rows as generators:
integer vectors `ψ_j` (`j ∈ Z`) spanning `ker Φ`, and the duality `Δ y = Σ_j (col_j · y) ψ_j`
(`KerData.expand`) where `col_j = e_{z j}` for `j ∈ Z` and `col_j` is a row otherwise.  Hence
(`kernel_decomp`) every real `y` is `e + p + r` with `r ∈ (1/(N Δ)) ℤ^ι`, `e` small when
`N (row · y)` is within `τ` of an integer for the independent rows, and
`p = Δ⁻¹ Σ_{j ∈ Z} y(z j) ψ_j ∈ ker Φ`.  `commonKernel_gen` shows that `K⁰` is spanned by `d`
vectors of coordinate log-height at most `p'`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

section Kill

variable {ι κ : Type*} [Fintype ι]

/-- A functional killing a spanning family kills the span. -/
theorem kill_of_span {g : κ → ι → ℚ} (θ : ι → ℤ) (h : ∀ k, ∑ i, (θ i : ℚ) * g k i = 0)
    {u : ι → ℚ} (hu : u ∈ Submodule.span ℚ (Set.range g)) : ∑ i, (θ i : ℚ) * u i = 0 := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact h k
  | zero => simp
  | add x y _ _ hx hy => simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hx, hy, add_zero]
  | smul t x _ hx =>
    simp only [Pi.smul_apply, smul_eq_mul]
    have : ∑ i, (θ i : ℚ) * (t * x i) = t * ∑ i, (θ i : ℚ) * x i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hx, mul_zero]

/-- Membership in the span of the generators is detected by the pivot functionals. -/
theorem mem_span_iff_kill {g : κ → ι → ℚ} (Z : Finset ι) (θ : ι → ι → ℤ)
    (hkill : ∀ j ∈ Z, ∀ k, ∑ i, (θ j i : ℚ) * g k i = 0)
    (hspan : ∀ y : ι → ℚ, (∀ j ∈ Z, ∑ i, (θ j i : ℚ) * y i = 0) →
      y ∈ Submodule.span ℚ (Set.range g))
    (y : ι → ℚ) : y ∈ Submodule.span ℚ (Set.range g) ↔ ∀ j ∈ Z, ∑ i, (θ j i : ℚ) * y i = 0 :=
  ⟨fun hy j hj => kill_of_span (θ j) (hkill j hj) hy, hspan y⟩

end Kill

section Generic

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

/-- The output of the pivot lemma for the rows `rows` of a system of integer functionals:
`ψ_j` (`j ∈ Z`) integer vectors killing the rows, `cols_j = e_{z j}` for `j ∈ Z` and
`cols_j` a row for `j ∉ Z`, with the duality `Σ_j cols_j(i) ψ_j(i') = Δ δ_{i i'}`. -/
structure KerData (rows : κ → ι → ℤ) where
  /-- The free columns. -/
  Z : Finset ι
  /-- The common denominator. -/
  Δ : ℕ
  /-- The kernel vectors. -/
  ψ : ι → ι → ℤ
  /-- The columns. -/
  cols : ι → ι → ℤ
  /-- The free coordinates. -/
  z : ι → ι
  Δ_pos : 0 < Δ
  I2 : ∀ i i', ∑ j, cols j i * ψ j i' = if i = i' then (Δ : ℤ) else 0
  colsZ : ∀ j ∈ Z, ∀ i, cols j i = if i = z j then 1 else 0
  colsk : ∀ j, j ∉ Z → ∃ k, cols j = rows k
  kill : ∀ j ∈ Z, ∀ k, ∑ i, ψ j i * rows k i = 0

namespace KerData

variable {rows : κ → ι → ℤ} (D : KerData rows)

/-- **The expansion** `Δ y = Σ_{j ∈ Z} y(z j) ψ_j + Σ_{j ∉ Z} (col_j · y) ψ_j`. -/
theorem expand {F : Type*} [Field F] [CharZero F] (y : ι → F) (i' : ι) :
    (D.Δ : F) * y i' = ∑ j ∈ D.Z, y (D.z j) * (D.ψ j i' : F) +
      ∑ j ∈ D.Zᶜ, (∑ i, (D.cols j i : F) * y i) * (D.ψ j i' : F) := by
  have h1 : ∀ i, ∑ j, (D.cols j i : F) * (D.ψ j i' : F) = if i = i' then (D.Δ : F) else 0 := by
    intro i
    have := congrArg (Int.cast : ℤ → F) (D.I2 i i')
    simpa only [Int.cast_sum, Int.cast_mul, Int.cast_ite, Int.cast_zero, Int.cast_natCast]
      using this
  have h2 : (D.Δ : F) * y i' = ∑ j, (∑ i, (D.cols j i : F) * y i) * (D.ψ j i' : F) := by
    calc (D.Δ : F) * y i' = ∑ i, (∑ j, (D.cols j i : F) * (D.ψ j i' : F)) * y i := by
          simp only [h1, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      _ = _ := by
          simp only [Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  rw [h2, ← Finset.sum_add_sum_compl D.Z]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have : ∑ i, (D.cols j i : F) * y i = y (D.z j) := by
    simp only [D.colsZ j hj, Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [this]

/-- A rational vector killed by all the rows is a rational combination of the `ψ_j`. -/
theorem span_of_ker (y : ι → ℚ) (hy : ∀ b, ∑ i, (rows b i : ℚ) * y i = 0) :
    y ∈ Submodule.span ℚ (Set.range fun j : D.Z => fun i => (D.ψ j i : ℚ)) := by
  have hΔ : (D.Δ : ℚ) ≠ 0 := by exact_mod_cast D.Δ_pos.ne'
  have hzero : ∀ j ∈ D.Zᶜ, (∑ i, (D.cols j i : ℚ) * y i) = 0 := by
    intro j hj
    obtain ⟨k, hk⟩ := D.colsk j (Finset.mem_compl.mp hj)
    rw [hk]
    exact hy k
  have hyeq : y = (D.Δ : ℚ)⁻¹ • ∑ j : D.Z, y (D.z j) • fun i => (D.ψ j i : ℚ) := by
    ext i'
    have h := D.expand y i'
    have h0 : ∑ j ∈ D.Zᶜ, (∑ i, (D.cols j i : ℚ) * y i) * (D.ψ j i' : ℚ) = 0 :=
      Finset.sum_eq_zero fun j hj => by rw [hzero j hj, zero_mul]
    rw [h0, add_zero] at h
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [Finset.sum_coe_sort D.Z (fun j => y (D.z j) * (D.ψ j i' : ℚ)), ← h]
    field_simp
  rw [hyeq]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))

/-- **The decomposition `y = e + p + r`.**  See the module documentation. -/
theorem kernel_decomp (y : ι → ℝ) (N : ℕ) (hN : 0 < N) (Y : ι → ℤ) {τ Hψ : ℝ} (hτ : 0 ≤ τ)
    (hHψ : 0 ≤ Hψ) (hH : ∀ j i, |(D.ψ j i : ℝ)| ≤ Hψ)
    (hφ : ∀ j, j ∉ D.Z → |(N : ℝ) * (∑ i, (D.cols j i : ℝ) * y i) - Y j| ≤ τ) :
    ∃ e r p : ι → ℝ, y = e + p + r ∧ (∀ i, |e i| ≤ Fintype.card ι * (τ * Hψ)) ∧
      (∀ i, ∃ w : ℤ, (w : ℝ) = ((N * D.Δ : ℕ) : ℝ) * r i) ∧
      p ∈ Submodule.span ℝ (Set.range fun j : D.Z => fun i => (D.ψ j i : ℝ)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hΔ' : (0 : ℝ) < D.Δ := by exact_mod_cast D.Δ_pos
  have hNΔ : (1 : ℝ) ≤ N * D.Δ := by
    have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have h2 : (1 : ℝ) ≤ D.Δ := by exact_mod_cast D.Δ_pos
    nlinarith
  let ev : ι → ℝ := fun j => ((N : ℝ) * (∑ i, (D.cols j i : ℝ) * y i) - Y j) / (N * D.Δ)
  let rv : ι → ℝ := fun j => (Y j : ℝ) / (N * D.Δ)
  refine ⟨∑ j ∈ D.Zᶜ, ev j • fun i => (D.ψ j i : ℝ), ∑ j ∈ D.Zᶜ, rv j • fun i => (D.ψ j i : ℝ),
    (D.Δ : ℝ)⁻¹ • ∑ j : D.Z, y (D.z j) • fun i => (D.ψ j i : ℝ), ?_, ?_, ?_, ?_⟩
  · ext i'
    have h := D.expand y i'
    simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [Finset.sum_coe_sort D.Z (fun j => y (D.z j) * (D.ψ j i' : ℝ))]
    have h3 : ∑ j ∈ D.Zᶜ, ev j * (D.ψ j i' : ℝ) + ∑ j ∈ D.Zᶜ, rv j * (D.ψ j i' : ℝ) =
        (D.Δ : ℝ)⁻¹ * ∑ j ∈ D.Zᶜ, (∑ i, (D.cols j i : ℝ) * y i) * (D.ψ j i' : ℝ) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [ev, rv]
      field_simp
      ring
    have h4 : y i' = (D.Δ : ℝ)⁻¹ * ((D.Δ : ℝ) * y i') := by field_simp
    rw [h4, h]
    rw [mul_add]
    linarith
  · intro i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    calc |∑ j ∈ D.Zᶜ, ev j * (D.ψ j i : ℝ)| ≤ ∑ j ∈ D.Zᶜ, |ev j * (D.ψ j i : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ D.Zᶜ, τ * Hψ := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [abs_mul]
          refine mul_le_mul ?_ (hH j i) (abs_nonneg _) hτ
          simp only [ev]
          rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < N * D.Δ), div_le_iff₀ (by positivity)]
          exact (hφ j (Finset.mem_compl.mp hj)).trans (by nlinarith)
      _ ≤ Fintype.card ι * (τ * Hψ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ _)
            (mul_nonneg hτ hHψ)
  · intro i
    refine ⟨∑ j ∈ D.Zᶜ, Y j * D.ψ j i, ?_⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [rv]
    field_simp
  · exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))

end KerData

end Generic

section Layers

variable {ι₁ ι₂ : Type*} [Fintype ι₁] {a : Step2Algebra ι₁ ι₂}

/-- The layers of a graded subalgebra are spanned by the layers of its generators. -/
theorem GradedSubalg.layer_eq_span {W : GradedSubalg a} {κ : Type*}
    {v : κ → (ι₁ → ℚ) × (ι₂ → ℚ)} (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule) :
    W.layer₁ = Submodule.span ℚ (Set.range fun r => (v r).1) ∧
      W.layer₂ = Submodule.span ℚ (Set.range fun r => (v r).2) := by
  have hmem : ∀ r, v r ∈ W.toSubmodule := fun r => by
    rw [← hv]
    exact Submodule.subset_span ⟨r, rfl⟩
  refine ⟨le_antisymm ?_ ?_, le_antisymm ?_ ?_⟩
  · intro x hx
    have h1 : (x, (0 : ι₂ → ℚ)) ∈ Submodule.span ℚ (Set.range v) := by rw [hv]; exact hx
    have h2 := Submodule.mem_map_of_mem (f := LinearMap.fst ℚ (ι₁ → ℚ) (ι₂ → ℚ)) h1
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact h2
  · rw [Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    exact W.fst_mem (v r) (hmem r)
  · intro x hx
    have h1 : ((0 : ι₁ → ℚ), x) ∈ Submodule.span ℚ (Set.range v) := by rw [hv]; exact hx
    have h2 := Submodule.mem_map_of_mem (f := LinearMap.snd ℚ (ι₁ → ℚ) (ι₂ → ℚ)) h1
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact h2
  · rw [Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    exact W.snd_mem (v r) (hmem r)

/-- `K⁰₁` is the common kernel of the two halves of the pivot functionals of `K₁`. -/
theorem commonKernel_layer₁_iff {K : GradedSubalg a.prod} {κ : Type*}
    {v : κ → (ι₁ ⊕ ι₁ → ℚ) × (ι₂ ⊕ ι₂ → ℚ)} (hv : Submodule.span ℚ (Set.range v) = K.toSubmodule)
    (Z : Finset (ι₁ ⊕ ι₁)) (θ : ι₁ ⊕ ι₁ → ι₁ ⊕ ι₁ → ℤ)
    (hkill : ∀ j ∈ Z, ∀ k, ∑ i, (θ j i : ℚ) * (v k).1 i = 0)
    (hspan : ∀ y : ι₁ ⊕ ι₁ → ℚ, (∀ j ∈ Z, ∑ i, (θ j i : ℚ) * y i = 0) →
      y ∈ Submodule.span ℚ (Set.range fun k => (v k).1)) (k : ι₁ → ℚ) :
    k ∈ K.commonKernel.layer₁ ↔ ∀ j ∈ Z, (∑ i, (θ j (.inl i) : ℚ) * k i = 0) ∧
      ∑ i, (θ j (.inr i) : ℚ) * k i = 0 := by
  rw [GradedSubalg.mem_layer₁_commonKernel, (GradedSubalg.layer_eq_span hv).1,
    mem_span_iff_kill Z θ hkill hspan, mem_span_iff_kill Z θ hkill hspan]
  have e1 : ∀ j, ∑ i, (θ j i : ℚ) * (Sum.elim k (0 : ι₁ → ℚ)) i =
      ∑ i, (θ j (.inl i) : ℚ) * k i := by
    intro j
    simp [Fintype.sum_sum_type]
  have e2 : ∀ j, ∑ i, (θ j i : ℚ) * (Sum.elim (0 : ι₁ → ℚ) k) i =
      ∑ i, (θ j (.inr i) : ℚ) * k i := by
    intro j
    simp [Fintype.sum_sum_type]
  simp only [e1, e2]
  constructor
  · rintro ⟨h1, h2⟩ j hj
    exact ⟨h1 j hj, h2 j hj⟩
  · intro h
    exact ⟨fun j hj => (h j hj).1, fun j hj => (h j hj).2⟩

/-- `K⁰₂` is the common kernel of the two halves of the pivot functionals of `K₂`. -/
theorem commonKernel_layer₂_iff [Fintype ι₂] {K : GradedSubalg a.prod} {κ : Type*}
    {v : κ → (ι₁ ⊕ ι₁ → ℚ) × (ι₂ ⊕ ι₂ → ℚ)} (hv : Submodule.span ℚ (Set.range v) = K.toSubmodule)
    (Z : Finset (ι₂ ⊕ ι₂)) (θ : ι₂ ⊕ ι₂ → ι₂ ⊕ ι₂ → ℤ)
    (hkill : ∀ j ∈ Z, ∀ k, ∑ i, (θ j i : ℚ) * (v k).2 i = 0)
    (hspan : ∀ y : ι₂ ⊕ ι₂ → ℚ, (∀ j ∈ Z, ∑ i, (θ j i : ℚ) * y i = 0) →
      y ∈ Submodule.span ℚ (Set.range fun k => (v k).2)) (k : ι₂ → ℚ) :
    k ∈ K.commonKernel.layer₂ ↔ ∀ j ∈ Z, (∑ i, (θ j (.inl i) : ℚ) * k i = 0) ∧
      ∑ i, (θ j (.inr i) : ℚ) * k i = 0 := by
  rw [GradedSubalg.mem_layer₂_commonKernel, (GradedSubalg.layer_eq_span hv).2,
    mem_span_iff_kill Z θ hkill hspan, mem_span_iff_kill Z θ hkill hspan]
  have e1 : ∀ j, ∑ i, (θ j i : ℚ) * (Sum.elim k (0 : ι₂ → ℚ)) i =
      ∑ i, (θ j (.inl i) : ℚ) * k i := by
    intro j
    simp [Fintype.sum_sum_type]
  have e2 : ∀ j, ∑ i, (θ j i : ℚ) * (Sum.elim (0 : ι₂ → ℚ) k) i =
      ∑ i, (θ j (.inr i) : ℚ) * k i := by
    intro j
    simp [Fintype.sum_sum_type]
  simp only [e1, e2]
  constructor
  · rintro ⟨h1, h2⟩ j hj
    exact ⟨h1 j hj, h2 j hj⟩
  · intro h
    exact ⟨fun j hj => (h j hj).1, fun j hj => (h j hj).2⟩

end Layers

section OfPivot

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

/-- **The kernel pivot with bounds.**  For integer rows `rows_k` with entries of absolute value
at most `H ≥ 1`, the kernel data of `exists_pivot_int` with `Δ` and the entries of `ψ` bounded
by `n! H^n`. -/
theorem exists_kerData (rows : κ → ι → ℤ) (H : ℕ) (hH : 1 ≤ H) (hrows : ∀ k i, |rows k i| ≤ H) :
    ∃ D : KerData rows, (D.Δ : ℤ) ≤ (Fintype.card ι).factorial * (H : ℤ) ^ Fintype.card ι ∧
      ∀ j i, |D.ψ j i| ≤ (Fintype.card ι).factorial * (H : ℤ) ^ Fintype.card ι := by
  obtain ⟨Z, Δ, θ, z, hΔ, hΔb, hθb, -, hkill, -, cols, hcolZ, hcolk, hI2, -⟩ :=
    exists_pivot_int rows H hH hrows
  exact ⟨⟨Z, Δ, θ, cols, z, hΔ, hI2, hcolZ, hcolk, hkill⟩, hΔb, hθb⟩

end OfPivot

end PrimeCarleson.Proof.Fplus31
