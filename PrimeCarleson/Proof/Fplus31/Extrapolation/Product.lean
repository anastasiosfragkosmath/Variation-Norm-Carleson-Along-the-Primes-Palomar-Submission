module

public import PrimeCarleson.Proof.Fplus31.Extrapolation.Generators

/-!
# The product `g × g` and the subalgebra `K⁰` of the type II variant (the extrapolation step)

Part of the abstract extrapolation, type II variant (the extrapolation step of the iteration of
`C2/CMain.lean`, proof of [F+] Proposition 3.1). For the type II analysis the symbol lives in the
product `gr × gr` of two copies of the graded Lie algebra, with the dilation pair
`(δ_{qℓ} X, δ_{qℓ'} X)`. Over the model of `Model.lean`:

* `Step2Algebra.prod a`: the algebra `g × g` (indices `ι₁ ⊕ ι₁`, `ι₂ ⊕ ι₂`, block-diagonal
  structure constants), `Step2Algebra.br_prod`;
* `SymbolGroup.biDil s t X`: the element `(δ_s X, δ_t X)` of the group of `a.prod`;
* `GradedSubalg.commonKernel K`: for a graded subalgebra `K` of `g × g` the subalgebra
  `K⁰ = {k : (k, 0) ∈ K and (0, k) ∈ K}` of `g` (the common kernel of all the characters `θ⁰, θ¹`
  killing `K`);
* the facts used by the descending stage: `(k, 0) ∈ W₁` for `k ∈ K⁰₁` when `K = W + D × D`
  (`plusDerived_layer₁`, `mem_layer₁_commonKernel`), the exposure `([k, k'], 0) ∈ W₂`
  (`exposure_commonKernel`) and `D ⊆ K⁰₂`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

variable {ι₁ ι₂ : Type*} [Fintype ι₁]

/-- The product `g × g` of the graded step-two Lie algebra with itself. -/
def Step2Algebra.prod (a : Step2Algebra ι₁ ι₂) : Step2Algebra (ι₁ ⊕ ι₁) (ι₂ ⊕ ι₂) where
  c i j k :=
    Sum.elim
      (fun i' => Sum.elim (fun j' => Sum.elim (fun k' => a.c i' j' k') (fun _ => 0) k)
        (fun _ => 0) j)
      (fun i' => Sum.elim (fun _ => 0)
        (fun j' => Sum.elim (fun _ => 0) (fun k' => a.c i' j' k') k) j) i
  c_neg i j k := by
    rcases i with i | i <;> rcases j with j | j <;> rcases k with k | k <;>
      simp only [Sum.elim_inl, Sum.elim_inr, neg_zero] <;> exact a.c_neg _ _ _

/-- The bracket of the product acts coordinatewise on the two factors. -/
theorem Step2Algebra.br_prod {K : Type*} [Field K] (a : Step2Algebra ι₁ ι₂) (u u' v v' : ι₁ → K) :
    a.prod.br (Sum.elim u u') (Sum.elim v v') = Sum.elim (a.br u v) (a.br u' v') := by
  ext k
  rcases k with k | k
  · simp [Step2Algebra.br_apply, Fintype.sum_sum_type, Step2Algebra.prod]
  · simp [Step2Algebra.br_apply, Fintype.sum_sum_type, Step2Algebra.prod]

namespace SymbolGroup

/-- The element `(δ_s X, δ_t X)` of the group of the product `g × g`. -/
def biDil {a : Step2Algebra ι₁ ι₂} (s t : ℝ) (X : SymbolGroup a) : SymbolGroup a.prod where
  fst := Sum.elim (s • X.fst) (t • X.fst)
  snd := Sum.elim ((s ^ 2) • X.snd) ((t ^ 2) • X.snd)

end SymbolGroup

/-- The embedding of one layer into the left factor. -/
def embL {ι : Type*} : (ι → ℚ) →ₗ[ℚ] (ι ⊕ ι → ℚ) where
  toFun k := Sum.elim k 0
  map_add' x y := by
    ext i
    rcases i with i | i <;> simp
  map_smul' t x := by
    ext i
    rcases i with i | i <;> simp

/-- The embedding of one layer into the right factor. -/
def embR {ι : Type*} : (ι → ℚ) →ₗ[ℚ] (ι ⊕ ι → ℚ) where
  toFun k := Sum.elim (0 : ι → ℚ) k
  map_add' x y := by
    ext i
    rcases i with i | i <;> simp
  map_smul' t x := by
    ext i
    rcases i with i | i <;> simp

theorem embL_apply {ι : Type*} (k : ι → ℚ) : embL k = Sum.elim k 0 := rfl

theorem embR_apply {ι : Type*} (k : ι → ℚ) : embR k = Sum.elim (0 : ι → ℚ) k := rfl

variable {a : Step2Algebra ι₁ ι₂}

/-- **The subalgebra `K⁰ = {k : (k, 0) ∈ K and (0, k) ∈ K}`** of `g` attached to a graded
subalgebra `K` of `g × g`. -/
def GradedSubalg.commonKernel (K : GradedSubalg a.prod) : GradedSubalg a where
  toSubmodule := K.toSubmodule.comap ((embL (ι := ι₁)).prodMap (embL (ι := ι₂))) ⊓
    K.toSubmodule.comap ((embR (ι := ι₁)).prodMap (embR (ι := ι₂)))
  fst_mem := by
    intro w hw
    obtain ⟨hw0, hw1⟩ := hw
    refine ⟨?_, ?_⟩
    · have := K.fst_mem _ hw0
      simpa [embL_apply] using this
    · have := K.fst_mem _ hw1
      simpa [embR_apply] using this
  snd_mem := by
    intro w hw
    obtain ⟨hw0, hw1⟩ := hw
    refine ⟨?_, ?_⟩
    · have := K.snd_mem _ hw0
      simpa [embL_apply] using this
    · have := K.snd_mem _ hw1
      simpa [embR_apply] using this
  bracket_mem := by
    intro x hx y hy
    obtain ⟨hx0, hx1⟩ := hx
    obtain ⟨hy0, hy1⟩ := hy
    refine ⟨?_, ?_⟩
    · have := K.bracket_mem _ hx0 _ hy0
      simpa [embL_apply, Step2Algebra.br_prod] using this
    · have := K.bracket_mem _ hx1 _ hy1
      simpa [embR_apply, Step2Algebra.br_prod] using this

theorem GradedSubalg.mem_layer₁_commonKernel {K : GradedSubalg a.prod} {k : ι₁ → ℚ} :
    k ∈ K.commonKernel.layer₁ ↔
      Sum.elim k (0 : ι₁ → ℚ) ∈ K.layer₁ ∧ Sum.elim (0 : ι₁ → ℚ) k ∈ K.layer₁ := by
  simp [GradedSubalg.mem_layer₁, GradedSubalg.commonKernel, embL_apply, embR_apply,
    Sum.elim_zero_zero]

theorem GradedSubalg.mem_layer₂_commonKernel {K : GradedSubalg a.prod} {k : ι₂ → ℚ} :
    k ∈ K.commonKernel.layer₂ ↔
      Sum.elim k (0 : ι₂ → ℚ) ∈ K.layer₂ ∧ Sum.elim (0 : ι₂ → ℚ) k ∈ K.layer₂ := by
  simp [GradedSubalg.mem_layer₂, GradedSubalg.commonKernel, embL_apply, embR_apply,
    Sum.elim_zero_zero]

/-- `K = W + D × D` has the same layer one as `W`. -/
theorem GradedSubalg.plusDerived_layer₁ (W : GradedSubalg a.prod) :
    W.plusDerived.layer₁ = W.layer₁ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx
    have hz1 : z.1 = 0 := by simpa using (Submodule.mem_prod.mp hz).1
    have hx1 : x = y.1 := by
      have := congrArg Prod.fst hyz
      simpa [hz1] using this.symm
    rw [GradedSubalg.mem_layer₁, hx1]
    exact W.fst_mem y hy
  · intro x hx
    exact W.le_plusDerived hx

/-- **Exposure.** For `K⁰` of `K = W + D × D`: if `k, k' ∈ K⁰₁` then `([k, k'], 0)` and
`(0, [k, k'])` lie in `W₂`; the reason is `(k, 0), (k', 0) ∈ W₁` and `β(W₁, W₁) ⊆ W₂`. -/
theorem GradedSubalg.exposure_commonKernel (W : GradedSubalg a.prod) {k k' : ι₁ → ℚ}
    (hk : k ∈ W.plusDerived.commonKernel.layer₁) (hk' : k' ∈ W.plusDerived.commonKernel.layer₁) :
    Sum.elim (a.br k k') (0 : ι₂ → ℚ) ∈ W.layer₂ ∧
      Sum.elim (0 : ι₂ → ℚ) (a.br k k') ∈ W.layer₂ := by
  rw [GradedSubalg.mem_layer₁_commonKernel, GradedSubalg.plusDerived_layer₁] at hk hk'
  refine ⟨?_, ?_⟩
  · have := W.br_mem_layer₂ hk.1 hk'.1
    simpa [Step2Algebra.br_prod] using this
  · have := W.br_mem_layer₂ hk.2 hk'.2
    simpa [Step2Algebra.br_prod] using this

/-- `D ⊆ K⁰₂` for `K = W + D × D`. -/
theorem GradedSubalg.derived_le_commonKernel (W : GradedSubalg a.prod) :
    derived a ≤ W.plusDerived.commonKernel.layer₂ := by
  rw [derived, Submodule.span_le]
  rintro _ ⟨x, y, rfl⟩
  rw [SetLike.mem_coe, GradedSubalg.mem_layer₂_commonKernel]
  refine ⟨GradedSubalg.mem_layer₂.mpr ?_, GradedSubalg.mem_layer₂.mpr ?_⟩
  · have := br_mem_derived (a := a.prod) (Sum.elim x (0 : ι₁ → ℚ)) (Sum.elim y (0 : ι₁ → ℚ))
    rw [Step2Algebra.br_prod] at this
    simpa using W.mem_plusDerived_of_derived this
  · have := br_mem_derived (a := a.prod) (Sum.elim (0 : ι₁ → ℚ) x) (Sum.elim (0 : ι₁ → ℚ) y)
    rw [Step2Algebra.br_prod] at this
    simpa using W.mem_plusDerived_of_derived this

end PrimeCarleson.Proof.Fplus31
