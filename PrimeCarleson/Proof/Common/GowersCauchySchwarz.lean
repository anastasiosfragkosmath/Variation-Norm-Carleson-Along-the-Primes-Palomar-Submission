module

public import PrimeCarleson.Frozen.GowersNormSpec
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# The Gowers–Cauchy–Schwarz inequality on `ℤ`

The Gowers inner product of a family `(F_w)_{w ∈ {0,1}^s}` of finitely supported functions
`ℤ →₀ ℂ`,
`⟨(F_w)⟩_{U^s} = ∑_{x, h₁, …, h_s ∈ ℤ} ∏_w C^{|w|} F_w (x + w · h)` (`C` = complex
conjugation), as in the lemma `CauchySchwarzGowers` of [F+] (L531-L535) and its use in the proof
of the `U^3` bound (L2145-L2147), together with the norm properties of the Gowers norm (L517,
L520-L540).  Source: [F+] `CauchySchwarzGowers`, L531–L535; [F+], L2145–L2151; [F+]
`sub:gowers_norms`, L517.

* `gowersInner s F`, `gowersTerm s F x h`: the inner product (a `tsum` over
  `ℤ × (Fin s → ℤ)`) and its summand; `gowersTerm_support_finite` says the summand has finite
  support;
* `gowersTerm_const`, `gowersInner_const_eq`, `gowersNorm_pow_eq`: for the
  constant family `F_w = f` the summand is `PrimeCarleson.multDiff s h f x`, so the inner
  product is the sum defining `PrimeCarleson.gowersNorm s f` (the `2^s`-th power of the norm);
  the vertex `w` is conjugated `|w|` times, the last coordinate of `h` being the outermost
  conjugation of the recursion of `multDiff`;
* `norm_gowersInner_le_prod_gowersNorm`: **Gowers–Cauchy–Schwarz**,
  `‖⟨(F_w)⟩_{U^s}‖ ≤ ∏_w ‖F_w‖_{U^s}` for every `s ≥ 1`;
* `gowersNorm_add_le`, `gowersNorm_smul`: the triangle inequality and homogeneity of
  `‖·‖_{U^s}`.

Proof: induction on `s`.  The last coordinate is peeled off
(`⟨F⟩_{s+1} = ∑_t ⟨F(·,0) conj F(·,1)(· + t)⟩_s`), the induction hypothesis is applied to every
`t`, Hölder's inequality in `t` (for `2^s` functions, proved from the Cauchy–Schwarz inequality
by induction on `s`) separates the vertices, and Cauchy–Schwarz in the other variables bounds
the resulting two-function inner products by the `U^{s+1}` norms.
-/

@[expose] public noncomputable section

open scoped ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Common


/-- The `n`-fold complex conjugate `C^n z`. -/
def gowersConjPow (n : ℕ) (z : ℂ) : ℂ := (starRingEnd ℂ)^[n] z

/-- `C^0` is the identity. -/
@[simp] theorem gowersConjPow_zero (z : ℂ) : gowersConjPow 0 z = z := rfl

/-- `C^{n+1} z = conj (C^n z)`. -/
theorem gowersConjPow_succ (n : ℕ) (z : ℂ) : gowersConjPow (n + 1) z = conj (gowersConjPow n z) :=
  Function.iterate_succ_apply' _ _ _

/-- `C^n` is multiplicative. -/
theorem gowersConjPow_mul (n : ℕ) (a b : ℂ) :
    gowersConjPow n (a * b) = gowersConjPow n a * gowersConjPow n b := by
  induction n with
  | zero => rfl
  | succ n ih => rw [gowersConjPow_succ, gowersConjPow_succ, gowersConjPow_succ, ih, map_mul]

/-- `C^n` is additive. -/
theorem gowersConjPow_add (n : ℕ) (a b : ℂ) :
    gowersConjPow n (a + b) = gowersConjPow n a + gowersConjPow n b := by
  induction n with
  | zero => rfl
  | succ n ih => rw [gowersConjPow_succ, gowersConjPow_succ, gowersConjPow_succ, ih, map_add]

/-- `C^n` commutes with complex conjugation. -/
theorem gowersConjPow_conj (n : ℕ) (z : ℂ) :
    gowersConjPow n (conj z) = conj (gowersConjPow n z) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [gowersConjPow_succ, gowersConjPow_succ, ih]

/-- `C^n z = 0` iff `z = 0`. -/
@[simp] theorem gowersConjPow_eq_zero_iff (n : ℕ) (z : ℂ) : gowersConjPow n z = 0 ↔ z = 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [gowersConjPow_succ, map_eq_zero, ih]

/-- `C^n 0 = 0`. -/
@[simp] theorem gowersConjPow_zero_right (n : ℕ) : gowersConjPow n 0 = 0 :=
  (gowersConjPow_eq_zero_iff n 0).2 rfl

/-- The weight `|w|` (number of ones) of a vertex `w ∈ {0,1}^s` of the cube. -/
def vertexWeight {s : ℕ} (w : Fin s → Fin 2) : ℕ := ∑ i, (w i : ℕ)

/-- The point `w · h = ∑ᵢ wᵢ hᵢ` of `ℤ`. -/
def cubePoint {s : ℕ} (w : Fin s → Fin 2) (h : Fin s → ℤ) : ℤ := ∑ i, ((w i : ℕ) : ℤ) * h i

/-- The summand of the Gowers inner product at `(x, h)`: `∏_w C^{|w|} F_w (x + w · h)`. -/
def gowersTerm (s : ℕ) (F : (Fin s → Fin 2) → ℤ →₀ ℂ) (x : ℤ) (h : Fin s → ℤ) : ℂ :=
  ∏ w, gowersConjPow (vertexWeight w) (F w (x + cubePoint w h))

/-- The Gowers inner product `∑_{x, h₁, …, h_s ∈ ℤ} ∏_{w ∈ {0,1}^s} C^{|w|} F_w (x + w · h)`
of a family of finitely supported functions on `ℤ` indexed by the vertices of the cube. -/
def gowersInner (s : ℕ) (F : (Fin s → Fin 2) → ℤ →₀ ℂ) : ℂ :=
  ∑' p : ℤ × (Fin s → ℤ), gowersTerm s F p.1 p.2

namespace GowersCS

/-- The weight of a vertex with an appended last coordinate. -/
theorem vertexWeight_snoc {s : ℕ} (w : Fin s → Fin 2) (ε : Fin 2) :
    vertexWeight (Fin.snoc (α := fun _ => Fin 2) w ε) = vertexWeight w + (ε : ℕ) := by
  simp [vertexWeight, Fin.sum_univ_castSucc]

/-- The point `w · h` of a vertex with an appended last coordinate. -/
theorem cubePoint_snoc {s : ℕ} (w : Fin s → Fin 2) (ε : Fin 2) (h : Fin (s + 1) → ℤ) :
    cubePoint (Fin.snoc (α := fun _ => Fin 2) w ε) h
      = cubePoint w (Fin.init h) + ((ε : ℕ) : ℤ) * h (Fin.last s) := by
  simp [cubePoint, Fin.sum_univ_castSucc, Fin.init]

/-- A product over the `(s+1)`-cube splits along the last coordinate. -/
theorem prod_cube_succ {M : Type*} [CommMonoid M] {s : ℕ} (φ : (Fin (s + 1) → Fin 2) → M) :
    ∏ w, φ w = (∏ w : Fin s → Fin 2, φ (Fin.snoc (α := fun _ => Fin 2) w 0)) *
      ∏ w : Fin s → Fin 2, φ (Fin.snoc (α := fun _ => Fin 2) w 1) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (s + 1) => Fin 2)).prod_comp, Fintype.prod_prod_type,
    Fin.prod_univ_two]
  rfl

/-- The face `w ↦ F (w, ε)` of a family on the `(s+1)`-cube. -/
def face {s : ℕ} (F : (Fin (s + 1) → Fin 2) → ℤ →₀ ℂ) (ε : Fin 2) :
    (Fin s → Fin 2) → ℤ →₀ ℂ :=
  fun w => F (Fin.snoc (α := fun _ => Fin 2) w ε)

/-- The summand for the `(s+1)`-cube in terms of the two faces of the family. -/
theorem gowersTerm_succ {s : ℕ} (F : (Fin (s + 1) → Fin 2) → ℤ →₀ ℂ) (x : ℤ)
    (h : Fin (s + 1) → ℤ) :
    gowersTerm (s + 1) F x h = gowersTerm s (face F 0) x (Fin.init h) *
      conj (gowersTerm s (face F 1) (x + h (Fin.last s)) (Fin.init h)) := by
  unfold gowersTerm
  rw [prod_cube_succ, map_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    simp [face, vertexWeight_snoc, cubePoint_snoc]
  · refine Finset.prod_congr rfl fun w _ => ?_
    simp only [face, vertexWeight_snoc, cubePoint_snoc]
    have : x + (cubePoint w (Fin.init h) + (((1 : Fin 2) : ℕ) : ℤ) * h (Fin.last s))
        = x + h (Fin.last s) + cubePoint w (Fin.init h) := by simp; ring
    rw [this]
    simp [gowersConjPow_succ]

end GowersCS

/-- The summand for the constant family `F_w = f` is the iterated difference `Δ_h f (x)`. -/
theorem gowersTerm_const (s : ℕ) (f : ℤ →₀ ℂ) (x : ℤ) (h : Fin s → ℤ) :
    gowersTerm s (fun _ => f) x h = PrimeCarleson.multDiff s h f x := by
  induction s generalizing x with
  | zero => simp [gowersTerm, PrimeCarleson.multDiff, vertexWeight, cubePoint]
  | succ s ih =>
    rw [GowersCS.gowersTerm_succ, PrimeCarleson.multDiff]
    exact congrArg₂ _ (ih _ _) (congrArg _ (ih _ _))

namespace GowersCS

/-- A function on a type with finite support is summable. -/
theorem summable_of_finite_support' {α M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    {f : α → M} (hf : (Function.support f).Finite) : Summable f :=
  summable_of_hasFiniteSupport hf

/-- The support of a finitely supported function is finite. -/
theorem finsupp_support_finite (f : ℤ →₀ ℂ) : (Function.support f).Finite := by
  rw [Finsupp.fun_support_eq]
  exact f.support.finite_toSet

/-- `eᵢ · h = hᵢ`. -/
theorem cubePoint_single {s : ℕ} (i : Fin s) (h : Fin s → ℤ) :
    cubePoint (Pi.single i (1 : Fin 2)) h = h i := by
  classical
  simp [cubePoint, Pi.single_apply, apply_ite]

end GowersCS

/-- The summand of the Gowers inner product has finite support (all `2^s` values
`F_w (x + w · h)` must be nonzero, in particular those at `w = 0` and `w = eᵢ`). -/
theorem gowersTerm_support_finite (s : ℕ) (F : (Fin s → Fin 2) → ℤ →₀ ℂ) :
    (Function.support fun p : ℤ × (Fin s → ℤ) => gowersTerm s F p.1 p.2).Finite := by
  classical
  let ψ : ℤ × (Fin s → ℤ) → ℤ × (Fin s → ℤ) := fun p => (p.1, fun i => p.1 + p.2 i)
  have hψ : Function.Injective ψ := by
    intro p q h
    simp only [ψ, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    refine Prod.ext h1 (funext fun i => ?_)
    have := congrFun h2 i
    simp only [h1, add_right_inj] at this
    exact this
  have hT : (Function.support (F 0) ×ˢ
      Set.pi Set.univ (fun i => Function.support (F (Pi.single i 1)))).Finite :=
    (GowersCS.finsupp_support_finite _).prod
      (Set.Finite.pi fun i => GowersCS.finsupp_support_finite _)
  have hsub : ψ '' Function.support (fun p : ℤ × (Fin s → ℤ) => gowersTerm s F p.1 p.2) ⊆
      Function.support (F 0) ×ˢ
        Set.pi Set.univ (fun i => Function.support (F (Pi.single i 1))) := by
    rintro _ ⟨⟨x, h⟩, hp, rfl⟩
    have hne : gowersTerm s F x h ≠ 0 := hp
    unfold gowersTerm at hne
    have key := Finset.prod_ne_zero_iff.mp hne
    refine ⟨?_, ?_⟩
    · have h0 := key 0 (Finset.mem_univ _)
      simpa [vertexWeight, cubePoint] using h0
    · intro i _
      have hi := key (Pi.single i 1) (Finset.mem_univ _)
      simpa [vertexWeight, GowersCS.cubePoint_single, ψ] using hi
  exact Set.Finite.of_finite_image (hT.subset hsub) hψ.injOn

namespace GowersCS

/-- A slice of a finitely supported function on a product is finitely supported. -/
theorem support_slice_finite {α β : Type*} (g : α × β → ℂ) (hg : (Function.support g).Finite)
    (a : α) : (Function.support fun b => g (a, b)).Finite :=
  Set.Finite.preimage (f := fun b : β => (a, b)) (fun _ _ _ _ h => (Prod.mk.inj h).2) hg

/-- The slice of a finitely supported function on a product in the other variable. -/
theorem support_slice_finite' {α β : Type*} (g : α × β → ℂ) (hg : (Function.support g).Finite)
    (b : β) : (Function.support fun a => g (a, b)).Finite :=
  Set.Finite.preimage (f := fun a : α => (a, b)) (fun _ _ _ _ h => (Prod.mk.inj h).1) hg

/-- Fubini for finitely supported functions, along an equivalence with a product. -/
theorem tsum_equiv_prod {γ α β : Type*} (e : γ ≃ α × β) (f : γ → ℂ)
    (hf : (Function.support f).Finite) :
    ∑' c, f c = ∑' a, ∑' b, f (e.symm (a, b)) := by
  have hs : (Function.support fun q : α × β => f (e.symm q)).Finite :=
    Set.Finite.preimage (f := e.symm) e.symm.injective.injOn hf
  rw [← e.symm.tsum_eq f]
  exact Summable.tsum_prod' (summable_of_finite_support' hs)
    fun a => summable_of_finite_support' (support_slice_finite _ hs a)

/-- `(corr f g t) x = f x * conj (g (x + t))`. -/
def corr (f g : ℤ →₀ ℂ) (t : ℤ) : ℤ →₀ ℂ :=
  Finsupp.onFinset f.support (fun x => f x * conj (g (x + t))) (by
    intro a ha
    rw [Finsupp.mem_support_iff]
    intro h0
    exact ha (by rw [h0, zero_mul]))

/-- Pointwise formula for `corr`. -/
@[simp] theorem corr_apply (f g : ℤ →₀ ℂ) (t x : ℤ) :
    corr f g t x = f x * conj (g (x + t)) := rfl

/-- The family `w ↦ F(w,0) · conj (F(w,1)(· + t))` on the `s`-cube. -/
def corrFamily {s : ℕ} (F : (Fin (s + 1) → Fin 2) → ℤ →₀ ℂ) (t : ℤ) :
    (Fin s → Fin 2) → ℤ →₀ ℂ :=
  fun w => corr (face F 0 w) (face F 1 w) t

/-- The summand of `corrFamily F t` in terms of the two faces of `F`. -/
theorem gowersTerm_corrFamily {s : ℕ} (F : (Fin (s + 1) → Fin 2) → ℤ →₀ ℂ) (t x : ℤ)
    (h : Fin s → ℤ) :
    gowersTerm s (corrFamily F t) x h =
      gowersTerm s (face F 0) x h * conj (gowersTerm s (face F 1) (x + t) h) := by
  unfold gowersTerm
  rw [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  simp only [corrFamily, corr_apply, gowersConjPow_mul, gowersConjPow_conj]
  rw [add_right_comm x (cubePoint w h) t]

/-- Splitting off the last coordinate. -/
def peelEquiv (s : ℕ) : ℤ × (Fin (s + 1) → ℤ) ≃ ℤ × (ℤ × (Fin s → ℤ)) where
  toFun p := (p.2 (Fin.last s), (p.1, Fin.init p.2))
  invFun q := (q.2.1, Fin.snoc (α := fun _ => ℤ) q.2.2 q.1)
  left_inv p := by simp [Fin.snoc_init_self]
  right_inv q := by simp

/-- Peeling the last coordinate: `⟨F⟩_{s+1} = ∑_t ⟨F(·,0) conj F(·,1)(· + t)⟩_s`. -/
theorem gowersInner_succ_eq_tsum {s : ℕ} (F : (Fin (s + 1) → Fin 2) → ℤ →₀ ℂ) :
    gowersInner (s + 1) F = ∑' t : ℤ, gowersInner s (corrFamily F t) := by
  unfold gowersInner
  rw [tsum_equiv_prod (peelEquiv s) _ (gowersTerm_support_finite _ _)]
  refine tsum_congr fun t => tsum_congr fun b => ?_
  simp only [peelEquiv, Equiv.coe_fn_symm_mk, gowersTerm_succ, Fin.init_snoc, Fin.snoc_last,
    gowersTerm_corrFamily]

/-- The double sum `∑_{x,t} a(x) conj (b(x+t)) = (∑ a) · conj (∑ b)` for finitely supported
`a, b : ℤ → ℂ`. -/
theorem tsum_prod_mul_conj_shift (a b : ℤ → ℂ) (ha : (Function.support a).Finite)
    (hb : (Function.support b).Finite) :
    ∑' p : ℤ × ℤ, a p.1 * conj (b (p.1 + p.2)) = (∑' x, a x) * conj (∑' y, b y) := by
  have hfin : (Function.support fun p : ℤ × ℤ => a p.1 * conj (b (p.1 + p.2))).Finite := by
    let ψ : ℤ × ℤ → ℤ × ℤ := fun p => (p.1, p.1 + p.2)
    have hψ : Function.Injective ψ := by
      intro p q h
      simp only [ψ, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      refine Prod.ext h1 ?_
      rw [h1] at h2
      exact add_left_cancel h2
    refine Set.Finite.of_finite_image
      ((ha.prod hb).subset ?_) hψ.injOn
    rintro _ ⟨⟨x, t⟩, hp, rfl⟩
    have hne : a x * conj (b (x + t)) ≠ 0 := hp
    exact ⟨left_ne_zero_of_mul hne, by simpa using right_ne_zero_of_mul hne⟩
  rw [Summable.tsum_prod' (summable_of_finite_support' hfin)
    fun x => summable_of_finite_support' (support_slice_finite _ hfin x)]
  have : ∀ x : ℤ, ∑' t : ℤ, a x * conj (b (x + t)) = a x * conj (∑' y, b y) := by
    intro x
    rw [tsum_mul_left, ← Complex.conj_tsum]
    congr 2
    exact (Equiv.addLeft x).tsum_eq b
  simp only [this]
  rw [tsum_mul_right]

/-- Splitting off the last coordinate, with the first `s` coordinates outermost. -/
def peelEquiv2 (s : ℕ) : ℤ × (Fin (s + 1) → ℤ) ≃ (Fin s → ℤ) × (ℤ × ℤ) where
  toFun p := (Fin.init p.2, (p.1, p.2 (Fin.last s)))
  invFun q := (q.2.1, Fin.snoc (α := fun _ => ℤ) q.1 q.2.2)
  left_inv p := by simp [Fin.snoc_init_self]
  right_inv q := by simp

/-- The partial sum over `x` of the summand, for fixed `h`. -/
def partialSum (s : ℕ) (F : (Fin s → Fin 2) → ℤ →₀ ℂ) (h : Fin s → ℤ) : ℂ :=
  ∑' x : ℤ, gowersTerm s F x h

/-- Peeling the last coordinate: `⟨F⟩_{s+1} = ∑_h A_0(h) conj A_1(h)` with `A_ε(h) = ∑ₓ
F(·,ε)-summand`. -/
theorem gowersInner_succ_eq_tsum_partialSum {s : ℕ} (F : (Fin (s + 1) → Fin 2) → ℤ →₀ ℂ) :
    gowersInner (s + 1) F =
      ∑' h : Fin s → ℤ, partialSum s (face F 0) h * conj (partialSum s (face F 1) h) := by
  unfold gowersInner
  rw [tsum_equiv_prod (peelEquiv2 s) _ (gowersTerm_support_finite _ _)]
  refine tsum_congr fun h => ?_
  have h0 := support_slice_finite' (fun p : ℤ × (Fin s → ℤ) => gowersTerm s (face F 0) p.1 p.2)
    (gowersTerm_support_finite _ _) h
  have h1 := support_slice_finite' (fun p : ℤ × (Fin s → ℤ) => gowersTerm s (face F 1) p.1 p.2)
    (gowersTerm_support_finite _ _) h
  unfold partialSum
  rw [← tsum_prod_mul_conj_shift _ _ h0 h1]
  refine tsum_congr fun q => ?_
  simp only [peelEquiv2, Equiv.coe_fn_symm_mk, gowersTerm_succ, Fin.init_snoc, Fin.snoc_last]

/-- Cauchy–Schwarz for finitely supported sequences. -/
theorem norm_tsum_mul_conj_sq_le {ι : Type*} (u v : ι → ℂ) (hu : (Function.support u).Finite)
    (hv : (Function.support v).Finite) :
    ‖∑' i, u i * conj (v i)‖ ^ 2 ≤ (∑' i, ‖u i‖ ^ 2) * ∑' i, ‖v i‖ ^ 2 := by
  classical
  set T : Finset ι := hu.toFinset ∪ hv.toFinset with hT
  have hu' : ∀ i ∉ T, u i = 0 := by
    intro i hi
    by_contra h
    exact hi (Finset.mem_union_left _ (hu.mem_toFinset.mpr h))
  have hv' : ∀ i ∉ T, v i = 0 := by
    intro i hi
    by_contra h
    exact hi (Finset.mem_union_right _ (hv.mem_toFinset.mpr h))
  have e1 : ∑' i, u i * conj (v i) = ∑ i ∈ T, u i * conj (v i) := by
    refine tsum_eq_sum' fun i hi => ?_
    by_contra hT'
    exact hi (by simp [hu' i hT'])
  have e2 : ∑' i, ‖u i‖ ^ 2 = ∑ i ∈ T, ‖u i‖ ^ 2 := by
    refine tsum_eq_sum' fun i hi => ?_
    by_contra hT'
    exact hi (by simp [hu' i hT'])
  have e3 : ∑' i, ‖v i‖ ^ 2 = ∑ i ∈ T, ‖v i‖ ^ 2 := by
    refine tsum_eq_sum' fun i hi => ?_
    by_contra hT'
    exact hi (by simp [hv' i hT'])
  rw [e1, e2, e3]
  calc ‖∑ i ∈ T, u i * conj (v i)‖ ^ 2 ≤ (∑ i ∈ T, ‖u i‖ * ‖v i‖) ^ 2 := by
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq T (fun i => ‖u i‖) fun i => ‖v i‖

/-- The family on the `(s+1)`-cube that ignores the last coordinate. -/
def dup {s : ℕ} (F : (Fin s → Fin 2) → ℤ →₀ ℂ) : (Fin (s + 1) → Fin 2) → ℤ →₀ ℂ :=
  fun w => F (Fin.init w)

/-- The faces of `dup F` are both `F`. -/
theorem face_dup {s : ℕ} (F : (Fin s → Fin 2) → ℤ →₀ ℂ) (ε : Fin 2) : face (dup F) ε = F := by
  funext w
  simp [face, dup]

/-- The partial sums `h ↦ ∑ₓ gowersTerm F x h` are finitely supported. -/
theorem partialSum_support_finite (s : ℕ) (F : (Fin s → Fin 2) → ℤ →₀ ℂ) :
    (Function.support (partialSum s F)).Finite := by
  refine ((gowersTerm_support_finite s F).image Prod.snd).subset ?_
  intro h hh
  by_contra hcon
  apply hh
  have : ∀ x, gowersTerm s F x h = 0 := by
    intro x
    by_contra hx
    exact hcon ⟨(x, h), hx, rfl⟩
  simp [partialSum, this]

/-- For a family constant in the last coordinate the inner product is a sum of squares. -/
theorem gowersInner_dup {s : ℕ} (F : (Fin s → Fin 2) → ℤ →₀ ℂ) :
    gowersInner (s + 1) (dup F) = ((∑' h, ‖partialSum s F h‖ ^ 2 : ℝ) : ℂ) := by
  rw [gowersInner_succ_eq_tsum_partialSum, Complex.ofReal_tsum]
  refine tsum_congr fun h => ?_
  rw [face_dup, face_dup, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- Norm of the inner product of a family constant in the last coordinate. -/
theorem norm_gowersInner_dup {s : ℕ} (F : (Fin s → Fin 2) → ℤ →₀ ℂ) :
    ‖gowersInner (s + 1) (dup F)‖ = ∑' h, ‖partialSum s F h‖ ^ 2 := by
  rw [gowersInner_dup, Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun _ => sq_nonneg _)]

/-- Cauchy–Schwarz in the last variable: symmetrization of a family in its last coordinate. -/
theorem norm_gowersInner_sq_le {s : ℕ} (F : (Fin (s + 1) → Fin 2) → ℤ →₀ ℂ) :
    ‖gowersInner (s + 1) F‖ ^ 2 ≤
      ‖gowersInner (s + 1) (dup (face F 0))‖ * ‖gowersInner (s + 1) (dup (face F 1))‖ := by
  rw [norm_gowersInner_dup, norm_gowersInner_dup, gowersInner_succ_eq_tsum_partialSum]
  exact norm_tsum_mul_conj_sq_le _ _ (partialSum_support_finite _ _)
    (partialSum_support_finite _ _)

/-- The family on the `(s+1)`-cube equal to `f` on the face `w_{s+1} = 0` and to `g` on the face
`w_{s+1} = 1`. -/
def pairFamily (s : ℕ) (f g : ℤ →₀ ℂ) : (Fin (s + 1) → Fin 2) → ℤ →₀ ℂ :=
  fun w => if w (Fin.last s) = 0 then f else g

/-- The face `w_{s+1} = 0` of `pairFamily s f g` is constant `f`. -/
theorem face_pairFamily_zero (s : ℕ) (f g : ℤ →₀ ℂ) :
    face (pairFamily s f g) 0 = fun _ => f := by
  funext w
  simp [face, pairFamily]

/-- The face `w_{s+1} = 1` of `pairFamily s f g` is constant `g`. -/
theorem face_pairFamily_one (s : ℕ) (f g : ℤ →₀ ℂ) :
    face (pairFamily s f g) 1 = fun _ => g := by
  funext w
  simp [face, pairFamily]

/-- The Gowers inner product of a constant family on the `(r+1)`-cube is a nonnegative real. -/
theorem gowersInner_const_succ (r : ℕ) (φ : ℤ →₀ ℂ) :
    gowersInner (r + 1) (fun _ => φ) =
      ((∑' h, ‖partialSum r (fun _ => φ) h‖ ^ 2 : ℝ) : ℂ) :=
  gowersInner_dup (fun _ => φ)

end GowersCS

/-- The Gowers inner product of the constant family `F_w = f` is the sum `∑_{x,h} Δ_h f(x)`
defining the Gowers norm (`PrimeCarleson.gowersNorm`). -/
theorem gowersInner_const_eq (s : ℕ) (f : ℤ →₀ ℂ) :
    gowersInner s (fun _ => f) =
      ∑' p : ℤ × (Fin s → ℤ), PrimeCarleson.multDiff s p.2 f p.1 :=
  tsum_congr fun p => gowersTerm_const s f p.1 p.2

/-- `‖f‖_{U^s}^{2^s} = ‖⟨f, …, f⟩_{U^s}‖`. -/
theorem gowersNorm_pow_eq (s : ℕ+) (f : ℤ →₀ ℂ) :
    PrimeCarleson.gowersNorm s f ^ (2 ^ (s : ℕ)) = ‖gowersInner s (fun _ => f)‖ := by
  obtain ⟨-, h0, h⟩ := PrimeCarleson.gowersNorm_spec s f
  rw [gowersInner_const_eq, ← h, norm_pow, Complex.norm_real, Real.norm_of_nonneg h0]

namespace GowersCS

/-- The Gowers norm indexed by `r = s - 1`. -/
def nm (r : ℕ) (f : ℤ →₀ ℂ) : ℝ := PrimeCarleson.gowersNorm (Nat.succPNat r) f

/-- `nm r f ≥ 0`. -/
theorem nm_nonneg (r : ℕ) (f : ℤ →₀ ℂ) : 0 ≤ nm r f :=
  (PrimeCarleson.gowersNorm_spec (Nat.succPNat r) f).2.1

/-- `nm r f ^ 2^(r+1) = ‖⟨f, …, f⟩_{U^{r+1}}‖`. -/
theorem nm_pow (r : ℕ) (f : ℤ →₀ ℂ) :
    nm r f ^ (2 ^ (r + 1)) = ‖gowersInner (r + 1) (fun _ => f)‖ :=
  gowersNorm_pow_eq (Nat.succPNat r) f

/-- The summand of the zero family vanishes. -/
theorem gowersTerm_zero (s : ℕ) (x : ℤ) (h : Fin s → ℤ) :
    gowersTerm s (fun _ => (0 : ℤ →₀ ℂ)) x h = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ (0 : Fin s → Fin 2)) (by simp)

/-- The Gowers inner product of the zero family vanishes. -/
theorem gowersInner_zero (s : ℕ) : gowersInner s (fun _ => (0 : ℤ →₀ ℂ)) = 0 := by
  simp [gowersInner, gowersTerm_zero]

/-- `nm r 0 = 0`. -/
theorem nm_zero (r : ℕ) : nm r 0 = 0 := by
  have h := nm_pow r 0
  rw [gowersInner_zero, norm_zero] at h
  exact pow_eq_zero_iff (by positivity) |>.mp h

/-- Hölder's inequality for the product of `2^j` nonnegative functions, finite sums. -/
theorem sum_prod_cube_pow_le {ι : Type*} (T : Finset ι) (j : ℕ) (a : (Fin j → Fin 2) → ι → ℝ)
    (ha : ∀ w t, 0 ≤ a w t) :
    (∑ t ∈ T, ∏ w, a w t) ^ (2 ^ j) ≤ ∏ w, ∑ t ∈ T, a w t ^ (2 ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    set X : ι → ℝ := fun t => ∏ w : Fin j → Fin 2, a (Fin.snoc (α := fun _ => Fin 2) w 0) t
      with hXdef
    set Y : ι → ℝ := fun t => ∏ w : Fin j → Fin 2, a (Fin.snoc (α := fun _ => Fin 2) w 1) t
      with hYdef
    have hXY : ∀ t, ∏ w, a w t = X t * Y t := fun t => prod_cube_succ (fun w => a w t)
    have hX0 : ∀ t, 0 ≤ X t := fun t => Finset.prod_nonneg fun w _ => ha _ _
    have hY0 : ∀ t, 0 ≤ Y t := fun t => Finset.prod_nonneg fun w _ => ha _ _
    have ihX := ih (fun w t => a (Fin.snoc (α := fun _ => Fin 2) w 0) t ^ 2)
      (fun w t => sq_nonneg _)
    have ihY := ih (fun w t => a (Fin.snoc (α := fun _ => Fin 2) w 1) t ^ 2)
      (fun w t => sq_nonneg _)
    have hX2 : ∀ t, X t ^ 2 = ∏ w : Fin j → Fin 2,
        a (Fin.snoc (α := fun _ => Fin 2) w 0) t ^ 2 := fun t => (Finset.prod_pow _ _ _).symm
    have hY2 : ∀ t, Y t ^ 2 = ∏ w : Fin j → Fin 2,
        a (Fin.snoc (α := fun _ => Fin 2) w 1) t ^ 2 := fun t => (Finset.prod_pow _ _ _).symm
    simp_rw [← hX2] at ihX
    simp_rw [← hY2] at ihY
    simp_rw [← pow_mul, ← pow_succ'] at ihX ihY
    have cs := Finset.sum_mul_sq_le_sq_mul_sq T X Y
    rw [prod_cube_succ (fun w => ∑ t ∈ T, a w t ^ 2 ^ (j + 1))]
    simp_rw [hXY]
    calc (∑ t ∈ T, X t * Y t) ^ 2 ^ (j + 1)
        = ((∑ t ∈ T, X t * Y t) ^ 2) ^ 2 ^ j := by rw [← pow_mul, ← pow_succ']
      _ ≤ ((∑ t ∈ T, X t ^ 2) * ∑ t ∈ T, Y t ^ 2) ^ 2 ^ j :=
          pow_le_pow_left₀ (sq_nonneg _) cs _
      _ = (∑ t ∈ T, X t ^ 2) ^ 2 ^ j * (∑ t ∈ T, Y t ^ 2) ^ 2 ^ j := mul_pow _ _ _
      _ ≤ _ := mul_le_mul ihX ihY (pow_nonneg (Finset.sum_nonneg fun t _ => sq_nonneg _) _)
          (Finset.prod_nonneg fun w _ => Finset.sum_nonneg fun t _ => pow_nonneg (ha _ _) _)

/-- Hölder's inequality for the product of `2^j` nonnegative finitely supported functions. -/
theorem tsum_prod_cube_pow_le {ι : Type*} (j : ℕ) (a : (Fin j → Fin 2) → ι → ℝ)
    (ha : ∀ w t, 0 ≤ a w t) (hfin : ∀ w, (Function.support (a w)).Finite) :
    (∑' t, ∏ w, a w t) ^ (2 ^ j) ≤ ∏ w, ∑' t, a w t ^ (2 ^ j) := by
  classical
  set T : Finset ι := Finset.univ.biUnion fun w => (hfin w).toFinset with hT
  have hT0 : ∀ w, ∀ t ∉ T, a w t = 0 := by
    intro w t ht
    by_contra h
    exact ht (Finset.mem_biUnion.mpr ⟨w, Finset.mem_univ _, (hfin w).mem_toFinset.mpr h⟩)
  have e1 : ∑' t, ∏ w, a w t = ∑ t ∈ T, ∏ w, a w t := by
    refine tsum_eq_sum' fun t ht => ?_
    by_contra hTt
    exact ht (Finset.prod_eq_zero (Finset.mem_univ 0) (hT0 _ t hTt))
  have e2 : ∀ w, ∑' t, a w t ^ (2 ^ j) = ∑ t ∈ T, a w t ^ (2 ^ j) := by
    intro w
    refine tsum_eq_sum' fun t ht => ?_
    by_contra hTt
    exact ht (by simp [hT0 w t hTt])
  rw [e1]
  simp_rw [e2]
  exact sum_prod_cube_pow_le T j a ha

/-- `corr f g t ≠ 0` only for finitely many `t`. -/
theorem corr_support_finite (f g : ℤ →₀ ℂ) : {t : ℤ | corr f g t ≠ 0}.Finite := by
  refine (Set.Finite.image2 (fun x y => y - x) f.support.finite_toSet
    g.support.finite_toSet).subset ?_
  intro t ht
  by_contra hcon
  apply ht
  ext x
  simp only [corr_apply, Finsupp.coe_zero, Pi.zero_apply]
  by_cases hx : f x = 0
  · simp [hx]
  · by_cases hy : g (x + t) = 0
    · simp [hy]
    · exact absurd ⟨x, by simpa using hx, x + t, by simpa using hy, by ring⟩ hcon

/-- `∑_t ‖f ⋆ g_t‖^{2^{r+1}}` is the inner product of the pair family. -/
theorem tsum_nm_corr_pow (r : ℕ) (f g : ℤ →₀ ℂ) :
    ∑' t : ℤ, nm r (corr f g t) ^ (2 ^ (r + 1)) =
      ‖gowersInner (r + 1 + 1) (pairFamily (r + 1) f g)‖ := by
  have hcorr : ∀ t, corrFamily (pairFamily (r + 1) f g) t = fun _ => corr f g t := by
    intro t
    funext w
    simp [corrFamily, face_pairFamily_zero, face_pairFamily_one]
  have hq : ∀ t, nm r (corr f g t) ^ (2 ^ (r + 1)) =
      ∑' h, ‖partialSum r (fun _ => corr f g t) h‖ ^ 2 := by
    intro t
    rw [nm_pow, gowersInner_const_succ, Complex.norm_real,
      Real.norm_of_nonneg (tsum_nonneg fun _ => sq_nonneg _)]
  rw [gowersInner_succ_eq_tsum]
  simp_rw [hcorr, gowersInner_const_succ]
  rw [← Complex.ofReal_tsum, Complex.norm_real,
    Real.norm_of_nonneg (tsum_nonneg fun t => tsum_nonneg fun _ => sq_nonneg _)]
  exact tsum_congr hq

/-- Cauchy–Schwarz for the pair family: `‖⟨f,g⟩_{U^{s+1}}‖ ≤ ‖f‖^{2^s} ‖g‖^{2^s}`. -/
theorem norm_gowersInner_pairFamily_le (s : ℕ) (f g : ℤ →₀ ℂ) :
    ‖gowersInner (s + 1) (pairFamily s f g)‖ ≤ nm s f ^ (2 ^ s) * nm s g ^ (2 ^ s) := by
  have h := norm_gowersInner_sq_le (pairFamily s f g)
  rw [face_pairFamily_zero, face_pairFamily_one] at h
  have h' : ‖gowersInner (s + 1) (pairFamily s f g)‖ ^ 2 ≤
      ‖gowersInner (s + 1) (fun _ => f)‖ * ‖gowersInner (s + 1) (fun _ => g)‖ := h
  rw [← nm_pow, ← nm_pow] at h'
  have e : nm s f ^ 2 ^ (s + 1) * nm s g ^ 2 ^ (s + 1) =
      (nm s f ^ 2 ^ s * nm s g ^ 2 ^ s) ^ 2 := by
    rw [mul_pow, ← pow_mul, ← pow_mul, pow_succ]
  rw [e] at h'
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (pow_nonneg (nm_nonneg _ _) _) (pow_nonneg (nm_nonneg _ _) _))
    two_ne_zero).mp h'

/-- Gowers–Cauchy–Schwarz, indexed by `r = s - 1`. -/
theorem norm_gowersInner_le_prod_nm (r : ℕ) :
    ∀ F : (Fin (r + 1) → Fin 2) → ℤ →₀ ℂ, ‖gowersInner (r + 1) F‖ ≤ ∏ w, nm r (F w) := by
  induction r with
  | zero =>
    intro F
    have h := norm_gowersInner_sq_le F
    have hd : ∀ ε : Fin 2, dup (face F ε) =
        fun _ => F (Fin.snoc (α := fun _ => Fin 2) (default : Fin 0 → Fin 2) ε) := by
      intro ε
      funext w
      change F (Fin.snoc (α := fun _ => Fin 2) (Fin.init w) ε) = _
      rw [Subsingleton.elim (Fin.init w) (default : Fin 0 → Fin 2)]
    rw [hd, hd] at h
    rw [← nm_pow, ← nm_pow] at h
    rw [prod_cube_succ (fun w => nm 0 (F w))]
    simp only [Finset.univ_unique, Finset.prod_singleton]
    have e : nm 0 (F (Fin.snoc (α := fun _ => Fin 2) (default : Fin 0 → Fin 2) 0)) ^ 2 ^ (0 + 1) *
        nm 0 (F (Fin.snoc (α := fun _ => Fin 2) (default : Fin 0 → Fin 2) 1)) ^ 2 ^ (0 + 1) =
        (nm 0 (F (Fin.snoc (α := fun _ => Fin 2) (default : Fin 0 → Fin 2) 0)) *
          nm 0 (F (Fin.snoc (α := fun _ => Fin 2) (default : Fin 0 → Fin 2) 1))) ^ 2 := by
      ring
    rw [e] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _)
      (mul_nonneg (nm_nonneg _ _) (nm_nonneg _ _)) two_ne_zero).mp h
  | succ r ih =>
    intro F
    set a : (Fin (r + 1) → Fin 2) → ℤ → ℝ := fun w t => nm r (corrFamily F t w) with ha_def
    have ha0 : ∀ w t, 0 ≤ a w t := fun w t => nm_nonneg _ _
    have ha_fin : ∀ w, (Function.support (a w)).Finite := by
      intro w
      refine (corr_support_finite (face F 0 w) (face F 1 w)).subset ?_
      intro t ht
      by_contra hcon
      apply ht
      have h0 : corr (face F 0 w) (face F 1 w) t = 0 := not_not.mp hcon
      change nm r (corr (face F 0 w) (face F 1 w) t) = 0
      rw [h0, nm_zero]
    have hc : ∀ t, ‖gowersInner (r + 1) (corrFamily F t)‖ ≤ ∏ w, a w t :=
      fun t => ih (corrFamily F t)
    have hb_fin : (Function.support fun t => ∏ w, a w t).Finite := by
      refine (ha_fin 0).subset ?_
      intro t ht
      exact (Finset.prod_ne_zero_iff.mp ht) 0 (Finset.mem_univ _)
    have hc_fin : (Function.support fun t => ‖gowersInner (r + 1) (corrFamily F t)‖).Finite := by
      refine hb_fin.subset ?_
      intro t ht
      have : 0 < ‖gowersInner (r + 1) (corrFamily F t)‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm ht)
      exact (this.trans_le (hc t)).ne'
    have h1 : ‖gowersInner (r + 1 + 1) F‖ ≤ ∑' t, ∏ w, a w t := by
      rw [gowersInner_succ_eq_tsum]
      refine (norm_tsum_le_tsum_norm (summable_of_finite_support' hc_fin)).trans ?_
      exact Summable.tsum_le_tsum hc (summable_of_finite_support' hc_fin)
        (summable_of_finite_support' hb_fin)
    have h2 := tsum_prod_cube_pow_le (r + 1) a ha0 ha_fin
    have h3 : ∀ w : Fin (r + 1) → Fin 2, ∑' t, a w t ^ 2 ^ (r + 1) =
        ‖gowersInner (r + 1 + 1) (pairFamily (r + 1) (face F 0 w) (face F 1 w))‖ :=
      fun w => tsum_nm_corr_pow r _ _
    have h4 : ∀ w : Fin (r + 1) → Fin 2,
        ‖gowersInner (r + 1 + 1) (pairFamily (r + 1) (face F 0 w) (face F 1 w))‖ ≤
          nm (r + 1) (face F 0 w) ^ 2 ^ (r + 1) * nm (r + 1) (face F 1 w) ^ 2 ^ (r + 1) :=
      fun w => norm_gowersInner_pairFamily_le (r + 1) _ _
    have h5 : (∏ w : Fin (r + 1) → Fin 2, ∑' t, a w t ^ 2 ^ (r + 1)) ≤
        (∏ w : Fin (r + 1 + 1) → Fin 2, nm (r + 1) (F w)) ^ 2 ^ (r + 1) := by
      calc (∏ w : Fin (r + 1) → Fin 2, ∑' t, a w t ^ 2 ^ (r + 1))
          ≤ ∏ w : Fin (r + 1) → Fin 2,
            (nm (r + 1) (face F 0 w) ^ 2 ^ (r + 1) * nm (r + 1) (face F 1 w) ^ 2 ^ (r + 1)) :=
            Finset.prod_le_prod₀
              (fun w _ => tsum_nonneg fun _ => pow_nonneg (ha0 _ _) _)
              (fun w _ => (h3 w).le.trans (h4 w))
        _ = (∏ w : Fin (r + 1) → Fin 2, (nm (r + 1) (face F 0 w) * nm (r + 1) (face F 1 w))) ^
              2 ^ (r + 1) := by
            rw [← Finset.prod_pow]
            exact Finset.prod_congr rfl fun w _ => (mul_pow _ _ _).symm
        _ = _ := by
            rw [prod_cube_succ (fun w => nm (r + 1) (F w)), Finset.prod_mul_distrib]
            rfl
    have h6 : ‖gowersInner (r + 1 + 1) F‖ ^ 2 ^ (r + 1) ≤
        (∏ w : Fin (r + 1 + 1) → Fin 2, nm (r + 1) (F w)) ^ 2 ^ (r + 1) :=
      calc ‖gowersInner (r + 1 + 1) F‖ ^ 2 ^ (r + 1) ≤ (∑' t, ∏ w, a w t) ^ 2 ^ (r + 1) :=
            pow_le_pow_left₀ (norm_nonneg _) h1 _
        _ ≤ ∏ w, ∑' t, a w t ^ 2 ^ (r + 1) := h2
        _ ≤ _ := h5
    exact (pow_le_pow_iff_left₀ (norm_nonneg _)
      (Finset.prod_nonneg fun w _ => nm_nonneg _ _) (pow_pos two_pos _).ne').mp h6

end GowersCS

/-- **Gowers–Cauchy–Schwarz inequality** on `ℤ`: for a family `(F_w)_{w ∈ {0,1}^s}` of finitely
supported functions, `|⟨(F_w)⟩_{U^s}| ≤ ∏_w ‖F_w‖_{U^s}`. -/
theorem norm_gowersInner_le_prod_gowersNorm {s : ℕ+} (F : (Fin s → Fin 2) → ℤ →₀ ℂ) :
    ‖gowersInner s F‖ ≤ ∏ w, PrimeCarleson.gowersNorm s (F w) := by
  obtain ⟨r, rfl⟩ : ∃ r : ℕ, s = Nat.succPNat r := ⟨s.natPred, (PNat.succPNat_natPred s).symm⟩
  exact GowersCS.norm_gowersInner_le_prod_nm r F

/-! ### The norm properties of `U^s(ℤ)` -/

namespace GowersCS

/-- Multilinear expansion of the constant family `f + g`. -/
theorem gowersTerm_add (s : ℕ) (f g : ℤ →₀ ℂ) (x : ℤ) (h : Fin s → ℤ) :
    gowersTerm s (fun _ => f + g) x h =
      ∑ c : (Fin s → Fin 2) → Bool,
        gowersTerm s (fun w => if c w then f else g) x h := by
  classical
  have e : ∀ w : Fin s → Fin 2, gowersConjPow (vertexWeight w) ((f + g) (x + cubePoint w h)) =
      ∑ b : Bool, (if b then gowersConjPow (vertexWeight w) (f (x + cubePoint w h))
        else gowersConjPow (vertexWeight w) (g (x + cubePoint w h))) := by
    intro w
    rw [Fintype.sum_bool, Finsupp.add_apply, gowersConjPow_add]
    rfl
  unfold gowersTerm
  simp_rw [e]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun c _ => Finset.prod_congr rfl fun w _ => ?_
  by_cases hc : c w <;> simp [hc]

/-- Multilinear expansion of the Gowers inner product of the constant family `f + g` into
`2^{2^s}` inner products. -/
theorem gowersInner_add (s : ℕ) (f g : ℤ →₀ ℂ) :
    gowersInner s (fun _ => f + g) =
      ∑ c : (Fin s → Fin 2) → Bool, gowersInner s (fun w => if c w then f else g) := by
  unfold gowersInner
  simp_rw [gowersTerm_add]
  rw [Summable.tsum_finsetSum]
  intro c _
  exact summable_of_finite_support' (gowersTerm_support_finite s _)

end GowersCS

/-- **Triangle inequality** for the Gowers norm `U^s(ℤ)`, `s ≥ 1`, on finitely supported
functions. -/
theorem gowersNorm_add_le (s : ℕ+) (f g : ℤ →₀ ℂ) :
    PrimeCarleson.gowersNorm s (f + g) ≤
      PrimeCarleson.gowersNorm s f + PrimeCarleson.gowersNorm s g := by
  classical
  have hf := (PrimeCarleson.gowersNorm_spec s f).2.1
  have hg := (PrimeCarleson.gowersNorm_spec s g).2.1
  have key : ‖gowersInner s (fun _ => f + g)‖ ≤
      (PrimeCarleson.gowersNorm s f + PrimeCarleson.gowersNorm s g) ^ 2 ^ (s : ℕ) := by
    rw [GowersCS.gowersInner_add]
    calc ‖∑ c : (Fin s → Fin 2) → Bool, gowersInner s (fun w => if c w then f else g)‖
        ≤ ∑ c : (Fin s → Fin 2) → Bool,
            ‖gowersInner s (fun w => if c w then f else g)‖ := norm_sum_le _ _
      _ ≤ ∑ c : (Fin s → Fin 2) → Bool, ∏ w : Fin s → Fin 2,
            (if c w then PrimeCarleson.gowersNorm s f else PrimeCarleson.gowersNorm s g) := by
          refine Finset.sum_le_sum fun c _ => ?_
          refine (norm_gowersInner_le_prod_gowersNorm _).trans (le_of_eq ?_)
          refine Finset.prod_congr rfl fun w _ => ?_
          by_cases hc : c w <;> simp [hc]
      _ = ∏ w : Fin s → Fin 2, ∑ b : Bool,
            (if b then PrimeCarleson.gowersNorm s f else PrimeCarleson.gowersNorm s g) :=
          (Fintype.prod_sum fun (_ : Fin s → Fin 2) (b : Bool) =>
            if b then PrimeCarleson.gowersNorm s f else PrimeCarleson.gowersNorm s g).symm
      _ = _ := by simp [Finset.prod_const]
  rw [← gowersNorm_pow_eq] at key
  exact (pow_le_pow_iff_left₀ (PrimeCarleson.gowersNorm_spec s _).2.1 (add_nonneg hf hg)
    (pow_pos two_pos _).ne').mp key

namespace GowersCS

/-- Unfolding of `PrimeCarleson.multDiff` at `s + 1`. -/
theorem multDiff_succ' (s : ℕ) (h : Fin (s + 1) → ℤ) (f : ℤ → ℂ) (x : ℤ) :
    PrimeCarleson.multDiff (s + 1) h f x =
      PrimeCarleson.multDiff s (Fin.init h) f x *
        conj (PrimeCarleson.multDiff s (Fin.init h) f (x + h (Fin.last s))) := rfl

/-- Homogeneity of the iterated difference: `Δ_h (c f) = |c|^{2^s} Δ_h f` for `s ≥ 1`. -/
theorem multDiff_smul (s : ℕ) (c : ℂ) (f : ℤ → ℂ) (h : Fin (s + 1) → ℤ) (x : ℤ) :
    PrimeCarleson.multDiff (s + 1) h (c • f) x =
      ((‖c‖ ^ 2 ^ (s + 1) : ℝ) : ℂ) * PrimeCarleson.multDiff (s + 1) h f x := by
  induction s generalizing x with
  | zero =>
    simp only [PrimeCarleson.multDiff, Pi.smul_apply, smul_eq_mul, map_mul]
    have : ((‖c‖ ^ 2 ^ (0 + 1) : ℝ) : ℂ) = c * conj c := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp
    rw [this]
    ring
  | succ s ih =>
    rw [multDiff_succ' (s + 1) h (c • f), multDiff_succ' (s + 1) h f, ih, ih, map_mul,
      Complex.conj_ofReal, pow_succ 2 (s + 1), pow_mul]
    push_cast
    ring

end GowersCS

/-- Homogeneity of the Gowers norm: `‖c f‖_{U^s} = |c| ‖f‖_{U^s}`. -/
theorem gowersNorm_smul (s : ℕ+) (c : ℂ) (f : ℤ →₀ ℂ) :
    PrimeCarleson.gowersNorm s (c • f) = ‖c‖ * PrimeCarleson.gowersNorm s f := by
  obtain ⟨r, rfl⟩ : ∃ r : ℕ, s = Nat.succPNat r := ⟨s.natPred, (PNat.succPNat_natPred s).symm⟩
  obtain ⟨-, h0, h⟩ := PrimeCarleson.gowersNorm_spec (Nat.succPNat r) (c • f)
  obtain ⟨-, h0', h'⟩ := PrimeCarleson.gowersNorm_spec (Nat.succPNat r) f
  have key : ((PrimeCarleson.gowersNorm (Nat.succPNat r) (c • f) : ℝ) : ℂ) ^
      2 ^ (Nat.succPNat r : ℕ) = (((‖c‖ * PrimeCarleson.gowersNorm (Nat.succPNat r) f) ^
        2 ^ (Nat.succPNat r : ℕ) : ℝ) : ℂ) := by
    rw [h]
    have : ∀ p : ℤ × (Fin (Nat.succPNat r) → ℤ),
        PrimeCarleson.multDiff (Nat.succPNat r) p.2 (⇑(c • f)) p.1 =
          ((‖c‖ ^ 2 ^ (r + 1) : ℝ) : ℂ) * PrimeCarleson.multDiff (Nat.succPNat r) p.2 f p.1 :=
      fun p => GowersCS.multDiff_smul r c f p.2 p.1
    simp_rw [this]
    rw [tsum_mul_left, ← h']
    push_cast
    rw [mul_pow]
    simp
  have key' : PrimeCarleson.gowersNorm (Nat.succPNat r) (c • f) ^ 2 ^ (Nat.succPNat r : ℕ) =
      (‖c‖ * PrimeCarleson.gowersNorm (Nat.succPNat r) f) ^ 2 ^ (Nat.succPNat r : ℕ) := by
    exact_mod_cast key
  exact (pow_left_inj₀ h0 (mul_nonneg (norm_nonneg _) h0') (pow_pos two_pos _).ne').mp key'

end PrimeCarleson.Proof.Common
