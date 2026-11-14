module

public import PrimeCarleson.Proof.Fplus31.Extrapolation.Height
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Data.Fintype.Perm

/-!
# The pivot structure of a rational subspace with bounded generators (extrapolation, Step 4)

Part of the abstract extrapolation (the extrapolation step of the iteration of `C2/CMain.lean`,
proof of [F+] Proposition 3.1). Let `U ⊆ ℚ^ι` be spanned by vectors of coordinate log-height at most
`p`. `exists_pivot` produces integer functionals `θ_j` (`j ∈ Z`) of sup norm at most `exp (2 p³)`, a
positive integer `Δ` and coordinates `z j` with

* `θ_j (e_{z j'}) = Δ δ_{j j'}` (the functionals are diagonal on the free coordinates `z j`),
* `θ_j` vanishes on `U`,
* a real vector killed by all `θ_j` lies in the real span of `U`.

The proof extends a basis of `U` among the generators by standard basis vectors to a basis of
`ℚ^ι`, makes the matrix of this basis square by a bijection of the index sets and uses the
adjugate: the `θ_j` are the rows of `±adj` belonging to the standard vectors, `Δ = |det|`.  The
sizes are controlled by the Leibniz formula (`n! H^n`, no Hadamard inequality needed).
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open Matrix

/-- Leibniz bound for the determinant of an integer matrix with entries of absolute value at most
`H`: `|det M| ≤ n! H^n`. -/
theorem abs_det_le_factorial_mul_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℤ) (H : ℕ) (hM : ∀ i j, |M i j| ≤ H) :
    |M.det| ≤ (Fintype.card ι).factorial * (H : ℤ) ^ Fintype.card ι := by
  rw [Matrix.det_apply']
  calc |∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤˣ) : ℤ) * ∏ i, M (σ i) i|
      ≤ ∑ σ : Equiv.Perm ι, |((Equiv.Perm.sign σ : ℤˣ) : ℤ) * ∏ i, M (σ i) i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm ι, (H : ℤ) ^ Fintype.card ι := by
        refine Finset.sum_le_sum fun σ _ => ?_
        rw [abs_mul, Finset.abs_prod]
        have hs : |((Equiv.Perm.sign σ : ℤˣ) : ℤ)| = 1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
        rw [hs, one_mul]
        calc ∏ i, |M (σ i) i| ≤ ∏ _i : ι, (H : ℤ) :=
              Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun i _ => hM _ _
          _ = (H : ℤ) ^ Fintype.card ι := by simp
    _ = (Fintype.card ι).factorial * (H : ℤ) ^ Fintype.card ι := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm]
        simp

/-- The entries of the adjugate satisfy the same bound (`H ≥ 1`). -/
theorem abs_adjugate_le {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ) (H : ℕ)
    (hH : 1 ≤ H) (hM : ∀ i j, |M i j| ≤ H) (i j : ι) :
    |M.adjugate i j| ≤ (Fintype.card ι).factorial * (H : ℤ) ^ Fintype.card ι := by
  rw [Matrix.adjugate_apply]
  apply abs_det_le_factorial_mul_pow
  intro a b
  rw [Matrix.updateRow_apply]
  split_ifs with h
  · rw [Pi.single_apply]
    split_ifs
    · simpa using (by exact_mod_cast hH : (1 : ℤ) ≤ H)
    · simp
  · exact hM _ _

/-- **The pivot structure, integer form.**  Let `g_k ∈ ℤ^ι` have entries of absolute value at
most `H ≥ 1`.  There are a set `Z` of free columns, a positive integer `Δ` and integer functionals
`θ_j` with entries bounded by `n! H^n`, such that `θ_j (e_{z j'}) = Δ δ_{j j'}` for `j, j' ∈ Z`,
each `θ_j` kills every `g_k`, and a real vector killed by all `θ_j`, `j ∈ Z`, lies in the real
span of the `g_k`. -/
theorem exists_pivot_int {ι κ : Type*} [Fintype ι] [DecidableEq ι] (g : κ → ι → ℤ) (H : ℕ)
    (hH : 1 ≤ H) (hg : ∀ k i, |g k i| ≤ H) :
    ∃ (Z : Finset ι) (Δ : ℕ) (θ : ι → ι → ℤ) (z : ι → ι),
      0 < Δ ∧ (Δ : ℤ) ≤ (Fintype.card ι).factorial * (H : ℤ) ^ Fintype.card ι ∧
      (∀ j i, |θ j i| ≤ (Fintype.card ι).factorial * (H : ℤ) ^ Fintype.card ι) ∧
      (∀ j ∈ Z, ∀ j' ∈ Z, θ j (z j') = if j = j' then (Δ : ℤ) else 0) ∧
      (∀ j ∈ Z, ∀ k, ∑ i, θ j i * g k i = 0) ∧
      (∀ y : ι → ℝ, (∀ j ∈ Z, ∑ i, (θ j i : ℝ) * y i = 0) →
        y ∈ Submodule.span ℝ (Set.range fun k i => (g k i : ℝ))) ∧
      ∃ cols : ι → ι → ℤ, (∀ j ∈ Z, ∀ i, cols j i = if i = z j then 1 else 0) ∧
        (∀ j, j ∉ Z → ∃ k, cols j = g k) ∧
        (∀ i i', ∑ j, cols j i * θ j i' = if i = i' then (Δ : ℤ) else 0) ∧
        (∀ j j', ∑ i, θ j i * cols j' i = if j = j' then (Δ : ℤ) else 0) := by
  classical
  let gq : κ → ι → ℚ := fun k i => (g k i : ℚ)
  let T : Set (ι → ℚ) := Set.range gq
  let std : Set (ι → ℚ) := Set.range fun j : ι => (Pi.single j (1 : ℚ) : ι → ℚ)
  obtain ⟨b, hbT, hbspan, hbli⟩ := exists_linearIndependent ℚ T
  have hs : LinearIndepOn ℚ id b := hbli
  have hst : b ⊆ b ∪ std := Set.subset_union_left
  have htop : ⊤ ≤ Submodule.span ℚ (b ∪ std) := by
    rw [← (Pi.basisFun ℚ ι).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    right
    exact ⟨j, by simp⟩
  let cb := Module.Basis.extendLe hs hst htop
  have hcb : ∀ x, cb x = (x : ι → ℚ) := fun x => by simp [cb]
  have hcsub : (hs.extend hst) ⊆ b ∪ std := hs.extend_subset hst
  have hbc : b ⊆ hs.extend hst := hs.subset_extend hst
  have : Finite (hs.extend hst) := Module.Finite.finite_basis cb
  have : Fintype (hs.extend hst) := Fintype.ofFinite _
  have hcard : Fintype.card ι = Fintype.card (hs.extend hst) := by
    have h1 := Module.finrank_eq_nat_card_basis cb
    rw [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card] at h1
    exact h1
  let φ : ι ≃ (hs.extend hst) := Fintype.equivOfCardEq hcard
  -- integer vectors for the elements of the basis
  have hint : ∀ x : hs.extend hst, ∃ xz : ι → ℤ, (∀ i, |xz i| ≤ H) ∧
      (x : ι → ℚ) = fun i => (xz i : ℚ) := by
    intro x
    rcases hcsub x.2 with hxb | hxs
    · obtain ⟨k, hk⟩ := hbT hxb
      exact ⟨g k, hg k, hk.symm⟩
    · obtain ⟨j, hj⟩ := hxs
      refine ⟨Pi.single j 1, ?_, ?_⟩
      · intro i
        by_cases h : i = j
        · subst h; simpa using (by exact_mod_cast hH : (1 : ℤ) ≤ H)
        · simp [h]
      · rw [← hj]
        ext i
        by_cases h : i = j
        · subst h; simp
        · simp [h]
  choose zv hzvb hzv using hint
  let M : Matrix ι ι ℤ := fun i j => zv (φ j) i
  have hMq : ∀ i j, ((M i j : ℤ) : ℚ) = ((φ j : hs.extend hst) : ι → ℚ) i := by
    intro i j
    have := congrFun (hzv (φ j)) i
    simpa [M] using this.symm
  have hlin : LinearIndependent ℚ (fun j => ((φ j : hs.extend hst) : ι → ℚ)) := by
    have h := cb.linearIndependent.comp φ φ.injective
    have heq : (⇑cb ∘ ⇑φ) = fun j => ((φ j : hs.extend hst) : ι → ℚ) := funext fun j => hcb _
    rwa [heq] at h
  have hcolMq : (M.map (Int.cast : ℤ → ℚ)).col = fun j => ((φ j : hs.extend hst) : ι → ℚ) := by
    ext j i
    simp [Matrix.col, hMq]
  have hunit : IsUnit (M.map (Int.cast : ℤ → ℚ)) := by
    rw [← Matrix.linearIndependent_col_iff_isUnit, hcolMq]
    exact hlin
  have hdet : M.det ≠ 0 := by
    have h := (Matrix.isUnit_iff_isUnit_det _).mp hunit
    have h2 : (M.map (Int.cast : ℤ → ℚ)).det = (M.det : ℚ) := by
      have := RingHom.map_det (Int.castRingHom ℚ) M
      simpa using this.symm
    rw [h2] at h
    intro h0
    rw [h0] at h
    simp at h
  -- sign
  set s : ℤ := if 0 < M.det then 1 else -1 with hs_def
  have hss : s * s = 1 := by
    rw [hs_def]; split_ifs <;> norm_num
  have hsabs : |s| = 1 := by
    rw [hs_def]; split_ifs <;> norm_num
  have hsdet : s * M.det = (M.det.natAbs : ℤ) := by
    rw [hs_def]
    split_ifs with h
    · rw [one_mul, Int.natAbs_of_nonneg h.le]
    · have : M.det < 0 := lt_of_le_of_ne (not_lt.mp h) hdet
      rw [neg_one_mul, Int.ofNat_natAbs_of_nonpos this.le]
  have hΔpos : 0 < M.det.natAbs := Int.natAbs_pos.mpr hdet
  -- the free columns
  let Z : Finset ι := Finset.univ.filter fun j => ((φ j : hs.extend hst) : ι → ℚ) ∉ b
  have hZstd : ∀ j, ∃ i₀ : ι, j ∈ Z → ((φ j : hs.extend hst) : ι → ℚ) = Pi.single i₀ 1 := by
    intro j
    by_cases hj : j ∈ Z
    · have hjb : ((φ j : hs.extend hst) : ι → ℚ) ∉ b := (Finset.mem_filter.mp hj).2
      rcases hcsub (φ j).2 with h | h
      · exact absurd h hjb
      · obtain ⟨i₀, hi₀⟩ := h
        exact ⟨i₀, fun _ => hi₀.symm⟩
    · exact ⟨j, fun h => absurd h hj⟩
  choose z hz using hZstd
  -- adjugate relation
  have hadj : ∀ j j', ∑ i, M.adjugate j i * M i j' = if j = j' then M.det else 0 := by
    intro j j'
    have := congrFun (congrFun (Matrix.adjugate_mul M) j) j'
    simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] using this
  have hcolZ : ∀ j ∈ Z, ∀ i, M i j = if i = z j then 1 else 0 := by
    intro j' hj' i
    have h1 := hMq i j'
    rw [hz j' hj'] at h1
    by_cases h : i = z j'
    · have h1' : ((M i j' : ℤ) : ℚ) = ((1 : ℤ) : ℚ) := by rw [h1, h]; simp
      have h2 : M i j' = 1 := Int.cast_injective h1'
      rw [h2]
      simp [h]
    · have h1' : ((M i j' : ℤ) : ℚ) = ((0 : ℤ) : ℚ) := by simpa [h] using h1
      have h2 : M i j' = 0 := Int.cast_injective h1'
      rw [h2]
      simp [h]
  have hadj' : ∀ i i', ∑ j, M i j * M.adjugate j i' = if i = i' then M.det else 0 := by
    intro i i'
    have := congrFun (congrFun (Matrix.mul_adjugate M) i) i'
    simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] using this
  refine ⟨Z, M.det.natAbs, fun j i => s * M.adjugate j i, z, hΔpos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := abs_det_le_factorial_mul_pow M H (fun i j => hzvb _ _)
    rw [Int.natCast_natAbs]
    exact this
  · intro j i
    rw [abs_mul, hsabs, one_mul]
    exact abs_adjugate_le M H hH (fun i j => hzvb _ _) j i
  · intro j hj j' hj'
    have hcol := hcolZ j' hj'
    have := hadj j j'
    simp only [hcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true] at this
    simp only [this]
    split_ifs with h
    · rw [hsdet]
    · simp
  · intro j hj k
    have hjb : ((φ j : hs.extend hst) : ι → ℚ) ∉ b := (Finset.mem_filter.mp hj).2
    let lam : (ι → ℚ) →ₗ[ℚ] ℚ :=
      ∑ i, ((s * M.adjugate j i : ℤ) : ℚ) • (LinearMap.proj i : (ι → ℚ) →ₗ[ℚ] ℚ)
    have hlam : ∀ v, lam v = ∑ i, ((s * M.adjugate j i : ℤ) : ℚ) * v i := by
      intro v; simp [lam]
    have hb0 : ∀ x ∈ b, lam x = 0 := by
      intro x hx
      let j'' := φ.symm ⟨x, hbc hx⟩
      have hj'' : ((φ j'' : hs.extend hst) : ι → ℚ) = x := by simp [j'']
      have hne : j ≠ j'' := by
        intro h; apply hjb; rw [h, hj'']; exact hx
      rw [hlam]
      have h1 := hadj j j''
      have h2 : ∑ i, ((s * M.adjugate j i : ℤ) : ℚ) * x i =
          ((s * ∑ i, M.adjugate j i * M i j'' : ℤ) : ℚ) := by
        rw [← hj'']
        push_cast
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hMq]
        ring
      rw [h2, h1]
      simp [hne]
    have hspan : gq k ∈ Submodule.span ℚ b := by
      rw [hbspan]; exact Submodule.subset_span ⟨k, rfl⟩
    have h3 : lam (gq k) = 0 :=
      (Submodule.span_le (p := LinearMap.ker lam)).mpr (fun x hx => hb0 x hx) hspan
    rw [hlam] at h3
    have h4 : ((∑ i, s * M.adjugate j i * g k i : ℤ) : ℚ) = 0 := by
      push_cast
      simpa [gq] using h3
    exact_mod_cast h4
  · intro y hy
    let w : ι → ℝ := fun j => ∑ i', (M.adjugate j i' : ℝ) * y i'
    have hs0 : (s : ℝ) ≠ 0 := by
      have : s ≠ 0 := by intro h0; simp [h0] at hss
      exact_mod_cast this
    have hw : ∀ j ∈ Z, w j = 0 := by
      intro j hj
      have h := hy j hj
      have h2 : (s : ℝ) * w j = 0 := by
        rw [← h]
        simp only [w, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        push_cast
        ring
      exact (mul_eq_zero.mp h2).resolve_left hs0
    have key : ∀ i, (M.det : ℝ) * y i = ∑ j, (M i j : ℝ) * w j := by
      intro i
      simp only [w, Finset.mul_sum]
      rw [Finset.sum_comm]
      have h5 : ∀ i', ∑ j, (M i j : ℝ) * ((M.adjugate j i' : ℝ) * y i') =
          (if i = i' then (M.det : ℝ) else 0) * y i' := by
        intro i'
        have h := hadj' i i'
        have h' : ∑ j, (M i j : ℝ) * (M.adjugate j i' : ℝ) =
            if i = i' then (M.det : ℝ) else 0 := by
          have := congrArg (Int.cast : ℤ → ℝ) h
          simpa only [Int.cast_sum, Int.cast_mul, Int.cast_ite, Int.cast_zero] using this
        calc ∑ j, (M i j : ℝ) * ((M.adjugate j i' : ℝ) * y i')
            = (∑ j, (M i j : ℝ) * (M.adjugate j i' : ℝ)) * y i' := by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun j _ => by ring
          _ = _ := by rw [h']
      rw [Finset.sum_congr rfl (fun i' _ => h5 i')]
      simp [Finset.sum_ite_eq]
    have hmem : (fun i => (M.det : ℝ) * y i) ∈
        Submodule.span ℝ (Set.range fun k i => (g k i : ℝ)) := by
      have heq : (fun i => (M.det : ℝ) * y i) = ∑ j, w j • (fun i => (M i j : ℝ)) := by
        ext i
        simp only [key i, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      rw [heq]
      refine Submodule.sum_mem _ fun j _ => ?_
      by_cases hj : j ∈ Z
      · rw [hw j hj, zero_smul]; exact Submodule.zero_mem _
      · have hjb : ((φ j : hs.extend hst) : ι → ℚ) ∈ b := by
          by_contra h; exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        obtain ⟨k, hk⟩ := hbT hjb
        refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, ?_⟩)
        ext i
        have h6 := hMq i j
        rw [← hk] at h6
        have h2 : M i j = g k i := by
          have h8 : ((M i j : ℤ) : ℚ) = ((g k i : ℤ) : ℚ) := h6
          exact_mod_cast h8
        simp [h2]
    have hdetR : (M.det : ℝ) ≠ 0 := by exact_mod_cast hdet
    have h7 := Submodule.smul_mem _ ((M.det : ℝ)⁻¹) hmem
    convert h7 using 1
    ext i
    simp [hdetR]
  · refine ⟨fun j i => M i j, hcolZ, ?_, ?_, ?_⟩
    · intro j hj
      have hjb : ((φ j : hs.extend hst) : ι → ℚ) ∈ b := by
        by_contra h
        exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      obtain ⟨k, hk⟩ := hbT hjb
      refine ⟨k, funext fun i => ?_⟩
      have h6 := hMq i j
      rw [← hk] at h6
      have h7 : ((M i j : ℤ) : ℚ) = ((g k i : ℤ) : ℚ) := h6
      exact Int.cast_injective h7
    · intro i i'
      have h1 := hadj' i i'
      calc ∑ j, M i j * (s * M.adjugate j i') = s * ∑ j, M i j * M.adjugate j i' := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = if i = i' then ((M.det.natAbs : ℕ) : ℤ) else 0 := by
            rw [h1]
            split_ifs
            · rw [hsdet]
            · simp
    · intro j j'
      have h1 := hadj j j'
      calc ∑ i, s * M.adjugate j i * M i j' = s * ∑ i, M.adjugate j i * M i j' := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
        _ = if j = j' then ((M.det.natAbs : ℕ) : ℤ) else 0 := by
            rw [h1]
            split_ifs
            · rw [hsdet]
            · simp

/-- The size of the pivot data: `n! (e^{p n})^n ≤ e^{2 p³}` for `n ≤ p`, `1 ≤ p`. -/
theorem factorial_mul_exp_pow_le {n : ℕ} {p : ℝ} (hp : 1 ≤ p) (hn : (n : ℝ) ≤ p) :
    (n.factorial : ℝ) * (Real.exp (p * n)) ^ n ≤ Real.exp (2 * p ^ 3) := by
  have h1 : (n.factorial : ℝ) ≤ Real.exp (p * n) := by
    calc (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
      _ ≤ (Real.exp p) ^ n := by
          apply pow_le_pow_left₀ (Nat.cast_nonneg _)
          linarith [Real.add_one_le_exp p]
      _ = Real.exp (p * n) := by rw [← Real.exp_nat_mul]; ring_nf
  have h2 : (Real.exp (p * n)) ^ n = Real.exp (p * n * n) := by
    rw [← Real.exp_nat_mul]; ring_nf
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc (n.factorial : ℝ) * (Real.exp (p * n)) ^ n
      ≤ Real.exp (p * n) * Real.exp (p * n * n) := by
        rw [h2]; exact mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
    _ = Real.exp (p * n * (n + 1)) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (2 * p ^ 3) := by
        apply Real.exp_le_exp.mpr
        have h3 : (n : ℝ) + 1 ≤ 2 * p := by linarith
        have h4 : p * n ≤ p * p := mul_le_mul_of_nonneg_left hn (by linarith)
        calc p * n * (n + 1) ≤ (p * p) * (2 * p) :=
              mul_le_mul h4 h3 (by positivity) (by positivity)
          _ = 2 * p ^ 3 := by ring

/-- **The pivot structure for rational generators.**  Let `U ⊆ ℚ^ι` be spanned by vectors
`g_k` of coordinate log-height at most `p`, where `1 ≤ p` and `|ι| ≤ p`.  There are a set `Z`,
a positive integer `Δ ≤ e^{2 p³}` and integer functionals `θ_j` (`j ∈ Z`) with entries at most
`e^{2 p³}` in absolute value such that: `θ_j (e_{z j'}) = Δ δ_{j j'}`; each `θ_j` kills every `g_k`;
a real vector killed by all `θ_j` is in the real span of the `g_k`. -/
theorem exists_pivot {ι κ : Type*} [Fintype ι] [DecidableEq ι] {p : ℝ} (hp : 1 ≤ p)
    (hn : (Fintype.card ι : ℝ) ≤ p) (g : κ → ι → ℚ) (hg : ∀ k i, ratLogHeight (g k i) ≤ p) :
    ∃ (Z : Finset ι) (Δ : ℕ) (θ : ι → ι → ℤ) (z : ι → ι),
      0 < Δ ∧ (Δ : ℝ) ≤ Real.exp (2 * p ^ 3) ∧
      (∀ j i, |(θ j i : ℝ)| ≤ Real.exp (2 * p ^ 3)) ∧
      (∀ j ∈ Z, ∀ j' ∈ Z, θ j (z j') = if j = j' then (Δ : ℤ) else 0) ∧
      (∀ j ∈ Z, ∀ k, ∑ i, (θ j i : ℚ) * g k i = 0) ∧
      (∀ y : ι → ℝ, (∀ j ∈ Z, ∑ i, (θ j i : ℝ) * y i = 0) →
        y ∈ Submodule.span ℝ (Set.range fun k i => (g k i : ℝ))) ∧
      (∀ y : ι → ℚ, (∀ j ∈ Z, ∑ i, (θ j i : ℚ) * y i = 0) →
        y ∈ Submodule.span ℚ (Set.range g)) := by
  choose L hLpos G hLG hGb using fun k => exists_clear_denominators (g k) (hg k)
  have hp0 : 0 ≤ p * Fintype.card ι := by positivity
  have hH1 : 1 ≤ ⌊Real.exp (p * Fintype.card ι)⌋₊ :=
    Nat.le_floor (by simpa using Real.one_le_exp hp0)
  have hGH : ∀ k i, |G k i| ≤ ((⌊Real.exp (p * Fintype.card ι)⌋₊ : ℕ) : ℤ) := by
    intro k i
    rw [Int.abs_eq_natAbs]
    have h1 : ((G k i).natAbs : ℝ) ≤ Real.exp (p * Fintype.card ι) := by
      have h2 : ((G k i).natAbs : ℝ) = |(G k i : ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      rw [h2]
      exact hGb k i
    exact_mod_cast Nat.le_floor h1
  obtain ⟨Z, Δ, θ, z, hΔ, hΔb, hθb, hdiag, hkill, hspan, cols, hcolZ, hcolk, hI2, hI1⟩ :=
    exists_pivot_int G ⌊Real.exp (p * Fintype.card ι)⌋₊ hH1 hGH
  have hB : ((Fintype.card ι).factorial : ℝ) * ((⌊Real.exp (p * Fintype.card ι)⌋₊ : ℕ) : ℝ) ^
      Fintype.card ι ≤ Real.exp (2 * p ^ 3) := by
    refine le_trans ?_ (factorial_mul_exp_pow_le hp hn)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _)
      (Nat.floor_le (Real.exp_nonneg _)) _) (by positivity)
  refine ⟨Z, Δ, θ, z, hΔ, ?_, ?_, hdiag, ?_, ?_, ?_⟩
  · have : (Δ : ℝ) ≤ (Fintype.card ι).factorial * ((⌊Real.exp (p * Fintype.card ι)⌋₊ : ℕ) : ℝ) ^
        Fintype.card ι := by exact_mod_cast hΔb
    linarith
  · intro j i
    have : |(θ j i : ℝ)| ≤ (Fintype.card ι).factorial *
        ((⌊Real.exp (p * Fintype.card ι)⌋₊ : ℕ) : ℝ) ^ Fintype.card ι := by
      exact_mod_cast hθb j i
    linarith
  · intro j hj k
    have h := hkill j hj k
    have h2 : ((∑ i, θ j i * G k i : ℤ) : ℚ) = 0 := by rw [h]; simp
    have h3 : (L k : ℚ) * ∑ i, (θ j i : ℚ) * g k i = 0 := by
      rw [Finset.mul_sum]
      rw [← h2]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hLG k i]
      ring
    exact (mul_eq_zero.mp h3).resolve_left (by exact_mod_cast (hLpos k).ne')
  · intro y hy
    refine Submodule.span_le.mpr ?_ (hspan y hy)
    rintro _ ⟨k, rfl⟩
    have : (fun i => (G k i : ℝ)) = (L k : ℝ) • fun i => (g k i : ℝ) := by
      ext i
      have h := congrArg (Rat.cast : ℚ → ℝ) (hLG k i)
      simp only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast] at h
      simp [← h]
    change (fun i => (G k i : ℝ)) ∈ Submodule.span ℝ _
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · intro y hy
    have hE1 : ∀ i, (Δ : ℚ) * y i =
        ∑ j, (∑ i', (θ j i' : ℚ) * y i') * (cols j i : ℚ) := by
      intro i
      have h1 : ∀ i', ∑ j, (cols j i : ℚ) * (θ j i' : ℚ) = if i = i' then (Δ : ℚ) else 0 := by
        intro i'
        have := congrArg (Int.cast : ℤ → ℚ) (hI2 i i')
        simpa only [Int.cast_sum, Int.cast_mul, Int.cast_ite, Int.cast_zero,
          Int.cast_natCast] using this
      calc (Δ : ℚ) * y i = ∑ i', (∑ j, (cols j i : ℚ) * (θ j i' : ℚ)) * y i' := by
            simp only [h1, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        _ = _ := by
            simp only [Finset.sum_mul]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i' _ => by ring
    have hΔq : (Δ : ℚ) ≠ 0 := by exact_mod_cast hΔ.ne'
    have hyeq : y = (Δ : ℚ)⁻¹ • ∑ j, (∑ i', (θ j i' : ℚ) * y i') • (fun i => (cols j i : ℚ)) := by
      ext i
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      rw [← hE1 i]
      field_simp
    rw [hyeq]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => ?_)
    by_cases hj : j ∈ Z
    · rw [hy j hj, zero_smul]
      exact Submodule.zero_mem _
    · obtain ⟨k, hk⟩ := hcolk j hj
      refine Submodule.smul_mem _ _ ?_
      have : (fun i => (cols j i : ℚ)) = (L k : ℚ) • g k := by
        ext i
        rw [hk]
        simp [← hLG k i]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- The size of the kernel pivot data: `n! H^n ≤ e^{3 p⁴}` for `H ≤ e^{2 p³}`, `n ≤ p`. -/
theorem factorial_mul_pow_le_exp {n : ℕ} {p : ℝ} (hp : 1 ≤ p) (hn : (n : ℝ) ≤ p) {H : ℝ}
    (hH0 : 0 ≤ H) (hH : H ≤ Real.exp (2 * p ^ 3)) :
    (n.factorial : ℝ) * H ^ n ≤ Real.exp (3 * p ^ 4) := by
  have h1 : (n.factorial : ℝ) ≤ Real.exp (p * n) := by
    calc (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
      _ ≤ (Real.exp p) ^ n := by
          apply pow_le_pow_left₀ (Nat.cast_nonneg _)
          linarith [Real.add_one_le_exp p]
      _ = Real.exp (p * n) := by rw [← Real.exp_nat_mul]; ring_nf
  have h2 : H ^ n ≤ Real.exp (2 * p ^ 3 * n) := by
    calc H ^ n ≤ (Real.exp (2 * p ^ 3)) ^ n := pow_le_pow_left₀ hH0 hH n
      _ = Real.exp (2 * p ^ 3 * n) := by rw [← Real.exp_nat_mul]; ring_nf
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc (n.factorial : ℝ) * H ^ n ≤ Real.exp (p * n) * Real.exp (2 * p ^ 3 * n) :=
        mul_le_mul h1 h2 (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (p * n + 2 * p ^ 3 * n) := by rw [← Real.exp_add]
    _ ≤ Real.exp (3 * p ^ 4) := by
        apply Real.exp_le_exp.mpr
        have h3 : p * n ≤ p * p := mul_le_mul_of_nonneg_left hn (by linarith)
        have h4 : 2 * p ^ 3 * n ≤ 2 * p ^ 3 * p :=
          mul_le_mul_of_nonneg_left hn (by positivity)
        have h5 : p * p ≤ p ^ 4 := by nlinarith [sq_nonneg (p - 1), sq_nonneg p]
        nlinarith

end PrimeCarleson.Proof.Fplus31
