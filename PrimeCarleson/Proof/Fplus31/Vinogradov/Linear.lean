module

public import PrimeCarleson.Proof.Fplus31.Vinogradov.Counting
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import Mathlib.Tactic.FieldSimp

/-!
# The linear Vinogradov lemma

Vinogradov-type estimate used by the extrapolation step of the iteration of `C2/CMain.lean` (proof
of [F+] Proposition 3.1), degree one (Leng's `l:vinogradov` = Green–Tao [GT14, Lemma 2.3],
arXiv:2312.10772v5 TeX L1471, for `ℓ = k = 1`). Elementary proof by
Dirichlet's theorem, a residue class and the window count of `Counting.lean`; the distance to the
nearest integer is `‖(x : UnitAddCircle)‖`.

* `linear_vinogradov`: if `K` is a set of integers in a real interval of length `M`, with
  `κ M ≤ |K|`, and `‖α k + β‖ ≤ ε` for `k ∈ K`, where `16 ε ≤ κ` and `M ≥ 80 / κ²`, then there is
  an integer `0 < q ≤ 5 / κ` with `‖q α‖ ≤ 40 ε / (κ² M)`;
* `linear_vinogradov_const`: the same, with the further conclusion
  `‖q β‖ ≤ 5 ε / κ + R · 40 ε / (κ² M)` for the constant term, where `|k| ≤ R` on `K`;
* `linear_vinogradov_inv`: both, in terms of `D = κ⁻¹ ≥ 1` (all bounds are polynomials in `D`).
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- The real-number arithmetic at the end of the proof of `linear_vinogradov`. -/
theorem linear_vinogradov_arith {κ ε T J : ℝ} (hκ1 : κ ≤ 1) (hT : 0 < T) (hε0 : 0 ≤ ε)
    (hε : 16 * ε ≤ κ) (hTκ : T ≤ κ / 4) (hJ : 16 ≤ κ * J) (hJ0 : 0 ≤ J)
    (hcount : κ * J ≤ (2 * ε / T + 1) * (T * J + 2 * ε + 1)) :
    T * (κ * J) ≤ 9 / 2 * ε := by
  have h1 : κ * J * T ≤ (2 * ε + T) * (T * J + 2 * ε + 1) := by
    have h2 := mul_le_mul_of_nonneg_right hcount hT.le
    have e : (2 * ε / T + 1) * (T * J + 2 * ε + 1) * T = (2 * ε + T) * (T * J + 2 * ε + 1) := by
      field_simp
    exact h2.trans_eq e
  have h3 : (2 * ε + T) * (T * J + 2 * ε + 1)
      = (2 * ε + T) * (T * J) + (2 * ε + T) * (2 * ε + 1) := by
    ring
  have hu : 0 ≤ T * J := by positivity
  have h4 : 5 / 8 * κ * (T * J) ≤ (κ - 2 * ε - T) * (T * J) := by
    apply mul_le_mul_of_nonneg_right _ hu
    linarith only [hε, hTκ]
  have h5 : (2 * ε + T) * (2 * ε + 1) ≤ 9 / 8 * (2 * ε + T) := by
    have h0 : 0 ≤ 2 * ε + T := by positivity
    have h8 : 2 * ε + 1 ≤ 9 / 8 := by linarith only [hε, hκ1]
    calc (2 * ε + T) * (2 * ε + 1) ≤ (2 * ε + T) * (9 / 8) := mul_le_mul_of_nonneg_left h8 h0
      _ = 9 / 8 * (2 * ε + T) := by ring
  have h6 : (5 / 8 * κ) * (T * J) ≤ 9 / 8 * (2 * ε + T) := by linarith only [h1, h3, h4, h5]
  have h7 : 16 * T ≤ T * (κ * J) := by linarith only [mul_le_mul_of_nonneg_left hJ hT.le]
  linarith only [h6, h7, hε0]

/-- Pigeonhole on residue classes: some residue class mod `q` contains at least `|K| / q`
elements of `K`. -/
theorem exists_residue_class (K : Finset ℤ) {q : ℕ} (hq : 0 < q) :
    ∃ r : ℤ, 0 ≤ r ∧ r < q ∧
      (K.card : ℝ) / q ≤ (K.filter (fun k => k % (q : ℤ) = r)).card := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to (s := K)
    (t := Finset.Ico (0 : ℤ) q) (f := fun k : ℤ => k % (q : ℤ)) (b := (K.card : ℝ) / q) (M := ℝ)
    (fun k _ => by
      rw [Finset.mem_Ico]
      exact ⟨Int.emod_nonneg _ hq'.ne', Int.emod_lt_of_pos _ hq'⟩)
    (by simp [hq]) (by
      simp only [Int.card_Ico, sub_zero, Int.toNat_natCast, nsmul_eq_mul]
      rw [mul_div_cancel₀]
      exact_mod_cast hq.ne')
  obtain ⟨r, hr, hr'⟩ := this
  rw [Finset.mem_Ico] at hr
  exact ⟨r, hr.1, hr.2, hr'⟩

/-- **Linear Vinogradov lemma.**  Let `K` be a set of integers in a real interval `[a, a + M]` with
at least `κ M` elements, and suppose `‖α k + β‖_{ℝ/ℤ} ≤ ε` for `k ∈ K`, where `16 ε ≤ κ` and
`M ≥ 80 / κ²`.  Then some integer `0 < q ≤ 5 / κ` satisfies `‖q α‖_{ℝ/ℤ} ≤ 40 ε / (κ² M)`. -/
theorem linear_vinogradov {κ ε a M α β : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hε0 : 0 ≤ ε)
    (hε : 16 * ε ≤ κ) (hM : 80 / κ ^ 2 ≤ M)
    (K : Finset ℤ) (hK : ∀ k ∈ K, a ≤ (k : ℝ) ∧ (k : ℝ) ≤ a + M) (hcard : κ * M ≤ K.card)
    (h : ∀ k ∈ K, ‖((α * k + β : ℝ) : UnitAddCircle)‖ ≤ ε) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ 5 / κ ∧
      ‖((q * α : ℝ) : UnitAddCircle)‖ ≤ 40 * ε / (κ ^ 2 * M) := by
  have hM0 : 0 < M := lt_of_lt_of_le (by positivity) hM
  -- Dirichlet's approximation theorem
  set N : ℕ := ⌈4 / κ⌉₊ with hN
  have hN4 : 4 / κ ≤ N := Nat.le_ceil _
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN4
    exact_mod_cast this
  have hNle : (N : ℝ) ≤ 5 / κ := by
    have h1 : (N : ℝ) < 4 / κ + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : 1 ≤ 1 / κ := by rw [le_div_iff₀ hκ]; linarith
    have h3 : 5 / κ = 4 / κ + 1 / κ := by ring
    linarith
  obtain ⟨j₀, k, hk0, hkN, hk⟩ := Real.exists_int_int_abs_mul_sub_le α hNpos
  lift k to ℕ using hk0.le
  have hq : 0 < k := by exact_mod_cast hk0
  have hqN : (k : ℝ) ≤ N := by exact_mod_cast hkN
  have hq5 : (k : ℝ) ≤ 5 / κ := hqN.trans hNle
  set θ : ℝ := (k : ℝ) * α - j₀ with hθ
  have hθ1 : |θ| ≤ κ / 4 := by
    have h1 : 1 / ((N : ℝ) + 1) ≤ κ / 4 := by
      have h2 : 4 / κ ≤ (N : ℝ) + 1 := by linarith
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      rw [div_le_iff₀ hκ] at h2
      linarith
    have : |θ| ≤ 1 / ((N : ℝ) + 1) := by simpa [hθ] using hk
    linarith
  have hnorm_le : ‖(((k : ℝ) * α : ℝ) : UnitAddCircle)‖ ≤ |θ| := by
    simpa [hθ] using norm_coe_le_abs_sub ((k : ℝ) * α) j₀
  refine ⟨k, hq, hq5, ?_⟩
  have hpos : 0 ≤ 40 * ε / (κ ^ 2 * M) := by positivity
  by_cases hθ0 : θ = 0
  · rw [hθ0, abs_zero] at hnorm_le
    exact hnorm_le.trans hpos
  refine hnorm_le.trans ?_
  -- a residue class
  set T : ℝ := |θ| with hT
  have hTpos : 0 < T := abs_pos.mpr hθ0
  have hKne : 0 < (K.card : ℝ) := lt_of_lt_of_le (by positivity) hcard
  obtain ⟨r, hr0, hrq, hr⟩ := exists_residue_class K hq
  set Kr := K.filter (fun x => x % (k : ℤ) = r) with hKr
  have hq0 : (0 : ℝ) < k := by exact_mod_cast hq
  -- the quotients `j = x / q`
  have hdecomp : ∀ x ∈ Kr, (x : ℝ) = k * ((x / (k : ℤ) : ℤ) : ℝ) + r := by
    intro x hx
    rw [hKr, Finset.mem_filter] at hx
    have := Int.mul_ediv_add_emod x (k : ℤ)
    rw [hx.2] at this
    have h' : ((k : ℤ) * (x / (k : ℤ)) + r : ℤ) = x := this
    exact_mod_cast h'.symm
  set S : Finset ℤ := Kr.image (fun x => x / (k : ℤ)) with hS
  have hinj : Set.InjOn (fun x : ℤ => x / (k : ℤ)) (Kr : Set ℤ) := by
    intro x hx y hy hxy
    have h1 := hdecomp x hx
    have h2 := hdecomp y hy
    simp only at hxy
    rw [hxy] at h1
    exact_mod_cast h1.trans h2.symm
  have hScard : S.card = Kr.card := Finset.card_image_of_injOn hinj
  have hJ0 : 0 ≤ M / k := by positivity
  have hSbd : ∀ j ∈ S, (a - r) / k ≤ (j : ℝ) ∧ (j : ℝ) ≤ (a - r) / k + M / k := by
    intro j hj
    rw [hS, Finset.mem_image] at hj
    obtain ⟨x, hx, rfl⟩ := hj
    have hxK : x ∈ K := (Finset.mem_filter.mp hx).1
    obtain ⟨h1, h2⟩ := hK x hxK
    have h3 := hdecomp x hx
    constructor
    · rw [div_le_iff₀ hq0]; linarith
    · rw [← add_div, le_div_iff₀ hq0]; linarith
  set c : ℝ := α * r + β with hc
  have hSnorm : ∀ j ∈ S, ‖((θ * (j : ℝ) + c : ℝ) : UnitAddCircle)‖ ≤ ε := by
    intro j hj
    rw [hS, Finset.mem_image] at hj
    obtain ⟨x, hx, rfl⟩ := hj
    have hxK : x ∈ K := (Finset.mem_filter.mp hx).1
    have h3 := hdecomp x hx
    have h4 := h x hxK
    have h5 : α * x + β = (θ * ((x / (k : ℤ) : ℤ) : ℝ) + c) + ((j₀ * (x / (k : ℤ)) : ℤ) : ℝ) := by
      rw [h3, hθ, hc]
      push_cast
      ring
    rw [h5, norm_coe_add_intCast] at h4
    exact h4
  have hcount := card_le_of_norm_le_abs hθ0 hε0 hJ0 S hSbd hSnorm
  rw [hScard] at hcount
  -- arithmetic
  have hn : κ * (M / k) ≤ Kr.card := by
    have h1 : (K.card : ℝ) / k ≤ Kr.card := hr
    have h2 : κ * M / k ≤ (K.card : ℝ) / k := by
      apply div_le_div_of_nonneg_right hcard hq0.le
    calc κ * (M / k) = κ * M / k := by ring
      _ ≤ _ := h2.trans h1
  have hJ16 : 16 ≤ κ * (M / k) := by
    have h1 : 16 / κ ≤ M / k := by
      rw [div_le_div_iff₀ hκ hq0]
      have h2 : (k : ℝ) * κ ≤ 5 := by
        have := mul_le_mul_of_nonneg_right hq5 hκ.le
        rwa [div_mul_cancel₀ _ hκ.ne'] at this
      have h3 : 80 ≤ M * κ ^ 2 := by
        rwa [div_le_iff₀ (by positivity)] at hM
      refine le_of_mul_le_mul_right ?_ hκ
      calc 16 * (k : ℝ) * κ = 16 * ((k : ℝ) * κ) := by ring
        _ ≤ 16 * 5 := mul_le_mul_of_nonneg_left h2 (by norm_num)
        _ = 80 := by norm_num
        _ ≤ M * κ ^ 2 := h3
        _ = M * κ * κ := by ring
    rw [div_le_iff₀ hκ] at h1
    linarith
  have key := linear_vinogradov_arith hκ1 hTpos hε0 hε (hθ1) hJ16 hJ0 (hn.trans hcount)
  -- T * (κ * (M / q)) ≤ 9/2 ε  ⟹  T ≤ 40 ε / (κ² M)
  rw [le_div_iff₀ (by positivity)]
  have h5 : (k : ℝ) * κ ≤ 5 := by
    have := mul_le_mul_of_nonneg_right hq5 hκ.le
    rwa [div_mul_cancel₀ _ hκ.ne'] at this
  have h6 : T * (κ * M) ≤ 9 / 2 * ε * k := by
    have : T * (κ * (M / k)) * k = T * (κ * M) := by field_simp
    rw [← this]
    exact mul_le_mul_of_nonneg_right key hq0.le
  have h7 := mul_le_mul_of_nonneg_right h6 hκ.le
  have h8 := mul_le_mul_of_nonneg_left h5 hε0
  linarith only [h7, h8, hε0]

/-- **Linear Vinogradov lemma, with the constant term.**  Under the hypotheses of
`linear_vinogradov`, and `|k| ≤ R` on `K`, the same `q` also satisfies
`‖q β‖ ≤ 5 ε / κ + R · (40 ε / (κ² M))`. -/
theorem linear_vinogradov_const {κ ε a M R α β : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hε0 : 0 ≤ ε)
    (hε : 16 * ε ≤ κ) (hM : 80 / κ ^ 2 ≤ M)
    (K : Finset ℤ) (hK : ∀ k ∈ K, a ≤ (k : ℝ) ∧ (k : ℝ) ≤ a + M) (hcard : κ * M ≤ K.card)
    (hR : ∀ k ∈ K, |(k : ℝ)| ≤ R)
    (h : ∀ k ∈ K, ‖((α * k + β : ℝ) : UnitAddCircle)‖ ≤ ε) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ 5 / κ ∧
      ‖((q * α : ℝ) : UnitAddCircle)‖ ≤ 40 * ε / (κ ^ 2 * M) ∧
      ‖((q * β : ℝ) : UnitAddCircle)‖ ≤ 5 * ε / κ + R * (40 * ε / (κ ^ 2 * M)) := by
  obtain ⟨q, hq, hq5, hα⟩ := linear_vinogradov hκ hκ1 hε0 hε hM K hK hcard h
  have hM0 : 0 < M := lt_of_lt_of_le (by positivity) hM
  have hKne : K.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < K.card := lt_of_lt_of_le (by positivity) hcard
    exact_mod_cast this
  obtain ⟨k, hk⟩ := hKne
  refine ⟨q, hq, hq5, hα, ?_⟩
  have h1 : (q : ℝ) * β = (q : ℤ) * (α * k + β) - k * (q * α) := by
    push_cast
    ring
  have h2 : ‖((((q : ℤ) : ℝ) * (α * k + β) : ℝ) : UnitAddCircle)‖ ≤ q * ε := by
    refine (norm_intCast_mul_coe_le (q : ℤ) _).trans ?_
    have h3 := h k hk
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    simp only [Int.cast_natCast, abs_of_nonneg hq0]
    exact mul_le_mul_of_nonneg_left h3 hq0
  have h4 : ‖(((k : ℝ) * (q * α) : ℝ) : UnitAddCircle)‖ ≤ R * (40 * ε / (κ ^ 2 * M)) := by
    refine (norm_intCast_mul_coe_le k _).trans ?_
    exact mul_le_mul (hR k hk) hα (norm_nonneg _) ((abs_nonneg _).trans (hR k hk))
  have h5 : ‖(((q : ℝ) * β : ℝ) : UnitAddCircle)‖ ≤ q * ε + R * (40 * ε / (κ ^ 2 * M)) := by
    rw [h1]
    refine (norm_coe_sub_le _ _).trans ?_
    linarith
  refine h5.trans ?_
  have : (q : ℝ) * ε ≤ 5 / κ * ε := mul_le_mul_of_nonneg_right hq5 hε0
  have e : 5 / κ * ε = 5 * ε / κ := by ring
  linarith

/-- **Linear Vinogradov lemma in terms of `D = κ⁻¹`.**  Let `K` be a set of integers in a real
interval `[a, a + M]` with `M / D ≤ |K|`, `16 ε D ≤ 1`, `80 D² ≤ M`, and `‖α k + β‖ ≤ ε` on `K`,
`|k| ≤ R`.  Then some integer `0 < q ≤ 5 D` has `‖q α‖ ≤ 40 ε D² / M` and
`‖q β‖ ≤ 5 D ε + R · 40 ε D² / M`. -/
theorem linear_vinogradov_inv {D ε a M R α β : ℝ} (hD : 1 ≤ D) (hε0 : 0 ≤ ε)
    (hε : 16 * ε * D ≤ 1) (hM : 80 * D ^ 2 ≤ M)
    (K : Finset ℤ) (hK : ∀ k ∈ K, a ≤ (k : ℝ) ∧ (k : ℝ) ≤ a + M) (hcard : M / D ≤ K.card)
    (hR : ∀ k ∈ K, |(k : ℝ)| ≤ R)
    (h : ∀ k ∈ K, ‖((α * k + β : ℝ) : UnitAddCircle)‖ ≤ ε) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ 5 * D ∧
      ‖((q * α : ℝ) : UnitAddCircle)‖ ≤ 40 * ε * D ^ 2 / M ∧
      ‖((q * β : ℝ) : UnitAddCircle)‖ ≤ 5 * D * ε + R * (40 * ε * D ^ 2 / M) := by
  have hD0 : 0 < D := lt_of_lt_of_le one_pos hD
  have hκ : 0 < D⁻¹ := inv_pos.mpr hD0
  have hκ1 : D⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hD
  have h1 : 16 * ε ≤ D⁻¹ := by
    rw [← one_div, le_div_iff₀ hD0]
    exact hε
  have h2 : 80 / (D⁻¹) ^ 2 ≤ M := by
    have : 80 / (D⁻¹) ^ 2 = 80 * D ^ 2 := by field_simp
    rwa [this]
  have h3 : D⁻¹ * M ≤ K.card := by
    have : D⁻¹ * M = M / D := by field_simp
    rwa [this]
  obtain ⟨q, hq, hq5, hα, hβ⟩ :=
    linear_vinogradov_const hκ hκ1 hε0 h1 h2 K hK h3 hR h
  have e1 : 5 / D⁻¹ = 5 * D := by field_simp
  have e2 : 40 * ε / ((D⁻¹) ^ 2 * M) = 40 * ε * D ^ 2 / M := by field_simp
  have e3 : 5 * ε / D⁻¹ = 5 * D * ε := by field_simp
  rw [e1] at hq5
  rw [e2] at hα hβ
  rw [e3] at hβ
  exact ⟨q, hq, hq5, hα, hβ⟩

end PrimeCarleson.Proof.Fplus31
