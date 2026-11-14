module

public import PrimeCarleson.Frozen.GowersNormSpec
public import PrimeCarleson.Frozen.GowersNormInterval
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Int.Interval

/-!
# The Eisner–Tao bound `‖f‖_{U³([N])} ≲ ‖f‖_{L²([N])}`

Lemma `l:ET` of `sources/Variational_Carleson.tex` (L710-L715) for `s = 3`, `p₃ = 2`, the only
case the paper uses (L709, applied at L724-L726 in the proof of `e:U3maxmod`), proved from
scratch.  Source: main paper `l:ET`, L710–L715 (the Eisner–Tao inequality); main paper
`s:Prelim`, L702–L707 and L685–L695 (the normalized `L^p` norms).

The route needs no Fourier analysis. For a finitely supported `F : ℤ →₀ ℂ` and
`G_k(x) = F(x) conj F(x + k)` the `U³` sum is, after regrouping the eight corners,
`‖F‖_{U³}⁸ = ∑_k ∑_a |∑_x G_k(x) conj G_k(x + a)|²`
(`gowersLp_sum_eq`, combined with `PrimeCarleson.gowersNorm_spec`). Cauchy–Schwarz gives
Young's inequality `ℓ¹ * ℓ² ⊆ ℓ²`, `∑_a |∑_x G(x) conj G(x + a)|² ≤ ‖G‖_{ℓ¹}² ‖G‖_{ℓ²}²`
(`gowersLp_u2_le`); here `‖G_k‖_{ℓ¹} ≤ ‖F‖_{ℓ²}²` and `∑_k ‖G_k‖_{ℓ²}² = ‖F‖_{ℓ²}⁴`, so
`‖F‖_{U³(ℤ)} ≤ ‖F‖_{ℓ²(ℤ)}` with constant `1` (`gowersNorm_three_le_sqrt`, scale-free).
For the normalization, counting the parallelepipeds `x + {0,1}·h` inside an interval of
`L` integers gives `‖1_I‖_{U³(ℤ)}⁸ ≥ L⁴ / 256` (`gowersNorm_three_indicator_ge`).

Main statements (absolute constant `2`):

* `gowersNorm_three_le_sqrt`: `‖F‖_{U³(ℤ)} ≤ (∑_{x ∈ I} |F x|²)^{1/2}` for `I ⊇ supp F`;
* `gowersNorm_three_Icc_le`: `‖g 1_I‖_{U³} ≤ 2 ‖g‖_{L²(I)} ‖1_I‖_{U³}` for any interval
  `I = [a, b]` (this covers the intervals `[-N, 2N]`, `[2^k]`, `[-2^k, 2^k]` of the paper);
* `gowersNormInterval_three_le`: `‖g‖_{U³([N])} ≤ 2 (N⁻¹ ∑_{n ∈ [N]} |g n|²)^{1/2}` for the
  `gowersNormInterval`.

Only `s = 3` is formalized; the case of general `s` (`p_s = 2^s/(s+1)`) is not needed.
-/

@[expose] public noncomputable section

open scoped ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Common

/-- The difference `Δ_k F(y) = F(y) · conj F(y + k)` (the one-step conjugation difference). -/
def gowersLpDelta (k : ℤ) (F : ℤ → ℂ) (y : ℤ) : ℂ := F y * conj (F (y + k))

/-- Explicit expansion of the triple iterated difference as a product over the cube
`{0,1}^3`: `Δ_{h₀,h₁,h₂} F(x) = ∏_ω C^{|ω|} F(x + ω · h)`. -/
theorem gowersLp_multDiff_three (h : Fin 3 → ℤ) (F : ℤ → ℂ) (x : ℤ) :
    multDiff 3 h F x =
      F x * conj (F (x + h 0)) * conj (F (x + h 1)) * F (x + h 0 + h 1) *
        conj (F (x + h 2)) * F (x + h 0 + h 2) * F (x + h 1 + h 2) *
        conj (F (x + h 0 + h 1 + h 2)) := by
  simp [multDiff, Fin.init, Fin.last]
  ring_nf

/-- The triple difference regrouped as the `U²` pattern for `Δ_{h₂} F`:
`Δ_{h₀,h₁,h₂} F(x) = G(x) conj G(x + h₀) conj G(x + h₁) G(x + h₀ + h₁)` with
`G = Δ_{h₂} F`. -/
theorem gowersLp_multDiff_three_eq (h : Fin 3 → ℤ) (F : ℤ → ℂ) (x : ℤ) :
    multDiff 3 h F x =
      gowersLpDelta (h 2) F x * conj (gowersLpDelta (h 2) F (x + h 0)) *
        conj (gowersLpDelta (h 2) F (x + h 1)) * gowersLpDelta (h 2) F (x + h 0 + h 1) := by
  rw [gowersLp_multDiff_three]
  simp only [gowersLpDelta, map_mul, Complex.conj_conj]
  ring_nf

/-- A nonzero triple difference forces `F` to be nonzero at `x` and at every `x + h i`. -/
theorem gowersLp_multDiff_three_ne_zero (h : Fin 3 → ℤ) (F : ℤ → ℂ) (x : ℤ)
    (hne : multDiff 3 h F x ≠ 0) : F x ≠ 0 ∧ ∀ i : Fin 3, F (x + h i) ≠ 0 := by
  rw [gowersLp_multDiff_three] at hne
  simp only [ne_eq, mul_eq_zero, map_eq_zero, not_or] at hne
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hne
  refine ⟨h1, fun i => ?_⟩
  fin_cases i
  · simpa using h2
  · simpa using h3
  · simpa using h5

/-- A sum over `(Fin 3 → ℤ)`-boxes as a triple sum. -/
theorem gowersLp_sum_piFinset_three {M : Type*} [AddCommMonoid M] (B : Finset ℤ)
    (φ : (Fin 3 → ℤ) → M) :
    ∑ h ∈ Fintype.piFinset (fun _ : Fin 3 => B), φ h =
      ∑ a ∈ B, ∑ b ∈ B, ∑ k ∈ B, φ ![a, b, k] := by
  have : ∑ a ∈ B, ∑ b ∈ B, ∑ k ∈ B, φ ![a, b, k] =
      ∑ p ∈ B ×ˢ B ×ˢ B, φ ![p.1, p.2.1, p.2.2] := by
    simp [Finset.sum_product]
  rw [this]
  refine Finset.sum_nbij' (fun h => (h 0, h 1, h 2)) (fun p => ![p.1, p.2.1, p.2.2])
    ?_ ?_ ?_ ?_ ?_
  · intro h hh
    simp only [Fintype.mem_piFinset] at hh
    simp [hh]
  · intro p hp
    simp only [Finset.mem_product] at hp
    simp only [Fintype.mem_piFinset]
    intro i
    fin_cases i <;> simp [hp]
  · intro h _
    funext i
    fin_cases i <;> simp
  · intro p _
    simp
  · intro h _
    congr 1
    funext i
    fin_cases i <;> simp

/-- The `2^3`-th power of the `U³` norm of a finitely supported `F` as a finite box sum, for
any finite `I ⊇ supp F` and any finite `B` containing all differences of elements of `I`. -/
theorem gowersLp_pow_eight_eq (F : ℤ →₀ ℂ) (I B : Finset ℤ) (hI : ∀ x, F x ≠ 0 → x ∈ I)
    (hB : ∀ x ∈ I, ∀ y ∈ I, y - x ∈ B) :
    ((gowersNorm 3 F : ℝ) : ℂ) ^ 8 =
      ∑ x ∈ I, ∑ a ∈ B, ∑ b ∈ B, ∑ k ∈ B, multDiff 3 ![a, b, k] F x := by
  have h : ((gowersNorm 3 F : ℝ) : ℂ) ^ 8 =
      ∑' p : ℤ × (Fin 3 → ℤ), multDiff 3 p.2 F p.1 := by
    simpa using (PrimeCarleson.gowersNorm_spec 3 F).2.2
  rw [h, tsum_eq_sum (s := I ×ˢ Fintype.piFinset fun _ : Fin 3 => B)]
  · rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact gowersLp_sum_piFinset_three B (fun h => multDiff 3 h F x)
  · rintro ⟨x, h⟩ hxh
    by_contra hne
    obtain ⟨h0, h1⟩ := gowersLp_multDiff_three_ne_zero h F x hne
    apply hxh
    simp only [Finset.mem_product, Fintype.mem_piFinset]
    have hx := hI x h0
    refine ⟨hx, fun i => ?_⟩
    have := hI _ (h1 i)
    simpa using hB x hx _ this

/-- Shifting a function supported in `I` over all differences `B ⊇ I - I`: for `x ∈ I`,
`∑_{a ∈ B} φ(x + a) = ∑_{y ∈ I} φ(y)`. -/
theorem gowersLp_sum_shift {M : Type*} [AddCommMonoid M] (I B : Finset ℤ)
    (hB : ∀ x ∈ I, ∀ y ∈ I, y - x ∈ B) (φ : ℤ → M) (hφ : ∀ y, y ∉ I → φ y = 0)
    {x : ℤ} (hx : x ∈ I) : ∑ a ∈ B, φ (x + a) = ∑ y ∈ I, φ y := by
  rw [← Finset.sum_image (f := φ) (g := fun a => x + a) (fun a _ b _ h => add_left_cancel h)]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro y hy
    rw [Finset.mem_image]
    exact ⟨y - x, hB x hx y hy, by ring⟩
  · intro y _ hy
    exact hφ y hy

/-- A shifted sum of a nonnegative function supported in `I` is at most the unshifted sum. -/
theorem gowersLp_sum_shift_le (I : Finset ℤ) (p : ℤ → ℝ) (hp0 : ∀ y, 0 ≤ p y)
    (hp : ∀ y, y ∉ I → p y = 0) (k : ℤ) : ∑ x ∈ I, p (x + k) ≤ ∑ y ∈ I, p y := by
  rw [← Finset.sum_image (f := p) (g := fun x => x + k) (fun a _ b _ h => add_right_cancel h)]
  calc ∑ y ∈ I.image (fun x => x + k), p y = ∑ y ∈ I.image (fun x => x + k) ∩ I, p y := by
        symm
        refine Finset.sum_subset Finset.inter_subset_left ?_
        intro y hy hyn
        apply hp
        intro hyI
        exact hyn (Finset.mem_inter.2 ⟨hy, hyI⟩)
    _ ≤ ∑ y ∈ I, p y :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun y _ _ => hp0 y)

/-- The `U²` estimate `‖G‖_{U²}⁴ = ∑_a |∑_x G(x) conj G(x + a)|² ≤ ‖G‖_{ℓ¹}² ‖G‖_{ℓ²}²`
(Young's inequality `ℓ¹ * ℓ² ⊆ ℓ²`), for `G` supported in a finite set `I` and the finite set
`B` of all differences. -/
theorem gowersLp_u2_le (I B : Finset ℤ) (hB : ∀ x ∈ I, ∀ y ∈ I, y - x ∈ B) (G : ℤ → ℂ)
    (hG : ∀ y, y ∉ I → G y = 0) :
    ∑ a ∈ B, ‖∑ x ∈ I, G x * conj (G (x + a))‖ ^ 2 ≤
      (∑ x ∈ I, ‖G x‖) ^ 2 * ∑ x ∈ I, ‖G x‖ ^ 2 := by
  have step : ∀ a : ℤ, ‖∑ x ∈ I, G x * conj (G (x + a))‖ ^ 2 ≤
      (∑ x ∈ I, ‖G x‖) * ∑ x ∈ I, ‖G x‖ * ‖G (x + a)‖ ^ 2 := by
    intro a
    have h1 : ‖∑ x ∈ I, G x * conj (G (x + a))‖ ≤ ∑ x ∈ I, ‖G x‖ * ‖G (x + a)‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_))
      simp
    calc ‖∑ x ∈ I, G x * conj (G (x + a))‖ ^ 2
        ≤ (∑ x ∈ I, ‖G x‖ * ‖G (x + a)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ x ∈ I, ‖G x‖) * ∑ x ∈ I, ‖G x‖ * ‖G (x + a)‖ ^ 2 :=
          Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul I (fun x _ => norm_nonneg _)
            (fun x _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)) (fun x _ => by
              apply le_of_eq; ring)
  calc ∑ a ∈ B, ‖∑ x ∈ I, G x * conj (G (x + a))‖ ^ 2
      ≤ ∑ a ∈ B, (∑ x ∈ I, ‖G x‖) * ∑ x ∈ I, ‖G x‖ * ‖G (x + a)‖ ^ 2 :=
        Finset.sum_le_sum fun a _ => step a
    _ = (∑ x ∈ I, ‖G x‖) * ∑ x ∈ I, ‖G x‖ * ∑ a ∈ B, ‖G (x + a)‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
    _ = (∑ x ∈ I, ‖G x‖) * ∑ x ∈ I, ‖G x‖ * ∑ y ∈ I, ‖G y‖ ^ 2 := by
        congr 1
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [gowersLp_sum_shift I B hB (fun y => ‖G y‖ ^ 2) (fun y hy => by simp [hG y hy]) hx]
    _ = (∑ x ∈ I, ‖G x‖) ^ 2 * ∑ x ∈ I, ‖G x‖ ^ 2 := by
        rw [← Finset.sum_mul]; ring

/-- The `U³`-type estimate for a function `F` supported in `I`:
`∑_k ∑_a |∑_x Δ_k F(x) conj Δ_k F(x + a)|² ≤ (∑_x |F(x)|²)⁴`. -/
theorem gowersLp_u3_le (I B : Finset ℤ) (hB : ∀ x ∈ I, ∀ y ∈ I, y - x ∈ B) (F : ℤ → ℂ)
    (hF : ∀ y, y ∉ I → F y = 0) :
    ∑ k ∈ B, ∑ a ∈ B, ‖∑ x ∈ I, gowersLpDelta k F x * conj (gowersLpDelta k F (x + a))‖ ^ 2 ≤
      (∑ x ∈ I, ‖F x‖ ^ 2) ^ 4 := by
  set S : ℝ := ∑ x ∈ I, ‖F x‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun x _ => sq_nonneg _
  have hΔ : ∀ k y, y ∉ I → gowersLpDelta k F y = 0 := fun k y hy => by
    simp [gowersLpDelta, hF y hy]
  have hnorm : ∀ k y, ‖gowersLpDelta k F y‖ = ‖F y‖ * ‖F (y + k)‖ := fun k y => by
    simp [gowersLpDelta]
  -- the `ℓ¹` norm of `Δ_k F` is at most `S`
  have h1 : ∀ k, ∑ x ∈ I, ‖gowersLpDelta k F x‖ ≤ S := by
    intro k
    have hcs : (∑ x ∈ I, ‖F x‖ * ‖F (x + k)‖) ^ 2 ≤ S * S := by
      calc (∑ x ∈ I, ‖F x‖ * ‖F (x + k)‖) ^ 2
          ≤ (∑ x ∈ I, ‖F x‖ ^ 2) * ∑ x ∈ I, ‖F (x + k)‖ ^ 2 :=
            Finset.sum_mul_sq_le_sq_mul_sq I _ _
        _ ≤ S * S := by
            refine mul_le_mul_of_nonneg_left ?_ hS0
            exact gowersLp_sum_shift_le I (fun y => ‖F y‖ ^ 2) (fun y => sq_nonneg _)
              (fun y hy => by simp [hF y hy]) k
    have : ∑ x ∈ I, ‖gowersLpDelta k F x‖ = ∑ x ∈ I, ‖F x‖ * ‖F (x + k)‖ :=
      Finset.sum_congr rfl fun x _ => hnorm k x
    rw [this]
    exact le_of_sq_le_sq (by simpa [sq] using hcs) hS0
  -- the squared `ℓ²` norm of `Δ_k F`
  have h2 : ∀ k, ∑ x ∈ I, ‖gowersLpDelta k F x‖ ^ 2 =
      ∑ x ∈ I, ‖F x‖ ^ 2 * ‖F (x + k)‖ ^ 2 := fun k =>
    Finset.sum_congr rfl fun x _ => by rw [hnorm, mul_pow]
  have h3 : ∑ k ∈ B, ∑ x ∈ I, ‖F x‖ ^ 2 * ‖F (x + k)‖ ^ 2 = S * S := by
    rw [Finset.sum_comm]
    calc ∑ x ∈ I, ∑ k ∈ B, ‖F x‖ ^ 2 * ‖F (x + k)‖ ^ 2 = ∑ x ∈ I, ‖F x‖ ^ 2 * S := by
          refine Finset.sum_congr rfl fun x hx => ?_
          rw [← Finset.mul_sum, gowersLp_sum_shift I B hB (fun y => ‖F y‖ ^ 2)
            (fun y hy => by simp [hF y hy]) hx]
      _ = S * S := by rw [← Finset.sum_mul]
  calc ∑ k ∈ B, ∑ a ∈ B, ‖∑ x ∈ I, gowersLpDelta k F x * conj (gowersLpDelta k F (x + a))‖ ^ 2
      ≤ ∑ k ∈ B, (∑ x ∈ I, ‖gowersLpDelta k F x‖) ^ 2 * ∑ x ∈ I, ‖gowersLpDelta k F x‖ ^ 2 :=
        Finset.sum_le_sum fun k _ => gowersLp_u2_le I B hB _ (hΔ k)
    _ ≤ ∑ k ∈ B, S ^ 2 * ∑ x ∈ I, ‖F x‖ ^ 2 * ‖F (x + k)‖ ^ 2 := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [h2 k]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => norm_nonneg _) (h1 k) 2)
          (Finset.sum_nonneg fun _ _ => by positivity)
    _ = S ^ 4 := by rw [← Finset.mul_sum, h3]; ring

/-- The `U²` sum of `G` as the squared modulus of the autocorrelation:
`∑_x ∑_b G(x) conj G(x + a) conj G(x + b) G(x + a + b) = |∑_x G(x) conj G(x + a)|²`. -/
theorem gowersLp_u2_sum_eq (I B : Finset ℤ) (hB : ∀ x ∈ I, ∀ y ∈ I, y - x ∈ B) (G : ℤ → ℂ)
    (hG : ∀ y, y ∉ I → G y = 0) (a : ℤ) :
    ∑ x ∈ I, ∑ b ∈ B, G x * conj (G (x + a)) * conj (G (x + b)) * G (x + a + b) =
      ((‖∑ x ∈ I, G x * conj (G (x + a))‖ ^ 2 : ℝ) : ℂ) := by
  have step : ∀ x ∈ I, ∑ b ∈ B, G x * conj (G (x + a)) * conj (G (x + b)) * G (x + a + b) =
      ∑ y ∈ I, G x * conj (G (x + a)) * (conj (G y) * G (y + a)) := by
    intro x hx
    rw [← gowersLp_sum_shift I B hB
      (fun y => G x * conj (G (x + a)) * (conj (G y) * G (y + a)))
      (fun y hy => by simp [hG y hy]) hx]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [add_right_comm x a b]
    ring
  rw [Finset.sum_congr rfl step]
  have h2 : ∑ x ∈ I, ∑ y ∈ I, G x * conj (G (x + a)) * (conj (G y) * G (y + a)) =
      (∑ x ∈ I, G x * conj (G (x + a))) * ∑ y ∈ I, conj (G y) * G (y + a) :=
    (Finset.sum_mul_sum _ _ _ _).symm
  rw [h2]
  have h3 : ∑ y ∈ I, conj (G y) * G (y + a) = conj (∑ x ∈ I, G x * conj (G (x + a))) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp [mul_comm]
  rw [h3, Complex.mul_conj']
  push_cast
  ring

/-- The `2^3`-th power of the `U³` norm of `F` as `∑_k ∑_a |∑_x Δ_k F(x) conj Δ_k F(x + a)|²`. -/
theorem gowersLp_sum_eq (I B : Finset ℤ) (hB : ∀ x ∈ I, ∀ y ∈ I, y - x ∈ B) (F : ℤ → ℂ)
    (hF : ∀ y, y ∉ I → F y = 0) :
    ∑ x ∈ I, ∑ a ∈ B, ∑ b ∈ B, ∑ k ∈ B, multDiff 3 ![a, b, k] F x =
      ((∑ k ∈ B, ∑ a ∈ B,
        ‖∑ x ∈ I, gowersLpDelta k F x * conj (gowersLpDelta k F (x + a))‖ ^ 2 : ℝ) : ℂ) := by
  have hreorder : ∑ x ∈ I, ∑ a ∈ B, ∑ b ∈ B, ∑ k ∈ B, multDiff 3 ![a, b, k] F x =
      ∑ k ∈ B, ∑ a ∈ B, ∑ x ∈ I, ∑ b ∈ B, multDiff 3 ![a, b, k] F x := by
    calc ∑ x ∈ I, ∑ a ∈ B, ∑ b ∈ B, ∑ k ∈ B, multDiff 3 ![a, b, k] F x
        = ∑ a ∈ B, ∑ x ∈ I, ∑ b ∈ B, ∑ k ∈ B, multDiff 3 ![a, b, k] F x := Finset.sum_comm
      _ = ∑ a ∈ B, ∑ x ∈ I, ∑ k ∈ B, ∑ b ∈ B, multDiff 3 ![a, b, k] F x :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = ∑ a ∈ B, ∑ k ∈ B, ∑ x ∈ I, ∑ b ∈ B, multDiff 3 ![a, b, k] F x :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ k ∈ B, ∑ a ∈ B, ∑ x ∈ I, ∑ b ∈ B, multDiff 3 ![a, b, k] F x := Finset.sum_comm
  rw [hreorder, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hG : ∀ y, y ∉ I → gowersLpDelta k F y = 0 := fun y hy => by
    simp [gowersLpDelta, hF y hy]
  rw [← gowersLp_u2_sum_eq I B hB (gowersLpDelta k F) hG a]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun b _ => ?_
  rw [gowersLp_multDiff_three_eq]
  simp

/-- The `2^3`-th power of the `U³(ℤ)` norm of a finitely supported `F` is at most the fourth
power of the squared `ℓ²` norm over any finite set `I` containing the support. -/
theorem gowersNorm_three_pow_eight_le (F : ℤ →₀ ℂ) (I : Finset ℤ) (hI : ∀ x, F x ≠ 0 → x ∈ I) :
    gowersNorm 3 F ^ 8 ≤ (∑ x ∈ I, ‖F x‖ ^ 2) ^ 4 := by
  classical
  set B : Finset ℤ := (I ×ˢ I).image (fun p => p.2 - p.1) with hBdef
  have hB : ∀ x ∈ I, ∀ y ∈ I, y - x ∈ B := fun x hx y hy =>
    Finset.mem_image.2 ⟨(x, y), Finset.mem_product.2 ⟨hx, hy⟩, rfl⟩
  have hF : ∀ y, y ∉ I → F y = 0 := fun y hy => by
    by_contra h
    exact hy (hI y h)
  have h := gowersLp_pow_eight_eq F I B hI hB
  rw [gowersLp_sum_eq I B hB F hF] at h
  have h' : gowersNorm 3 F ^ 8 = ∑ k ∈ B, ∑ a ∈ B,
      ‖∑ x ∈ I, gowersLpDelta k F x * conj (gowersLpDelta k F (x + a))‖ ^ 2 := by
    exact_mod_cast h
  rw [h']
  exact gowersLp_u3_le I B hB F hF

/-- **Eisner–Tao for `s = 3` on `ℤ`, with constant `1`**: `‖F‖_{U³(ℤ)} ≤ ‖F‖_{ℓ²(ℤ)}`, for any
finite set `I` containing the support of `F`. -/
theorem gowersNorm_three_le_sqrt (F : ℤ →₀ ℂ) (I : Finset ℤ) (hI : ∀ x, F x ≠ 0 → x ∈ I) :
    gowersNorm 3 F ≤ Real.sqrt (∑ x ∈ I, ‖F x‖ ^ 2) := by
  have h := gowersNorm_three_pow_eight_le F I hI
  have hS : 0 ≤ ∑ x ∈ I, ‖F x‖ ^ 2 := Finset.sum_nonneg fun x _ => sq_nonneg _
  have h8 : (Real.sqrt (∑ x ∈ I, ‖F x‖ ^ 2)) ^ 8 = (∑ x ∈ I, ‖F x‖ ^ 2) ^ 4 := by
    rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, Real.sq_sqrt hS]
  exact le_of_pow_le_pow_left₀ (by norm_num) (Real.sqrt_nonneg _) (h8 ▸ h)

/-- Monotonicity of a nonnegative fourfold box sum in each of its index sets. -/
theorem gowersLp_sum4_mono (X I J B : Finset ℤ) (T : ℤ → ℤ → ℤ → ℤ → ℝ)
    (h0 : ∀ x a b k, 0 ≤ T x a b k) (hXI : X ⊆ I) (hJB : J ⊆ B) :
    ∑ x ∈ X, ∑ a ∈ J, ∑ b ∈ J, ∑ k ∈ J, T x a b k ≤
      ∑ x ∈ I, ∑ a ∈ B, ∑ b ∈ B, ∑ k ∈ B, T x a b k := by
  have n1 : ∀ x a b, 0 ≤ ∑ k ∈ B, T x a b k := fun x a b =>
    Finset.sum_nonneg fun k _ => h0 x a b k
  have n2 : ∀ x a, 0 ≤ ∑ b ∈ B, ∑ k ∈ B, T x a b k := fun x a =>
    Finset.sum_nonneg fun b _ => n1 x a b
  have n3 : ∀ x, 0 ≤ ∑ a ∈ B, ∑ b ∈ B, ∑ k ∈ B, T x a b k := fun x =>
    Finset.sum_nonneg fun a _ => n2 x a
  calc ∑ x ∈ X, ∑ a ∈ J, ∑ b ∈ J, ∑ k ∈ J, T x a b k
      ≤ ∑ x ∈ X, ∑ a ∈ B, ∑ b ∈ B, ∑ k ∈ B, T x a b k := by
        refine Finset.sum_le_sum fun x _ => ?_
        calc ∑ a ∈ J, ∑ b ∈ J, ∑ k ∈ J, T x a b k
            ≤ ∑ a ∈ J, ∑ b ∈ B, ∑ k ∈ B, T x a b k := by
              refine Finset.sum_le_sum fun a _ => ?_
              calc ∑ b ∈ J, ∑ k ∈ J, T x a b k ≤ ∑ b ∈ J, ∑ k ∈ B, T x a b k :=
                    Finset.sum_le_sum fun b _ =>
                      Finset.sum_le_sum_of_subset_of_nonneg hJB (fun k _ _ => h0 x a b k)
                _ ≤ ∑ b ∈ B, ∑ k ∈ B, T x a b k :=
                    Finset.sum_le_sum_of_subset_of_nonneg hJB (fun b _ _ => n1 x a b)
          _ ≤ ∑ a ∈ B, ∑ b ∈ B, ∑ k ∈ B, T x a b k :=
              Finset.sum_le_sum_of_subset_of_nonneg hJB (fun a _ _ => n2 x a)
    _ ≤ ∑ x ∈ I, ∑ a ∈ B, ∑ b ∈ B, ∑ k ∈ B, T x a b k :=
        Finset.sum_le_sum_of_subset_of_nonneg hXI (fun x _ _ => n3 x)

/-- **Size of the normalizing constant**: for the indicator of an interval of `L` consecutive
integers, `‖1_{[a, a + L)}‖_{U³(ℤ)}⁸ ≥ L⁴ / 256` (the parallelepipeds inside the interval). -/
theorem gowersNorm_three_indicator_ge (a : ℤ) (L : ℕ) :
    (L : ℝ) ^ 4 ≤
      256 * gowersNorm 3 (Finsupp.indicator (Finset.Icc a (a + L - 1)) fun _ _ => (1 : ℂ)) ^ 8 := by
  classical
  set I : Finset ℤ := Finset.Icc a (a + L - 1) with hIdef
  set B : Finset ℤ := Finset.Icc (-(L : ℤ)) L with hBdef
  set F : ℤ →₀ ℂ := Finsupp.indicator I fun _ _ => (1 : ℂ) with hFdef
  set ind : ℤ → ℝ := fun y => if y ∈ I then 1 else 0 with hind
  have hFy : ∀ y, F y = ((ind y : ℝ) : ℂ) := fun y => by
    by_cases hy : y ∈ I <;> simp [hFdef, hind, Finsupp.indicator_apply, hy]
  have hind0 : ∀ y, 0 ≤ ind y := fun y => by
    by_cases hy : y ∈ I <;> simp [hind, hy]
  have hI : ∀ x, F x ≠ 0 → x ∈ I := fun x hx => by
    by_contra hxI
    exact hx (by simp [hFy, hind, hxI])
  have hB : ∀ x ∈ I, ∀ y ∈ I, y - x ∈ B := fun x hx y hy => by
    simp only [hIdef, hBdef, Finset.mem_Icc] at hx hy ⊢
    omega
  have hmd : ∀ (h : Fin 3 → ℤ) (x : ℤ), multDiff 3 h F x =
      ((ind x * ind (x + h 0) * ind (x + h 1) * ind (x + h 0 + h 1) * ind (x + h 2) *
        ind (x + h 0 + h 2) * ind (x + h 1 + h 2) * ind (x + h 0 + h 1 + h 2) : ℝ) : ℂ) := by
    intro h x
    rw [gowersLp_multDiff_three]
    simp only [hFy, Complex.conj_ofReal]
    push_cast
    ring
  set T : ℤ → ℤ → ℤ → ℤ → ℝ := fun x a' b k => (multDiff 3 ![a', b, k] F x).re with hT
  have hT0 : ∀ x a' b k, 0 ≤ T x a' b k := fun x a' b k => by
    simp only [hT, hmd, Complex.ofReal_re]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (hind0 _) (hind0 _)) (hind0 _)) (hind0 _)) (hind0 _)) (hind0 _))
      (hind0 _)) (hind0 _)
  have hpow := gowersLp_pow_eight_eq F I B hI hB
  have hpow' : gowersNorm 3 F ^ 8 = ∑ x ∈ I, ∑ a' ∈ B, ∑ b ∈ B, ∑ k ∈ B, T x a' b k := by
    have := congrArg Complex.re hpow
    simpa [Complex.re_sum, ← Complex.ofReal_pow, hT] using this
  -- the smaller box
  set m : ℕ := (L + 3) / 4 with hm
  set X : Finset ℤ := Finset.Ico a (a + m) with hX
  set J : Finset ℤ := Finset.Ico 0 (m : ℤ) with hJ
  have hXI : X ⊆ I := fun x hx => by
    simp only [hX, hIdef, Finset.mem_Ico, Finset.mem_Icc] at hx ⊢
    omega
  have hJB : J ⊆ B := fun x hx => by
    simp only [hJ, hBdef, Finset.mem_Ico, Finset.mem_Icc] at hx ⊢
    omega
  have hT1 : ∀ x ∈ X, ∀ a' ∈ J, ∀ b ∈ J, ∀ k ∈ J, T x a' b k = 1 := by
    intro x hx a' ha' b hb k hk
    simp only [hX, hJ, Finset.mem_Ico] at hx ha' hb hk
    simp only [hT, hmd, Complex.ofReal_re]
    have hi : ∀ y, a ≤ y → y ≤ a + L - 1 → ind y = 1 := fun y h1 h2 => by
      have hy : y ∈ I := Finset.mem_Icc.2 ⟨h1, h2⟩
      simp [hind, hy]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    have hmL : 4 * (m : ℤ) ≤ L + 3 := by omega
    rw [hi x (by omega) (by omega), hi (x + a') (by omega) (by omega),
      hi (x + b) (by omega) (by omega), hi (x + a' + b) (by omega) (by omega),
      hi (x + k) (by omega) (by omega), hi (x + a' + k) (by omega) (by omega),
      hi (x + b + k) (by omega) (by omega), hi (x + a' + b + k) (by omega) (by omega)]
    norm_num
  have hlow : ((m : ℝ)) ^ 4 ≤ gowersNorm 3 F ^ 8 := by
    rw [hpow']
    refine le_trans (le_of_eq ?_) (gowersLp_sum4_mono X I J B T hT0 hXI hJB)
    rw [Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun a' ha' =>
      Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun k hk => hT1 x hx a' ha' b hb k hk]
    simp [hX, hJ]
    ring
  have hLm : (L : ℝ) ≤ 4 * m := by
    have : L ≤ 4 * m := by omega
    exact_mod_cast this
  calc (L : ℝ) ^ 4 ≤ (4 * (m : ℝ)) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hLm 4
    _ = 256 * (m : ℝ) ^ 4 := by ring
    _ ≤ 256 * gowersNorm 3 F ^ 8 := by gcongr

/-- **Eisner–Tao for `s = 3` on an interval of `L` consecutive integers** (unnormalized form):
`‖g 1_I‖_{U³(ℤ)} ≤ 2 ‖g‖_{L²(I)} ‖1_I‖_{U³(ℤ)}` for `I = {a, …, a + L - 1}`, where
`‖g‖_{L²(I)}² = |I|⁻¹ ∑_{n ∈ I} |g n|²`. -/
theorem gowersNorm_three_indicator_le (a : ℤ) (L : ℕ) (g : ℤ → ℂ) :
    gowersNorm 3 (Finsupp.indicator (Finset.Icc a (a + L - 1)) fun n _ => g n) ≤
      2 * ((L : ℝ)⁻¹ * ∑ n ∈ Finset.Icc a (a + L - 1), ‖g n‖ ^ 2) ^ ((1 : ℝ) / 2) *
        gowersNorm 3 (Finsupp.indicator (Finset.Icc a (a + L - 1)) fun _ _ => (1 : ℂ)) := by
  classical
  set I : Finset ℤ := Finset.Icc a (a + L - 1) with hIdef
  set F : ℤ →₀ ℂ := Finsupp.indicator I fun n _ => g n with hFdef
  set V : ℤ →₀ ℂ := Finsupp.indicator I fun _ _ => (1 : ℂ) with hVdef
  set S : ℝ := ∑ n ∈ I, ‖g n‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun x _ => sq_nonneg _
  have hI : ∀ x, F x ≠ 0 → x ∈ I := fun x hx => by
    by_contra hxI
    exact hx (by simp [hFdef, Finsupp.indicator_apply, hxI])
  have hSF : ∑ x ∈ I, ‖F x‖ ^ 2 = S := Finset.sum_congr rfl fun x hx => by
    simp [hFdef, Finsupp.indicator_apply, hx]
  have hu : gowersNorm 3 F ≤ Real.sqrt S := by
    have := gowersNorm_three_le_sqrt F I hI
    rwa [hSF] at this
  have hv0 : 0 ≤ gowersNorm 3 V := (PrimeCarleson.gowersNorm_spec 3 V).2.1
  have hu0 : 0 ≤ gowersNorm 3 F := (PrimeCarleson.gowersNorm_spec 3 F).2.1
  rcases Nat.eq_zero_or_pos L with hL | hL
  · have hI0 : I = ∅ := by
      ext x
      simp only [hIdef, Finset.mem_Icc, Finset.notMem_empty, iff_false]
      omega
    have hS' : S = 0 := by rw [hS, hI0]; simp
    rw [hS'] at hu
    simp only [Real.sqrt_zero] at hu
    have : 0 ≤ 2 * ((L : ℝ)⁻¹ * S) ^ ((1 : ℝ) / 2) * gowersNorm 3 V := by positivity
    linarith
  · have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
    have hlow := gowersNorm_three_indicator_ge a L
    have hv : Real.sqrt L / 2 ≤ gowersNorm 3 V := by
      refine le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) hv0 ?_
      have h8 : (Real.sqrt L / 2) ^ 8 = (L : ℝ) ^ 4 / 256 := by
        rw [div_pow, show (8 : ℕ) = 2 * 4 from rfl, pow_mul, Real.sq_sqrt hLpos.le]
        norm_num
      rw [h8, div_le_iff₀ (by norm_num : (0 : ℝ) < 256)]
      linarith
    have hrpow : ((L : ℝ)⁻¹ * S) ^ ((1 : ℝ) / 2) = Real.sqrt ((L : ℝ)⁻¹ * S) := by
      rw [Real.sqrt_eq_rpow]
    rw [hrpow]
    have hkey : Real.sqrt S = Real.sqrt ((L : ℝ)⁻¹ * S) * Real.sqrt L := by
      rw [← Real.sqrt_mul (by positivity)]
      congr 1
      field_simp
    calc gowersNorm 3 F ≤ Real.sqrt S := hu
      _ = 2 * Real.sqrt ((L : ℝ)⁻¹ * S) * (Real.sqrt L / 2) := by rw [hkey]; ring
      _ ≤ 2 * Real.sqrt ((L : ℝ)⁻¹ * S) * gowersNorm 3 V :=
          mul_le_mul_of_nonneg_left hv (by positivity)

/-- **Eisner–Tao for `s = 3` on an arbitrary integer interval** `I = {a, …, b}`:
`‖g 1_I‖_{U³(ℤ)} ≤ 2 ‖g‖_{L²(I)} ‖1_I‖_{U³(ℤ)}`, i.e. `‖g‖_{U³(I)} ≤ 2 ‖g‖_{L²(I)}` in the
normalization of the main paper `s:Prelim`, L702–L707. -/
theorem gowersNorm_three_Icc_le (a b : ℤ) (g : ℤ → ℂ) :
    gowersNorm 3 (Finsupp.indicator (Finset.Icc a b) fun n _ => g n) ≤
      2 * (((Finset.Icc a b).card : ℝ)⁻¹ * ∑ n ∈ Finset.Icc a b, ‖g n‖ ^ 2) ^ ((1 : ℝ) / 2) *
        gowersNorm 3 (Finsupp.indicator (Finset.Icc a b) fun _ _ => (1 : ℂ)) := by
  have hI : Finset.Icc a (a + ((b + 1 - a).toNat : ℕ) - 1) = Finset.Icc a b := by
    ext x
    simp only [Finset.mem_Icc]
    omega
  have := gowersNorm_three_indicator_le a (b + 1 - a).toNat g
  rw [hI] at this
  rwa [Int.card_Icc]

/-- **Lemma `l:ET` for `s = 3`** (`p₃ = 2`): the normalized `U³([N])` norm is bounded by twice
the normalized `L²([N])` norm, `‖g‖_{U³([N])} ≤ 2 (N⁻¹ ∑_{n ∈ [N]} |g n|²)^{1/2}`, with the
absolute constant `2`. -/
theorem gowersNormInterval_three_le (N : ℕ+) (g : ℤ → ℂ) :
    gowersNormInterval 3 N g ≤
      2 * ((N : ℝ)⁻¹ * ∑ n ∈ Finset.Icc (1 : ℤ) N, ‖g n‖ ^ 2) ^ ((1 : ℝ) / 2) := by
  have hI : Finset.Icc (1 : ℤ) (1 + (N : ℕ) - 1) = Finset.Icc (1 : ℤ) N := by
    ext x
    simp only [Finset.mem_Icc]
    omega
  have hup := gowersNorm_three_indicator_le 1 N g
  have hlow := gowersNorm_three_indicator_ge 1 N
  rw [hI] at hup hlow
  have hV : restrictInterval N 1 = Finsupp.indicator (Finset.Icc (1 : ℤ) N) fun _ _ => (1 : ℂ) :=
    rfl
  have hF : restrictInterval N g = Finsupp.indicator (Finset.Icc (1 : ℤ) N) fun n _ => g n :=
    rfl
  have hv0 : 0 < gowersNorm 3 (restrictInterval N 1) := by
    rw [hV]
    have hv0' : 0 ≤ gowersNorm 3 (Finsupp.indicator (Finset.Icc (1 : ℤ) N) fun _ _ => (1 : ℂ)) :=
      (PrimeCarleson.gowersNorm_spec 3 _).2.1
    refine lt_of_le_of_ne hv0' (fun h0 => ?_)
    rw [← h0] at hlow
    have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
    norm_num at hlow
    exact absurd hlow (not_le.2 (pow_pos hNpos 4))
  unfold gowersNormInterval
  rw [div_le_iff₀ hv0, hF, hV]
  exact hup

end PrimeCarleson.Proof.Common
