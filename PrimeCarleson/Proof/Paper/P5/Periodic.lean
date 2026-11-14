module

public import PrimeCarleson.Proof.Paper.P5.Blocks
public import PrimeCarleson.Proof.Paper.Defs.Norms
public import PrimeCarleson.Proof.Goal0.Operators
public import PrimeCarleson.Proof.Goal0.InverseMd
public import PrimeCarleson.Frozen.PeriodicBlockMaxBound

/-!
# The periodic setting: `N = 𝒬_B`, `M_B`, `𝔪_B`

Source: main paper `s:per`, L2117–L2129 and L2281, on top of the `periodicBlockMax` and the
proved `periodicBlockMax_bound` (`Goal0/*`).

* `M_B` is the `periodicBlockMax B` (L2117–L2125): `𝔼_{r ∈ ℤ/N}` is the average over
  `r ∈ {0, …, N-1}`; `MB_periodic`: `M_B f` is `N`-periodic for `N`-periodic `f`
  (L2281);
* `mB B = 𝔪_B := sup {‖M_B f‖ : ‖f‖ = 1}` over `N`-periodic `f` (the norms `ℓ²` of one period,
  whose normalization by `N^{-1/2}` cancels in the quotient), `l2_MB_le_mB_mul`,
  `mB_le_of_forall`, `bddAbove_mBSet`, and the link with the bound
  `mB_le_of_sum_bound`, `mB_le_of_blockPartition`;
* `inv_totient_le_mB` and `inv_le_mB` (L2126–L2129): `𝔪_B ≥ max_{q ∈ B} 1/φ(q) ≥ Q^{-1}`
  for a nonempty block `B ⊆ (Q/2, Q]` of squarefree integers (test on the character
  `f(y) = e(y (q-1)/q)`, orthogonality of the characters of `ℤ/N`).
-/

@[expose] public noncomputable section

open scoped ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0

/-! ### `M_B`, periodic extension -/

/-- `M_B f` is `N`-periodic when `f` is (`N = 𝒬_B`). -/
theorem MB_periodic (B : Finset ℕ) {f : ℤ → ℂ} (hf : Function.Periodic f (lcmQ B : ℤ)) :
    Function.Periodic (periodicBlockMax B f) (lcmQ B : ℤ) := by
  intro x
  unfold periodicBlockMax
  refine iSup_congr fun θ => ?_
  congr 2
  refine Finset.sum_congr rfl fun r _ => ?_
  have : f (x + (lcmQ B : ℤ) - ((r : ℕ) : ℤ)) = f (x - ((r : ℕ) : ℤ)) := by
    rw [show x + (lcmQ B : ℤ) - ((r : ℕ) : ℤ) = x - ((r : ℕ) : ℤ) + (lcmQ B : ℤ) by ring]
    exact hf _
  rw [this]

/-! ### The operator norm `𝔪_B` -/

/-- The values `‖M_B f‖` over `N`-periodic `f` of unit `ℓ²([0, N))` norm. The normalization of
`L²(ℤ/N)` by `N^{-1/2}` multiplies `‖f‖` and `‖M_B f‖` by the same constant, so the supremum is
the operator norm of the paper (L2122-L2125). -/
def mBSet (B : Finset ℕ) : Set ℝ :=
  {c | ∃ f : ℤ → ℂ, Function.Periodic f (lcmQ B : ℤ) ∧ l2 (lcmQ B) (fun x => ‖f x‖) = 1 ∧
    c = l2 (lcmQ B) (periodicBlockMax B f)}

/-- `𝔪_B := ‖M_B‖_{L²(ℤ/N) → L²(ℤ/N)} = sup_{‖f‖ = 1} ‖M_B f‖` (Source: main paper `s:per`,
L2117–L2125). -/
def mB (B : Finset ℕ) : ℝ := sSup (mBSet B)

/-- The crude bound `‖M_B f‖ ≤ (∑_{q ∈ B} τ(q)/φ(q)) ‖f‖` over one period. -/
theorem l2_MB_le_const {B : Finset ℕ} (hB : ∀ q ∈ B, 0 < q) {f : ℤ → ℂ}
    (hf : Function.Periodic f (lcmQ B : ℤ)) :
    l2 (lcmQ B) (periodicBlockMax B f) ≤
      (∑ q ∈ B, ((q.totient : ℝ))⁻¹ * q.divisors.card) * l2 (lcmQ B) (fun x => ‖f x‖) := by
  refine (l2_periodicBlockMax_le_sum hB f).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun q hq => ?_
  have hqN : q ∣ lcmQ B := dvd_lcmQ hq
  have h1 : ∑ d ∈ q.divisors, l2 (B.lcm id) (fiberMax (B.lcm id) d f) ≤
      q.divisors.card * l2 (lcmQ B) (fun x => ‖f x‖) := by
    calc _ ≤ ∑ _d ∈ q.divisors, l2 (lcmQ B) (fun x => ‖f x‖) :=
          Finset.sum_le_sum fun d hd => l2_fiberMax_le (Nat.pos_of_mem_divisors hd)
            ((Nat.dvd_of_mem_divisors hd).trans hqN) hf
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  calc ((q.totient : ℝ))⁻¹ * ∑ d ∈ q.divisors, l2 (B.lcm id) (fiberMax (B.lcm id) d f)
      ≤ ((q.totient : ℝ))⁻¹ * (q.divisors.card * l2 (lcmQ B) (fun x => ‖f x‖)) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 (Nat.cast_nonneg _))
    _ = ((q.totient : ℝ))⁻¹ * q.divisors.card * l2 (lcmQ B) (fun x => ‖f x‖) := by ring

theorem bddAbove_mBSet {B : Finset ℕ} (hB : ∀ q ∈ B, 0 < q) : BddAbove (mBSet B) := by
  refine ⟨∑ q ∈ B, ((q.totient : ℝ))⁻¹ * q.divisors.card, ?_⟩
  rintro c ⟨f, hf, hn, rfl⟩
  have := l2_MB_le_const hB hf
  rwa [hn, mul_one] at this

/-- `l2 N` of the constant function `c ≥ 0` is `c √N`. -/
theorem l2_const (N : ℕ) {c : ℝ} (hc : 0 ≤ c) : l2 N (fun _ => c) = c * √(N : ℝ) := by
  unfold l2
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Real.sqrt_mul (Nat.cast_nonneg _),
    Real.sqrt_sq hc, mul_comm]

theorem mBSet_nonempty {B : Finset ℕ} (hB : ∀ q ∈ B, 0 < q) : (mBSet B).Nonempty := by
  have hN : (0 : ℝ) < lcmQ B := by exact_mod_cast lcmQ_pos hB
  have hs : 0 < √((lcmQ B : ℕ) : ℝ) := Real.sqrt_pos.2 hN
  refine ⟨_, fun _ => (√((lcmQ B : ℕ) : ℝ) : ℂ)⁻¹, fun _ => rfl, ?_, rfl⟩
  have h : (fun x : ℤ => ‖((√((lcmQ B : ℕ) : ℝ) : ℝ) : ℂ)⁻¹‖) =
      fun _ => (√((lcmQ B : ℕ) : ℝ))⁻¹ := by
    funext x
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hs.le]
  rw [h, l2_const _ (inv_nonneg.2 hs.le), inv_mul_cancel₀ hs.ne']

/-- `‖M_B f‖ ≤ 𝔪_B ‖f‖` for `N`-periodic `f`. -/
theorem l2_MB_le_mB_mul {B : Finset ℕ} (hB : ∀ q ∈ B, 0 < q) {f : ℤ → ℂ}
    (hf : Function.Periodic f (lcmQ B : ℤ)) :
    l2 (lcmQ B) (periodicBlockMax B f) ≤ mB B * l2 (lcmQ B) (fun x => ‖f x‖) := by
  set t := l2 (lcmQ B) (fun x => ‖f x‖) with ht
  have ht0 : 0 ≤ t := l2_nonneg _ _
  rcases ht0.eq_or_lt with h0 | hpos
  · have := l2_MB_le_const hB hf
    rw [← ht, ← h0] at this
    rw [← h0]
    simpa using this
  · let g : ℤ → ℂ := fun x => ((t : ℝ) : ℂ)⁻¹ * f x
    have hg : Function.Periodic g (lcmQ B : ℤ) := fun x => by simp only [g, hf x]
    have hgn : l2 (lcmQ B) (fun x => ‖g x‖) = 1 := by
      have : (fun x => ‖g x‖) = fun x => t⁻¹ * ‖f x‖ := by
        funext x
        simp only [g, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hpos.le]
      rw [this, l2_const_mul _ (inv_nonneg.2 hpos.le), ← ht, inv_mul_cancel₀ hpos.ne']
    have hMg : periodicBlockMax B g = fun x => t⁻¹ * periodicBlockMax B f x := by
      funext x
      have : g = ((t : ℝ) : ℂ)⁻¹ • f := rfl
      rw [this, periodicBlockMax_smul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg hpos.le]
    have hle : l2 (lcmQ B) (periodicBlockMax B g) ≤ mB B :=
      le_csSup (bddAbove_mBSet hB) ⟨g, hg, hgn, rfl⟩
    rw [hMg, l2_const_mul _ (inv_nonneg.2 hpos.le)] at hle
    rw [inv_mul_le_iff₀ hpos] at hle
    linarith

/-- `𝔪_B ≤ C` if `‖M_B f‖ ≤ C ‖f‖` for every `N`-periodic `f`. -/
theorem mB_le_of_forall {B : Finset ℕ} (hB : ∀ q ∈ B, 0 < q) {C : ℝ}
    (h : ∀ f : ℤ → ℂ, Function.Periodic f (lcmQ B : ℤ) →
      l2 (lcmQ B) (periodicBlockMax B f) ≤ C * l2 (lcmQ B) (fun x => ‖f x‖)) : mB B ≤ C := by
  refine csSup_le (mBSet_nonempty hB) ?_
  rintro c ⟨f, hf, hn, rfl⟩
  have := h f hf
  rwa [hn, mul_one] at this

/-- `𝔪_B ≤ K` if `∑_{x < N} M_B f(x)² ≤ K² ∑_{x < N} |f(x)|²` for every `N`-periodic `f`, the form
of the `periodicBlockMax_bound`. -/
theorem mB_le_of_sum_bound {B : Finset ℕ} (hB : ∀ q ∈ B, 0 < q) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ f : ℤ → ℂ, Function.Periodic f (lcmQ B : ℤ) →
      ∑ x ∈ Finset.range (lcmQ B), periodicBlockMax B f x ^ 2 ≤
        K ^ 2 * ∑ x ∈ Finset.range (lcmQ B), ‖f x‖ ^ 2) : mB B ≤ K := by
  refine mB_le_of_forall hB fun f hf => ?_
  have h1 := h f hf
  have hsq : l2 (lcmQ B) (periodicBlockMax B f) ≤
      √(K ^ 2 * ∑ x ∈ Finset.range (lcmQ B), ‖f x‖ ^ 2) := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK] at hsq
  exact hsq

/-- **The blocks of a partition satisfy `𝔪_B ≲ Q^{κ-1-ε}`**: the `periodicBlockMax_bound`
applied to every block of a `BlockPartition` (whose blocks meet its hypotheses). -/
theorem mB_le_of_blockPartition :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ ε : ℝ, 0 < ε → ε ≤ κ / 100 →
      ∀ A : ℝ, ∃ C : ℝ, ∀ (j : ℕ) (π : BlockPartition j κ A), ∀ B ∈ π.blocks,
        mB B ≤ |C| * ((2 : ℝ) ^ j) ^ (κ - 1 - ε) := by
  obtain ⟨κ₀, hκ₀, h⟩ := periodicBlockMax_bound
  refine ⟨κ₀, hκ₀, fun κ hκ hκκ₀ ε hε hεκ A => ?_⟩
  obtain ⟨C, hC⟩ := h κ hκ hκκ₀ ε hε hεκ A
  refine ⟨C, fun j π B hB => ?_⟩
  have hpos : ∀ q ∈ B, 0 < q := fun q hq =>
    Nat.pos_of_ne_zero (π.squarefree_of_mem hB hq).ne_zero
  refine mB_le_of_sum_bound hpos (by positivity) fun f hf => ?_
  have := hC j B (π.subset_sqfreeSet hB) (π.card_ge B hB) (π.card_le B hB) f hf
  calc ∑ x ∈ Finset.range (lcmQ B), periodicBlockMax B f x ^ 2
      ≤ (C * ((2 : ℝ) ^ j) ^ (κ - 1 - ε)) ^ 2 * ∑ x ∈ Finset.range (lcmQ B), ‖f x‖ ^ 2 := this
    _ = (|C| * ((2 : ℝ) ^ j) ^ (κ - 1 - ε)) ^ 2 * ∑ x ∈ Finset.range (lcmQ B), ‖f x‖ ^ 2 := by
        rw [mul_pow, mul_pow, sq_abs]

/-! ### The lower bound `𝔪_B ≥ Q^{-1}` (Source: main paper `s:per`, L2126–L2129) -/

/-- The coefficient `μ(q)/φ(q)` of the fraction `a/q` in `w_{Q,B}`. -/
def coefFrac (r : ℚ) : ℂ :=
  (((ArithmeticFunction.moebius r.den : ℤ) : ℝ) / (Nat.totient r.den : ℝ) : ℂ)

theorem exists_int_mul_rat {N : ℕ} {r : ℚ} (h : r.den ∣ N) :
    ∃ k : ℤ, (N : ℝ) * (r : ℝ) = k := by
  obtain ⟨m, hm⟩ := h
  refine ⟨m * r.num, ?_⟩
  have h1 : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
    have := Rat.cast_def (K := ℝ) r
    exact this
  have hd : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_nz
  rw [hm, h1]
  push_cast
  field_simp

/-- Orthogonality of the characters of `ℤ/N`: for `r₀ = a/q` reduced with `q ∈ B`,
`N⁻¹ ∑_{l < N} w_{Q,B}(l) e(-l r₀) = μ(q)/φ(q)`. -/
theorem avg_blockWeight_mul_e_neg {B : Finset ℕ} (hB : ∀ q ∈ B, 0 < q) {r₀ : ℚ}
    (hr₀ : r₀ ∈ reducedFractions B) :
    ((lcmQ B : ℕ) : ℂ)⁻¹ * ∑ l ∈ Finset.range (lcmQ B),
        blockWeight B (l : ℤ) * e (-((l : ℝ) * (r₀ : ℝ))) = coefFrac r₀ := by
  have hN : 0 < lcmQ B := lcmQ_pos hB
  have hNC : ((lcmQ B : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have h1 : ∀ l : ℕ, blockWeight B (l : ℤ) * e (-((l : ℝ) * (r₀ : ℝ))) =
      ∑ r ∈ reducedFractions B, coefFrac r * e ((l : ℝ) * ((r : ℝ) - r₀)) := by
    intro l
    rw [blockWeight_eq_sum_reducedFractions, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [mul_assoc, ← e_add]
    simp only [coefFrac]
    congr 2
    push_cast
    ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ r ∈ reducedFractions B,
      ∑ l ∈ Finset.range (lcmQ B), coefFrac r * e ((l : ℝ) * ((r : ℝ) - r₀)) =
        if r = r₀ then ((lcmQ B : ℕ) : ℂ) * coefFrac r else 0 := by
    intro r hr
    rw [← Finset.mul_sum]
    obtain ⟨k₁, hk₁⟩ := exists_int_mul_rat (N := lcmQ B) (r := r)
      (dvd_lcmQ (mem_reducedFractions.1 hr).2.2)
    obtain ⟨k₂, hk₂⟩ := exists_int_mul_rat (N := lcmQ B) (r := r₀)
      (dvd_lcmQ (mem_reducedFractions.1 hr₀).2.2)
    have hNR : (lcmQ B : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hdiff : ∀ l : ℕ,
        (l : ℝ) * ((r : ℝ) - r₀) = (l : ℝ) * ((k₁ - k₂ : ℤ) : ℝ) / (lcmQ B : ℝ) := by
      intro l
      push_cast
      field_simp
      linear_combination (l : ℝ) * (hk₁ - hk₂)
    simp_rw [hdiff]
    rw [sum_range_e_mul_div hN]
    have hr1 := mem_reducedFractions.1 hr
    have hr0 := mem_reducedFractions.1 hr₀
    by_cases hrr : r = r₀
    · subst hrr
      have : k₁ = k₂ := by
        have : (k₁ : ℝ) = k₂ := by rw [← hk₁, ← hk₂]
        exact_mod_cast this
      simp [this]
      ring
    · rw [ite_eq_right hrr]
      have hnd : ¬ ((lcmQ B : ℕ) : ℤ) ∣ (k₁ - k₂) := by
        rintro ⟨z, hz⟩
        apply hrr
        have h3 : ((r : ℝ) - r₀) = (z : ℝ) := by
          have : ((k₁ - k₂ : ℤ) : ℝ) = (lcmQ B : ℝ) * z := by exact_mod_cast hz
          push_cast at this
          apply mul_left_cancel₀ hNR
          linear_combination hk₁ - hk₂ + this
        have hr1' : (r : ℝ) < 1 := by exact_mod_cast hr1.2.1
        have hr0' : (0 : ℝ) ≤ r₀ := by exact_mod_cast hr0.1
        have hz1 : (z : ℝ) < 1 := by linarith
        have hr1'' : (0 : ℝ) ≤ r := by exact_mod_cast hr1.1
        have hr0'' : (r₀ : ℝ) < 1 := by exact_mod_cast hr0.2.1
        have hz2 : (-1 : ℝ) < z := by linarith
        have hz0 : z = 0 := by
          have a1 : z < 1 := by exact_mod_cast hz1
          have a2 : -1 < z := by exact_mod_cast hz2
          omega
        rw [hz0] at h3
        have : (r : ℝ) = r₀ := by simpa [sub_eq_zero] using h3
        exact_mod_cast this
      rw [ite_eq_right hnd]
      simp
  rw [Finset.sum_congr rfl h2, Finset.sum_ite_eq' (reducedFractions B) r₀]
  rw [ite_eq_left hr₀]
  field_simp

/-- **Lower bound for `𝔪_B`**: `𝔪_B ≥ 1/φ(q)` for every `q ∈ B` (the supremum defining
`𝔪_B` specialized to the character `f(y) = e(y (q-1)/q)`). -/
theorem inv_totient_le_mB {B : Finset ℕ} (hB : ∀ q ∈ B, 0 < q) (hsq : ∀ q ∈ B, Squarefree q)
    {q : ℕ} (hq : q ∈ B) : ((q.totient : ℝ))⁻¹ ≤ mB B := by
  have hN0 : 0 < lcmQ B := lcmQ_pos hB
  have hq0 := hB q hq
  set r₀ : ℚ := ((q - 1 : ℕ) : ℚ) / q with hr₀def
  have hcop : Nat.Coprime (q - 1) q := by
    obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
    simp
  have hden : r₀.den = q := den_natCast_div hq0 hcop
  have hr₀ : r₀ ∈ reducedFractions B := by
    refine mem_reducedFractions.2 ⟨by positivity, ?_, by rwa [hden]⟩
    rw [hr₀def, div_lt_one (by exact_mod_cast hq0)]
    exact_mod_cast (by omega : q - 1 < q)
  obtain ⟨k, hk⟩ := exists_int_mul_rat (N := lcmQ B) (r := r₀)
    (by rw [hden]; exact dvd_lcmQ hq)
  have hs : 0 < √((lcmQ B : ℕ) : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hN0)
  set c : ℂ := ((√((lcmQ B : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ with hc
  have hcnorm : ‖c‖ = (√((lcmQ B : ℕ) : ℝ))⁻¹ := by
    rw [hc, norm_inv, Complex.norm_real, Real.norm_of_nonneg hs.le]
  set F : ℤ → ℂ := fun y => c * e ((y : ℝ) * (r₀ : ℝ)) with hF
  have hper : Function.Periodic F (lcmQ B : ℤ) := by
    intro y
    simp only [hF]
    congr 1
    have : (((y + (lcmQ B : ℤ) : ℤ) : ℝ) * (r₀ : ℝ)) = (y : ℝ) * r₀ + k := by
      push_cast
      linear_combination hk
    rw [this, e_add_intCast]
  have hnF : l2 (lcmQ B) (fun x => ‖F x‖) = 1 := by
    have : (fun x => ‖F x‖) = fun _ => (√((lcmQ B : ℕ) : ℝ))⁻¹ := by
      funext x
      simp only [hF, norm_mul, norm_e, mul_one, hcnorm]
    rw [this, l2_const _ (inv_nonneg.2 hs.le), inv_mul_cancel₀ hs.ne']
  have hcoef : ‖coefFrac r₀‖ = ((q.totient : ℝ))⁻¹ := by
    simp only [coefFrac, hden]
    rw [← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs, abs_div]
    have hμ : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| = 1 := by
      rw [ArithmeticFunction.moebius_apply_of_squarefree (hsq q hq)]
      simp
    rw [hμ, abs_of_pos (by exact_mod_cast Nat.totient_pos.2 hq0), one_div]
  have hMF : ∀ x : ℤ, ‖c‖ * ((q.totient : ℝ))⁻¹ ≤ periodicBlockMax B F x := by
    intro x
    have hN0' : 0 < B.lcm id := hN0
    have horth : ((B.lcm id : ℕ) : ℂ)⁻¹ * ∑ l ∈ Finset.range (B.lcm id),
        blockWeight B (l : ℤ) * e (-((l : ℝ) * (r₀ : ℝ))) = coefFrac r₀ :=
      avg_blockWeight_mul_e_neg hB hr₀
    refine le_trans (le_of_eq ?_) (norm_le_periodicBlockMax B F x ⟨0, hN0'⟩)
    rw [Fin.sum_univ_eq_sum_range (fun r : ℕ => F (x - (r : ℤ)) * blockWeight B (r : ℤ) *
      e (((r : ℕ) : ℝ) * (((⟨0, hN0'⟩ : Fin (B.lcm id)) : ℕ) : ℝ) / ((B.lcm id : ℕ) : ℝ)))
      (B.lcm id)]
    have hterm : ∀ r ∈ Finset.range (B.lcm id),
        F (x - (r : ℤ)) * blockWeight B (r : ℤ) *
          e (((r : ℕ) : ℝ) * (((⟨0, hN0'⟩ : Fin (B.lcm id)) : ℕ) : ℝ) / ((B.lcm id : ℕ) : ℝ)) =
        c * e ((x : ℝ) * r₀) * (blockWeight B (r : ℤ) * e (-((r : ℝ) * (r₀ : ℝ)))) := by
      intro r _
      simp only [hF, Nat.cast_zero, mul_zero, zero_div, e_zero, mul_one]
      have : (((x - (r : ℤ) : ℤ) : ℝ) * (r₀ : ℝ)) = (x : ℝ) * r₀ + -((r : ℝ) * r₀) := by
        push_cast
        ring
      rw [this, e_add]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have h2 : ((B.lcm id : ℕ) : ℂ)⁻¹ * (c * e ((x : ℝ) * r₀) * ∑ r ∈ Finset.range (B.lcm id),
        blockWeight B (r : ℤ) * e (-((r : ℝ) * (r₀ : ℝ)))) =
        c * e ((x : ℝ) * r₀) * (((B.lcm id : ℕ) : ℂ)⁻¹ * ∑ r ∈ Finset.range (B.lcm id),
        blockWeight B (r : ℤ) * e (-((r : ℝ) * (r₀ : ℝ)))) := by ring
    rw [h2, horth, norm_mul, norm_mul, norm_e, mul_one, hcoef]
  have hle := le_csSup (bddAbove_mBSet hB) ⟨F, hper, hnF, rfl⟩
  have hφ : (0 : ℝ) ≤ ((q.totient : ℝ))⁻¹ := inv_nonneg.2 (Nat.cast_nonneg _)
  have hge : l2 (lcmQ B) (fun _ => ‖c‖ * ((q.totient : ℝ))⁻¹) ≤
      l2 (lcmQ B) (periodicBlockMax B F) :=
    l2_mono (fun _ => mul_nonneg (norm_nonneg _) hφ) hMF
  rw [l2_const _ (mul_nonneg (norm_nonneg _) hφ), hcnorm] at hge
  calc ((q.totient : ℝ))⁻¹ = (√((lcmQ B : ℕ) : ℝ))⁻¹ * ((q.totient : ℝ))⁻¹ *
        √((lcmQ B : ℕ) : ℝ) := by field_simp
    _ ≤ _ := hge
    _ ≤ mB B := hle

/-- **Lower bound for `𝔪_B`**: `𝔪_B ≥ Q^{-1}` for a nonempty block `B ⊆ (Q/2, Q]` of
squarefree integers (`Q = 2^j`), since `1/φ(q) ≥ 1/q ≥ 1/Q`. -/
theorem inv_le_mB {B : Finset ℕ} {j : ℕ} (hB : B ⊆ sqfreeSet j) (hne : B.Nonempty) :
    ((2 : ℝ) ^ j)⁻¹ ≤ mB B := by
  obtain ⟨q, hq⟩ := hne
  have hmem := mem_sqfreeSet.1 (hB hq)
  have hpos : ∀ q ∈ B, 0 < q := fun q hq => Nat.pos_of_ne_zero (mem_sqfreeSet.1 (hB hq)).2.2.ne_zero
  refine le_trans ?_ (inv_totient_le_mB hpos (fun q hq => (mem_sqfreeSet.1 (hB hq)).2.2) hq)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hpos q hq
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (hpos q hq)
  refine inv_anti₀ hφ ?_
  have h1 : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have h2 : (q : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast hmem.2.1
  linarith

end PrimeCarleson.Proof.Paper
