module

public import PrimeCarleson.Proof.Paper.Defs.Norms
public import PrimeCarleson.Proof.Common.GowersLp
public import PrimeCarleson.Proof.Common.GowersCauchySchwarz
public import PrimeCarleson.Frozen.GowersNormSpec
public import PrimeCarleson.Frozen.GowersNormInterval

/-!
# Conjugation differences and Gowers norms

The definitions of `sources/Variational_Carleson.tex` L645–L707 and of the companion [F+]
(L496–L516), with the characterization lemmas the later files use. Paper steps proved here:

* the operator `Δ_h f(x) = f(x) conj f(x + h)` (Source: main paper `e:triangle`, L647–L651;
  [F+], L496–L500): `conjDiff` (an alias of `Common.gowersLpDelta`), with `conjDiff_apply`;
* the iterated operator `Δ_{h₁,…,h_s} f = Δ_{h_s}(Δ_{h₁,…,h_{s-1}} f)` (Source: main paper,
  L658–L662; [F+], L507–L511): the `PrimeCarleson.multDiff`, with `multDiff_succ` (the
  recursion) and `multDiff_zero`;
* the squaring identity `|∑ f|² = ∑_{x, h} Δ_h f(x)` (Source: main paper `e;double`, L652–L657):
  `norm_sq_tsum_eq_tsum_conjDiff` (sum over `ℤ × ℤ`
  of a finitely supported function) and `norm_sq_sum_eq_sum_conjDiff` (the finite box form);
* the definition `‖f‖_{U^s(ℤ)}^{2^s} = ∑_{x, h₁, …, h_s} Δ_{h₁,…,h_s} f(x)` of the Gowers norm
  (Source: main paper `e;GowersDef`, L663–L667; [F+], L512–L516): the
  `PrimeCarleson.gowersNorm`, with `gowersNorm_pow_eq_tsum`, `gowersSum_support_finite`
  and the finite box form `gowersNorm_pow_eq_sum_box` (all `s ≥ 1`, from `multDiff_ne_zero`);
* the Gowers sum is a nonnegative real (the paper does not state this step, which the `2^s`-th
  root presupposes, near L663–L667): this is part of the `gowersNorm_spec`, used in
  `gowersNorm_nonneg` and `gowersNorm_pow_eq_re_tsum`;
* the normalized norm `‖f‖_{U^s(I)} = ‖f‖_{U^s(ℤ)} / ‖1_I‖_{U^s(ℤ)}` (Source: main paper,
  L702–L707): for a
  finite set `I ⊆ ℤ` (in particular the intervals `[N]`, `[-N, 2N]`, `[2^k]`, `[-2^k, 2^k]`),
  `gowersNormOn s I g`, with `gowersNormInterval_eq_gowersNormOn` (the
  `gowersNormInterval s N = gowersNormOn s (Icc 1 N)`), the positivity of the normalization
  `one_le_gowersNorm_restrictFinset_one` for nonempty `I`, homogeneity, the triangle inequality,
  and the bridge `gowersNormOn_three_Icc_le` to `Common/GowersLp.lean`
  (`‖g‖_{U³(I)} ≤ 2 ‖g‖_{L²(I)}`).

The formula `gowersNormOn s I g = ‖g 1_I‖_{U^s(ℤ)} / ‖1_I‖_{U^s(ℤ)}` is the paper's quotient, as in
the `gowersNormInterval` (which has `I = [N]`); it has source meaning for `I` nonempty,
where the denominator is `≥ 1` (`one_le_gowersNorm_restrictFinset_one`), and every lemma that
depends on the denominator carries `I.Nonempty`.
-/

@[expose] public noncomputable section

open scoped ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-! ### The conjugation-difference operator (L645-L662) -/

/-- The conjugation-difference operator `Δ_h f(x) := f(x) conj f(x + h)` (Source: main paper
`e:triangle`, L647–L651; [F+], L496–L500): `Common.gowersLpDelta`. -/
abbrev conjDiff (h : ℤ) (f : ℤ → ℂ) : ℤ → ℂ := Common.gowersLpDelta h f

/-- `Δ_h f(x) = f(x) conj f(x + h)`. -/
theorem conjDiff_apply (h : ℤ) (f : ℤ → ℂ) (x : ℤ) : conjDiff h f x = f x * conj (f (x + h)) :=
  rfl

/-- `Δ_0 f(x) = |f(x)|²`. -/
theorem conjDiff_zero (f : ℤ → ℂ) (x : ℤ) : conjDiff 0 f x = ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
  rw [conjDiff_apply, add_zero, Complex.mul_conj']
  push_cast
  ring

/-- The iterated difference starts at the identity: `Δ_∅ f = f`. -/
theorem multDiff_zero (h : Fin 0 → ℤ) (f : ℤ → ℂ) : multDiff 0 h f = f := rfl

/-- The recursion `Δ_{h₁,…,h_{s+1}} f = Δ_{h_{s+1}}(Δ_{h₁,…,h_s} f)` (Source: main paper,
L658–L662; [F+], L507–L511): the `multDiff`. -/
theorem multDiff_succ (s : ℕ) (h : Fin (s + 1) → ℤ) (f : ℤ → ℂ) :
    multDiff (s + 1) h f = conjDiff (h (Fin.last s)) (multDiff s (Fin.init h) f) := rfl

/-- A nonzero iterated difference forces `f` to be nonzero at `x` and at every `x + h_i`. -/
theorem multDiff_ne_zero {s : ℕ} (h : Fin s → ℤ) (f : ℤ → ℂ) (x : ℤ)
    (hne : multDiff s h f x ≠ 0) : f x ≠ 0 ∧ ∀ i : Fin s, f (x + h i) ≠ 0 := by
  induction s generalizing x with
  | zero =>
    exact ⟨hne, fun i => i.elim0⟩
  | succ s ih =>
    rw [multDiff_succ, conjDiff_apply] at hne
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hne
    have h2' : multDiff s (Fin.init h) f (x + h (Fin.last s)) ≠ 0 := by
      intro h0
      exact h2 (by simp [h0])
    obtain ⟨a1, a2⟩ := ih (Fin.init h) x h1
    obtain ⟨b1, _⟩ := ih (Fin.init h) (x + h (Fin.last s)) h2'
    refine ⟨a1, fun i => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact b1
    · exact a2 j

/-! ### `e:double` (L652-L657) -/

/-- **`e:double`, finite box form**: `|∑_{x ∈ I} f(x)|² = ∑_{x ∈ I} ∑_{h ∈ B} Δ_h f(x)` for `f`
supported in the finite set `I` and any finite set `B` containing all differences of `I`. -/
theorem norm_sq_sum_eq_sum_conjDiff (I B : Finset ℤ) (hB : ∀ x ∈ I, ∀ y ∈ I, y - x ∈ B)
    (f : ℤ → ℂ) (hf : ∀ y, y ∉ I → f y = 0) :
    ((‖∑ x ∈ I, f x‖ ^ 2 : ℝ) : ℂ) = ∑ x ∈ I, ∑ h ∈ B, conjDiff h f x := by
  have step : ∀ x ∈ I, ∑ h ∈ B, conjDiff h f x = f x * conj (∑ y ∈ I, f y) := by
    intro x hx
    rw [map_sum, ← Common.gowersLp_sum_shift I B hB (fun y => conj (f y))
      (fun y hy => by simp [hf y hy]) hx, Finset.mul_sum]
    rfl
  rw [Finset.sum_congr rfl step, ← Finset.sum_mul, Complex.mul_conj']
  push_cast
  ring

/-- **`e:double`**: `|∑_x f(x)|² = ∑_{x, h} Δ_h f(x)` for a finitely supported
`f : ℤ → ℂ` (both sides are sums over `ℤ` and `ℤ × ℤ`, with finitely many nonzero terms). -/
theorem norm_sq_tsum_eq_tsum_conjDiff (f : ℤ → ℂ) (hf : (Function.support f).Finite) :
    ((‖∑' x, f x‖ ^ 2 : ℝ) : ℂ) = ∑' p : ℤ × ℤ, conjDiff p.2 f p.1 := by
  classical
  set I : Finset ℤ := hf.toFinset with hI
  have hf0 : ∀ y, y ∉ I → f y = 0 := fun y hy => by
    by_contra hne
    exact hy (hf.mem_toFinset.2 hne)
  set B : Finset ℤ := (I ×ˢ I).image (fun p => p.2 - p.1) with hBdef
  have hB : ∀ x ∈ I, ∀ y ∈ I, y - x ∈ B := fun x hx y hy =>
    Finset.mem_image.2 ⟨(x, y), Finset.mem_product.2 ⟨hx, hy⟩, rfl⟩
  have h1 : ∑' x, f x = ∑ x ∈ I, f x := tsum_eq_sum fun x hx => hf0 x hx
  have h2 : ∑' p : ℤ × ℤ, conjDiff p.2 f p.1 = ∑ p ∈ I ×ˢ B, conjDiff p.2 f p.1 := by
    refine tsum_eq_sum fun p hp => ?_
    rw [conjDiff_apply]
    by_cases hx : p.1 ∈ I
    · have hy : p.1 + p.2 ∉ I := fun hy => hp (Finset.mem_product.2 ⟨hx, by
        simpa using hB _ hx _ hy⟩)
      simp [hf0 _ hy]
    · simp [hf0 _ hx]
  rw [h1, h2, Finset.sum_product]
  exact norm_sq_sum_eq_sum_conjDiff I B hB f hf0

/-! ### The Gowers norm on `ℤ` (L663-L667) -/

/-- **The definition of the Gowers norm** (Source: main paper `e;GowersDef`, L663–L667; [F+]
`e;GowersDef`, L512–L516): the defining identity of the
`gowersNorm`, `‖f‖_{U^s(ℤ)}^{2^s} = ∑_{x, h₁, …, h_s} Δ_{h₁,…,h_s} f(x)`. -/
theorem gowersNorm_pow_eq_tsum (s : ℕ+) (f : ℤ →₀ ℂ) :
    ((gowersNorm s f : ℝ) : ℂ) ^ (2 ^ (s : ℕ)) =
      ∑' p : ℤ × (Fin s → ℤ), multDiff s p.2 f p.1 :=
  (gowersNorm_spec s f).2.2

/-- The Gowers sum has finitely many nonzero terms. -/
theorem gowersSum_support_finite (s : ℕ+) (f : ℤ →₀ ℂ) :
    (Function.support fun p : ℤ × (Fin s → ℤ) => multDiff s p.2 f p.1).Finite :=
  (gowersNorm_spec s f).1

/-- The Gowers norm is nonnegative. -/
theorem gowersNorm_nonneg (s : ℕ+) (f : ℤ →₀ ℂ) : 0 ≤ gowersNorm s f :=
  (gowersNorm_spec s f).2.1

/-- The `2^s`-th power of the Gowers norm is the real part of the Gowers sum. -/
theorem gowersNorm_pow_eq_re_tsum (s : ℕ+) (f : ℤ →₀ ℂ) :
    gowersNorm s f ^ 2 ^ (s : ℕ) = (∑' p : ℤ × (Fin s → ℤ), multDiff s p.2 f p.1).re := by
  rw [← gowersNorm_pow_eq_tsum]
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-- **`e:GowersDef`, finite box form**: for a finite `I ⊇ supp F` and a finite `B` containing all
differences of `I`, `‖F‖_{U^s(ℤ)}^{2^s} = ∑_{x ∈ I} ∑_{h ∈ B^s} Δ_{h₁,…,h_s} F(x)`. -/
theorem gowersNorm_pow_eq_sum_box (s : ℕ+) (F : ℤ →₀ ℂ) (I B : Finset ℤ)
    (hI : ∀ x, F x ≠ 0 → x ∈ I) (hB : ∀ x ∈ I, ∀ y ∈ I, y - x ∈ B) :
    ((gowersNorm s F : ℝ) : ℂ) ^ (2 ^ (s : ℕ)) =
      ∑ x ∈ I, ∑ h ∈ Fintype.piFinset (fun _ : Fin s => B), multDiff s h F x := by
  classical
  rw [gowersNorm_pow_eq_tsum, tsum_eq_sum (s := I ×ˢ Fintype.piFinset fun _ : Fin s => B)]
  · rw [Finset.sum_product]
  · rintro ⟨x, h⟩ hxh
    by_contra hne
    obtain ⟨h0, h1⟩ := multDiff_ne_zero h F x hne
    apply hxh
    simp only [Finset.mem_product, Fintype.mem_piFinset]
    have hx := hI x h0
    refine ⟨hx, fun i => ?_⟩
    have := hI _ (h1 i)
    simpa using hB x hx _ this

/-! ### The normalized norms `U^s(I)` (L702-L707) -/

/-- The extension by zero of `g` restricted to the finite set `I ⊆ ℤ` (`g 1_I`, as a finitely
supported function); the `restrictInterval` is the case `I = [N]`. -/
def restrictFinset (I : Finset ℤ) (g : ℤ → ℂ) : ℤ →₀ ℂ :=
  Finsupp.indicator I fun n _ => g n

/-- `(g 1_I)(n) = g(n)` for `n ∈ I` and `0` otherwise. -/
theorem restrictFinset_apply (I : Finset ℤ) (g : ℤ → ℂ) (n : ℤ) :
    restrictFinset I g n = if n ∈ I then g n else 0 := by
  simp [restrictFinset, Finsupp.indicator_apply]

/-- The normalized Gowers norm `‖g‖_{U^s(I)} := ‖g 1_I‖_{U^s(ℤ)} / ‖1_I‖_{U^s(ℤ)}` on a finite
set `I ⊆ ℤ` (Source: main paper, L702–L707), for `g` extended by zero. The paper
defines it for `I = [N]` and uses it for the intervals `[-N, 2N]`, `[2^k]`, `[-2^k, 2^k]`;
it has source meaning for `I` nonempty. -/
def gowersNormOn (s : ℕ+) (I : Finset ℤ) (g : ℤ → ℂ) : ℝ :=
  gowersNorm s (restrictFinset I g) / gowersNorm s (restrictFinset I 1)

/-- The `gowersNormInterval` is `gowersNormOn` on `[N]`. -/
theorem gowersNormInterval_eq_gowersNormOn (s N : ℕ+) (g : ℤ → ℂ) :
    gowersNormInterval s N g = gowersNormOn s (Finset.Icc (1 : ℤ) N) g := rfl

/-- `‖g‖_{U^s(I)} ≥ 0`. -/
theorem gowersNormOn_nonneg (s : ℕ+) (I : Finset ℤ) (g : ℤ → ℂ) : 0 ≤ gowersNormOn s I g :=
  div_nonneg (gowersNorm_nonneg _ _) (gowersNorm_nonneg _ _)

/-- Each Gowers term of an indicator function is a nonnegative real. -/
theorem multDiff_indicator_nonneg (I : Finset ℤ) :
    ∀ (s : ℕ) (h : Fin s → ℤ) (x : ℤ),
      ∃ r : ℝ, 0 ≤ r ∧ multDiff s h (restrictFinset I 1) x = (r : ℂ) := by
  intro s
  induction s with
  | zero =>
    intro h x
    rw [multDiff_zero, restrictFinset_apply]
    by_cases hx : x ∈ I
    · exact ⟨1, zero_le_one, by simp [hx]⟩
    · exact ⟨0, le_rfl, by simp [hx]⟩
  | succ s ih =>
    intro h x
    obtain ⟨r1, h1, e1⟩ := ih (Fin.init h) x
    obtain ⟨r2, h2, e2⟩ := ih (Fin.init h) (x + h (Fin.last s))
    refine ⟨r1 * r2, mul_nonneg h1 h2, ?_⟩
    rw [multDiff_succ, conjDiff_apply, e1, e2, Complex.conj_ofReal]
    push_cast
    rfl

/-- The Gowers term of an indicator function at `x ∈ I`, `h = 0` is `1`. -/
theorem multDiff_indicator_zero (I : Finset ℤ) :
    ∀ (s : ℕ) (x : ℤ), x ∈ I → multDiff s (0 : Fin s → ℤ) (restrictFinset I 1) x = 1 := by
  intro s
  induction s with
  | zero =>
    intro x hx
    rw [multDiff_zero, restrictFinset_apply]
    simp [hx]
  | succ s ih =>
    intro x hx
    have h0 : Fin.init (0 : Fin (s + 1) → ℤ) = 0 := rfl
    rw [multDiff_succ, conjDiff_apply, h0, ih x hx]
    simp only [Pi.zero_apply, add_zero]
    rw [ih x hx]
    simp

/-- **The normalization is at least one**: `‖1_I‖_{U^s(ℤ)} ≥ 1` for `I` nonempty (the term
`x ∈ I`, `h = 0` of the Gowers sum is `1` and all terms are nonnegative). -/
theorem one_le_gowersNorm_restrictFinset_one (s : ℕ+) {I : Finset ℤ} (hI : I.Nonempty) :
    1 ≤ gowersNorm s (restrictFinset I 1) := by
  classical
  obtain ⟨x0, hx0⟩ := hI
  set F : ℤ →₀ ℂ := restrictFinset I 1 with hF
  set g : ℤ × (Fin s → ℤ) → ℂ := fun p => multDiff s p.2 F p.1 with hg
  have hfin := gowersSum_support_finite s F
  have hre : ∀ p, 0 ≤ (g p).re := fun p => by
    obtain ⟨r, hr, hr'⟩ := multDiff_indicator_nonneg I s p.2 p.1
    simp only [hg, hF, hr', Complex.ofReal_re]
    exact hr
  have hp0 : (g (x0, 0)) = 1 := multDiff_indicator_zero I s x0 hx0
  have hmem : ((x0, (0 : Fin s → ℤ)) : ℤ × (Fin s → ℤ)) ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset, Function.mem_support]
    change g (x0, 0) ≠ 0
    rw [hp0]
    exact one_ne_zero
  have hsum : ∑' p, g p = ∑ p ∈ hfin.toFinset, g p :=
    tsum_eq_sum fun p hp => by simpa using hp
  have hle : 1 ≤ (∑' p, g p).re := by
    rw [hsum, Complex.re_sum]
    calc (1 : ℝ) = (g (x0, 0)).re := by rw [hp0]; simp
      _ ≤ ∑ p ∈ hfin.toFinset, (g p).re :=
        Finset.single_le_sum (f := fun p => (g p).re) (fun p _ => hre p) hmem
  have hpow := gowersNorm_pow_eq_re_tsum s F
  exact (one_le_pow_iff_of_nonneg (gowersNorm_nonneg s F) (by positivity)).1 (hpow ▸ hle)

/-- The normalization `‖1_I‖_{U^s(ℤ)}` is positive for `I` nonempty. -/
theorem gowersNorm_restrictFinset_one_pos (s : ℕ+) {I : Finset ℤ} (hI : I.Nonempty) :
    0 < gowersNorm s (restrictFinset I 1) :=
  zero_lt_one.trans_le (one_le_gowersNorm_restrictFinset_one s hI)

/-- The defining relation `‖g‖_{U^s(I)} ‖1_I‖_{U^s(ℤ)} = ‖g 1_I‖_{U^s(ℤ)}`, for `I` nonempty. -/
theorem gowersNormOn_mul_norm_one (s : ℕ+) {I : Finset ℤ} (hI : I.Nonempty) (g : ℤ → ℂ) :
    gowersNormOn s I g * gowersNorm s (restrictFinset I 1) = gowersNorm s (restrictFinset I g) :=
  div_mul_cancel₀ _ (gowersNorm_restrictFinset_one_pos s hI).ne'

/-- `‖g‖_{U^s(I)}` only depends on the values of `g` on `I`. -/
theorem gowersNormOn_congr (s : ℕ+) (I : Finset ℤ) {g g' : ℤ → ℂ} (h : ∀ n ∈ I, g n = g' n) :
    gowersNormOn s I g = gowersNormOn s I g' := by
  have : restrictFinset I g = restrictFinset I g' := by
    ext n
    rw [restrictFinset_apply, restrictFinset_apply]
    by_cases hn : n ∈ I
    · simp [hn, h n hn]
    · simp [hn]
  rw [gowersNormOn, gowersNormOn, this]

/-- Homogeneity: `‖c g‖_{U^s(I)} = |c| ‖g‖_{U^s(I)}`. -/
theorem gowersNormOn_smul (s : ℕ+) (I : Finset ℤ) (c : ℂ) (g : ℤ → ℂ) :
    gowersNormOn s I (c • g) = ‖c‖ * gowersNormOn s I g := by
  have : restrictFinset I (c • g) = c • restrictFinset I g := by
    ext n
    simp only [restrictFinset_apply, Pi.smul_apply, Finsupp.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [gowersNormOn, gowersNormOn, this, Common.gowersNorm_smul, mul_div_assoc]

/-- The triangle inequality: `‖f + g‖_{U^s(I)} ≤ ‖f‖_{U^s(I)} + ‖g‖_{U^s(I)}`. -/
theorem gowersNormOn_add_le (s : ℕ+) (I : Finset ℤ) (f g : ℤ → ℂ) :
    gowersNormOn s I (f + g) ≤ gowersNormOn s I f + gowersNormOn s I g := by
  have : restrictFinset I (f + g) = restrictFinset I f + restrictFinset I g := by
    ext n
    simp only [restrictFinset_apply, Pi.add_apply, Finsupp.add_apply]
    split_ifs <;> simp
  rw [gowersNormOn, gowersNormOn, gowersNormOn, this, ← add_div]
  exact div_le_div_of_nonneg_right (Common.gowersNorm_add_le s _ _) (gowersNorm_nonneg _ _)

/-- The bridge to `Common/GowersLp.lean` (`l:ET` for `s = 3`): for every integer interval
`I = [a, b]`, `‖g‖_{U³(I)} ≤ 2 ‖g‖_{L²(I)}`, with the normalized `L²` norm `lpNormOn`. -/
theorem gowersNormOn_three_Icc_le {a b : ℤ} (hab : a ≤ b) (g : ℤ → ℂ) :
    gowersNormOn 3 (Finset.Icc a b) g ≤ 2 * lpNormOn 2 (Finset.Icc a b) g := by
  have hI : (Finset.Icc a b).Nonempty := ⟨a, Finset.mem_Icc.2 ⟨le_rfl, hab⟩⟩
  have hpos := gowersNorm_restrictFinset_one_pos 3 hI
  have h := Common.gowersNorm_three_Icc_le a b g
  rw [lpNormOn_two, gowersNormOn, div_le_iff₀ hpos]
  exact h

end PrimeCarleson.Proof.Paper
