module

public import PrimeCarleson.Proof.Paper.P2.U2Fourier
public import PrimeCarleson.Proof.Paper.P2.Normalization
public import PrimeCarleson.Proof.Paper.Defs.Norms
public import PrimeCarleson.Proof.Common.HausdorffYoung

/-!
# The Eisner–Tao bound `‖f‖_{U^s([N])} ≲_s ‖f‖_{L^{p_s}([N])}` for `s ∈ {1, 2, 3}`

Lemma `l:ET` of `sources/Variational_Carleson.tex` (Source: main paper `l:ET`, L710–L715, quoted
from Eisner–Tao; the normalized norms are those of L702–L707 and L685–L695): for
`p_s = 2^s / (s + 1)`,
`‖g‖_{U^s(I)} ≤ C_s ‖g‖_{L^{p_s}(I)}`, `‖g‖_{L^p(I)} = (|I|⁻¹ ∑_{n ∈ I} |g(n)|^p)^{1/p}`.

**What is proved.** The cases `s = 1` (`p₁ = 1`, constant `1`), `s = 2` (`p₂ = 4/3`, a constant
from the Hausdorff–Young inequality `ℓ^{4/3} → L⁴(𝕋)`) and `s = 3` (`p₃ = 2`, constant `2`,
`Common/GowersLp.lean`), for every interval `I = [a, b]` of integers (this contains `[N]`, the
`gowersNormInterval`, and the intervals `[-N, 2N]`, `[2^k]`, `[-2^k, 2^k]`). The paper uses
only `s = 3` (`e:U3maxmod`, L724–L726; `[F+]` and the `U²` convolution step
L836–L837 use no instance of `l:ET`). **Not proved: `s ≥ 4`** (the general Eisner–Tao induction).

* `gowersNorm_one_eq_norm_tsum`: `‖F‖_{U¹(ℤ)} = |∑ F|` (the case `s = 1` of `e:double`);
* `gowersNorm_two_le_sum_rpow`: `‖F‖_{U²(ℤ)} ≤ C (∑_{n ∈ S} |F n|^{4/3})^{3/4}` for `S ⊇ supp F`
  (`e:U2-ell4`, `U2Fourier.lean`, and the Hausdorff–Young inequality of
  `Common/HausdorffYoung.lean`);
* `gowersNormOn_one_le_lpNormOn`, `gowersNormOn_two_le_lpNormOn`, `gowersNormOn_three_le_lpNormOn`
  (`s = 1, 2, 3`) for `I = [a, b]`, the normalizations being `‖1_I‖_{U^s(ℤ)} ≥ c_s |I|^{(s+1)/2^s}`
  (`gowersNorm_Icc_indicator_approx`);
* `eisnerTao_Icc` (all of `s ∈ {1, 2, 3}` together) and `eisnerTao_interval` (the
  `gowersNormInterval s N` against the `L^{p_s}([N])` norm `lpNormOn p_s (bracket N)`).
-/

@[expose] public noncomputable section

open scoped ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-! ### `s = 1` -/

/-- The sum of the extension by zero of `g` to `I`, as a finite sum. -/
theorem tsum_restrictFinset (I : Finset ℤ) (g : ℤ → ℂ) :
    ∑' x, restrictFinset I g x = ∑ n ∈ I, g n := by
  rw [tsum_eq_sum (s := I)]
  · exact Finset.sum_congr rfl fun n hn => by simp [restrictFinset_apply, hn]
  · intro x hx
    simp [restrictFinset_apply, hx]

/-- **`‖F‖_{U¹(ℤ)} = |∑ F|`** (the case `s = 1` of the Gowers sum; `e:double`, L652-L657). -/
theorem gowersNorm_one_eq_norm_tsum (F : ℤ →₀ ℂ) : gowersNorm 1 F = ‖∑' x, F x‖ := by
  have h1 : ((gowersNorm 1 F : ℝ) : ℂ) ^ 2 = ∑' p : ℤ × (Fin 1 → ℤ), multDiff 1 p.2 F p.1 :=
    gowersNorm_pow_eq_tsum 1 F
  have h2 : ∑' p : ℤ × (Fin 1 → ℤ), multDiff 1 p.2 F p.1 =
      ∑' q : ℤ × ℤ, conjDiff q.2 F q.1 := by
    rw [← (Equiv.prodCongr (Equiv.refl ℤ) (Equiv.funUnique (Fin 1) ℤ)).tsum_eq
      (fun q : ℤ × ℤ => conjDiff q.2 F q.1)]
    rfl
  have h3 := norm_sq_tsum_eq_tsum_conjDiff (⇑F) (Common.GowersCS.finsupp_support_finite F)
  have h4 : ((gowersNorm 1 F ^ 2 : ℝ) : ℂ) = ((‖∑' x, F x‖ ^ 2 : ℝ) : ℂ) := by
    rw [h3, ← h2, ← h1]
    push_cast
    rfl
  have h5 : gowersNorm 1 F ^ 2 = ‖∑' x, F x‖ ^ 2 := by exact_mod_cast h4
  exact (sq_eq_sq₀ (gowersNorm_nonneg 1 F) (norm_nonneg _)).1 h5

/-- **`l:ET` for `s = 1`** (`p₁ = 1`): `‖g‖_{U¹(I)} ≤ ‖g‖_{L¹(I)}` on every interval `I = [a, b]`,
that is `|E_{n ∈ I} g(n)| ≤ E_{n ∈ I} |g(n)|`. -/
theorem gowersNormOn_one_le_lpNormOn {a b : ℤ} (hab : a ≤ b) (g : ℤ → ℂ) :
    gowersNormOn 1 (Finset.Icc a b) g ≤ lpNormOn 1 (Finset.Icc a b) g := by
  set I : Finset ℤ := Finset.Icc a b with hI
  have hne : I.Nonempty := ⟨a, Finset.mem_Icc.2 ⟨le_rfl, hab⟩⟩
  have hcard : (0 : ℝ) < I.card := by exact_mod_cast hne.card_pos
  have h1 : gowersNorm 1 (restrictFinset I 1) = I.card := by
    rw [gowersNorm_one_eq_norm_tsum, tsum_restrictFinset]
    simp
  have h2 : gowersNorm 1 (restrictFinset I g) = ‖∑ n ∈ I, g n‖ := by
    rw [gowersNorm_one_eq_norm_tsum, tsum_restrictFinset]
  rw [gowersNormOn, h1, h2, div_eq_inv_mul]
  simp only [lpNormOn, Real.rpow_one, div_one]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.2 hcard.le)

/-! ### `s = 2` -/

/-- The Hölder pair `(4, 4/3)`. -/
private theorem holderConjugate_four : (4 : ℝ).HolderConjugate (4 / 3) := by
  rw [Real.holderConjugate_iff]
  constructor <;> norm_num

/-- **`‖F‖_{U²(ℤ)} ≲ ‖F‖_{ℓ^{4/3}}`**: there is an absolute `C ≥ 0` with
`‖F‖_{U²(ℤ)} ≤ C (∑_{n ∈ S} |F(n)|^{4/3})^{3/4}` for every finitely supported `F` and every
finite `S ⊇ supp F`. By `e:U2-ell4` the left side is `‖F̂‖_{L⁴(𝕋)}`, and Hausdorff–Young
gives `‖F̂‖_{L⁴(𝕋)} ≤ C ‖F‖_{ℓ^{4/3}}`. -/
theorem gowersNorm_two_le_sum_rpow :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : ℤ →₀ ℂ) (S : Finset ℤ), F.support ⊆ S →
      gowersNorm 2 F ≤ C * (∑ n ∈ S, ‖F n‖ ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) := by
  classical
  obtain ⟨C, hC0, hC⟩ := Common.hausdorffYoung_T (r := 4) (r' := 4 / 3) (by norm_num)
    holderConjugate_four
  refine ⟨C, hC0, fun F S hS => ?_⟩
  set S' : Finset ℤ := S.image Neg.neg with hS'
  have hinj : Set.InjOn (Neg.neg : ℤ → ℤ) ↑S := fun x _ y _ h => neg_injective h
  have hfour : ∀ ξ : ℝ, Common.fourierZ F ξ = ∑ m ∈ S', F (-m) * e ((m : ℝ) * ξ) := by
    intro ξ
    rw [Common.fourierZ_eq_sum_of_support_subset F hS, hS', Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp [neg_mul]
  have hsum : ∑ m ∈ S', ‖F (-m)‖ ^ (4 / 3 : ℝ) = ∑ n ∈ S, ‖F n‖ ^ (4 / 3 : ℝ) := by
    rw [hS', Finset.sum_image hinj]
    simp
  have h4 := gowersNorm_two_pow_four_eq_integral F
  have hint : ∫ ξ in (0 : ℝ)..1, ‖Common.fourierZ F ξ‖ ^ 4 =
      ∫ ξ in (0 : ℝ)..1, ‖∑ m ∈ S', F (-m) * e ((m : ℝ) * ξ)‖ ^ (4 : ℝ) := by
    refine intervalIntegral.integral_congr fun ξ _ => ?_
    simp only [hfour ξ]
    exact (Real.rpow_natCast _ 4).symm
  rw [hint] at h4
  have hHY := hC S' (fun m => F (-m))
  beta_reduce at hHY
  rw [hsum, show (1 : ℝ) / (4 / 3) = 3 / 4 by norm_num] at hHY
  have hg : gowersNorm 2 F = (∫ ξ in (0 : ℝ)..1,
      ‖∑ m ∈ S', F (-m) * e ((m : ℝ) * ξ)‖ ^ (4 : ℝ)) ^ (1 / 4 : ℝ) := by
    rw [← h4, ← Real.rpow_natCast, ← Real.rpow_mul (gowersNorm_nonneg 2 F)]
    norm_num
  rw [hg]
  exact hHY

/-- The normalization of the sizes of `[a, b]`: for `a ≤ b` there is `L ≥ 1` with
`[a, b] = {a, …, a + L - 1}` and `|[a, b]| = L`. -/
private theorem exists_length {a b : ℤ} (hab : a ≤ b) :
    ∃ L : ℕ, 1 ≤ L ∧ Finset.Icc a b = Finset.Icc a (a + L - 1) ∧
      ((Finset.Icc a b).card : ℝ) = L := by
  obtain ⟨L, hL⟩ : ∃ L : ℕ, (L : ℤ) = b + 1 - a := ⟨(b + 1 - a).toNat, by omega⟩
  refine ⟨L, by omega, ?_, ?_⟩
  · ext x
    simp only [Finset.mem_Icc]
    omega
  · simp only [Int.card_Icc]
    have : (b + 1 - a).toNat = L := by omega
    rw [this]

/-- **`l:ET` for `s = 2`** (`p₂ = 4/3`): there is an absolute `C > 0` with
`‖g‖_{U²(I)} ≤ C ‖g‖_{L^{4/3}(I)}` for every interval `I = [a, b]` of integers and every
`g : ℤ → ℂ`. -/
theorem gowersNormOn_two_le_lpNormOn :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℤ, a ≤ b → ∀ g : ℤ → ℂ,
      gowersNormOn 2 (Finset.Icc a b) g ≤ C * lpNormOn (4 / 3) (Finset.Icc a b) g := by
  obtain ⟨C₁, hC₁, hHY⟩ := gowersNorm_two_le_sum_rpow
  obtain ⟨c, C₂, hc, -, happ⟩ := gowersNorm_Icc_indicator_approx 2
  refine ⟨(C₁ + 1) / c, by positivity, fun a b hab g => ?_⟩
  obtain ⟨L, hL1, hIeq, hcard⟩ := exists_length hab
  set I : Finset ℤ := Finset.Icc a b with hI
  have hne : I.Nonempty := ⟨a, Finset.mem_Icc.2 ⟨le_rfl, hab⟩⟩
  have hpos := gowersNorm_restrictFinset_one_pos 2 hne
  have hlow := (happ a L).1
  rw [← hIeq] at hlow
  have hexp : (((2 : ℕ+) : ℝ) + 1) / 2 ^ ((2 : ℕ+) : ℕ) = 3 / 4 := by norm_num
  rw [hexp] at hlow
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
  set P : ℝ := lpNormOn (4 / 3) I g with hP
  have hP0 : 0 ≤ P := lpNormOn_nonneg _ _ _
  have hsum : ∑ n ∈ I, ‖g n‖ ^ (4 / 3 : ℝ) = L * P ^ (4 / 3 : ℝ) := by
    have := lpNormOn_rpow (p := 4 / 3) (by norm_num) I g
    rw [← hP, hcard] at this
    rw [this, ← mul_assoc, mul_inv_cancel₀ hLpos.ne', one_mul]
  have hF : ∀ n ∉ I, restrictFinset I g n = 0 := fun n hn => by
    simp [restrictFinset_apply, hn]
  have hsupp : (restrictFinset I g).support ⊆ I := fun n hn => by
    by_contra h
    exact (Finsupp.mem_support_iff.1 hn) (hF n h)
  have hup := hHY (restrictFinset I g) I hsupp
  have hsum' : ∑ n ∈ I, ‖restrictFinset I g n‖ ^ (4 / 3 : ℝ) = ∑ n ∈ I, ‖g n‖ ^ (4 / 3 : ℝ) :=
    Finset.sum_congr rfl fun n hn => by simp [restrictFinset_apply, hn]
  rw [hsum', hsum, Real.mul_rpow hLpos.le (Real.rpow_nonneg hP0 _), ← Real.rpow_mul hP0,
    show (4 / 3 : ℝ) * (3 / 4) = 1 by norm_num, Real.rpow_one] at hup
  rw [gowersNormOn, div_le_iff₀ hpos]
  have hLp : 0 ≤ (L : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_nonneg hLpos.le _
  calc gowersNorm 2 (restrictFinset I g) ≤ C₁ * ((L : ℝ) ^ (3 / 4 : ℝ) * P) := hup
    _ ≤ (C₁ + 1) / c * P * (c * (L : ℝ) ^ (3 / 4 : ℝ)) := by
        have h : (C₁ + 1) / c * P * (c * (L : ℝ) ^ (3 / 4 : ℝ)) =
            (C₁ + 1) * ((L : ℝ) ^ (3 / 4 : ℝ) * P) := by
          field_simp
        rw [h]
        nlinarith [mul_nonneg hLp hP0]
    _ ≤ (C₁ + 1) / c * P * gowersNorm 2 (restrictFinset I 1) :=
        mul_le_mul_of_nonneg_left hlow (by positivity)

/-! ### `s = 3` -/

/-- **`l:ET` for `s = 3`** (`p₃ = 2`; the case used by the paper, `e:U3maxmod`, L724–L726):
`‖g‖_{U³(I)} ≤ C ‖g‖_{L²(I)}` with `C = 2` on every interval `I = [a, b]`
(`Common/GowersLp.lean`). -/
theorem gowersNormOn_three_le_lpNormOn :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℤ, a ≤ b → ∀ g : ℤ → ℂ,
      gowersNormOn 3 (Finset.Icc a b) g ≤ C * lpNormOn 2 (Finset.Icc a b) g :=
  ⟨2, two_pos, fun _ _ hab g => gowersNormOn_three_Icc_le hab g⟩

/-! ### `l:ET` -/

/-- **`l:ET`** (Source: main paper `l:ET`, L710–L715) for `s ∈ {1, 2, 3}`: with
`p_s = 2^s/(s+1)` there is
`C_s > 0` such that for every interval `I = [a, b]` of integers and every `g : ℤ → ℂ`,
`‖g‖_{U^s(I)} ≤ C_s ‖g‖_{L^{p_s}(I)}`, the normalized norms of L702–L707 and
L685–L695. (Not proved for `s ≥ 4`.) -/
theorem eisnerTao_Icc (s : ℕ+) (hs : s ≤ 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℤ, a ≤ b → ∀ g : ℤ → ℂ,
      gowersNormOn s (Finset.Icc a b) g ≤
        C * lpNormOn ((2 : ℝ) ^ (s : ℕ) / ((s : ℝ) + 1)) (Finset.Icc a b) g := by
  have hs' : (s : ℕ) = 1 ∨ (s : ℕ) = 2 ∨ (s : ℕ) = 3 := by
    have h1 := s.pos
    have h2 : (s : ℕ) ≤ 3 := by exact_mod_cast hs
    omega
  rcases hs' with h | h | h
  · obtain rfl : s = 1 := PNat.eq (by simpa using h)
    refine ⟨1, one_pos, fun a b hab g => ?_⟩
    have e1 : ((2 : ℝ) ^ ((1 : ℕ+) : ℕ) / (((1 : ℕ+) : ℝ) + 1)) = 1 := by norm_num
    rw [e1, one_mul]
    exact gowersNormOn_one_le_lpNormOn hab g
  · obtain rfl : s = 2 := PNat.eq (by simpa using h)
    obtain ⟨C, hC, hb⟩ := gowersNormOn_two_le_lpNormOn
    refine ⟨C, hC, fun a b hab g => ?_⟩
    have e2 : ((2 : ℝ) ^ ((2 : ℕ+) : ℕ) / (((2 : ℕ+) : ℝ) + 1)) = 4 / 3 := by norm_num
    rw [e2]
    exact hb a b hab g
  · obtain rfl : s = 3 := PNat.eq (by simpa using h)
    obtain ⟨C, hC, hb⟩ := gowersNormOn_three_le_lpNormOn
    refine ⟨C, hC, fun a b hab g => ?_⟩
    have e3 : ((2 : ℝ) ^ ((3 : ℕ+) : ℕ) / (((3 : ℕ+) : ℝ) + 1)) = 2 := by norm_num
    rw [e3]
    exact hb a b hab g

/-- **`l:ET` for `[N]`** (Source: main paper `l:ET`, L710–L715) for `s ∈ {1, 2, 3}`: with
the
normalized norm `gowersNormInterval s N` (`‖g‖_{U^s([N])}`) and `p_s = 2^s/(s+1)`,
`‖g‖_{U^s([N])} ≤ C_s ‖g‖_{L^{p_s}([N])}` for all `N ≥ 1` and every `g : ℤ → ℂ`. -/
theorem eisnerTao_interval (s : ℕ+) (hs : s ≤ 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (g : ℤ → ℂ), gowersNormInterval s N g ≤
      C * lpNormOn ((2 : ℝ) ^ (s : ℕ) / ((s : ℝ) + 1)) (bracket N) g := by
  obtain ⟨C, hC, h⟩ := eisnerTao_Icc s hs
  refine ⟨C, hC, fun N g => ?_⟩
  rw [gowersNormInterval_eq_gowersNormOn]
  exact h 1 N (by exact_mod_cast N.pos) g

end PrimeCarleson.Proof.Paper
