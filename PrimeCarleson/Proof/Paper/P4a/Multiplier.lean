module

public import PrimeCarleson.Proof.Common.FourierZ
public import PrimeCarleson.Proof.Paper.Defs.Modulated
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Algebra.Order.Chebyshev

/-!
# The multiplier of the modulated average `A_λ` and its dyadic increments

Source: main paper `e:multsf`, L963–L1021 (proof of `l:crudeV2lambda`, L944–L1022): the multiplier
computation L963–L986, the two cases L987–L997 and L998–L1008, and the conclusion L1010–L1021.

With `m(ξ) = N⁻¹ ∑_{n=1}^N w(n) e(-ξ n)` (`modMultiplier`, L963) and the Fourier series
`f̂(ξ) = ∑ f(n) e(-nξ)` (`Common.fourierZ`):

* `modAverage_eq_convZ`, `fourierZ_modAverage`: `A_λ f = f ⋆ k_λ` with the averaging kernel
  `k_λ(n) = N⁻¹ w(n) e(λ n) 1_{[N]}(n)` (`avgKernel`), so `A_λ` has Fourier multiplier `m(ξ - λ)`;
* `multiplierIncrement_eq`: the multiplier of `D_{K,α,s} = A_{α+(s+1)/K} - A_{α+s/K}` is
  `m(ξ-α-(s+1)/K) - m(ξ-α-s/K) = N⁻¹ ∑_n w(n) e((α-ξ)n) e(sn/K) (e(n/K) - 1)`;
* `sum_norm_sq_multiplierIncrement` (the orthogonality step, L963–L986): orthogonality
  modulo `K` (cyclic Plancherel, `Common.sum_norm_sq_cyclic`),
  `∑_{s<K} |m(ξ-α-(s+1)/K) - m(ξ-α-s/K)|² = K ∑_{l ∈ ℤ/K} |N⁻¹ ∑_{n ≡ l (K)} w(n) e((α-ξ)n)
  (e(n/K) - 1)|²`;
* `multiplierIncrement_sq_le_of_le` (the case `K ≤ N`, L987–L997), constant `8`, and
  `multiplierIncrement_sq_le_of_gt` (the case `K > N`, L998–L1008), constant `4π²`;
* `multiplierIncrement_le` (**`e:multsf`**): `(∑_{s<K} |…|²)^{1/2} ≤ 2π min{1, (N/K)^{1/2}}
  ‖w‖_{L²([N])}`, uniformly in `ξ`, `α` and `K ≥ 1`.

The paper's "absolute implicit constants" are `8`, `4π²` (squared) and `2π`. The functions `w` and
`f` are `ℤ → ℂ`; only the values of `w` on `[N]` matter.
-/

@[expose] public noncomputable section

open scoped ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

/-! ### `|e(t) - 1| ≤ 2π |t|` -/

/-- `|e(t) - 1| ≤ 2π |t|`. -/
theorem norm_e_sub_one_le (t : ℝ) : ‖e t - 1‖ ≤ 2 * Real.pi * |t| := by
  have h : e t = Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)) := by
    unfold e
    push_cast
    ring_nf
  rw [h]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_two, abs_of_pos Real.pi_pos]

/-- `|e(t) - 1| ≤ 2`. -/
theorem norm_e_sub_one_le_two (t : ℝ) : ‖e t - 1‖ ≤ 2 := by
  calc ‖e t - 1‖ ≤ ‖e t‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_e, norm_one]; norm_num

/-! ### The multiplier and the averaging kernel -/

/-- The multiplier `m(ξ) := N⁻¹ ∑_{n=1}^N w(n) e(-ξ n)` of the modulated average
(L963-L964). -/
def modMultiplier (N : ℕ+) (w : ℤ → ℂ) (ξ : ℝ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ bracket N, w n * e (-((n : ℝ) * ξ))

/-- The averaging kernel `k_λ(n) = N⁻¹ w(n) e(λ n) 1_{[N]}(n)` as a finitely supported sequence:
`A_λ f = f ⋆ k_λ` (`modAverage_eq_convZ`). -/
def avgKernel (N : ℕ+) (w : ℤ → ℂ) (lam : ℝ) : ℤ →₀ ℂ :=
  Finsupp.onFinset (bracket N)
    (fun n => if n ∈ bracket N then (N : ℂ)⁻¹ * (w n * e (lam * n)) else 0)
    (fun n hn => by
      by_contra h
      exact hn (by simp [h]))

/-- The values of the averaging kernel. -/
theorem avgKernel_apply (N : ℕ+) (w : ℤ → ℂ) (lam : ℝ) (n : ℤ) :
    avgKernel N w lam n = if n ∈ bracket N then (N : ℂ)⁻¹ * (w n * e (lam * n)) else 0 :=
  rfl

/-- The averaging kernel is carried by `[N]`. -/
theorem avgKernel_support_subset (N : ℕ+) (w : ℤ → ℂ) (lam : ℝ) :
    (avgKernel N w lam).support ⊆ bracket N :=
  Finsupp.support_onFinset_subset

/-- The Fourier series of the averaging kernel is `m(ξ - λ)`. -/
theorem fourierZ_avgKernel (N : ℕ+) (w : ℤ → ℂ) (lam ξ : ℝ) :
    fourierZ (avgKernel N w lam) ξ = modMultiplier N w (ξ - lam) := by
  rw [fourierZ_eq_sum_of_support_subset _ (avgKernel_support_subset N w lam), modMultiplier,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  simp only [avgKernel_apply, hn, ↓reduceIte]
  have h : e (lam * n) * e (-((n : ℝ) * ξ)) = e (-((n : ℝ) * (ξ - lam))) := by
    rw [← e_add]
    congr 1
    ring
  calc (N : ℂ)⁻¹ * (w n * e (lam * n)) * e (-((n : ℝ) * ξ))
      = (N : ℂ)⁻¹ * (w n * (e (lam * n) * e (-((n : ℝ) * ξ)))) := by ring
    _ = (N : ℂ)⁻¹ * (w n * e (-((n : ℝ) * (ξ - lam)))) := by rw [h]

/-- `A_λ F = F ⋆ k_λ` for a finitely supported `F`. -/
theorem modAverage_eq_convZ (N : ℕ+) (w : ℤ → ℂ) (F : ℤ →₀ ℂ) (lam : ℝ) (x : ℤ) :
    modAverage N w (⇑F) lam x = convZ F (avgKernel N w lam) x := by
  rw [convZ_apply, Finsupp.sum, modAverage_eq]
  have h1 : ∑ k ∈ F.support, F k * avgKernel N w lam (x - k) =
      ∑' k : ℤ, F k * avgKernel N w lam (x - k) :=
    (tsum_eq_sum (fun k hk => by simp [Finsupp.notMem_support_iff.1 hk])).symm
  rw [h1, ← (Equiv.subLeft x).tsum_eq]
  simp only [Equiv.subLeft_apply, sub_sub_cancel]
  rw [tsum_eq_sum (s := bracket N) (fun n hn => by simp [avgKernel_apply, hn])]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  simp only [avgKernel_apply, hn, ↓reduceIte]
  ring

/-- **`A_λ` has Fourier multiplier `m(ξ - λ)`** (first claim of the orthogonality step of
`e:multsf`, L963–L966): `\widehat{A_λ F}(ξ) = m(ξ - λ) F̂(ξ)`. -/
theorem fourierZ_modAverage (N : ℕ+) (w : ℤ → ℂ) (F : ℤ →₀ ℂ) (lam ξ : ℝ) :
    fourierZ (convZ F (avgKernel N w lam)) ξ = modMultiplier N w (ξ - lam) * fourierZ F ξ := by
  rw [fourierZ_convZ, fourierZ_avgKernel, mul_comm]

/-! ### The multiplier of the dyadic increments -/

/-- The multiplier of `D_{K,α,s} = A_{α+(s+1)/K} - A_{α+s/K}` (L967-L971):
`m(ξ - α - (s+1)/K) - m(ξ - α - s/K)`. -/
def multiplierIncrement (N : ℕ+) (w : ℤ → ℂ) (K : ℕ) (α : ℝ) (s : ℕ) (ξ : ℝ) : ℂ :=
  modMultiplier N w (ξ - α - ((s : ℝ) + 1) / K) - modMultiplier N w (ξ - α - (s : ℝ) / K)

/-- The multiplier of `D_{K,α,s}` is `N⁻¹ ∑_{n ∈ [N]} w(n) e((α-ξ)n) e(sn/K) (e(n/K) - 1)` (second
claim of the orthogonality step of `e:multsf`, L967–L973). -/
theorem multiplierIncrement_eq (N : ℕ+) (w : ℤ → ℂ) (K : ℕ) (α : ℝ) (s : ℕ) (ξ : ℝ) :
    multiplierIncrement N w K α s ξ = (N : ℂ)⁻¹ * ∑ n ∈ bracket N,
      w n * e ((α - ξ) * n) * e ((s : ℝ) * n / K) * (e ((n : ℝ) / K) - 1) := by
  unfold multiplierIncrement modMultiplier
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  have h1 : e (-((n : ℝ) * (ξ - α - ((s : ℝ) + 1) / K))) =
      e ((α - ξ) * n) * e ((s : ℝ) * n / K) * e ((n : ℝ) / K) := by
    rw [← e_add, ← e_add]
    congr 1
    ring
  have h2 : e (-((n : ℝ) * (ξ - α - (s : ℝ) / K))) =
      e ((α - ξ) * n) * e ((s : ℝ) * n / K) := by
    rw [← e_add]
    congr 1
    ring
  rw [h1, h2]
  ring

/-- Grouping by residue classes modulo `K`, the multiplier of `D_{K,α,s}` is the cyclic Fourier sum
`∑_{l<K} B_l e(sl/K)` of the residue sums `B_l = ∑_{n ≡ l (K)} c_n`, `c_n = N⁻¹ w(n) e((α-ξ)n)
(e(n/K) - 1)`. -/
theorem multiplierIncrement_eq_cyclic (N : ℕ+) (w : ℤ → ℂ) {K : ℕ} (hK : 0 < K) (α : ℝ) (s : ℕ)
    (ξ : ℝ) :
    multiplierIncrement N w K α s ξ = ∑ l ∈ Finset.range K,
      (∑ n ∈ (bracket N).filter (fun n : ℤ => n % (K : ℤ) = (l : ℤ)),
        (N : ℂ)⁻¹ * (w n * e ((α - ξ) * n) * (e ((n : ℝ) / K) - 1))) *
        e ((s : ℝ) * l / K) := by
  classical
  rw [multiplierIncrement_eq, Finset.mul_sum]
  have hmaps : ∀ n ∈ bracket N, (n % (K : ℤ)).toNat ∈ Finset.range K := by
    intro n _
    have h0 : 0 ≤ n % (K : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hK.ne')
    have h1 : n % (K : ℤ) < K := Int.emod_lt_of_pos _ (by exact_mod_cast hK)
    rw [Finset.mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Finset.sum_mul]
  have hfilt : (bracket N).filter (fun n : ℤ => (n % (K : ℤ)).toNat = l) =
      (bracket N).filter (fun n : ℤ => n % (K : ℤ) = (l : ℤ)) := by
    refine Finset.filter_congr fun n _ => ?_
    have h0 : 0 ≤ n % (K : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hK.ne')
    omega
  rw [hfilt]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' : n % (K : ℤ) = (l : ℤ) := (Finset.mem_filter.1 hn).2
  have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have he : e ((s : ℝ) * n / K) = e ((s : ℝ) * l / K) := by
    have hn2 : (n : ℝ) = (l : ℝ) + (K : ℝ) * ((n / (K : ℤ) : ℤ) : ℝ) := by
      have := Int.mul_ediv_add_emod n (K : ℤ)
      rw [hn'] at this
      have h3 : ((n : ℤ) : ℝ) = (((K : ℤ) * (n / (K : ℤ)) + (l : ℤ) : ℤ) : ℝ) := by rw [this]
      push_cast at h3
      linarith
    have : (s : ℝ) * n / K = (s : ℝ) * l / K + (((s : ℤ) * (n / (K : ℤ)) : ℤ) : ℝ) := by
      rw [hn2]
      push_cast
      field_simp
    rw [this, e_add_intCast]
  rw [he]
  ring

/-- **The orthogonality step of `e:multsf`** (L963–L986): for `K ≥ 1`, `α, ξ ∈ ℝ`,
`∑_{s<K} |m(ξ-α-(s+1)/K) - m(ξ-α-s/K)|² =
K ∑_{l ∈ ℤ/K} |N⁻¹ ∑_{1≤n≤N, n ≡ l (mod K)} w(n) e((α-ξ)n) (e(n/K) - 1)|²`
(cyclic Plancherel `Common.sum_norm_sq_cyclic`). The identification of the multiplier of `A_λ`
and of `D_{K,α,s}` is `fourierZ_modAverage` and `multiplierIncrement_eq`. Source: main paper
`e:multsf`, L963–L986. -/
theorem sum_norm_sq_multiplierIncrement (N : ℕ+) (w : ℤ → ℂ) {K : ℕ} (hK : 0 < K) (α ξ : ℝ) :
    ∑ s ∈ Finset.range K, ‖multiplierIncrement N w K α s ξ‖ ^ 2 =
      K * ∑ l ∈ Finset.range K, ‖(N : ℂ)⁻¹ *
        ∑ n ∈ (bracket N).filter (fun n : ℤ => n % (K : ℤ) = (l : ℤ)),
          w n * e ((α - ξ) * n) * (e ((n : ℝ) / K) - 1)‖ ^ 2 := by
  simp_rw [multiplierIncrement_eq_cyclic N w hK α _ ξ]
  rw [sum_norm_sq_cyclic hK (fun l => ∑ n ∈ (bracket N).filter
    (fun n : ℤ => n % (K : ℤ) = (l : ℤ)),
      (N : ℂ)⁻¹ * (w n * e ((α - ξ) * n) * (e ((n : ℝ) / K) - 1)))]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum]


/-! ### The two cases `K ≤ N` and `K > N` -/

/-- Summing over the residue classes modulo `K` recovers the sum over the whole set. -/
theorem sum_range_filter_emod {M : Type*} [AddCommMonoid M] {K : ℕ} (hK : 0 < K) (S : Finset ℤ)
    (F : ℤ → M) :
    ∑ l ∈ Finset.range K, ∑ n ∈ S.filter (fun n : ℤ => n % (K : ℤ) = (l : ℤ)), F n =
      ∑ n ∈ S, F n := by
  classical
  have hmaps : ∀ n ∈ S, (n % (K : ℤ)).toNat ∈ Finset.range K := by
    intro n _
    have h0 : 0 ≤ n % (K : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hK.ne')
    have h1 : n % (K : ℤ) < K := Int.emod_lt_of_pos _ (by exact_mod_cast hK)
    rw [Finset.mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun l _ => ?_
  refine Finset.sum_congr ?_ fun _ _ => rfl
  refine Finset.filter_congr fun n _ => ?_
  have h0 : 0 ≤ n % (K : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hK.ne')
  omega

/-- A residue class modulo `K` contains at most `N / K + 1` integers of `[N]`. -/
theorem card_filter_bracket_le (N : ℕ+) {K : ℕ} (hK : 0 < K) (l : ℤ) :
    ((bracket N).filter (fun n : ℤ => n % (K : ℤ) = l)).card ≤ (N : ℕ) / K + 1 := by
  classical
  have hK' : (0 : ℤ) < K := by exact_mod_cast hK
  have hmaps : ∀ n ∈ (bracket N).filter (fun n : ℤ => n % (K : ℤ) = l),
      n / (K : ℤ) ∈ Finset.Icc (0 : ℤ) (((N : ℕ) / K : ℕ) : ℤ) := by
    intro n hn
    obtain ⟨hn1, _⟩ := Finset.mem_filter.1 hn
    have hb := mem_bracket.1 hn1
    rw [Finset.mem_Icc]
    refine ⟨Int.ediv_nonneg (by omega) hK'.le, ?_⟩
    have := Int.ediv_le_ediv hK' hb.2
    simpa [Int.natCast_div] using this
  have hinj : Set.InjOn (fun n : ℤ => n / (K : ℤ))
      ↑((bracket N).filter (fun n : ℤ => n % (K : ℤ) = l)) := by
    intro n₁ h₁ n₂ h₂ h
    have e1 := Int.mul_ediv_add_emod n₁ (K : ℤ)
    have e2 := Int.mul_ediv_add_emod n₂ (K : ℤ)
    have m1 : n₁ % (K : ℤ) = l := (Finset.mem_filter.1 h₁).2
    have m2 : n₂ % (K : ℤ) = l := (Finset.mem_filter.1 h₂).2
    simp only at h
    rw [m1, h] at e1
    rw [m2] at e2
    omega
  calc ((bracket N).filter (fun n : ℤ => n % (K : ℤ) = l)).card
      ≤ (Finset.Icc (0 : ℤ) (((N : ℕ) / K : ℕ) : ℤ)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = (N : ℕ) / K + 1 := by
        rw [Int.card_Icc]
        generalize (N : ℕ) / K = q
        omega

/-- `‖w‖²_{L²([N])} = N⁻¹ ∑_{n ∈ [N]} |w(n)|²`. -/
theorem lpNormOn_bracket_two_sq (N : ℕ+) (w : ℤ → ℂ) :
    lpNormOn 2 (bracket N) w ^ 2 = (N : ℝ)⁻¹ * ∑ n ∈ bracket N, ‖w n‖ ^ 2 := by
  have h := lpNormOn_rpow (p := 2) two_pos (bracket N) w
  simpa [Real.rpow_two, card_bracket] using h

/-- The bound shared by the two cases of `e:multsf`: if every residue class modulo `K` contains at
most `c` integers of `[N]` and `|e(n/K) - 1| ≤ M` on `[N]`, then
`∑_{s<K} |m(ξ-α-(s+1)/K) - m(ξ-α-s/K)|² ≤ K c M² N⁻² ∑_{n ∈ [N]} |w(n)|²`
(Cauchy-Schwarz inside each residue class). -/
theorem sum_norm_sq_multiplierIncrement_le (N : ℕ+) (w : ℤ → ℂ) {K : ℕ} (hK : 0 < K) (α ξ : ℝ)
    {c M : ℝ}
    (hcard : ∀ l : ℕ, (((bracket N).filter (fun n : ℤ => n % (K : ℤ) = (l : ℤ))).card : ℝ) ≤ c)
    (hM : ∀ n ∈ bracket N, ‖e ((n : ℝ) / K) - 1‖ ≤ M) :
    ∑ s ∈ Finset.range K, ‖multiplierIncrement N w K α s ξ‖ ^ 2 ≤
      K * (c * M ^ 2 * ((N : ℝ)⁻¹) ^ 2 * ∑ n ∈ bracket N, ‖w n‖ ^ 2) := by
  classical
  rw [sum_norm_sq_multiplierIncrement N w hK α ξ]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have hNinv : ‖(N : ℂ)⁻¹‖ = (N : ℝ)⁻¹ := by simp
  have hl : ∀ l ∈ Finset.range K,
      ‖(N : ℂ)⁻¹ * ∑ n ∈ (bracket N).filter (fun n : ℤ => n % (K : ℤ) = (l : ℤ)),
          w n * e ((α - ξ) * n) * (e ((n : ℝ) / K) - 1)‖ ^ 2 ≤
        c * M ^ 2 * ((N : ℝ)⁻¹) ^ 2 *
          ∑ n ∈ (bracket N).filter (fun n : ℤ => n % (K : ℤ) = (l : ℤ)), ‖w n‖ ^ 2 := by
    intro l _
    set F := (bracket N).filter (fun n : ℤ => n % (K : ℤ) = (l : ℤ)) with hF
    have h1 : ‖∑ n ∈ F, w n * e ((α - ξ) * n) * (e ((n : ℝ) / K) - 1)‖ ≤
        ∑ n ∈ F, ‖w n‖ * M := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
      rw [norm_mul, norm_mul, norm_e, mul_one]
      exact mul_le_mul_of_nonneg_left (hM n (Finset.mem_filter.1 hn).1) (norm_nonneg _)
    have h2 : (∑ n ∈ F, ‖w n‖ * M) ^ 2 ≤ F.card * ∑ n ∈ F, (‖w n‖ * M) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h3 : ∑ n ∈ F, (‖w n‖ * M) ^ 2 = M ^ 2 * ∑ n ∈ F, ‖w n‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [norm_mul, hNinv, mul_pow]
    have hsq : ‖∑ n ∈ F, w n * e ((α - ξ) * n) * (e ((n : ℝ) / K) - 1)‖ ^ 2 ≤
        c * (M ^ 2 * ∑ n ∈ F, ‖w n‖ ^ 2) := by
      calc _ ≤ (∑ n ∈ F, ‖w n‖ * M) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ ≤ F.card * ∑ n ∈ F, (‖w n‖ * M) ^ 2 := h2
        _ = F.card * (M ^ 2 * ∑ n ∈ F, ‖w n‖ ^ 2) := by rw [h3]
        _ ≤ c * (M ^ 2 * ∑ n ∈ F, ‖w n‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_right (hcard l) ?_
          exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    calc ((N : ℝ)⁻¹) ^ 2 * ‖∑ n ∈ F, w n * e ((α - ξ) * n) * (e ((n : ℝ) / K) - 1)‖ ^ 2
        ≤ ((N : ℝ)⁻¹) ^ 2 * (c * (M ^ 2 * ∑ n ∈ F, ‖w n‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = c * M ^ 2 * ((N : ℝ)⁻¹) ^ 2 * ∑ n ∈ F, ‖w n‖ ^ 2 := by ring
  calc _ ≤ ∑ l ∈ Finset.range K, c * M ^ 2 * ((N : ℝ)⁻¹) ^ 2 *
          ∑ n ∈ (bracket N).filter (fun n : ℤ => n % (K : ℤ) = (l : ℤ)), ‖w n‖ ^ 2 :=
        Finset.sum_le_sum hl
    _ = c * M ^ 2 * ((N : ℝ)⁻¹) ^ 2 * ∑ n ∈ bracket N, ‖w n‖ ^ 2 := by
        rw [← Finset.mul_sum, sum_range_filter_emod hK (bracket N) (fun n => ‖w n‖ ^ 2)]

/-- **The case `K ≤ N` of `e:multsf`** (L987–L997): for `1 ≤ K ≤ N`,
`∑_{s<K} |m(ξ-α-(s+1)/K) - m(ξ-α-s/K)|² ≤ 8 · N⁻¹ ∑_{n ∈ [N]} |w(n)|²`
(each residue class contains at most `2N/K` integers of `[N]` and `|e(n/K) - 1| ≤ 2`). Source: main
paper `e:multsf`, L987–L997. -/
theorem multiplierIncrement_sq_le_of_le (N : ℕ+) (w : ℤ → ℂ) {K : ℕ} (hK : 0 < K)
    (hKN : K ≤ (N : ℕ)) (α ξ : ℝ) :
    ∑ s ∈ Finset.range K, ‖multiplierIncrement N w K α s ξ‖ ^ 2 ≤
      8 * ((N : ℝ)⁻¹ * ∑ n ∈ bracket N, ‖w n‖ ^ 2) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
  have hKNr : (K : ℝ) ≤ N := by exact_mod_cast hKN
  have hcard : ∀ l : ℕ, (((bracket N).filter (fun n : ℤ => n % (K : ℤ) = (l : ℤ))).card : ℝ) ≤
      2 * (N : ℝ) / K := by
    intro l
    have h1 := card_filter_bracket_le N hK (l : ℤ)
    have h2 : (((bracket N).filter (fun n : ℤ => n % (K : ℤ) = (l : ℤ))).card : ℝ) ≤
        (((N : ℕ) / K : ℕ) : ℝ) + 1 := by exact_mod_cast h1
    have h3 : (((N : ℕ) / K : ℕ) : ℝ) ≤ (N : ℝ) / K := Nat.cast_div_le
    have h4 : (1 : ℝ) ≤ (N : ℝ) / K := by rw [le_div_iff₀ hKr]; linarith
    calc _ ≤ _ := h2
      _ ≤ (N : ℝ) / K + (N : ℝ) / K := by linarith
      _ = 2 * (N : ℝ) / K := by ring
  have h := sum_norm_sq_multiplierIncrement_le N w hK α ξ (c := 2 * (N : ℝ) / K) (M := 2) hcard
    (fun n _ => norm_e_sub_one_le_two _)
  refine h.trans (le_of_eq ?_)
  field_simp
  ring

/-- **The case `K > N` of `e:multsf`** (L998–L1008): for `K > N ≥ 1`,
`∑_{s<K} |m(ξ-α-(s+1)/K) - m(ξ-α-s/K)|² ≤ 4π² (N/K) · N⁻¹ ∑_{n ∈ [N]} |w(n)|²`
(each residue class contains at most one integer of `[N]` and `|e(n/K) - 1| ≤ 2πN/K`). Source: main
paper `e:multsf`, L998–L1008. -/
theorem multiplierIncrement_sq_le_of_gt (N : ℕ+) (w : ℤ → ℂ) {K : ℕ} (hKN : (N : ℕ) < K)
    (α ξ : ℝ) :
    ∑ s ∈ Finset.range K, ‖multiplierIncrement N w K α s ξ‖ ^ 2 ≤
      4 * Real.pi ^ 2 * ((N : ℝ) / K) * ((N : ℝ)⁻¹ * ∑ n ∈ bracket N, ‖w n‖ ^ 2) := by
  have hK : 0 < K := (N.pos).trans hKN
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
  have hcard : ∀ l : ℕ, (((bracket N).filter (fun n : ℤ => n % (K : ℤ) = (l : ℤ))).card : ℝ) ≤
      1 := by
    intro l
    have h1 := card_filter_bracket_le N hK (l : ℤ)
    rw [Nat.div_eq_of_lt hKN, zero_add] at h1
    exact_mod_cast h1
  have hM : ∀ n ∈ bracket N, ‖e ((n : ℝ) / K) - 1‖ ≤ 2 * Real.pi * ((N : ℝ) / K) := by
    intro n hn
    have hb := mem_bracket.1 hn
    refine (norm_e_sub_one_le _).trans ?_
    have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (by omega : (0 : ℤ) ≤ n)
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast hb.2
    rw [abs_of_nonneg (div_nonneg hn0 hKr.le)]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnN hKr.le)
      (by positivity)
  have h := sum_norm_sq_multiplierIncrement_le N w hK α ξ (c := 1)
    (M := 2 * Real.pi * ((N : ℝ) / K)) hcard hM
  refine h.trans (le_of_eq ?_)
  field_simp
  ring

/-- **`e:multsf`** (L1010-L1021): uniformly in `ξ, α ∈ ℝ` and the integer `K ≥ 1`,
`(∑_{s<K} |m(ξ-α-(s+1)/K) - m(ξ-α-s/K)|²)^{1/2} ≤ 2π min{1, (N/K)^{1/2}} ‖w‖_{L²([N])}`
(the sup over `ξ ∈ 𝕋` of the paper is the universal quantifier over `ξ`). Source: main paper
`e:multsf`, L1010–L1021;
the absolute implicit constant is `2π`. -/
theorem multiplierIncrement_le (N : ℕ+) (w : ℤ → ℂ) {K : ℕ} (hK : 0 < K) (α ξ : ℝ) :
    Real.sqrt (∑ s ∈ Finset.range K, ‖multiplierIncrement N w K α s ξ‖ ^ 2) ≤
      2 * Real.pi * min 1 (Real.sqrt ((N : ℝ) / K)) * lpNormOn 2 (bracket N) w := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
  have hX : (0 : ℝ) ≤ (N : ℝ)⁻¹ * ∑ n ∈ bracket N, ‖w n‖ ^ 2 :=
    mul_nonneg (inv_nonneg.2 hNr.le) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hnorm : lpNormOn 2 (bracket N) w = Real.sqrt ((N : ℝ)⁻¹ * ∑ n ∈ bracket N, ‖w n‖ ^ 2) := by
    rw [← lpNormOn_bracket_two_sq, Real.sqrt_sq (lpNormOn_nonneg _ _ _)]
  rw [hnorm]
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  rcases le_or_gt K (N : ℕ) with hKN | hKN
  · have h1 : (1 : ℝ) ≤ Real.sqrt ((N : ℝ) / K) := by
      rw [Real.one_le_sqrt, one_le_div hKr]
      exact_mod_cast hKN
    rw [min_eq_left h1, mul_one]
    have h := multiplierIncrement_sq_le_of_le N w hK hKN α ξ
    calc Real.sqrt _ ≤ Real.sqrt (8 * ((N : ℝ)⁻¹ * ∑ n ∈ bracket N, ‖w n‖ ^ 2)) :=
          Real.sqrt_le_sqrt h
      _ = Real.sqrt 8 * Real.sqrt ((N : ℝ)⁻¹ * ∑ n ∈ bracket N, ‖w n‖ ^ 2) :=
          Real.sqrt_mul (by norm_num) _
      _ ≤ 2 * Real.pi * Real.sqrt ((N : ℝ)⁻¹ * ∑ n ∈ bracket N, ‖w n‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
          refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
          nlinarith
  · have hlt : (N : ℝ) / K < 1 := by
      rw [div_lt_one hKr]
      exact_mod_cast hKN
    have h1 : Real.sqrt ((N : ℝ) / K) ≤ 1 := by
      rw [Real.sqrt_le_one]
      exact hlt.le
    rw [min_eq_right h1]
    have h := multiplierIncrement_sq_le_of_gt N w hKN α ξ
    calc Real.sqrt _ ≤ Real.sqrt (4 * Real.pi ^ 2 * ((N : ℝ) / K) *
          ((N : ℝ)⁻¹ * ∑ n ∈ bracket N, ‖w n‖ ^ 2)) := Real.sqrt_le_sqrt h
      _ = 2 * Real.pi * Real.sqrt ((N : ℝ) / K) *
          Real.sqrt ((N : ℝ)⁻¹ * ∑ n ∈ bracket N, ‖w n‖ ^ 2) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
            show (4 : ℝ) * Real.pi ^ 2 = (2 * Real.pi) ^ 2 by ring,
            Real.sqrt_sq (by positivity)]

end PrimeCarleson.Proof.Paper
