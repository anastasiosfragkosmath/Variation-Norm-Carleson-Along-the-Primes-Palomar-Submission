module

public import PrimeCarleson.Proof.Paper.P2.U2Fourier

/-!
# The recursive identity for Gowers norms

Display `e:foliate` (Source: main paper `e:foliate`, L673–L676): for
`s ≥ 1` and finitely supported `f`,
`‖f‖_{U^{s+1}(ℤ)}^{2^{s+1}} = ∑_{h₁,…,h_{s-1}} ‖Δ_{h₁,…,h_{s-1}} f‖_{U²(ℤ)}⁴`.

The iterated difference `Δ_{h₁,…,h_t} f = multDiff t h f` of the API is a function
`ℤ → ℂ`; since the `gowersNorm` takes finitely supported functions, it is regarded as
the finitely supported `multDiffFinsupp t h f` (its support lies in that of `f`).

* `gowersNorm_pow_two_add` (`t = s - 1`): `‖f‖_{U^{t+2}}^{2^{t+2}} = ∑'_{h : Fin t → ℤ}
  ‖Δ_h f‖_{U²}⁴`;
* `gowersNorm_pow_two_add_eq_sum_box`: the finite form, the sum over `h ∈ B^t` for any finite
  `B` containing all differences of the support (the case `s = 2`, `t = 1`, is
  `gowersNorm_three_pow_eight_eq_sum`, the recursive identity used by `e:U3maxmod`).

Proof. Split the `t + 2` differences `h = (h', a, b)`; then
`Δ_{h',a,b} f = Δ_{a,b}(Δ_{h'} f)` (`multDiff_snoc_snoc`), the Gowers sum
`∑_{x,h} Δ_h f(x)` regroups (a finite-support Fubini along an equivalence) as the sum over `h'`
of the `U²` sums of `Δ_{h'} f`, which are `‖Δ_{h'} f‖_{U²}⁴` by definition.
-/

@[expose] public noncomputable section

open scoped ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0

/-- A nonzero iterated difference forces `f` to be nonzero at that point, so the support of
`Δ_h f` is finite for finitely supported `f`. -/
theorem multDiff_support_finite (t : ℕ) (h : Fin t → ℤ) (f : ℤ →₀ ℂ) :
    (Function.support (multDiff t h ⇑f)).Finite :=
  (Common.GowersCS.finsupp_support_finite f).subset fun x hx =>
    (multDiff_ne_zero h (⇑f) x hx).1

/-- The iterated conjugation-difference `Δ_{h₁,…,h_t} f` of a finitely supported `f`, as a
finitely supported function (so that the `gowersNorm` applies to it). -/
def multDiffFinsupp (t : ℕ) (h : Fin t → ℤ) (f : ℤ →₀ ℂ) : ℤ →₀ ℂ :=
  Finsupp.ofSupportFinite (multDiff t h ⇑f) (multDiff_support_finite t h f)

/-- `(Δ_h f)(x)` of the finitely supported version is the iterated difference. -/
theorem multDiffFinsupp_apply (t : ℕ) (h : Fin t → ℤ) (f : ℤ →₀ ℂ) (x : ℤ) :
    multDiffFinsupp t h f x = multDiff t h ⇑f x := rfl

/-- `Δ_{h₁,…,h_t,a,b} f = Δ_{a,b}(Δ_{h₁,…,h_t} f)`. -/
theorem multDiff_snoc_snoc (t : ℕ) (h' : Fin t → ℤ) (a b : ℤ) (f : ℤ → ℂ) (x : ℤ) :
    multDiff (t + 2) (Fin.snoc (Fin.snoc h' a : Fin (t + 1) → ℤ) b) f x =
      multDiff 2 ![a, b] (multDiff t h' f) x := by
  rw [multDiff_two_apply]
  simp only [multDiff_succ, conjDiff_apply, Fin.init_snoc, Fin.snoc_last]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]

/-- The re-indexing of the parameters `(x, h₁, …, h_{t+2})` of the Gowers sum by
`(h₁, …, h_t)` and the parameters `(x, a, b)` of a `U²` sum. -/
private def foliateEquiv (t : ℕ) :
    (Fin t → ℤ) × (ℤ × (Fin 2 → ℤ)) ≃ ℤ × (Fin (t + 2) → ℤ) where
  toFun q := (q.2.1, Fin.snoc (Fin.snoc q.1 (q.2.2 0) : Fin (t + 1) → ℤ) (q.2.2 1))
  invFun p := (Fin.init (Fin.init p.2), p.1, ![Fin.init p.2 (Fin.last t), p.2 (Fin.last (t + 1))])
  left_inv := by
    rintro ⟨h', x, k⟩
    simp only [Fin.init_snoc, Fin.snoc_last, Prod.mk.injEq, true_and]
    refine funext fun i => ?_
    fin_cases i <;> simp
  right_inv := by
    rintro ⟨x, h⟩
    simp only [Prod.mk.injEq, true_and]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    simp only [Fin.snoc_init_self]

/-- **`e:foliate`, in the indexing `t = s - 1`** (Source: main paper `e:foliate`, L673–L676):
`‖f‖_{U^{t+2}(ℤ)}^{2^{t+2}} = ∑_{h₁,…,h_t} ‖Δ_{h₁,…,h_t} f‖_{U²(ℤ)}⁴` for finitely supported
`f`; the sum over `h : Fin t → ℤ` has finitely many nonzero terms. -/
theorem gowersNorm_pow_two_add (t : ℕ) (f : ℤ →₀ ℂ) :
    gowersNorm ⟨t + 2, by omega⟩ f ^ 2 ^ (t + 2) =
      ∑' h : Fin t → ℤ, gowersNorm 2 (multDiffFinsupp t h f) ^ 4 := by
  classical
  set F : ℤ × (Fin (t + 2) → ℤ) → ℂ := fun p => multDiff (t + 2) p.2 (⇑f) p.1 with hF
  have hFfin : (Function.support F).Finite :=
    gowersSum_support_finite ⟨t + 2, by omega⟩ f
  have h0 : ((gowersNorm ⟨t + 2, by omega⟩ f : ℝ) : ℂ) ^ 2 ^ (t + 2) = ∑' p, F p :=
    gowersNorm_pow_eq_tsum ⟨t + 2, by omega⟩ f
  set G : (Fin t → ℤ) × (ℤ × (Fin 2 → ℤ)) → ℂ := fun q =>
    multDiff 2 q.2.2 (multDiff t q.1 ⇑f) q.2.1 with hG
  have hGF : ∀ q, F (foliateEquiv t q) = G q := fun q => by
    simp only [hF, hG, foliateEquiv, Equiv.coe_fn_mk]
    rw [multDiff_snoc_snoc]
    congr 2
    funext i
    fin_cases i <;> rfl
  have hGfin : (Function.support G).Finite := by
    have : Function.support G = foliateEquiv t ⁻¹' Function.support F := by
      ext q
      simp [Function.mem_support, ← hGF q]
    rw [this]
    exact Set.Finite.preimage (foliateEquiv t).injective.injOn hFfin
  have h1 : ∑' p, F p = ∑' q, G q := by
    rw [← (foliateEquiv t).tsum_eq F]
    exact tsum_congr hGF
  rw [h1, Common.GowersCS.tsum_equiv_prod (Equiv.refl _) G hGfin] at h0
  have h2 : ∀ h' : Fin t → ℤ,
      ∑' z : ℤ × (Fin 2 → ℤ), G ((Equiv.refl _).symm (h', z)) =
        ((gowersNorm 2 (multDiffFinsupp t h' f) : ℝ) : ℂ) ^ 2 ^ 2 := fun h' =>
    (gowersNorm_pow_eq_tsum 2 (multDiffFinsupp t h' f)).symm
  rw [tsum_congr h2] at h0
  have h3 : ∑' h' : Fin t → ℤ, ((gowersNorm 2 (multDiffFinsupp t h' f) : ℝ) : ℂ) ^ 2 ^ 2 =
      ((∑' h' : Fin t → ℤ, gowersNorm 2 (multDiffFinsupp t h' f) ^ 4 : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun h' => ?_
    push_cast
    norm_num
  rw [h3] at h0
  exact_mod_cast h0


/-- If `Δ_h f ≠ 0` then every `h_i` is a difference of two points of the support: if all
differences of the support of `f` lie in `B` and some `h_i ∉ B`, then `Δ_h f = 0`. -/
theorem multDiffFinsupp_eq_zero_of_notMem (t : ℕ) (f : ℤ →₀ ℂ) (B : Finset ℤ)
    (hB : ∀ x y, f x ≠ 0 → f y ≠ 0 → y - x ∈ B) (h : Fin t → ℤ) (i : Fin t) (hi : h i ∉ B) :
    multDiffFinsupp t h f = 0 := by
  ext x
  by_contra hne
  obtain ⟨h0, h1⟩ := multDiff_ne_zero h (⇑f) x hne
  have := hB x (x + h i) h0 (h1 i)
  rw [add_sub_cancel_left] at this
  exact hi this

/-- **`e:foliate`, finite form**: if `B` contains all differences `y - x` of points of the support
of `f`, then `‖f‖_{U^{t+2}(ℤ)}^{2^{t+2}} = ∑_{h ∈ B^t} ‖Δ_h f‖_{U²(ℤ)}⁴`. -/
theorem gowersNorm_pow_two_add_eq_sum_box (t : ℕ) (f : ℤ →₀ ℂ) (B : Finset ℤ)
    (hB : ∀ x y, f x ≠ 0 → f y ≠ 0 → y - x ∈ B) :
    gowersNorm ⟨t + 2, by omega⟩ f ^ 2 ^ (t + 2) =
      ∑ h ∈ Fintype.piFinset (fun _ : Fin t => B),
        gowersNorm 2 (multDiffFinsupp t h f) ^ 4 := by
  classical
  rw [gowersNorm_pow_two_add]
  refine tsum_eq_sum fun h hh => ?_
  have : ∃ i, h i ∉ B := by
    by_contra hcon
    push Not at hcon
    exact hh (Fintype.mem_piFinset.2 hcon)
  obtain ⟨i, hi⟩ := this
  rw [multDiffFinsupp_eq_zero_of_notMem t f B hB h i hi]
  have h0 : gowersNorm 2 (0 : ℤ →₀ ℂ) = 0 := Common.GowersCS.nm_zero 1
  rw [h0]
  norm_num

/-- The differences of the support of `f`: a finite set `B` with `y - x ∈ B` for all
`x, y ∈ supp f`. -/
theorem exists_finset_differences (f : ℤ →₀ ℂ) :
    ∃ B : Finset ℤ, ∀ x y, f x ≠ 0 → f y ≠ 0 → y - x ∈ B :=
  ⟨(f.support ×ˢ f.support).image (fun p => p.2 - p.1), fun x y hx hy =>
    Finset.mem_image.2 ⟨(x, y), Finset.mem_product.2 ⟨Finsupp.mem_support_iff.2 hx,
      Finsupp.mem_support_iff.2 hy⟩, rfl⟩⟩

/-- `Δ_h f(x) = f(x) conj f(x + h)` for the one-step finitely supported difference. -/
theorem multDiffFinsupp_one_apply (h : ℤ) (f : ℤ →₀ ℂ) (x : ℤ) :
    multDiffFinsupp 1 (fun _ => h) f x = f x * conj (f (x + h)) := rfl

/-- **`e:foliate` for `s = 2`** (Source: main paper `e:foliate`, L673–L676; the case used in the
proof of
`e:U3maxmod`, L877): if `B` contains all differences of points of the support of `f`,
`‖f‖_{U³(ℤ)}⁸ = ∑_{h ∈ B} ‖Δ_h f‖_{U²(ℤ)}⁴` with `Δ_h f(x) = f(x) conj f(x + h)`. -/
theorem gowersNorm_three_pow_eight_eq_sum (f : ℤ →₀ ℂ) (B : Finset ℤ)
    (hB : ∀ x y, f x ≠ 0 → f y ≠ 0 → y - x ∈ B) :
    gowersNorm 3 f ^ 8 = ∑ h ∈ B, gowersNorm 2 (multDiffFinsupp 1 (fun _ => h) f) ^ 4 := by
  classical
  have h1 : gowersNorm 3 f ^ 8 =
      ∑' h : Fin 1 → ℤ, gowersNorm 2 (multDiffFinsupp 1 h f) ^ 4 := gowersNorm_pow_two_add 1 f
  rw [h1, ← (Equiv.funUnique (Fin 1) ℤ).symm.tsum_eq]
  have hc : ∀ a : ℤ, (Equiv.funUnique (Fin 1) ℤ).symm a = fun _ => a := fun a => rfl
  simp only [hc]
  refine tsum_eq_sum fun a ha => ?_
  rw [multDiffFinsupp_eq_zero_of_notMem 1 f B hB (fun _ => a) 0 ha]
  have h0 : gowersNorm 2 (0 : ℤ →₀ ℂ) = 0 := Common.GowersCS.nm_zero 1
  rw [h0]
  norm_num

/-- `Δ_{0,…,0} f(x) = |f(x)|^{2^{t+1}}` (for `t + 1 ≥ 1` differences). -/
theorem multDiff_zero_succ (t : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    multDiff (t + 1) 0 f x = ((‖f x‖ ^ 2 ^ (t + 1) : ℝ) : ℂ) := by
  induction t generalizing x with
  | zero =>
    have h : multDiff 1 (0 : Fin 1 → ℤ) f x = conjDiff 0 f x := rfl
    rw [h, conjDiff_zero]
    norm_num
  | succ t ih =>
    have h0 : Fin.init (0 : Fin (t + 1 + 1) → ℤ) = 0 := rfl
    rw [multDiff_succ, conjDiff_apply, h0, Pi.zero_apply, add_zero, ih, Complex.conj_ofReal]
    push_cast
    rw [← pow_add]
    congr 1
    ring

/-- **The Gowers norm `U^s(ℤ)` is definite for `s ≥ 2`**: `‖f‖_{U^s(ℤ)} = 0` forces `f = 0`
(from `e:foliate`, the term `h = 0`, and the `U²` case). -/
theorem eq_zero_of_gowersNorm_eq_zero (s : ℕ+) (hs : 2 ≤ s) {f : ℤ →₀ ℂ}
    (h : gowersNorm s f = 0) : f = 0 := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, s = ⟨t + 2, by omega⟩ :=
    ⟨(s : ℕ) - 2, PNat.eq (by have := PNat.coe_le_coe 2 s |>.2 hs; simp at this ⊢; omega)⟩
  classical
  obtain ⟨B, hB⟩ := exists_finset_differences f
  have h8 := gowersNorm_pow_two_add_eq_sum_box t f B hB
  rw [h, zero_pow (by positivity)] at h8
  by_cases hf : f = 0
  · exact hf
  exfalso
  have hne : ∃ x, f x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hf (Finsupp.ext hcon)
  obtain ⟨x0, hx0⟩ := hne
  have h0B : (0 : ℤ) ∈ B := by simpa using hB x0 x0 hx0 hx0
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun h _ => by positivity).1 h8.symm
    (0 : Fin t → ℤ) (Fintype.mem_piFinset.2 fun _ => h0B)
  have h4 : gowersNorm 2 (multDiffFinsupp t 0 f) = 0 := by
    have := pow_eq_zero_iff (n := 4) (by norm_num) |>.1 hz
    exact this
  have hD := eq_zero_of_gowersNorm_two_eq_zero h4
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · exact hf (Finsupp.ext fun x => by
      have := congrArg (fun g : ℤ →₀ ℂ => g x) hD
      simpa [multDiffFinsupp_apply, multDiff] using this)
  · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have hx := congrArg (fun g : ℤ →₀ ℂ => g x0) hD
    simp only [multDiffFinsupp_apply, multDiff_zero_succ, Finsupp.coe_zero, Pi.zero_apply,
      Complex.ofReal_eq_zero] at hx
    exact hx0 (by simpa using pow_eq_zero_iff (by positivity) |>.1 hx)

end PrimeCarleson.Proof.Paper
