module

public import PrimeCarleson.Proof.Paper.Defs.VariationH
public import Mathlib.Analysis.MeanInequalities

/-!
# Lemma S and chain bookkeeping for the entropy lemma

Lemma S, used in the chaining proof of `l:entest` (`sources/Variational_Carleson.tex`
L1824–L1860): the `r`-variation of a step function is at most twice the
`ℓ^r` norm of its values on the set of steps.

The proof is carried out on one chain `t₀ < ⋯ < t_K`:

* `sum_enorm_sub_rpow_le_of_monotone`: for a monotone map `b` into a linear order, a function `w`
  and a finite set `U ⊇ range b`,
  `∑_k ‖w(b_k) - w(b_{k+1})‖^r ≤ 2^r ∑_{u ∈ U} ‖w u‖^r`; the terms with `b_k = b_{k+1}`
  vanish and on the others both `k ↦ b_k` and `k ↦ b_{k+1}` are injective.
* `rVariationOnH_le_two_mul_of_retraction`: the real-parameter form. A function `h` on a set `S`
  that factors through a monotone retraction `β` onto a finite set `U` (`h t = h (β t)`) has
  `V^r(h) ≤ 2 (∑_{u∈U} ‖h u‖^r)^{1/r}`. The step form (a function that is constant
  between consecutive elements of `U`, with the first point in `U`) is a special case with
  `β t = max {u ∈ U : u ≤ t}`; `rVariationOnH_le_two_mul_sum` is `U = S`, `β = id`.
* `enorm_sub_le_rVariationOnH`, `enorm_le_enorm_add_rVariationOnH`: two-point chains, used for the
  base-point/selector step `|a_t| ≤ |a_{t₀}| + V^r(a)` (Theorem A(c), Theorem B(c));
* `rVariationOnH_le_ofReal_iff`: `V^s(h : S) ≤ λ` iff every chain has `∑ ‖Δh‖^s ≤ λ^s`;
* `Lp_sum_le_sum`: Minkowski for a finite sum of finite families, in `ℝ≥0∞`.
* `rVariationOnH_le_of_index`: a bound for `V^r` over a finite index set `T = u '' [0, N)`
  follows from the bound for index chains `j₀ < ⋯ < j_K < N`.
-/

@[expose] public noncomputable section

open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

variable {H : Type*} [SeminormedAddCommGroup H]

/-- Convexity: `‖x - y‖^r ≤ 2^{r-1} (‖x‖^r + ‖y‖^r)` for `1 ≤ r`. -/
theorem enorm_sub_rpow_le {r : ℝ} (hr : 1 ≤ r) (x y : H) :
    ‖x - y‖ₑ ^ r ≤ 2 ^ (r - 1) * (‖x‖ₑ ^ r + ‖y‖ₑ ^ r) :=
  (ENNReal.rpow_le_rpow enorm_sub_le (by linarith)).trans
    (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hr)

/-- `2^{r-1} · 2 = 2^r` in `ℝ≥0∞`. -/
theorem two_rpow_sub_one_mul_two (r : ℝ) :
    (2 : ℝ≥0∞) ^ (r - 1) * 2 = 2 ^ r := by
  calc (2 : ℝ≥0∞) ^ (r - 1) * 2 = 2 ^ (r - 1) * 2 ^ (1 : ℝ) := by rw [ENNReal.rpow_one]
    _ = 2 ^ (r - 1 + 1) := (ENNReal.rpow_add _ _ (by norm_num) (by norm_num)).symm
    _ = 2 ^ r := by rw [sub_add_cancel]

/-- The core of Lemma S, for one chain. Let `b : Fin (K+1) → κ` be monotone with values in the
finite set `U` of a linear order `κ`, and `w : κ → H`. Then
`∑_k ‖w(b_k) - w(b_{k+1})‖^r ≤ 2^r ∑_{u ∈ U} ‖w u‖^r` for `1 ≤ r`. -/
theorem sum_enorm_sub_rpow_le_of_monotone {κ : Type*} [LinearOrder κ] {K : ℕ}
    {b : Fin (K + 1) → κ} (hb : Monotone b) (w : κ → H) (U : Finset κ) (hU : ∀ k, b k ∈ U)
    {r : ℝ} (hr : 1 ≤ r) :
    ∑ k : Fin K, ‖w (b k.castSucc) - w (b k.succ)‖ₑ ^ r ≤ 2 ^ r * ∑ u ∈ U, ‖w u‖ₑ ^ r := by
  classical
  have hr0 : 0 < r := by linarith
  set S : Finset (Fin K) := Finset.univ.filter fun k => b k.castSucc < b k.succ with hS
  have hmemS : ∀ k, k ∈ S ↔ b k.castSucc < b k.succ := fun k => by simp [hS]
  have h1 : ∑ k : Fin K, ‖w (b k.castSucc) - w (b k.succ)‖ₑ ^ r =
      ∑ k ∈ S, ‖w (b k.castSucc) - w (b k.succ)‖ₑ ^ r := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun k _ hk => ?_
    have hle : b k.castSucc ≤ b k.succ := hb (Fin.castSucc_lt_succ).le
    have heq : b k.castSucc = b k.succ := by
      by_contra hne
      exact hk ((hmemS k).2 (lt_of_le_of_ne hle hne))
    simp [heq, ENNReal.zero_rpow_of_pos hr0]
  have hstrict : ∀ k ∈ S, ∀ k' ∈ S, k < k' →
      b k.succ < b k'.succ ∧ b k.castSucc < b k'.castSucc := by
    intro k hk k' hk' hlt
    have hmid : b k.succ ≤ b k'.castSucc := hb (Fin.succ_le_castSucc_iff.2 hlt)
    exact ⟨lt_of_le_of_lt hmid ((hmemS k').1 hk'), lt_of_lt_of_le ((hmemS k).1 hk) hmid⟩
  have hinj : ∀ f : Fin K → κ, (∀ k ∈ S, ∀ k' ∈ S, k < k' → f k < f k') → Set.InjOn f S := by
    intro f hf k hk k' hk' h
    rcases lt_trichotomy k k' with hlt | heq | hgt
    · exact absurd h (hf k hk k' hk' hlt).ne
    · exact heq
    · exact absurd h (hf k' hk' k hk hgt).ne'
  have hinj1 : Set.InjOn (fun k : Fin K => b k.succ) S :=
    hinj _ fun k hk k' hk' hlt => (hstrict k hk k' hk' hlt).1
  have hinj2 : Set.InjOn (fun k : Fin K => b k.castSucc) S :=
    hinj _ fun k hk k' hk' hlt => (hstrict k hk k' hk' hlt).2
  have hsum1 : ∑ k ∈ S, ‖w (b k.succ)‖ₑ ^ r ≤ ∑ u ∈ U, ‖w u‖ₑ ^ r := by
    rw [← Finset.sum_image (f := fun u => ‖w u‖ₑ ^ r) hinj1]
    exact Finset.sum_le_sum_of_subset (by
      intro u hu
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hu
      exact hU _)
  have hsum2 : ∑ k ∈ S, ‖w (b k.castSucc)‖ₑ ^ r ≤ ∑ u ∈ U, ‖w u‖ₑ ^ r := by
    rw [← Finset.sum_image (f := fun u => ‖w u‖ₑ ^ r) hinj2]
    exact Finset.sum_le_sum_of_subset (by
      intro u hu
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hu
      exact hU _)
  calc ∑ k : Fin K, ‖w (b k.castSucc) - w (b k.succ)‖ₑ ^ r
      = ∑ k ∈ S, ‖w (b k.castSucc) - w (b k.succ)‖ₑ ^ r := h1
    _ ≤ ∑ k ∈ S, 2 ^ (r - 1) * (‖w (b k.castSucc)‖ₑ ^ r + ‖w (b k.succ)‖ₑ ^ r) :=
        Finset.sum_le_sum fun k _ => enorm_sub_rpow_le hr _ _
    _ = 2 ^ (r - 1) * (∑ k ∈ S, ‖w (b k.castSucc)‖ₑ ^ r + ∑ k ∈ S, ‖w (b k.succ)‖ₑ ^ r) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ 2 ^ (r - 1) * (∑ u ∈ U, ‖w u‖ₑ ^ r + ∑ u ∈ U, ‖w u‖ₑ ^ r) := by gcongr
    _ = 2 ^ r * ∑ u ∈ U, ‖w u‖ₑ ^ r := by
        rw [← two_mul, ← mul_assoc, two_rpow_sub_one_mul_two]

/-- The `r`-th root form of `sum_enorm_sub_rpow_le_of_monotone`:
`(∑_k ‖w(b_k) - w(b_{k+1})‖^r)^{1/r} ≤ 2 (∑_{u∈U} ‖w u‖^r)^{1/r}`. -/
theorem chain_variation_le_two_mul {κ : Type*} [LinearOrder κ] {K : ℕ}
    {b : Fin (K + 1) → κ} (hb : Monotone b) (w : κ → H) (U : Finset κ) (hU : ∀ k, b k ∈ U)
    {r : ℝ} (hr : 1 ≤ r) :
    (∑ k : Fin K, ‖w (b k.castSucc) - w (b k.succ)‖ₑ ^ r) ^ (1 / r) ≤
      2 * (∑ u ∈ U, ‖w u‖ₑ ^ r) ^ (1 / r) := by
  have hr0 : 0 ≤ 1 / r := by positivity
  calc (∑ k : Fin K, ‖w (b k.castSucc) - w (b k.succ)‖ₑ ^ r) ^ (1 / r)
      ≤ (2 ^ r * ∑ u ∈ U, ‖w u‖ₑ ^ r) ^ (1 / r) :=
        ENNReal.rpow_le_rpow (sum_enorm_sub_rpow_le_of_monotone hb w U hU hr) hr0
    _ = 2 * (∑ u ∈ U, ‖w u‖ₑ ^ r) ^ (1 / r) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hr0, ← ENNReal.rpow_mul]
        have : r * (1 / r) = 1 := mul_one_div_cancel (by linarith)
        rw [this, ENNReal.rpow_one]

/-- **Lemma S** (retraction form). Let `h : ℝ → H` on a set `S ⊆ ℝ` factor through a monotone map
`β` into a finite set `U`: `β t ∈ U` and `h t = h (β t)` for `t ∈ S`. Then for `1 ≤ r`,
`V^r(h : t ∈ S) ≤ 2 (∑_{u∈U} ‖h u‖^r)^{1/r}`.

This is Lemma S in its step form: a step function of `t` is constant between consecutive elements of
`U` and `β t = max {u ∈ U : u ≤ t}`. The constant is absolute. -/
theorem rVariationOnH_le_two_mul_of_retraction {S : Set ℝ} {h : ℝ → H} {β : ℝ → ℝ}
    (hβ : MonotoneOn β S) {U : Finset ℝ} (hU : ∀ t ∈ S, β t ∈ U)
    (hh : ∀ t ∈ S, h t = h (β t)) {r : ℝ} (hr : 1 ≤ r) :
    rVariationOnH r S h ≤ 2 * (∑ u ∈ U, ‖h u‖ₑ ^ r) ^ (1 / r) := by
  refine rVariationOnH_le_iff.2 fun J t ht hS => ?_
  have hb : Monotone fun k => β (t k) := fun k k' hkk' => hβ (hS k) (hS k') (ht.monotone hkk')
  have := chain_variation_le_two_mul hb h U (fun k => hU _ (hS k)) hr (K := J)
  simpa only [← hh _ (hS _)] using this

/-- **Lemma S**, `U = S`: for a finite index set `S`, `V^r(h : t ∈ S) ≤ 2 (∑_{t∈S} ‖h t‖^r)^{1/r}`
(the constant function `β = id`). -/
theorem rVariationOnH_le_two_mul_sum (S : Finset ℝ) (h : ℝ → H) {r : ℝ} (hr : 1 ≤ r) :
    rVariationOnH r (S : Set ℝ) h ≤ 2 * (∑ u ∈ S, ‖h u‖ₑ ^ r) ^ (1 / r) :=
  rVariationOnH_le_two_mul_of_retraction (β := id) monotoneOn_id (U := S)
    (fun _ ht => ht) (fun _ _ => rfl) hr

/-- **Lemma S**, `U = S`, `ℂ`-valued, `rVariationOn`. -/
theorem rVariationOn_le_two_mul_sum (S : Finset ℝ) (h : ℝ → ℂ) {r : ℝ} (hr : 1 ≤ r) :
    PrimeCarleson.rVariationOn r (S : Set ℝ) h ≤ 2 * (∑ u ∈ S, ‖h u‖ₑ ^ r) ^ (1 / r) :=
  rVariationOnH_le_two_mul_sum S h hr

/-- **Two-point chains.** For `s, t ∈ S` and `0 < r`: `‖h s - h t‖ ≤ V^r(h : S)`. -/
theorem enorm_sub_le_rVariationOnH {S : Set ℝ} {h : ℝ → H} {r : ℝ} (hr : 0 < r) {s t : ℝ}
    (hs : s ∈ S) (ht : t ∈ S) : ‖h s - h t‖ₑ ≤ rVariationOnH r S h := by
  have key : ∀ {a b : ℝ}, a < b → a ∈ S → b ∈ S → ‖h a - h b‖ₑ ≤ rVariationOnH r S h := by
    intro a b hab ha hb
    have hm : StrictMono (![a, b] : Fin 2 → ℝ) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    have := le_rVariationOnH (c := h) (r := r) (S := S) (J := 1) hm (by
      intro i; fin_cases i <;> simp [ha, hb])
    simp only [Fin.sum_univ_one] at this
    simpa [ENNReal.rpow_rpow_inv hr.ne'] using this
  rcases lt_trichotomy s t with hst | rfl | hts
  · exact key hst hs ht
  · simp
  · rw [enorm_sub_rev]; exact key hts ht hs

/-- **Base point and variation**: for `s, t₀ ∈ S`, `‖h s‖ ≤ ‖h t₀‖ + V^r(h : S)` (`0 < r`), by the
two-point chain `{s, t₀}`. -/
theorem enorm_le_enorm_add_rVariationOnH {S : Set ℝ} {h : ℝ → H} {r : ℝ} (hr : 0 < r) {s t₀ : ℝ}
    (hs : s ∈ S) (ht₀ : t₀ ∈ S) : ‖h s‖ₑ ≤ ‖h t₀‖ₑ + rVariationOnH r S h :=
  calc ‖h s‖ₑ = ‖(h s - h t₀) + h t₀‖ₑ := by rw [sub_add_cancel]
    _ ≤ ‖h s - h t₀‖ₑ + ‖h t₀‖ₑ := enorm_add_le _ _
    _ ≤ rVariationOnH r S h + ‖h t₀‖ₑ := by
        gcongr
        exact enorm_sub_le_rVariationOnH hr hs ht₀
    _ = ‖h t₀‖ₑ + rVariationOnH r S h := add_comm _ _

/-- A family on an empty index set has variation `0`. -/
theorem rVariationOnH_empty (r : ℝ) (h : ℝ → H) : rVariationOnH r (∅ : Set ℝ) h = 0 :=
  le_antisymm (rVariationOnH_le_iff.2 fun _ _ _ hS => absurd (hS 0) (Set.notMem_empty _)) zero_le

/-- **Chain-wise form of the variation bound.** `V^s(h : S) ≤ λ` (`λ ≥ 0`, `s > 0`) iff every chain
`t₀ < ⋯ < t_J` in `S` has `∑ ‖h t_i - h t_{i+1}‖^s ≤ λ^s`. This is hypothesis (V) of the entropy
lemma and the `H`-valued seminorm bound. -/
theorem rVariationOnH_le_ofReal_iff {S : Set ℝ} {h : ℝ → H} {s lam : ℝ} (hs : 0 < s)
    (hlam : 0 ≤ lam) :
    rVariationOnH s S h ≤ ENNReal.ofReal lam ↔
      ∀ (J : ℕ) (t : Fin (J + 1) → ℝ), StrictMono t → (∀ i, t i ∈ S) →
        ∑ i : Fin J, ‖h (t i.castSucc) - h (t i.succ)‖ ^ s ≤ lam ^ s := by
  rw [rVariationOnH_le_iff]
  refine forall_congr' fun J => forall_congr' fun t => forall_congr' fun _ =>
    forall_congr' fun _ => ?_
  set X : ℝ := ∑ i : Fin J, ‖h (t i.castSucc) - h (t i.succ)‖ ^ s with hX
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun i _ => by positivity
  have hE : ∑ i : Fin J, ‖h (t i.castSucc) - h (t i.succ)‖ₑ ^ s = ENNReal.ofReal X := by
    rw [hX, ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hs.le]
  rw [hE, ENNReal.ofReal_rpow_of_nonneg hX0 (by positivity), ENNReal.ofReal_le_ofReal_iff hlam,
    one_div, Real.rpow_inv_le_iff_of_pos hX0 hlam hs]

/-- Minkowski's inequality for a finite sum of finite families in `ℝ≥0∞`:
`(∑_i (∑_v f_v(i))^p)^{1/p} ≤ ∑_v (∑_i f_v(i)^p)^{1/p}` for `1 ≤ p`. -/
theorem Lp_sum_le_sum {ι κ : Type*} (s : Finset ι) (t : Finset κ) (f : κ → ι → ℝ≥0∞) {p : ℝ}
    (hp : 1 ≤ p) :
    (∑ i ∈ s, (∑ v ∈ t, f v i) ^ p) ^ (1 / p) ≤ ∑ v ∈ t, (∑ i ∈ s, f v i ^ p) ^ (1 / p) := by
  classical
  have hp0 : 0 < p := by linarith
  induction t using Finset.induction_on with
  | empty =>
    simp [ENNReal.zero_rpow_of_pos hp0, hp0]
  | insert v t hv ih =>
    simp only [Finset.sum_insert hv]
    exact (ENNReal.Lp_add_le s (f v) (fun i => ∑ w ∈ t, f w i) hp).trans
      (add_le_add_right ih _)

/-- Minkowski for the norms of a finite sum of vectors along a chain:
`(∑_i ‖∑_v x_v(i)‖^p)^{1/p} ≤ ∑_v (∑_i ‖x_v(i)‖^p)^{1/p}`. -/
theorem Lp_enorm_sum_le_sum {ι κ : Type*} (s : Finset ι) (t : Finset κ) (x : κ → ι → H) {p : ℝ}
    (hp : 1 ≤ p) :
    (∑ i ∈ s, ‖∑ v ∈ t, x v i‖ₑ ^ p) ^ (1 / p) ≤
      ∑ v ∈ t, (∑ i ∈ s, ‖x v i‖ₑ ^ p) ^ (1 / p) := by
  have hp0 : 0 ≤ p := by linarith
  calc (∑ i ∈ s, ‖∑ v ∈ t, x v i‖ₑ ^ p) ^ (1 / p)
      ≤ (∑ i ∈ s, (∑ v ∈ t, ‖x v i‖ₑ) ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (Finset.sum_le_sum fun i _ =>
          ENNReal.rpow_le_rpow (enorm_sum_le _ _) hp0) (by positivity)
    _ ≤ ∑ v ∈ t, (∑ i ∈ s, ‖x v i‖ₑ ^ p) ^ (1 / p) :=
        Lp_sum_le_sum s t (fun v i => ‖x v i‖ₑ) hp

/-- **From index chains to real chains.** Let `u : ℕ → ℝ` be strictly increasing on `[0, N)` with
image `T`. If `(∑_k ‖f(u j_k) - f(u j_{k+1})‖^r)^{1/r} ≤ B` for every strictly increasing index
chain `j₀ < ⋯ < j_K < N`, then `V^r(f : t ∈ T) ≤ B`. -/
theorem rVariationOnH_le_of_index {N : ℕ} {u : ℕ → ℝ} (hu : StrictMonoOn u (Set.Iio N))
    {T : Set ℝ} (hT : T ⊆ u '' Set.Iio N) (f : ℝ → H) {r : ℝ} {B : ℝ≥0∞}
    (h : ∀ (K : ℕ) (j : Fin (K + 1) → ℕ), StrictMono j → (∀ k, j k < N) →
      (∑ k : Fin K, ‖f (u (j k.castSucc)) - f (u (j k.succ))‖ₑ ^ r) ^ (1 / r) ≤ B) :
    rVariationOnH r T f ≤ B := by
  refine rVariationOnH_le_iff.2 fun J t ht hS => ?_
  have hex : ∀ k, ∃ i : ℕ, i < N ∧ u i = t k := fun k => hT (hS k)
  choose j hjN hju using hex
  have hjm : StrictMono j := by
    intro k k' hkk'
    have : u (j k) < u (j k') := by rw [hju, hju]; exact ht hkk'
    exact (hu.lt_iff_lt (hjN k) (hjN k')).1 this
  have := h J j hjm hjN
  simpa only [hju] using this

/-- Existence of an increasing enumeration of a finite set of reals: there are `N` and `u : ℕ → ℝ`
strictly increasing on `[0, N)` with `T = u '' [0, N)`. -/
theorem exists_enumeration {T : Set ℝ} (hT : T.Finite) :
    ∃ (N : ℕ) (u : ℕ → ℝ), StrictMonoOn u (Set.Iio N) ∧ T = u '' Set.Iio N := by
  classical
  set F : Finset ℝ := hT.toFinset with hF
  refine ⟨F.card, fun j => if h : j < F.card then F.orderEmbOfFin rfl ⟨j, h⟩ else 0, ?_, ?_⟩
  · intro i hi j hj hij
    simp only [Set.mem_Iio] at hi hj
    simp only [hi, hj, dite_true]
    exact (F.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.2 hij)
  · ext x
    constructor
    · intro hx
      have hxF : x ∈ F := by simpa [hF] using hx
      obtain ⟨k, hk⟩ : x ∈ Set.range (F.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]; exact hxF
      exact ⟨k.1, k.2, by simp [k.2, hk]⟩
    · rintro ⟨j, hj, rfl⟩
      simp only [Set.mem_Iio] at hj
      simp only [hj, dite_true]
      exact (Set.Finite.mem_toFinset hT).1 (Finset.orderEmbOfFin_mem F rfl ⟨j, hj⟩)

section Step

end Step

end PrimeCarleson.Proof.Paper
