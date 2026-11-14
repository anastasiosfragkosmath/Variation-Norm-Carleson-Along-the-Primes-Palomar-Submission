module

public import PrimeCarleson.Proof.FplusProp21.Expansion

/-!
# The off-diagonal exponential sums

The off-diagonal step of [F+] Proposition 2.1 ([F+] TeX
L758–L776). The steps, with their sources:

* the geometric series bound (`norm_sum_e_le_of_intConvex`): if `D θ ∈ ℤ` and `θ ∉ ℤ`, then
  `|∑_{x ∈ I} e(x θ)| ≤ D` for every finite interval `I` of integers (the full periods of `e(x θ)`
  cancel, by the geometric sum; the remainder has fewer than `D` terms);
* [F+] `expansion-non-diagonal`, L758–L776 (`norm_cubeW_le`): if `D L_j ∈ ℤ` for all `j` and some
  `L_j ∉ ℤ`, then `|W_M(L)| ≤ (2M + 1)³ D`. For fixed values of the other three variables the
  admissible values of the variable paired with the non-integral `L_j` form an interval, since every
  constraint `x + ω · h ∈ [M]` is monotone in it (for `L_1, L_2, L_3` this is the case that [F+]
  L765 leaves to the reader).
-/

@[expose] public noncomputable section

open Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.FplusProp21

open PrimeCarleson.Proof.Goal0

/-- A finite set of integers containing every integer between two of its elements. -/
def IntConvex (X : Finset ℤ) : Prop := ∀ x ∈ X, ∀ y ∈ X, ∀ z, x ≤ z → z ≤ y → z ∈ X

/-- `e(l θ) = e(θ)^l`. -/
theorem e_natCast_mul (l : ℕ) (θ : ℝ) : e (l * θ) = e θ ^ l := by
  induction l with
  | zero => simp [e_zero]
  | succ n ih =>
    rw [pow_succ, ← ih, ← e_add]
    congr 1
    push_cast
    ring

/-- `e(θ) = 1` only for integral `θ`. -/
theorem isInt_of_e_eq_one {θ : ℝ} (h : e θ = 1) : IsInt θ := by
  rw [e, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
  have : ((θ : ℝ) : ℂ) = (n : ℂ) := by
    apply mul_left_cancel₀ hpi
    rw [hn]
    ring
  exact_mod_cast this

/-- Partial geometric sums of a nontrivial `D`-th root of unity are bounded by `D`. -/
theorem norm_sum_range_pow_le {z : ℂ} (hz : ‖z‖ = 1) {D : ℕ} (hD : 0 < D) (hzD : z ^ D = 1)
    (hz1 : z ≠ 1) (L : ℕ) : ‖∑ l ∈ range L, z ^ l‖ ≤ D := by
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    rcases Nat.lt_or_ge L D with hL | hL
    · calc ‖∑ l ∈ range L, z ^ l‖ ≤ ∑ l ∈ range L, ‖z ^ l‖ := norm_sum_le _ _
        _ = L := by simp [norm_pow, hz]
        _ ≤ D := by exact_mod_cast hL.le
    · obtain ⟨L', rfl⟩ : ∃ L', L = D + L' := ⟨L - D, by omega⟩
      have hgeom : ∑ l ∈ range D, z ^ l = 0 := by
        rw [geom_sum_eq hz1, hzD]
        simp
      rw [sum_range_add, hgeom, zero_add]
      simp_rw [pow_add, hzD, one_mul]
      exact ih L' (by omega)

/-- A sum of `e(x θ)` over an integer interval. -/
theorem sum_Icc_e_eq (m m' : ℤ) (θ : ℝ) :
    ∑ x ∈ Icc m m', e (x * θ) = e (m * θ) * ∑ l ∈ range (m' + 1 - m).toNat, e θ ^ l := by
  rw [Int.Icc_eq_finset_map, sum_map, mul_sum]
  refine sum_congr rfl fun l _ => ?_
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply]
  rw [← e_natCast_mul, ← e_add]
  congr 1
  push_cast
  ring

/-- A nonempty `IntConvex` set is the interval between its least and greatest elements. -/
theorem eq_Icc_of_intConvex {X : Finset ℤ} (hX : IntConvex X) (hne : X.Nonempty) :
    X = Icc (X.min' hne) (X.max' hne) := by
  ext z
  constructor
  · intro hz
    exact mem_Icc.2 ⟨min'_le X z hz, le_max' X z hz⟩
  · intro hz
    rw [mem_Icc] at hz
    exact hX _ (min'_mem X hne) _ (max'_mem X hne) z hz.1 hz.2

/-- **Geometric-series bound**: if `D θ ∈ ℤ` and `θ ∉ ℤ`, then `|∑_{x ∈ X} e(x θ)| ≤ D` for every
finite integer interval `X`. -/
theorem norm_sum_e_le_of_intConvex {X : Finset ℤ} (hX : IntConvex X) {θ : ℝ} {D : ℕ}
    (hD : 0 < D) (hDθ : IsInt (D * θ)) (hθ : ¬ IsInt θ) : ‖∑ x ∈ X, e (x * θ)‖ ≤ D := by
  rcases X.eq_empty_or_nonempty with rfl | hne
  · simp
  rw [eq_Icc_of_intConvex hX hne, sum_Icc_e_eq, norm_mul, norm_e, one_mul]
  refine norm_sum_range_pow_le (norm_e θ) hD ?_ (fun h => hθ (isInt_of_e_eq_one h)) _
  obtain ⟨n, hn⟩ := hDθ
  rw [← e_natCast_mul, hn, e_intCast]

/-- The same bound for a sum restricted by an order-convex condition and twisted by a phase. -/
theorem norm_sum_ite_e_le {J : Finset ℤ} (hJ : IntConvex J) (P : ℤ → Prop) [DecidablePred P]
    (hP : ∀ x y z, P x → P y → x ≤ z → z ≤ y → P z) {θ : ℝ} (c : ℝ) {D : ℕ} (hD : 0 < D)
    (hDθ : IsInt (D * θ)) (hθ : ¬ IsInt θ) (g : ℤ → ℂ)
    (hg : ∀ v, g v = if P v then e (v * θ + c) else 0) : ‖∑ v ∈ J, g v‖ ≤ D := by
  simp_rw [hg]
  rw [← sum_filter]
  simp_rw [e_add]
  rw [← sum_mul, norm_mul, norm_e, mul_one]
  refine norm_sum_e_le_of_intConvex (fun x hx y hy z hxz hzy => ?_) hD hDθ hθ
  rw [mem_filter] at hx hy ⊢
  exact ⟨hJ x hx.1 y hy.1 z hxz hzy, hP x y z hx.2 hy.2 hxz hzy⟩

/-- Integer intervals are `IntConvex`. -/
theorem intConvex_Icc (m m' : ℤ) : IntConvex (Icc m m') := by
  intro x hx y hy z hxz hzy
  rw [mem_Icc] at hx hy ⊢
  exact ⟨hx.1.trans hxz, hzy.trans hy.2⟩

/-- Constraints `1 ≤ A_ω + c_ω v ≤ M` with `c_ω ≥ 0` define an order-convex set of `v`. -/
theorem affine_mem_Icc_convex (M : ℕ) (A c : Cube → ℤ) (hc : ∀ ω, 0 ≤ c ω) {x y z : ℤ}
    (hx : ∀ ω, A ω + c ω * x ∈ Icc (1 : ℤ) M) (hy : ∀ ω, A ω + c ω * y ∈ Icc (1 : ℤ) M)
    (hxz : x ≤ z) (hzy : z ≤ y) : ∀ ω, A ω + c ω * z ∈ Icc (1 : ℤ) M := by
  intro ω
  have h1 := hx ω
  have h2 := hy ω
  rw [mem_Icc] at h1 h2 ⊢
  have h3 := mul_le_mul_of_nonneg_left hxz (hc ω)
  have h4 := mul_le_mul_of_nonneg_left hzy (hc ω)
  constructor <;> linarith

/-- The cube indicator is order-convex in each of its four variables. -/
theorem cubeIn_convex_of_affine (M : ℕ) (f : ℤ → Cube → ℤ) (A c : Cube → ℤ)
    (hc : ∀ ω, 0 ≤ c ω) (hf : ∀ v ω, f v ω = A ω + c ω * v) :
    ∀ x y z, (∀ ω, f x ω ∈ Icc (1 : ℤ) M) → (∀ ω, f y ω ∈ Icc (1 : ℤ) M) → x ≤ z → z ≤ y →
      ∀ ω, f z ω ∈ Icc (1 : ℤ) M := by
  intro x y z hx hy hxz hzy
  simp_rw [hf] at hx hy ⊢
  exact affine_mem_Icc_convex M A c hc hx hy hxz hzy

/-- A fourfold box sum is bounded by `|J|³` times a bound for its innermost sums. -/
theorem norm_sum4_le (J : Finset ℤ) (G : ℤ → ℤ → ℤ → ℤ → ℂ) (D : ℝ)
    (h : ∀ x ∈ J, ∀ a ∈ J, ∀ b ∈ J, ‖∑ k ∈ J, G x a b k‖ ≤ D) :
    ‖∑ x ∈ J, ∑ a ∈ J, ∑ b ∈ J, ∑ k ∈ J, G x a b k‖ ≤ (J.card : ℝ) ^ 3 * D := by
  calc ‖∑ x ∈ J, ∑ a ∈ J, ∑ b ∈ J, ∑ k ∈ J, G x a b k‖ ≤ ∑ x ∈ J, ∑ a ∈ J, ∑ b ∈ J, D :=
        norm_sum_le_of_le _ fun x hx => norm_sum_le_of_le _ fun a ha =>
          norm_sum_le_of_le _ fun b hb => h x hx a ha b hb
    _ = (J.card : ℝ) ^ 3 * D := by
        simp only [sum_const, nsmul_eq_mul]
        ring

/-- **The off-diagonal bound** (Source: [F+] `expansion-non-diagonal`, L765–L770): if `D L_j ∈ ℤ`
for all `j` and some `L_j ∉ ℤ`, then `|W_M(L)| ≤ (2M + 1)³ D`. -/
theorem norm_cubeW_le (M : ℕ) {L0 L1 L2 L3 : ℝ} {D : ℕ} (hD : 0 < D) (h0 : IsInt (D * L0))
    (h1 : IsInt (D * L1)) (h2 : IsInt (D * L2)) (h3 : IsInt (D * L3))
    (hnd : ¬ (IsInt L0 ∧ IsInt L1 ∧ IsInt L2 ∧ IsInt L3)) :
    ‖cubeW M L0 L1 L2 L3‖ ≤ (2 * M + 1) ^ 3 * D := by
  set J : Finset ℤ := Icc (-(M : ℤ)) M with hJ
  have hJc : (J.card : ℝ) = 2 * M + 1 := by
    rw [hJ, Int.card_Icc]
    have : (M + 1 - -(M : ℤ)).toNat = 2 * M + 1 := by omega
    rw [this]
    push_cast
    ring
  have hJconv : IntConvex J := intConvex_Icc _ _
  set g : ℤ → ℤ → ℤ → ℤ → ℂ := fun x a b k =>
    if CubeIn M x a b k then e (x * L0 + a * L1 + b * L2 + k * L3) else 0 with hg
  have hW : cubeW M L0 L1 L2 L3 = ∑ x ∈ J, ∑ a ∈ J, ∑ b ∈ J, ∑ k ∈ J, g x a b k := rfl
  -- the four affine descriptions of the cube indicator
  have hk : ∀ x a b : ℤ, ∀ v ω, cubePt ω x a b v = cubePt ω x a b 0 + ((ω 2 : ℕ) : ℤ) * v := by
    intro x a b v ω; simp only [cubePt]; ring
  have hb : ∀ x a k : ℤ, ∀ v ω, cubePt ω x a v k = cubePt ω x a 0 k + ((ω 1 : ℕ) : ℤ) * v := by
    intro x a k v ω; simp only [cubePt]; ring
  have ha : ∀ x b k : ℤ, ∀ v ω, cubePt ω x v b k = cubePt ω x 0 b k + ((ω 0 : ℕ) : ℤ) * v := by
    intro x b k v ω; simp only [cubePt]; ring
  have hx : ∀ a b k : ℤ, ∀ v ω, cubePt ω v a b k = cubePt ω 0 a b k + 1 * v := by
    intro a b k v ω; simp only [cubePt]; ring
  rw [← hJc, hW]
  by_cases i3 : IsInt L3
  · by_cases i2 : IsInt L2
    · by_cases i1 : IsInt L1
      · have i0 : ¬ IsInt L0 := fun i0 => hnd ⟨i0, i1, i2, i3⟩
        -- sum over `x` innermost
        have hperm : ∑ x ∈ J, ∑ a ∈ J, ∑ b ∈ J, ∑ k ∈ J, g x a b k =
            ∑ a ∈ J, ∑ b ∈ J, ∑ k ∈ J, ∑ x ∈ J, g x a b k := by
          rw [sum_comm]
          refine sum_congr rfl fun a _ => ?_
          rw [sum_comm]
          refine sum_congr rfl fun b _ => ?_
          rw [sum_comm]
        rw [hperm]
        refine norm_sum4_le J (fun a b k x => g x a b k) D fun a _ b _ k _ =>
          norm_sum_ite_e_le hJconv (fun v => CubeIn M v a b k) ?_ (a * L1 + b * L2 + k * L3)
            hD h0 i0 _ fun v => ?_
        · exact cubeIn_convex_of_affine M (fun v ω => cubePt ω v a b k) _ (fun _ => 1)
            (fun _ => zero_le_one) (hx a b k)
        · simp only [hg]
          split_ifs
          · congr 1; ring
          · rfl
      · -- sum over `a` innermost
        have hperm : ∑ x ∈ J, ∑ a ∈ J, ∑ b ∈ J, ∑ k ∈ J, g x a b k =
            ∑ x ∈ J, ∑ b ∈ J, ∑ k ∈ J, ∑ a ∈ J, g x a b k := by
          refine sum_congr rfl fun x _ => ?_
          rw [sum_comm]
          refine sum_congr rfl fun b _ => ?_
          rw [sum_comm]
        rw [hperm]
        refine norm_sum4_le J (fun x b k a => g x a b k) D fun x _ b _ k _ =>
          norm_sum_ite_e_le hJconv (fun v => CubeIn M x v b k) ?_ (x * L0 + b * L2 + k * L3)
            hD h1 i1 _ fun v => ?_
        · exact cubeIn_convex_of_affine M (fun v ω => cubePt ω x v b k) _
            (fun ω => ((ω 0 : ℕ) : ℤ)) (fun _ => Nat.cast_nonneg _) (ha x b k)
        · simp only [hg]
          split_ifs
          · congr 1; ring
          · rfl
    · -- sum over `b` innermost
      have hperm : ∑ x ∈ J, ∑ a ∈ J, ∑ b ∈ J, ∑ k ∈ J, g x a b k =
          ∑ x ∈ J, ∑ a ∈ J, ∑ k ∈ J, ∑ b ∈ J, g x a b k := by
        refine sum_congr rfl fun x _ => sum_congr rfl fun a _ => ?_
        rw [sum_comm]
      rw [hperm]
      refine norm_sum4_le J (fun x a k b => g x a b k) D fun x _ a _ k _ =>
        norm_sum_ite_e_le hJconv (fun v => CubeIn M x a v k) ?_ (x * L0 + a * L1 + k * L3)
          hD h2 i2 _ fun v => ?_
      · exact cubeIn_convex_of_affine M (fun v ω => cubePt ω x a v k) _
          (fun ω => ((ω 1 : ℕ) : ℤ)) (fun _ => Nat.cast_nonneg _) (hb x a k)
      · simp only [hg]
        split_ifs
        · congr 1; ring
        · rfl
  · -- sum over `k` innermost
    refine norm_sum4_le J g D fun x _ a _ b _ =>
      norm_sum_ite_e_le hJconv (fun v => CubeIn M x a b v) ?_ (x * L0 + a * L1 + b * L2)
        hD h3 i3 _ fun v => ?_
    · exact cubeIn_convex_of_affine M (fun v ω => cubePt ω x a b v) _
        (fun ω => ((ω 2 : ℕ) : ℤ)) (fun _ => Nat.cast_nonneg _) (hk x a b)
    · simp only [hg]
      split_ifs
      · congr 1; ring
      · rfl

end PrimeCarleson.Proof.FplusProp21
