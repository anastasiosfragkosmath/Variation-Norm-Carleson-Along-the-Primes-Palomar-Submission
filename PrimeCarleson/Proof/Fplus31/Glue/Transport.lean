module

public import PrimeCarleson.Proof.Fplus31.G1.Start
public import PrimeCarleson.Proof.Paper.Defs.Gowers

/-!
# The transport of the Gowers norm: `finiteSupportGowersNorm` versus `gowersNormInterval`

Part of the final assembly of [F+] Proposition 3.1 (`Glue/Assembly.lean`). The quantitative `U³`
inverse theorem of the vendored `OAI.Combinatorics.Progressions` is stated for the normalised norm
`finiteSupportGowersNorm j Q f` of a function on a finite set `Q ⊆ Unit → ℤ` (the sum over the cubes
`x + ω · h` inside `Q`, divided by their number, to the power `1 / 2^j`), the paper and the
statements for `gowersNormInterval s N g` (`‖g 1_{[N]}‖_{U^s(ℤ)} / ‖1_{[N]}‖_{U^s(ℤ)}`, with `ℤ` in
place of `Unit → ℤ`). For `Q = intervalPoints N` (`G1/Start.lean`, the encoding of `{1, …, N}`) the
two coincide exactly:

* `tsum_multDiff_restrictInterval`: the Gowers sum `∑_{x, h} Δ_h (g 1_{[N]})(x)` of the
  `gowersNorm` equals the cube sum `supportedCubeSum s (intervalPoints N)` of the vendored norm
  (`cubeToPair` is the bijection between the cubes inside `{1, …, N}` and the pairs `(x, h)` with
  a nonzero term; `mixedCubeProduct_unit`: the cube product of the encoding is the product of
  `gowersTerm`; `cubeVertexEquiv`: the vertices `Bool` versus `Fin 2`);
* `finiteSupportGowersNorm_intervalPoints`: for every `s` and every `g : ℤ → ℂ`,
  `finiteSupportGowersNorm s (intervalPoints N) (g ∘ ev) = gowersNormInterval s N g`, with no
  constant: the number of cubes is `‖1_{[N]}‖_{U^s(ℤ)}^{2^s}`, and `g 1_{[N]}` is the extension
  by zero of the restriction of `g` to the interval (`ev x = x ()`);
* `finiteSupportGowersNorm_three_intervalPoints` (`s = 3`, with `g ∘ ev`) and
  `interval_start_hypotheses`: the hypotheses of `exists_leng_start_interval` (`G1/Start.lean`)
  from a lower bound `e^{-p} ≤ ‖g‖_{U³[N]}` of the norm and `‖g‖ ≤ 1` on `[1, N]`.

The identity holds for every `g : ℤ → ℂ` (both sides only see `g` on `{1, …, N}`).
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open PrimeCarleson

/-- The identification of the vertices of the cube `{0,1}^s`, `Bool` against `Fin 2`. -/
def cubeVertexEquiv (s : ℕ) : (Fin s → Bool) ≃ (Fin s → Fin 2) :=
  Equiv.piCongrRight fun _ => finTwoEquiv.symm

/-- The coordinates of the vertex `cubeVertexEquiv s ω`: `1` where `ω` is true, `0` elsewhere. -/
theorem cubeVertexEquiv_apply_val {s : ℕ} (ω : Fin s → Bool) (i : Fin s) :
    ((cubeVertexEquiv s ω i : Fin 2) : ℕ) = if ω i then 1 else 0 := by
  have key : ∀ b : Bool, ((finTwoEquiv.symm b : Fin 2) : ℕ) = if b then 1 else 0 := by
    intro b
    cases b <;> rfl
  exact key (ω i)

/-- The weight of a vertex: `Common.vertexWeight` against the vendored `booleanWeight`. -/
theorem vertexWeight_cubeVertexEquiv {s : ℕ} (ω : Fin s → Bool) :
    Common.vertexWeight (cubeVertexEquiv s ω) = OAI.Erdos3.booleanWeight ω := by
  simp [Common.vertexWeight, OAI.Erdos3.booleanWeight, cubeVertexEquiv_apply_val]

/-- The point `w · h` of a vertex `w = cubeVertexEquiv s ω`: the sum of the `h i` with `ω i`. -/
theorem cubePoint_cubeVertexEquiv {s : ℕ} (h : Fin s → ℤ) (ω : Fin s → Bool) :
    Common.cubePoint (cubeVertexEquiv s ω) h = ∑ i, if ω i then h i else 0 := by
  simp only [Common.cubePoint, cubeVertexEquiv_apply_val]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : ω i <;> simp [hi]

/-- The vendored `cubeShift` of steps `fun i _ => h i` in `Unit → ℤ`, evaluated at the point. -/
theorem cubeShift_unit_apply {s : ℕ} (h : Fin s → ℤ) (ω : Fin s → Bool) (u : Unit) :
    OAI.Erdos3.cubeShift (fun i (_ : Unit) => h i) ω u = ∑ i, if ω i then h i else 0 := by
  simp only [OAI.Erdos3.cubeShift, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : ω i <;> simp [hi]

/-- The vendored conjugation power is the `n`-fold complex conjugate `Common.gowersConjPow`. -/
theorem conjugationPower_eq (n : ℕ) (z : ℂ) :
    OAI.Erdos3.conjugationPower n z = Common.gowersConjPow n z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Common.gowersConjPow_succ, ← ih]
    rfl

/-- The cube product of the vendored norm at `(fun _ => x, fun i _ => h i)` is the product over
the vertices of `Fin 2`-cube of the side (`Common.gowersTerm`). -/
theorem mixedCubeProduct_unit {s : ℕ} (G : (Unit → ℤ) → ℂ) (h : Fin s → ℤ) (x : ℤ) :
    OAI.Erdos3.mixedCubeProduct (fun _ => G) (fun i (_ : Unit) => h i) (fun _ => x) =
      ∏ w : Fin s → Fin 2, Common.gowersConjPow (Common.vertexWeight w)
        (G (fun _ => x + Common.cubePoint w h)) := by
  unfold OAI.Erdos3.mixedCubeProduct
  refine Fintype.prod_equiv (cubeVertexEquiv s) _ _ fun ω => ?_
  have hpt : (fun _ : Unit => x) + OAI.Erdos3.cubeShift (fun i (_ : Unit) => h i) ω =
      fun _ => x + Common.cubePoint (cubeVertexEquiv s ω) h := by
    funext u
    rw [Pi.add_apply, cubeShift_unit_apply, cubePoint_cubeVertexEquiv]
  rw [conjugationPower_eq, vertexWeight_cubeVertexEquiv, hpt]

/-- The pair `(x, h) ∈ ℤ × ℤ^s` of base point and steps of a cube in `Unit → ℤ`. -/
def cubeToPair {s : ℕ} {Q : Set (Unit → ℤ)} (c : OAI.Erdos3.SupportedCube s Q) :
    ℤ × (Fin s → ℤ) :=
  (c.val.2 (), fun i => c.val.1 i ())

/-- `cubeToPair` is injective: a point of `Unit → ℤ` is determined by its value at `()`. -/
theorem cubeToPair_injective (s : ℕ) (Q : Set (Unit → ℤ)) :
    Function.Injective (cubeToPair (s := s) (Q := Q)) := by
  intro c d hcd
  have h1 : c.val.2 () = d.val.2 () := congrArg Prod.fst hcd
  have h2 : ∀ i, c.val.1 i () = d.val.1 i () := fun i => congrFun (congrArg Prod.snd hcd) i
  apply Subtype.ext
  refine Prod.ext (funext fun i => funext fun u => ?_) (funext fun u => ?_)
  · exact h2 i
  · exact h1

/-- The `restrictInterval N g` is `g` on `[1, N]` and `0` elsewhere. -/
theorem restrictInterval_apply (N : ℕ+) (g : ℤ → ℂ) (y : ℤ) :
    restrictInterval N g y = if y ∈ Finset.Icc (1 : ℤ) N then g y else 0 :=
  Paper.restrictFinset_apply (Finset.Icc (1 : ℤ) N) g y

/-- A point where `restrictInterval N g` is nonzero lies in `[1, N]`. -/
theorem mem_Icc_of_restrictInterval_ne_zero {N : ℕ+} {g : ℤ → ℂ} {y : ℤ}
    (h : restrictInterval N g y ≠ 0) : y ∈ Finset.Icc (1 : ℤ) N := by
  by_contra hy
  simp [restrictInterval_apply, hy] at h

/-- **The Gowers sum of the interval is the cube sum of the encoding.**  The sum
`∑_{x, h₁, …, h_s} Δ_{h₁,…,h_s} (g 1_{[N]})(x)` over `ℤ × ℤ^s` defining the `gowersNorm`
equals the vendored `supportedCubeSum s (intervalPoints N)` of the function `x ↦ g (x ())`. -/
theorem tsum_multDiff_restrictInterval (s : ℕ) (N : ℕ+) (g : ℤ → ℂ) :
    ∑' p : ℤ × (Fin s → ℤ), multDiff s p.2 (restrictInterval N g) p.1 =
      OAI.Erdos3.supportedCubeSum s ((intervalPoints N : Finset (Unit → ℤ)) : Set (Unit → ℤ))
        (fun _ => fun x => g (x ())) := by
  classical
  set Q : Finset (Unit → ℤ) := intervalPoints N with hQ
  set F : ℤ →₀ ℂ := restrictInterval N g with hF
  have hterm : ∀ (x : ℤ) (h : Fin s → ℤ), multDiff s h F x =
      ∏ w : Fin s → Fin 2, Common.gowersConjPow (Common.vertexWeight w)
        (F (x + Common.cubePoint w h)) := fun x h =>
    (Common.gowersTerm_const s F x h).symm
  have hsupp : Function.support (fun p : ℤ × (Fin s → ℤ) => multDiff s p.2 F p.1) ⊆
      Set.range (cubeToPair (s := s) (Q := (Q : Set (Unit → ℤ)))) := by
    rintro ⟨x, h⟩ hne
    have hne' : multDiff s h F x ≠ 0 := hne
    rw [hterm, Finset.prod_ne_zero_iff] at hne'
    have hmem : ∀ ω : Fin s → Bool,
        (fun _ : Unit => x) + OAI.Erdos3.cubeShift (fun i (_ : Unit) => h i) ω ∈ Q := by
      intro ω
      have h1 := hne' (cubeVertexEquiv s ω) (Finset.mem_univ _)
      have h2 : F (x + Common.cubePoint (cubeVertexEquiv s ω) h) ≠ 0 := fun h0 =>
        h1 (by rw [h0]; exact Common.gowersConjPow_zero_right _)
      have h3 := mem_Icc_of_restrictInterval_ne_zero h2
      rw [Finset.mem_Icc] at h3
      rw [hQ, mem_intervalPoints, Pi.add_apply, cubeShift_unit_apply]
      rw [cubePoint_cubeVertexEquiv] at h3
      exact h3
    exact ⟨⟨((fun i (_ : Unit) => h i), fun _ => x), hmem⟩, rfl⟩
  rw [← (cubeToPair_injective s (Q : Set (Unit → ℤ))).tsum_eq hsupp, tsum_fintype]
  unfold OAI.Erdos3.supportedCubeSum
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨⟨hs, x₀⟩, hc⟩ := c
  obtain ⟨x, rfl⟩ : ∃ x : ℤ, x₀ = fun _ => x := ⟨x₀ (), rfl⟩
  obtain ⟨h, rfl⟩ : ∃ h : Fin s → ℤ, hs = fun i _ => h i := ⟨fun i => hs i (), rfl⟩
  simp only [cubeToPair]
  rw [hterm, mixedCubeProduct_unit]
  refine Finset.prod_congr rfl fun w _ => ?_
  congr 1
  have h1 := hc ((cubeVertexEquiv s).symm w)
  rw [Finset.mem_coe, hQ, mem_intervalPoints, Pi.add_apply, cubeShift_unit_apply,
    ← cubePoint_cubeVertexEquiv, Equiv.apply_symm_apply] at h1
  have h2 : x + Common.cubePoint w h ∈ Finset.Icc (1 : ℤ) N := Finset.mem_Icc.2 h1
  change F (x + Common.cubePoint w h) = g (x + Common.cubePoint w h)
  rw [hF, restrictInterval_apply]
  simp [h2]

/-- **Transport of the Gowers norm to the interval norm** (all `s`): for `N` a positive
integer and every `g : ℤ → ℂ`, the vendored `finiteSupportGowersNorm s` of `x ↦ g (x ())` on the
encoding `intervalPoints N` of `{1, …, N}` is the `gowersNormInterval s N g`, exactly. -/
theorem finiteSupportGowersNorm_intervalPoints (s N : ℕ+) (g : ℤ → ℂ) :
    OAI.Erdos3.finiteSupportGowersNorm (s : ℕ) (intervalPoints N) (fun x => g (x ())) =
      gowersNormInterval s N g := by
  have hf := tsum_multDiff_restrictInterval (s : ℕ) N g
  have h1 := tsum_multDiff_restrictInterval (s : ℕ) N 1
  have hnum : (OAI.Erdos3.supportedCubeSum (s : ℕ)
      ((intervalPoints N : Finset (Unit → ℤ)) : Set (Unit → ℤ))
      (fun _ => fun x => g (x ()))).re = gowersNorm s (restrictInterval N g) ^ 2 ^ (s : ℕ) := by
    rw [← hf, Paper.gowersNorm_pow_eq_re_tsum]
  have hcard : (Nat.card (OAI.Erdos3.SupportedCube (s : ℕ)
      ((intervalPoints N : Finset (Unit → ℤ)) : Set (Unit → ℤ))) : ℝ) =
      gowersNorm s (restrictInterval N 1) ^ 2 ^ (s : ℕ) := by
    rw [Paper.gowersNorm_pow_eq_re_tsum, h1]
    have h2 := OAI.Erdos3.supportedCubeSum_one (s : ℕ) (intervalPoints N)
    rw [show (fun (_ : Fin (s : ℕ) → Bool) (x : Unit → ℤ) => (1 : ℤ → ℂ) (x ())) =
      fun _ _ => 1 from rfl, h2]
    simp
  unfold OAI.Erdos3.finiteSupportGowersNorm gowersNormInterval
  rw [hnum, hcard, ← div_pow]
  exact Real.pow_rpow_inv_natCast (div_nonneg (Paper.gowersNorm_nonneg _ _)
    (Paper.gowersNorm_nonneg _ _)) (pow_ne_zero _ (by norm_num))

/-- **Transport, `s = 3`**: `finiteSupportGowersNorm 3 (intervalPoints N) (x ↦ g (x ()))` is the
`gowersNormInterval 3 N g`. -/
theorem finiteSupportGowersNorm_three_intervalPoints (N : ℕ+) (g : ℤ → ℂ) :
    OAI.Erdos3.finiteSupportGowersNorm 3 (intervalPoints N) (fun x => g (x ())) =
      gowersNormInterval 3 N g :=
  finiteSupportGowersNorm_intervalPoints 3 N g

/-- **The hypotheses of `exists_leng_start_interval` from the norm.**  A function
`g : ℤ → ℂ` with `‖g‖ ≤ 1` on `[1, N]` and `e^{-p} ≤ ‖g‖_{U³[N]}` (the
`gowersNormInterval`) satisfies the hypotheses `‖f x‖ ≤ 1` on `intervalPoints N` and
`e^{-p} ≤ finiteSupportGowersNorm 3 (intervalPoints N) f` for `f x = g (x ())`. -/
theorem interval_start_hypotheses {N : ℕ+} {p : ℝ} {g : ℤ → ℂ}
    (hg : ∀ n ∈ Finset.Icc (1 : ℤ) N, ‖g n‖ ≤ 1)
    (h : Real.exp (-p) ≤ gowersNormInterval 3 N g) :
    (∀ x ∈ intervalPoints N, ‖g (x ())‖ ≤ 1) ∧
      Real.exp (-p) ≤
        OAI.Erdos3.finiteSupportGowersNorm 3 (intervalPoints N) (fun x => g (x ())) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := mem_intervalPoints.mp hx
    exact hg (x ()) (Finset.mem_Icc.2 ⟨h1, h2⟩)
  · rw [finiteSupportGowersNorm_three_intervalPoints]
    exact h

end PrimeCarleson.Proof.Fplus31
