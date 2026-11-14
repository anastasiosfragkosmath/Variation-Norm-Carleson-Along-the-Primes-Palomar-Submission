/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Lattices/FourAffineRefinement.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.FourBalancedRelations
@[expose] public section

namespace OAI

section

namespace Erdos3

variable {R I E : Type*} {V : I → Type*} [CommRing R]
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
  [AddCommGroup E] [Module R E]

def fourFunctionDifference (f : (∀ i, V i) → E) (v : ∀ i, Fin 4 → V i) : E :=
  f (fun i => v i 0) + f (fun i => v i 1) - f (fun i => v i 2) - f (fun i => v i 3)

theorem four_affine_balanced_invariant (f : (∀ i, V i) → E) (C D : ∀ i, Submodule R (V i))
    (haffine : ∀ x : ∀ i, V i, (∀ i, x i ∈ C i) →
      ∃ A : (∀ i, D i) →ₗ[R] E, ∀ y : ∀ i, D i,
        f (fun i => x i + (y i : V i)) = f x + A y)
    (v z : ∀ i, Fin 4 → V i) (hv : ∀ i, v i ∈ fourCommonModulo (C i) (D i))
    (hz : ∀ i, z i ∈ fourBalancedDependent (D i)) :
    fourFunctionDifference f (fun i k => v i k + z i k) = fourFunctionDifference f v := by
  let x : ∀ i, V i := fun i => v i 0
  obtain ⟨A, hA⟩ := haffine x (fun i => ((mem_fourCommonModulo (C i) (D i) (v i)).mp (hv i)).1 0)
  let y (k : Fin 4) : ∀ i, D i := fun i =>
    ⟨v i k - v i 0, ((mem_fourCommonModulo (C i) (D i) (v i)).mp (hv i)).2 k⟩
  let t (k : Fin 4) : ∀ i, D i := fun i =>
    ⟨z i k, ((mem_fourBalancedDependent (D i) (z i)).mp (hz i)).1 k⟩
  have hbase (k : Fin 4) : f (fun i => v i k) = f x + A (y k) := by
    have heq : (fun i => x i + ((y k) i : V i)) = fun i => v i k := by
      funext i
      dsimp only [x, y]
      abel
    simpa only [heq] using hA (y k)
  have hnew (k : Fin 4) : f (fun i => v i k + z i k) = f x + (A (y k) + A (t k)) := by
    have heq : (fun i => x i + ((y k + t k) i : V i)) = fun i => v i k + z i k := by
      funext i
      change v i 0 + (v i k - v i 0 + z i k) = _
      abel
    simpa only [heq, map_add] using hA (y k + t k)
  have ht : t 0 + t 1 - t 2 - t 3 = 0 := by
    funext i
    apply Subtype.ext
    change z i 0 + z i 1 - z i 2 - z i 3 = 0
    exact ((mem_fourBalancedDependent (D i) (z i)).mp (hz i)).2
  have hAt : A (t 0) + A (t 1) - A (t 2) - A (t 3) = 0 := by
    rw [← map_add, ← map_sub, ← map_sub, ht, map_zero]
  calc
    _ = fourFunctionDifference f v + (A (t 0) + A (t 1) - A (t 2) - A (t 3)) := by
      unfold fourFunctionDifference
      rw [hnew 0, hnew 1, hnew 2, hnew 3, hbase 0, hbase 1, hbase 2, hbase 3]
      abel
    _ = _ := by rw [hAt, add_zero]

theorem four_refined_affine_identity (f : (∀ i, V i) → E) (C D : ∀ i, Submodule R (V i))
    (haffine : ∀ x : ∀ i, V i, (∀ i, x i ∈ C i) →
      ∃ A : (∀ i, D i) →ₗ[R] E, ∀ y : ∀ i, D i,
        f (fun i => x i + (y i : V i)) = f x + A y)
    (K : ∀ i, Submodule R (Fin 4 → V i))
    (hK : ∀ v : ∀ i, Fin 4 → V i, (∀ i, v i ∈ K i) → fourFunctionDifference f v = 0)
    (v : ∀ i, Fin 4 → V i) (hv : ∀ i, v i ∈ fourRefinedRelation (C i) (D i) (K i)) :
    fourFunctionDifference f v = 0 := by
  classical
  have hdecomp (i : I) : ∃ u ∈ K i ⊓ fourCommonModulo (C i) (D i),
      ∃ z ∈ fourBalancedDependent (D i), u + z = v i := Submodule.mem_sup.mp (hv i)
  choose u hu z hz heq using hdecomp
  have hvEq : (fun i k => u i k + z i k) = v := by
    funext i k
    exact congrFun (heq i) k
  rw [← hvEq, four_affine_balanced_invariant f C D haffine u z (fun i => (hu i).2) hz]
  exact hK u (fun i => (hu i).1)

end Erdos3

end

end OAI
