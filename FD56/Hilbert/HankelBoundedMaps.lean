/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.HankelFrameMinimal
import FD56.LinearAlgebra.HankelAction

/-! The finite-dimensional image and obstruction maps for a Hankel frame. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K] {b c : ℕ}

abbrev HankelOutput (g : Fin c → ℕ) (d : ℕ) := ∀ i, BoundedPoly K (g i+d)
abbrev HankelObstruction (h : Fin b → ℕ) (d : ℕ) := (Σ j, Fin (h j-(d+1))) → K

def hankelObstructionMap (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → K) (d : ℕ) :
    HankelOutput (K := K) g d →ₗ[K] HankelObstruction (K := K) h d where
  toFun p jr := fullHankelAction a (fun i => (p i).val) jr.1 jr.2.val
  map_add' p q := by
    funext jr
    simp [fullHankelAction,map_add,Finset.sum_add_distrib]
  map_smul' x p := by
    funext jr
    simp [fullHankelAction,map_smul,Finset.smul_sum,Finset.mul_sum]

def hankelFrameBoundedMap (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → K)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) K) (d : ℕ) :
    ((Fin c ⊕ Fin b) → BoundedPoly K d) →ₗ[K] HankelOutput (K := K) g d where
  toFun x i := boundedPolyOf _
    (hankelFrame_bounded_image_degree h g a B d (fun w => (x w).val)
      (fun w => boundedPoly_degree d (x w)) i)
  map_add' x y := by
    funext i
    apply Subtype.ext
    exact congrFun (Matrix.mulVec_add (hankelFrame h g a B)
      (fun w => (x w).val) (fun w => (y w).val)) i
  map_smul' t x := by
    funext i
    apply Subtype.ext
    exact congrFun (Matrix.mulVec_smul (hankelFrame h g a B) t (fun w => (x w).val)) i

theorem hankelFrameBoundedMap_ker (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → K)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) K) (d : ℕ) :
    LinearMap.ker (hankelFrameBoundedMap h g a B d) =
      polynomialKernelAtDegree (hankelFrame h g a B) d := by
  ext x
  change (hankelFrameBoundedMap h g a B d x=0) ↔ _
  constructor
  · intro hx
    funext i
    exact congrArg Subtype.val (congrFun hx i)
  · intro hx
    funext i
    apply Subtype.ext
    exact congrFun hx i

theorem hankelFrameBoundedMap_range_le (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → K)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) K)
    (hHB : blockHankel h g a*B=1) (d : ℕ) :
    LinearMap.range (hankelFrameBoundedMap h g a B d) ≤
      LinearMap.ker (hankelObstructionMap h g a d) := by
  rintro _ ⟨x,rfl⟩
  funext jr
  exact hankelFrame_bounded_image_relations h g a B hHB d (fun w => (x w).val)
    (fun w => boundedPoly_degree d (x w)) jr.1 jr.2.val (by have := jr.2.isLt; omega)

theorem hankelObstructionMap_surjective (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → K)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) K)
    (hHB : blockHankel h g a*B=1) (hg : ∀ i, 0<g i) (d : ℕ) :
    Function.Surjective (hankelObstructionMap h g a d) := by
  intro x
  let y : (Σ j, Fin (h j)) → K := fun jr =>
    if hr : jr.2.val<h jr.1-(d+1) then x ⟨jr.1,⟨jr.2.val,hr⟩⟩ else 0
  let q := hankelCoefficientPolynomial g (B *ᵥ y)
  have hq (i : Fin c) : (q i).natDegree<g i := by
    have he : (q i).natDegree≤g i-1 := by
      apply natDegree_sum_le_of_forall_le
      intro s _
      exact (natDegree_monomial_le _).trans (by have := s.isLt; omega)
    have := hg i
    omega
  let p : HankelOutput (K := K) g d := fun i => boundedPolyOf (q i) (by have := hq i; omega)
  refine ⟨p,?_⟩
  funext jr
  change fullHankelAction a q jr.1 jr.2.val=x jr
  rw [fullHankelAction_truncated g a q hq]
  have hr : jr.2.val<h jr.1 := by have := jr.2.isLt; omega
  change polynomialHankelAction g a (hankelCoefficientPolynomial g (B *ᵥ y)) jr.1 jr.2.val= _
  rw [hankelCoefficientPolynomial_action h g a (B *ᵥ y) jr.1 ⟨jr.2.val,hr⟩,
    Matrix.mulVec_mulVec,hHB,Matrix.one_mulVec]
  simp only [y,dif_pos jr.2.isLt]

end FD56
