/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.HankelBoundedMaps

/-! Equality of the bounded frame image with the truncated Hankel relation space. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K] {b c : ℕ}

set_option maxHeartbeats 800000 in
theorem hankelFrameBoundedMap_range_eq (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → K)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) K)
    (hBH : B*blockHankel h g a=1) (hHB : blockHankel h g a*B=1)
    (hh : ∀ j, 0<h j) (hg : ∀ i, 0<g i) (hsum : ∑ i, g i=∑ j, h j) (d : ℕ) :
    LinearMap.range (hankelFrameBoundedMap h g a B d) =
      LinearMap.ker (hankelObstructionMap h g a d) := by
  apply Submodule.eq_of_le_of_finrank_eq (hankelFrameBoundedMap_range_le h g a B hHB d)
  have hi := (hankelFrameBoundedMap h g a B d).finrank_range_add_finrank_ker
  rw [hankelFrameBoundedMap_ker,hankelFrame_kernel_hilbert h g a B hBH hHB hh hg] at hi
  have ho := (hankelObstructionMap h g a d).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (hankelObstructionMap_surjective h g a B hHB hg d),
    finrank_top] at ho
  have hdom : Module.finrank K ((Fin c ⊕ Fin b) → BoundedPoly K d)=(c+b)*(d+1) := by
    simp [Module.finrank_pi_fintype,Fintype.sum_sum_type]
  have hout : Module.finrank K (HankelOutput (K := K) g d)=(∑ i, g i)+c*(d+1) := by
    simp [HankelOutput,Module.finrank_pi_fintype,Finset.sum_add_distrib]
    ring
  have hobs : Module.finrank K (HankelObstruction (K := K) h d)=∑ j, (h j-(d+1)) := by
    simp [HankelObstruction,Module.finrank_pi_fintype,Fintype.card_sigma]
  rw [hdom] at hi
  rw [hout,hobs,hsum] at ho
  have har : (∑ j, (d+1-h j))+(∑ j, h j)=(∑ j, (h j-(d+1)))+b*(d+1) := by
    have ht (j : Fin b) : (d+1-h j)+h j=(h j-(d+1))+(d+1) := by omega
    have he := Finset.sum_congr (show (Finset.univ : Finset (Fin b))=Finset.univ from rfl) (fun j _ => ht j)
    simpa [Finset.sum_add_distrib,Nat.mul_add] using he
  rw [Nat.add_mul] at hi
  omega

theorem hankelFrame_bounded_lift_iff (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → K)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) K)
    (hBH : B*blockHankel h g a=1) (hHB : blockHankel h g a*B=1)
    (hh : ∀ j, 0<h j) (hg : ∀ i, 0<g i) (hsum : ∑ i, g i=∑ j, h j)
    (d : ℕ) (p : Fin c → K[X]) (hp : ∀ i, (p i).natDegree≤g i+d) :
    (∃ x : Fin c ⊕ Fin b → K[X], (∀ w, (x w).natDegree≤d) ∧ hankelFrame h g a B *ᵥ x=p) ↔
      ∀ j r, r+d+1<h j → fullHankelAction a p j r=0 := by
  constructor
  · rintro ⟨x,hx,rfl⟩ j r hr
    exact hankelFrame_bounded_image_relations h g a B hHB d x hx j r hr
  · intro hz
    let p' : HankelOutput (K := K) g d := fun i => boundedPolyOf (p i) (hp i)
    have hm : p' ∈ LinearMap.ker (hankelObstructionMap h g a d) := by
      funext jr
      exact hz jr.1 jr.2.val (by have := jr.2.isLt; omega)
    rw [← hankelFrameBoundedMap_range_eq h g a B hBH hHB hh hg hsum d] at hm
    obtain ⟨x,hx⟩ := hm
    refine ⟨fun w => (x w).val,fun w => boundedPoly_degree d (x w),?_⟩
    funext i
    exact congrArg Subtype.val (congrFun hx i)

theorem hankelFrame_right_inverse (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → K)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) K)
    (hBH : B*blockHankel h g a=1) (hHB : blockHankel h g a*B=1)
    (hh : ∀ j, 0<h j) (hg : ∀ i, 0<g i) (hsum : ∑ i, g i=∑ j, h j) :
    ∃ Q : Matrix (Fin c ⊕ Fin b) (Fin c) K[X], hankelFrame h g a B * Q=1 := by
  have hl (i : Fin c) : ∃ x : Fin c ⊕ Fin b → K[X],
      hankelFrame h g a B *ᵥ x=Pi.single i 1 := by
    have hp (k : Fin c) : ((Pi.single i 1 : Fin c → K[X]) k).natDegree≤g k+(∑ j, h j) := by
      by_cases hk : k=i <;> simp [Pi.single_apply,hk]
    obtain ⟨x,_,hx⟩ := (hankelFrame_bounded_lift_iff h g a B hBH hHB hh hg hsum
      (∑ j, h j) (Pi.single i 1) hp).mpr (by
        intro j r hr
        have he : h j≤∑ k, h k := Finset.single_le_sum (fun k _ => Nat.zero_le _) (Finset.mem_univ j)
        omega)
    exact ⟨x,hx⟩
  choose x hx using hl
  refine ⟨fun w i => x i w,?_⟩
  funext i j
  have he := congrFun (hx j) i
  simpa [Matrix.mul_apply,Matrix.mulVec,dotProduct,Matrix.one_apply,Pi.single_apply] using he

theorem hankelFrame_transpose_injective (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → K)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) K)
    (hBH : B*blockHankel h g a=1) (hHB : blockHankel h g a*B=1)
    (hh : ∀ j, 0<h j) (hg : ∀ i, 0<g i) (hsum : ∑ i, g i=∑ j, h j) :
    Function.Injective (hankelFrame h g a B).transpose.mulVec := by
  obtain ⟨Q,hQ⟩ := hankelFrame_right_inverse h g a B hBH hHB hh hg hsum
  have he : Q.transpose*(hankelFrame h g a B).transpose=1 := by
    rw [← Matrix.transpose_mul,hQ,Matrix.transpose_one]
  intro x y hxy
  have hz := congrArg (fun z => Q.transpose *ᵥ z) hxy
  simpa only [Matrix.mulVec_mulVec,he,Matrix.one_mulVec] using hz

end FD56
