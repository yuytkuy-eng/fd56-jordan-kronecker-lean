/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.ReducedFactorDegrees
import FD56.Hilbert.KernelDimension

/-! Two bounded tangent-kernel tests force balance of a reduced factor.
Only containment in the tangent kernel is needed. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

theorem polynomial_kernel_hilbert_lower_of_injective_frame
    {K a b r : Type*} [Field K] [Fintype b] [Fintype r]
    (A : Matrix a b K[X]) (Z : Matrix b r K[X]) (f : r → ℕ)
    (hAZ : A*Z=0) (hZ : ∀ i j, (Z i j).natDegree≤f j)
    (hinj : Function.Injective Z.mulVec) (d : ℕ) :
    (∑ j, (d+1-f j))≤Module.finrank K (polynomialKernelAtDegree A d) := by
  classical
  have hi : Function.Injective (kernelFromCoordinates A Z f d hAZ hZ) := by
    intro c c' h
    have hz : Z*ᵥ(fun j => (c j).val)=Z*ᵥ(fun j => (c' j).val) :=
      congrArg (fun Y : polynomialKernelAtDegree A d => fun i => (Y.val i).val) h
    have hc := hinj hz
    funext j
    exact Subtype.ext (congrFun hc j)
  letI (j : r) : Module.Finite K (Polynomial.degreeLT K (d+1-f j)) :=
    Module.Finite.of_injective (Polynomial.degreeLTEquiv K (d+1-f j)).toLinearMap
      (Polynomial.degreeLTEquiv K (d+1-f j)).injective
  have hh := LinearMap.finrank_le_finrank_of_injective hi
  have hd : Module.finrank K (∀j,Polynomial.degreeLT K (d+1-f j))=∑j,(d+1-f j) := by
    rw [Module.finrank_pi_fintype]
    apply Finset.sum_congr rfl
    intro j _
    rw [(Polynomial.degreeLTEquiv K (d+1-f j)).finrank_eq]
    simp
  rwa [hd] at hh

theorem reduced_factor_balanced_of_two_kernel_tests
    {K n r s t : Type*} [Field K] [Fintype r] [Fintype s]
    (V : Matrix n r K[X]) (C : Matrix r s K[X]) (e : r → ℕ) (D k b : ℕ)
    (hV : ∀ i j, (V i j).natDegree≤e j)
    (hlead : Function.Injective (Matrix.mulVec (fun i j => (V i j).coeff (e j))))
    (hC : Function.Injective C.transpose.mulVec) (hVC : DegreeBound (V*C) D)
    (A : Matrix t s K[X]) (hAC : A*C.transpose=0)
    (hk : 0<k) (hb : b<Fintype.card r)
    (hsum : (∑ i,e i)+(Fintype.card r*k+b)=Fintype.card r*D)
    (hzero : Module.finrank K (polynomialKernelAtDegree A (k-1))=0)
    (hcritical : Module.finrank K (polynomialKernelAtDegree A k)≤Fintype.card r-b) :
    ∀ i j, e i≤e j+1 := by
  classical
  obtain ⟨he,hdegree⟩ := reduced_factor_degree_bounds V C e D hV hlead hC hVC
  let f : r → ℕ := fun i => D-e i
  have hbound (d : ℕ) : (∑ i,(d+1-f i))≤Module.finrank K (polynomialKernelAtDegree A d) :=
    polynomial_kernel_hilbert_lower_of_injective_frame A C.transpose f hAC
      (fun i j => hdegree j i) hC d
  have hfSum : (∑ i,f i)=Fintype.card r*k+b := by
    change (∑ i,(D-e i))=_
    rw [Finset.sum_tsub_distrib _ (fun i _ => he i)]
    simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
    omega
  have hfLower (i : r) : k≤f i := by
    have hz := hbound (k-1)
    rw [hzero,show k-1+1=k by omega] at hz
    have hzi : k-f i=0 := (Finset.sum_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hz)) i (Finset.mem_univ i)
    omega
  have hc : (∑ i,(k+1-f i))≤Fintype.card r-b := (hbound k).trans hcritical
  have hp (i : r) (_ : i∈Finset.univ) : k+1≤f i+(k+1-f i) := by omega
  have hs : (∑ _i : r,(k+1))=∑ i,(f i+(k+1-f i)) := by
    apply le_antisymm (Finset.sum_le_sum hp)
    rw [Finset.sum_add_distrib,hfSum]
    simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
    have hr : Fintype.card r-b+b=Fintype.card r := by omega
    nlinarith
  have hpoint := (Finset.sum_eq_sum_iff_of_le hp).mp hs
  have hfUpper (i : r) : f i≤k+1 := by
    have hi := hpoint i (Finset.mem_univ i)
    omega
  intro i j
  have hi := hfLower i
  have hj := hfUpper j
  have hei := he i
  have hej := he j
  dsimp [f] at hi hj
  omega

end FD56
