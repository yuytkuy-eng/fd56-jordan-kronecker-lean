/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.KernelCoefficientIsotropy

/-! A finite endpoint matrix excludes bounded polynomial kernel chains.
The compression uses a generalized inverse of the constant coefficient. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
variable {K n r : Type*} [Field K] [Fintype n] [DecidableEq n] [Fintype r]

def affineEndpointMatrix (B T : Matrix n n K) (N : Matrix n r K) (d : ℕ) :
    Matrix n (Fin (d+1) × r) K :=
  fun i kj => (B*T^(d-kj.1.val)*N) i kj.2

private theorem mulVec_fintype_sum {ι : Type*} [Fintype ι]
    (A : Matrix n n K) (v : ι → n → K) :
    A *ᵥ (∑ i, v i)=∑ i, A *ᵥ v i :=
  map_sum (Matrix.toLin' A) v Finset.univ

private theorem recurrence_closed_form
    (T : Matrix n n K) (N : Matrix n r K)
    (v : ℕ → n → K) (u : ℕ → r → K)
    (h0 : v 0=N *ᵥ u 0)
    (hs : ∀ k, v (k+1)=T *ᵥ v k+N *ᵥ u (k+1)) (d : ℕ) :
    v d=∑ k : Fin (d+1), (T^(d-k.val)*N) *ᵥ u k.val := by
  induction d with
  | zero => simpa using h0
  | succ d ih =>
    rw [hs,ih,mulVec_fintype_sum]
    conv_rhs => rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_last,Nat.sub_self,pow_zero,Matrix.one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    have hk : d+1-k.val=(d-k.val)+1 := by have := k.isLt; omega
    change T *ᵥ ((T^(d-k.val)*N) *ᵥ u k.val)=(T^(d+1-k.val)*N) *ᵥ u k.val
    rw [hk,pow_succ',Matrix.mul_assoc,Matrix.mulVec_mulVec]

theorem affine_coefficient_chain_zero_of_endpoint_injective
    (A B L : Matrix n n K) (N : Matrix n r K) (F : Matrix r n K)
    (hLA : L*A+N*F=1) (d : ℕ)
    (hend : Function.Injective (affineEndpointMatrix B (-(L*B)) N d).mulVec)
    (v : ℕ → n → K) (h0 : A *ᵥ v 0=0)
    (hs : ∀ k, A *ᵥ v (k+1)+B *ᵥ v k=0) (hd : B *ᵥ v d=0) :
    ∀ k, k≤d → v k=0 := by
  classical
  let T := -(L*B)
  let u : ℕ → r → K := fun k => F *ᵥ v k
  have hid (k : ℕ) : L *ᵥ (A *ᵥ v k)+N *ᵥ u k=v k := by
    simpa only [Matrix.add_mulVec,Matrix.mulVec_mulVec,Matrix.one_mulVec,u] using
      congrArg (fun H : Matrix n n K => H *ᵥ v k) hLA
  have hv0 : v 0=N *ᵥ u 0 := by
    simpa only [h0,Matrix.mulVec_zero,zero_add] using (hid 0).symm
  have hvs (k : ℕ) : v (k+1)=T *ᵥ v k+N *ᵥ u (k+1) := by
    have h := congrArg (fun w => L *ᵥ w) (hs k)
    simp only [Matrix.mulVec_add,Matrix.mulVec_zero] at h
    have he : L *ᵥ (A *ᵥ v (k+1))=-(L *ᵥ (B *ᵥ v k)) :=
      eq_neg_of_add_eq_zero_left h
    rw [← hid (k+1),he]
    simp only [T,Matrix.neg_mulVec,Matrix.mulVec_mulVec]
  have hclosed := recurrence_closed_form T N v u hv0 hvs
  let z : Fin (d+1) × r → K := fun kj => u kj.1.val kj.2
  have hz : affineEndpointMatrix B T N d *ᵥ z=0 := by
    calc
      affineEndpointMatrix B T N d *ᵥ z=
          ∑ k : Fin (d+1), (B*T^(d-k.val)*N) *ᵥ u k.val := by
        funext i
        simp only [affineEndpointMatrix,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,
          Finset.sum_apply,z]
      _ = B *ᵥ v d := by
        rw [hclosed d,mulVec_fintype_sum]
        simp only [Matrix.mul_assoc,Matrix.mulVec_mulVec]
      _ = 0 := hd
  have hzero : z=0 := hend (hz.trans (Matrix.mulVec_zero _).symm)
  have hu (k : ℕ) (hk : k≤d) : u k=0 := by
    funext j
    exact congrFun hzero (⟨k,by omega⟩,j)
  intro k hk
  rw [hclosed k]
  apply Finset.sum_eq_zero
  intro i _
  rw [hu i.val (by have := i.isLt; omega),Matrix.mulVec_zero]

theorem affine_kernel_zero_of_endpoint_injective
    (A B L : Matrix n n K) (N : Matrix n r K) (F : Matrix r n K)
    (hLA : L*A+N*F=1) (d : ℕ)
    (hend : Function.Injective (affineEndpointMatrix B (-(L*B)) N d).mulVec)
    (v : n → K[X]) (hv : affineMatrixPencil A B *ᵥ v=0)
    (hdeg : ∀ i, (v i).natDegree≤d) : v=0 := by
  have hhigh : (fun i => (v i).coeff (d+1))=0 := by
    funext i
    exact Polynomial.coeff_eq_zero_of_natDegree_lt ((hdeg i).trans_lt (by omega))
  have hendv : B *ᵥ (fun i => (v i).coeff d)=0 := by
    simpa only [hhigh,Matrix.mulVec_zero,zero_add] using
      affine_kernel_coefficient_recurrence A B v hv d
  have hz := affine_coefficient_chain_zero_of_endpoint_injective A B L N F hLA d hend
    (fun k i => (v i).coeff k) (affine_kernel_coefficient_initial A B v hv)
    (affine_kernel_coefficient_recurrence A B v hv) hendv
  funext i
  apply Polynomial.ext
  intro k
  simp only [Pi.zero_apply,Polynomial.coeff_zero]
  by_cases hk : k≤d
  · exact congrFun (hz k hk) i
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((hdeg i).trans_lt (by omega))

end FD56
