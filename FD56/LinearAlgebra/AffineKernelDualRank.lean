/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.AffineKernelDualLift
import FD56.LinearAlgebra.PolynomialMatrix

/-! The finite-dimensional image of affine evaluation on a reduced kernel
basis, including composition with an injective polynomial matrix. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K a n j l : Type*} [Field K] [Fintype n] [DecidableEq n] [Fintype j]

def affineDualPairMap (V : Matrix n j K[X]) :
    ((n → K) × (n → K)) →ₗ[K] (j → K[X]) where
  toFun x := V.transpose *ᵥ (fun i => C (x.1 i) + X*C (x.2 i))
  map_add' x y := by
    have h : (fun i => C ((x+y).1 i) + X*C ((x+y).2 i)) =
        (fun i => C (x.1 i) + X*C (x.2 i)) +
        (fun i => C (y.1 i) + X*C (y.2 i)) := by
      funext i
      simp only [Prod.fst_add,Prod.snd_add,Pi.add_apply,map_add]
      ring
    rw [h,Matrix.mulVec_add]
  map_smul' c x := by
    have h : (fun i => C ((c • x).1 i) + X*C ((c • x).2 i)) =
        c • (fun i => C (x.1 i) + X*C (x.2 i) : n → K[X]) := by
      funext i
      simp only [Prod.smul_fst,Prod.smul_snd,Pi.smul_apply,smul_eq_mul,
        map_mul,Polynomial.smul_eq_C_mul]
      ring
    rw [h,Matrix.mulVec_smul]
    rfl

omit [DecidableEq n] [Fintype j] in
private theorem affineDualPairMap_degree (V : Matrix n j K[X]) (d : j → ℕ)
    (hdegree : ∀ i j, (V i j).natDegree ≤ d j)
    (x : (n → K) × (n → K)) (j : j) :
    (affineDualPairMap V x j).natDegree ≤ d j+1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  apply Polynomial.natDegree_mul_le.trans
  apply Nat.add_le_add (hdegree i j)
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · simp
  · exact Polynomial.natDegree_mul_le.trans (by simp)

def boundedAffineKernelDualMap (V : Matrix n j K[X]) (d : j → ℕ)
    (hdegree : ∀ i j, (V i j).natDegree ≤ d j) :
    ((n → K) × (n → K)) →ₗ[K] (∀ j, BoundedPoly K (d j+1)) where
  toFun x j := boundedPolyOf (affineDualPairMap V x j)
    (affineDualPairMap_degree V d hdegree x j)
  map_add' x y := by
    funext j
    apply Subtype.ext
    exact congrFun ((affineDualPairMap V).map_add x y) j
  map_smul' c x := by
    funext j
    apply Subtype.ext
    exact congrFun ((affineDualPairMap V).map_smul c x) j

theorem boundedAffineKernelDualMap_surjective (A B : Matrix a n K)
    (basis : Basis j K[X] (LinearMap.ker (Matrix.toLin' (affineMatrixPencil A B))))
    (d : j → ℕ)
    (hdegree : ∀ i j, (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis i j).natDegree ≤ d j)
    (hlead : Function.Injective (Matrix.mulVec
      (fun i j => (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis i j).coeff (d j)))) :
    Function.Surjective (boundedAffineKernelDualMap
      (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis) d hdegree) := by
  intro p
  obtain ⟨u,v,h⟩ := affine_kernel_dual_affine_lift A B basis d hdegree hlead
    (fun j => (p j).val) (fun j => boundedPoly_degree (d j+1) (p j))
  refine ⟨(u,v), ?_⟩
  funext j
  apply Subtype.ext
  exact congrFun h j

theorem boundedAffineKernelDualMap_finrank_range (A B : Matrix a n K)
    (basis : Basis j K[X] (LinearMap.ker (Matrix.toLin' (affineMatrixPencil A B))))
    (d : j → ℕ)
    (hdegree : ∀ i j, (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis i j).natDegree ≤ d j)
    (hlead : Function.Injective (Matrix.mulVec
      (fun i j => (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis i j).coeff (d j)))) :
    Module.finrank K (LinearMap.range (boundedAffineKernelDualMap
      (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis) d hdegree)) =
      ∑ j, (d j+2) := by
  rw [LinearMap.range_eq_top.mpr
    (boundedAffineKernelDualMap_surjective A B basis d hdegree hlead),finrank_top]
  simp [Module.finrank_pi_fintype,Nat.add_assoc]

theorem affineKernelDual_comp_finrank_range [DecidableEq j] (A B : Matrix a n K)
    (basis : Basis j K[X] (LinearMap.ker (Matrix.toLin' (affineMatrixPencil A B))))
    (d : j → ℕ)
    (hdegree : ∀ i j, (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis i j).natDegree ≤ d j)
    (hlead : Function.Injective (Matrix.mulVec
      (fun i j => (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis i j).coeff (d j))))
    (C : Matrix j l K[X]) (hC : Function.Injective C.transpose.mulVec) :
    Module.finrank K (LinearMap.range
      (((Matrix.toLin' C.transpose).restrictScalars K).comp
        (affineDualPairMap (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis)))) =
      ∑ j, (d j+2) := by
  let f : (∀ j, BoundedPoly K (d j+1)) →ₗ[K] (l → K[X]) :=
    { toFun := fun p => C.transpose *ᵥ (fun j => (p j).val)
      map_add' := fun p q => Matrix.mulVec_add _ _ _
      map_smul' := fun c p => by
        change C.transpose *ᵥ (c • (fun j => (p j).val)) = _
        exact Matrix.mulVec_smul _ c _ }
  have hf : Function.Injective f := by
    intro p q h
    have hv := hC h
    funext j
    apply Subtype.ext
    exact congrFun hv j
  have hcomp : ((Matrix.toLin' C.transpose).restrictScalars K).comp
        (affineDualPairMap (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis)) =
      f.comp (boundedAffineKernelDualMap
        (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis) d hdegree) := by
    apply LinearMap.ext
    intro x
    funext i
    rfl
  rw [hcomp,LinearMap.range_comp_of_range_eq_top f
    (LinearMap.range_eq_top.mpr
      (boundedAffineKernelDualMap_surjective A B basis d hdegree hlead)),
    LinearMap.finrank_range_of_inj hf]
  simp [Module.finrank_pi_fintype,Nat.add_assoc]

end FD56
