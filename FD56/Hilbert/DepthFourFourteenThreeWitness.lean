/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthFourFourteenThreeData
import FD56.Hilbert.KernelDegreesFromBezout
import FD56.Stabilizer.ObservabilityMatrix
import FD56.LinearAlgebra.RankSpecializationExtension

/-! A verified reduced kernel basis of degree fifteen for a depth-four affine witness. -/
noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option Elab.async false

def fourteenThreeMZero : Matrix (Fin 14) (Fin 14) ℤ := ![![0,0,1,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,1,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,1,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,1,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,1,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,1,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,1,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,1,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,1,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,1,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,1,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,1],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0]]

def fourteenThreeBlockZero : Fin 4 → Matrix (Fin 3) (Fin 14) ℤ := ![![![0,0,1,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,1,0,0,0,0,1,0],![1,1,0,0,0,0,0,0,0,0,0,0,0,0]],![![0,0,0,0,1,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,1,0,0,0,0],![0,0,1,1,0,0,0,0,0,0,0,0,0,0]],![![0,0,0,0,0,0,1,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,1,0,0],![0,0,0,0,1,1,0,0,0,0,0,0,0,0]],![![0,0,0,0,0,0,0,0,1,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,1],![0,0,0,0,0,0,1,1,0,0,0,0,0,0]]]

def fourteenThreeOZero : Matrix (Fin 4 × Fin 3) (Fin 14) ℤ :=
  fun i j => fourteenThreeBlockZero i.1 i.2 j

def fourteenThreeRZero : Matrix (Fin 14) (Fin 4 × Fin 3) ℤ :=
  fun i j => ![![0,0,1,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0],![1,0,0,0,0,0,0,0,0,0,0,0],![-1,0,0,0,0,1,0,0,0,0,0,0],![0,0,0,1,0,0,0,0,0,0,0,0],![0,0,0,-1,0,0,0,0,1,0,0,0],![0,0,0,0,0,0,1,0,0,0,0,0],![0,0,0,0,0,0,-1,0,0,0,0,1],![0,0,0,0,0,0,0,0,0,1,0,0],![0,0,0,0,1,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,1,0,0,0,0],![0,1,0,0,0,0,1,0,0,0,0,-1],![0,0,0,0,0,0,0,0,0,0,1,0]] i (⟨3*j.1.val+j.2.val,by omega⟩ : Fin 12)

theorem fourteenThree_evalM : (fourteenThreeM (K := K)).map (Polynomial.evalRingHom 0)=
    (fourteenThreeMZero).map (Int.castRingHom K) := by
  have he : ∀ i j, (fourteenThreeMData i j).getD 0 0=(fourteenThreeMZero) i j := by decide
  funext i j
  change (integerPolynomial (fourteenThreeMData i j)).eval 0=((fourteenThreeMZero) i j : K)
  rw [← Polynomial.coeff_zero_eq_eval_zero,integerPolynomial_coeff,he]

theorem fourteenThree_evalP : (fourteenThreeP (K := K)).map (Polynomial.evalRingHom 0)=
    (fourteenThreeBlockZero 0).map (Int.castRingHom K) := by
  have he : ∀ i j, (fourteenThreePData i j).getD 0 0=(fourteenThreeBlockZero 0) i j := by decide
  funext i j
  change (integerPolynomial (fourteenThreePData i j)).eval 0=((fourteenThreeBlockZero 0) i j : K)
  rw [← Polynomial.coeff_zero_eq_eval_zero,integerPolynomial_coeff,he]

theorem fourteenThree_constant_step (i : Fin 3) :
    (fourteenThreeBlockZero i.castSucc).map (Int.castRingHom K)*fourteenThreeMZero.map (Int.castRingHom K)=
      (fourteenThreeBlockZero i.succ).map (Int.castRingHom K) := by
  rw [← Matrix.map_mul]
  have h : ∀ i : Fin 3, fourteenThreeBlockZero i.castSucc*fourteenThreeMZero=fourteenThreeBlockZero i.succ := by decide
  rw [h]

theorem fourteenThree_evalO : (observabilityMatrix (fourteenThreeM (K := K)) fourteenThreeP 4).map
    (Polynomial.evalRingHom 0)=fourteenThreeOZero.map (Int.castRingHom K) := by
  rw [observabilityMatrix_map,fourteenThree_evalM,fourteenThree_evalP]
  funext i j
  rcases i with ⟨i,r⟩
  have h0 := fourteenThree_constant_step (K := K) 0
  have h1 := fourteenThree_constant_step (K := K) 1
  have h2 := fourteenThree_constant_step (K := K) 2
  change (fourteenThreeBlockZero 0).map (Int.castRingHom K)*fourteenThreeMZero.map (Int.castRingHom K)=(fourteenThreeBlockZero 1).map (Int.castRingHom K) at h0
  change (fourteenThreeBlockZero 1).map (Int.castRingHom K)*fourteenThreeMZero.map (Int.castRingHom K)=(fourteenThreeBlockZero 2).map (Int.castRingHom K) at h1
  change (fourteenThreeBlockZero 2).map (Int.castRingHom K)*fourteenThreeMZero.map (Int.castRingHom K)=(fourteenThreeBlockZero 3).map (Int.castRingHom K) at h2
  change (((fourteenThreeBlockZero 0).map (Int.castRingHom K))*(fourteenThreeMZero.map (Int.castRingHom K))^i.val) r j=_
  fin_cases i
  · simp only [Fin.val_zero,pow_zero,Matrix.mul_one]; rfl
  · simpa only [Fin.val_one,pow_one] using congrFun (congrFun h0 r) j
  · simp only [Fin.val_two,pow_two,← Matrix.mul_assoc]
    rw [h0,h1]
    rfl
  · simp only [Fin.reduceFinMk,pow_succ,pow_zero,Matrix.mul_one,← Matrix.mul_assoc]
    rw [h0,h1,h2]
    rfl

theorem fourteenThree_constant_right_inverse :
    (observabilityMatrix (fourteenThreeM (K := K)) fourteenThreeP 4).map (Polynomial.evalRingHom 0)*
      fourteenThreeRZero.map (Int.castRingHom K)=1 := by
  rw [fourteenThree_evalO,← Matrix.map_mul]
  have h : fourteenThreeOZero*fourteenThreeRZero=1 := by decide
  rw [h,Matrix.map_one] <;> simp

theorem fourteenThree_kernel_columns : observabilityMatrix (fourteenThreeM (K := K)) fourteenThreeP 4*(fourteenThreeV0 (K := K))=(0 : Matrix (Fin 4 × Fin 3) (Fin 2) K[X]) := by
  funext i j
  rcases i with ⟨i,r⟩
  change (((fourteenThreeP (K := K))*fourteenThreeM^i.val)*fourteenThreeV0 : Matrix (Fin 3) (Fin 2) K[X]) r j=0
  fin_cases i
  · simpa only [Fin.val_zero,pow_zero,Matrix.mul_one] using congrFun (congrFun (fourteenThree_output0 (K := K)) r) j
  · simpa only [Fin.val_one,pow_one,Matrix.mul_assoc,fourteenThree_step0] using congrFun (congrFun (fourteenThree_output1 (K := K)) r) j
  · simpa only [Fin.val_two,pow_two,Matrix.mul_assoc,fourteenThree_step0,fourteenThree_step1] using congrFun (congrFun (fourteenThree_output2 (K := K)) r) j
  · simpa only [Fin.reduceFinMk,pow_succ,pow_zero,Matrix.one_mul,Matrix.mul_assoc,fourteenThree_step0,fourteenThree_step1,fourteenThree_step2] using congrFun (congrFun (fourteenThree_output3 (K := K)) r) j

theorem fourteenThree_fraction_nullity :
    Module.finrank (FractionRing K[X]) (LinearMap.ker (Matrix.toLin'
      ((observabilityMatrix (fourteenThreeM (K := K)) fourteenThreeP 4).map (algebraMap K[X] (FractionRing K[X])))))=2 := by
  let A := observabilityMatrix (fourteenThreeM (K := K)) fourteenThreeP 4
  have hs : Function.Surjective (A.map (Polynomial.evalRingHom 0)).mulVec := by
    intro v
    refine ⟨fourteenThreeRZero.map (Int.castRingHom K)*ᵥv,?_⟩
    rw [Matrix.mulVec_mulVec,fourteenThree_constant_right_inverse,Matrix.one_mulVec]
  have h0 := (Matrix.toLin' (A.map (Polynomial.evalRingHom 0))).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs,finrank_top] at h0
  have hF := (Matrix.toLin' (A.map (algebraMap K[X] (FractionRing K[X])))).finrank_range_add_finrank_ker
  have hle := Submodule.finrank_le (LinearMap.range (Matrix.toLin' (A.map (algebraMap K[X] (FractionRing K[X])))))
  have hu := matrix_kernel_finrank_le_of_field_specialization (Polynomial.evalRingHom (0 : K))
    (algebraMap K[X] (FractionRing K[X])) (IsFractionRing.injective _ _) A
  simp only [Module.finrank_fintype_fun_eq_card,Fintype.card_prod,Fintype.card_fin] at h0 hF hle
  change Module.finrank (FractionRing K[X]) (LinearMap.ker (Matrix.toLin' (A.map (algebraMap K[X] (FractionRing K[X])))))=2
  omega

theorem fourteenThree_alpha_degrees [CharZero K] :
    HasMinimalKernelDegrees (observabilityMatrix (fourteenThreeM (K := K)) fourteenThreeP 4) [15,15] := by
  let L : Matrix (Fin 2) (Fin 14) K[X] := C ((1060967992213313909236 : K)⁻¹) • fourteenThreeLeft
  have hL : L*(fourteenThreeV0 (K := K))=(1 : Matrix (Fin 2) (Fin 2) K[X]) := by
    dsimp only [L]
    rw [Matrix.smul_mul,fourteenThree_left_scaled,smul_smul,← C_mul,inv_mul_cancel₀ (by norm_num),C_1,one_smul]
  have h := minimal_degrees_of_left_inverse_and_nullity
    (algebraMap K[X] (FractionRing K[X])) (IsFractionRing.injective _ _)
    (observabilityMatrix (fourteenThreeM (K := K)) fourteenThreeP 4) fourteenThreeV0 L hL fourteenThree_kernel_columns
    fourteenThree_fraction_nullity (fun _ => 15) fourteenThree_V0_degree fourteenThree_leading_injective
  simpa [List.ofFn_succ] using h

end FD56
