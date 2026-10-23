/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthTwoRowLifting
import FD56.Hilbert.DepthTwoKernelTransport

/-! Triangular changes of the quadratic stack preserve its polynomial kernel. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K m n r : Type*} [Field K]
  [Fintype m] [Fintype n] [Fintype r]
  [DecidableEq m] [DecidableEq n] [DecidableEq r]

def depthTwoStackChange {R : Type*} [CommRing R]
    (A D : Matrix m m R) : Matrix (m ⊕ m) (m ⊕ m) R :=
  Matrix.fromBlocks 1 0 A D

def depthTwoStackChangeInverse {R : Type*} [CommRing R]
    (A E : Matrix m m R) : Matrix (m ⊕ m) (m ⊕ m) R :=
  Matrix.fromBlocks 1 0 (-E * A) E

omit [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r] in
theorem depthTwoStackChange_inverse {R : Type*} [CommRing R] (A D E : Matrix m m R)
    (hDE : D * E = 1) (hED : E * D = 1) :
    depthTwoStackChange A D * depthTwoStackChangeInverse A E = 1 ∧
      depthTwoStackChangeInverse A E * depthTwoStackChange A D = 1 := by
  have hDEA : D * (E * A) = A := by rw [← Matrix.mul_assoc, hDE, Matrix.one_mul]
  constructor
  · simp [depthTwoStackChange, depthTwoStackChangeInverse, Matrix.fromBlocks_multiply,
      Matrix.mul_assoc, hDE, hDEA, Matrix.fromBlocks_one]
  · simp [depthTwoStackChange, depthTwoStackChangeInverse, Matrix.fromBlocks_multiply,
      Matrix.mul_assoc, hED, Matrix.fromBlocks_one]

omit [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r] in
theorem depthTwoStackChange_mul (P Q : Matrix m n K[X]) (A D : Matrix m m K[X]) :
    depthTwoStackChange A D * depthTwoStack P Q = depthTwoStack P (A * P + D * Q) := by
  funext i j
  cases i <;> simp [depthTwoStackChange, depthTwoStack, Matrix.mul_apply,
    Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]

theorem depthTwo_stack_change_basis (P Q : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (depthTwoStack P Q))))
    (R : Matrix n (m ⊕ m) K[X]) (hR : depthTwoStack P Q * R = 1)
    (A D E : Matrix m m K[X]) (hDE : D * E = 1) (hED : E * D = 1) :
    ∃ (B' : Basis r K[X]
        (LinearMap.ker (Matrix.toLin' (depthTwoStack P (A * P + D * Q)))))
      (R' : Matrix n (m ⊕ m) K[X]),
      polynomialKernelBasisMatrix _ B' = polynomialKernelBasisMatrix _ B ∧
      depthTwoStack P (A * P + D * Q) * R' = 1 := by
  let O := depthTwoStack P Q
  let V := polynomialKernelBasisMatrix O B
  let U := depthTwoStackChange A D
  let U' := depthTwoStackChangeInverse A E
  obtain ⟨hUU', hU'U⟩ := depthTwoStackChange_inverse A D E hDE hED
  change U * U' = 1 at hUU'
  change U' * U = 1 at hU'U
  obtain ⟨S,hSV,hVR⟩ := polynomial_kernel_basis_split O B R hR
  have hO' : depthTwoStack P (A * P + D * Q) = U * O :=
    (depthTwoStackChange_mul P Q A D).symm
  have hOV : (U * O) * V = 0 := by
    rw [Matrix.mul_assoc, polynomialKernelBasisMatrix_mul, Matrix.mul_zero]
  have hVR' : V * S + (R * U') * (U * O) = 1 := by
    rw [Matrix.mul_assoc R, ← Matrix.mul_assoc U', hU'U, Matrix.one_mul]
    exact hVR
  have hR' : (U * O) * (R * U') = 1 := by
    rw [Matrix.mul_assoc U, ← Matrix.mul_assoc O, hR, Matrix.one_mul, hUU']
  rw [hO']
  exact ⟨splitPolynomialKernelBasis _ _ _ _ hOV hSV hVR', R * U',
    polynomialKernelBasisMatrix_split _ _ _ _ hOV hSV hVR', hR'⟩

omit [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r] in
theorem depthTwo_stack_change_leading (P Q : Matrix m n K[X])
    (A : Matrix m m K[X]) (D E : Matrix m m K)
    (hDE : D * E = 1) (hED : E * D = 1)
    (hP : DegreeBound P 1) (hQ : DegreeBound Q 2) (hA : DegreeBound A 1)
    (hlead : Function.Injective (Matrix.mulVec (fun x i =>
      (depthTwoStack P Q i x).coeff (depthTwoRowDegree i)))) :
    Function.Injective (Matrix.mulVec (fun x i =>
      (depthTwoStack P (A * P + D.map C * Q) i x).coeff (depthTwoRowDegree i))) := by
  let W : Matrix (m ⊕ m) n K := fun i x =>
    (depthTwoStack P Q i x).coeff (depthTwoRowDegree i)
  let U := depthTwoStackChange (matrixCoeff A 1) D
  let U' := depthTwoStackChangeInverse (matrixCoeff A 1) E
  have hUU' : U * U' = 1 := (depthTwoStackChange_inverse _ _ _ hDE hED).1
  have hDt : matrixCoeff (D.map C) 0 = D := by funext i j; simp [matrixCoeff]
  have hDdeg : DegreeBound (D.map C) 0 := by intro i j; simp
  have hnew : (show Matrix (m ⊕ m) n K from fun i x =>
      (depthTwoStack P (A * P + D.map C * Q) i x).coeff (depthTwoRowDegree i)) = U * W := by
    funext i x
    cases i with
    | inl i => simp [U,W,depthTwoStackChange,depthTwoStack,depthTwoRowDegree,
        Matrix.mul_apply,Fintype.sum_sum_type,Matrix.fromBlocks,Matrix.one_apply]
    | inr i =>
      have hAP := congrFun (congrFun (matrixCoeff_mul A P 1 1 hA hP) i) x
      have hDQ := congrFun (congrFun (matrixCoeff_mul (D.map C) Q 0 2 hDdeg hQ) i) x
      rw [hDt] at hDQ
      change ((A * P + D.map C * Q) i x).coeff 2 = _
      rw [Matrix.add_apply,Polynomial.coeff_add]
      change matrixCoeff (A * P) 2 i x + matrixCoeff (D.map C * Q) 2 i x = _
      rw [hAP,hDQ]
      simp [U,W,depthTwoStackChange,depthTwoStack,depthTwoRowDegree,
        Matrix.mul_apply,Fintype.sum_sum_type,Matrix.fromBlocks,matrixCoeff]
  have hnewT := congrArg Matrix.transpose hnew
  change (show Matrix n (m ⊕ m) K from fun x i =>
      (depthTwoStack P (A * P + D.map C * Q) i x).coeff (depthTwoRowDegree i)) = _ at hnewT
  rw [Matrix.transpose_mul] at hnewT
  dsimp only at hnewT
  rw [hnewT]
  intro v w hvw
  have hh : U.transpose *ᵥ v = U.transpose *ᵥ w := by
    apply hlead
    simpa only [Matrix.mulVec_mulVec] using hvw
  have h := congrArg (fun z => U'.transpose *ᵥ z) hh
  dsimp only at h
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
    hUU', Matrix.transpose_one, Matrix.one_mulVec, Matrix.one_mulVec] at h
  exact h

end FD56
