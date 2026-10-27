/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.SLKirillovPencil

/-! Coefficients of Kirillov pencils are the Kirillov matrices of the coefficients. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem glKirillovMatrix_coefficient (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (k : ℕ) :
    (fun i j => (glKirillovMatrix M P i j).coeff k)=
      glKirillovMatrix (fun i j => (M i j).coeff k) (fun i j => (P i j).coeff k) := by
  funext i j
  cases i <;> cases j <;>
    simp [glKirillovMatrix,glTraceDualIndexEquiv,glEquationMatrix,
      LinearMap.toMatrix'_apply,glEquationLinearMap,matrixPairEquiv,
      stabilizerResidual,Matrix.mul_apply,Pi.single_apply,apply_ite,ite_apply]

theorem slKirillovMatrix_coefficient (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (i₀ : n) (k : ℕ) :
    (fun i j => (slKirillovMatrix M P i₀ i j).coeff k)=
      slKirillovMatrix (fun i j => (M i j).coeff k) (fun i j => (P i j).coeff k) i₀ := by
  let E : Matrix (SLInput n m) (SLChartInput n m i₀) K := slChartEmbeddingMatrix i₀
  have hE : slChartEmbeddingMatrix (R:=K[X]) (m:=m) i₀=E.map Polynomial.C :=
    (slChartEmbeddingMatrix_map Polynomial.C i₀).symm
  calc
    _ = E.transpose * (show Matrix (SLInput n m) (SLInput n m) K from
        fun i j => (glKirillovMatrix M P i j).coeff k) * E := by
      funext i j
      simp only [slKirillovMatrix,hE,Matrix.mul_apply,Matrix.transpose_apply,
        Matrix.map_apply,Polynomial.finset_sum_coeff,Polynomial.coeff_mul_C,
        Polynomial.coeff_C_mul]
    _ = _ := by rw [glKirillovMatrix_coefficient]; rfl

end FD56
