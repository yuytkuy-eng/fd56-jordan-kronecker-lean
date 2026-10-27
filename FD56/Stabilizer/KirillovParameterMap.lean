/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.KirillovCoefficient
import FD56.LinearAlgebra.PolynomialPencilEndpoints

/-! Linearity in the coadjoint parameter and independent generating covectors. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

def glKirillovParameterMap :
    (Matrix n n K × Matrix m n K) →ₗ[K]
      Matrix (SLInput n m) (SLInput n m) K where
  toFun z := glKirillovMatrix z.1 z.2
  map_add' z w := by
    funext i j
    cases i <;>
      simp [glKirillovMatrix,glEquationMatrix,LinearMap.toMatrix'_apply,
        glEquationLinearMap,glTraceDualIndexEquiv,stabilizerResidual,
        Matrix.add_mul,Matrix.mul_add] <;> abel
  map_smul' c z := by
    funext i j
    cases i <;>
      simp [glKirillovMatrix,glEquationMatrix,LinearMap.toMatrix'_apply,
        glEquationLinearMap,glTraceDualIndexEquiv,stabilizerResidual,
        Matrix.smul_mul,Matrix.mul_smul,smul_sub] <;> ring

theorem affine_pair_endpoints_independent_of_kirillov
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (h : LinearIndependent K ![(fun i j => (glKirillovMatrix M P i j).coeff 0),
      (fun i j => (glKirillovMatrix M P i j).coeff 1)]) :
    LinearIndependent K ![((fun i j => (M i j).coeff 0),(fun i j => (P i j).coeff 0)),
      ((fun i j => (M i j).coeff 1),(fun i j => (P i j).coeff 1))] := by
  apply LinearIndependent.of_comp glKirillovParameterMap
  convert h using 1
  funext k
  fin_cases k <;> simp [Function.comp_def,glKirillovParameterMap,
    glKirillovMatrix_coefficient]

end FD56
