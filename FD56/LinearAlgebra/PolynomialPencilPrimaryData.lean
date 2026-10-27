/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.RegularPencilPrimaryData

/-! Primary invariants for polynomial matrices of degree at most one. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

def polynomialPencilOperator (H : Matrix n n K[X]) : Module.End K (n → K) :=
  let A : Matrix n n K := fun i j => (H i j).coeff 0
  let B : Matrix n n K := fun i j => (H i j).coeff 1
  Matrix.toLin' (-B⁻¹*A)

theorem polynomial_affine_evaluation (H : Matrix n n K[X]) (hH : DegreeBound H 1) (x : K) :
    H.map (Polynomial.evalRingHom x)=
      (fun i j => (H i j).coeff 0)+x•(fun i j => (H i j).coeff 1) := by
  have h := congrArg (fun A => A.map (Polynomial.evalRingHom x))
    (affineMatrixPencil_coefficients H hH)
  dsimp only at h
  rw [← h]
  funext i j
  simp [affineMatrixPencil,Matrix.map_apply]
  ring

theorem polynomial_pencil_primary_rank_two (H : Matrix n n K[X]) (hH : DegreeBound H 1)
    (hB : Matrix.det (fun i j => (H i j).coeff 1)≠0)
    (x : K) (m : ℕ) (hm : 1≤m)
    (hmult : rootMultiplicity x H.det=2*m)
    (hker : Module.finrank K (LinearMap.ker (Matrix.toLin'
      (H.map (Polynomial.evalRingHom x))))=2*m-2) :
    Module.finrank K ((polynomialPencilOperator H).maxGenEigenspace x)=2*m ∧
      IsNilpotent (primaryShift (polynomialPencilOperator H) x) ∧
      Module.finrank K (LinearMap.range (primaryShift (polynomialPencilOperator H) x))=2 := by
  apply affine_pencil_primary_rank_two (fun i j => (H i j).coeff 0)
    (fun i j => (H i j).coeff 1) hB x m hm
  · rwa [affineMatrixPencil_coefficients H hH]
  · rwa [polynomial_affine_evaluation H hH x] at hker

end FD56
