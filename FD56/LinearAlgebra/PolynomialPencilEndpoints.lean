/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialPencilEigenvalues
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! A regular affine pencil with two distinct finite poles has independent endpoints. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n] [Nonempty n]

theorem polynomial_pencil_endpoints_independent_of_two_roots
    (H : Matrix n n K[X]) (hH : DegreeBound H 1)
    (hB : Matrix.det (fun i j => (H i j).coeff 1)≠0)
    (x y : K) (hxy : x≠y) (hx : H.det.eval x=0) (hy : H.det.eval y=0) :
    LinearIndependent K ![(fun i j => (H i j).coeff 0),
      (fun i j => (H i j).coeff 1)] := by
  let A : Matrix n n K := fun i j => (H i j).coeff 0
  let B : Matrix n n K := fun i j => (H i j).coeff 1
  change LinearIndependent K ![A,B]
  apply linearIndependent_fin2.mpr
  refine ⟨?_,?_⟩
  · change B≠0
    intro hz
    exact hB (by change B.det=0; rw [hz,Matrix.det_zero inferInstance])
  · intro c hc
    change c•B=A at hc
    have hroot (z : K) (hz : H.det.eval z=0) : c+z=0 := by
      have he := (Polynomial.evalRingHom z).map_det H
      change H.det.eval z=(H.map (Polynomial.evalRingHom z)).det at he
      rw [polynomial_affine_evaluation H hH] at he
      change H.det.eval z=(A+z•B).det at he
      rw [← hc,← add_smul,Matrix.det_smul,hz] at he
      exact pow_eq_zero ((mul_eq_zero.mp he.symm).resolve_right hB)
    have hcx := hroot x hx
    have hcy := hroot y hy
    exact hxy (add_left_cancel (hcx.trans hcy.symm))

theorem polynomial_pencil_endpoints_independent_of_two_eigenvalues
    (H : Matrix n n K[X]) (hH : DegreeBound H 1)
    (hB : Matrix.det (fun i j => (H i j).coeff 1)≠0)
    (a b : (polynomialPencilOperator H).Eigenvalues) (hab : a≠b) :
    LinearIndependent K ![(fun i j => (H i j).coeff 0),
      (fun i j => (H i j).coeff 1)] :=
  polynomial_pencil_endpoints_independent_of_two_roots H hH hB a.val b.val
    (fun h => hab (Subtype.ext h))
    (polynomial_pencil_eigenvalue_det_root H hH hB a.val a.property)
    (polynomial_pencil_eigenvalue_det_root H hH hB b.val b.property)

end FD56
