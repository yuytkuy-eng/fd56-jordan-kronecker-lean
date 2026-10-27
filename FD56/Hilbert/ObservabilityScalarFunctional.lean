/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.ObservabilityDeterminantDerivative
import FD56.Hilbert.SLScalarDivisibility

/-! The determinant derivative is a polynomial linear functional on the adjugate scalar lift. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {R n m : Type*} [CommRing R] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

def matrixPairTraceFunctional (D : Matrix n n R) (Q : Matrix m n R) :
    (SLInput n m → R) →ₗ[R] R where
  toFun v := Matrix.trace (D * (matrixPairEquiv R R n m v).1) +
    Matrix.trace (Q * (matrixPairEquiv R R n m v).2)
  map_add' v w := by simp [map_add,Matrix.mul_add,Matrix.trace_add]; ring
  map_smul' c v := by simp [map_smul,Matrix.mul_smul,Matrix.trace_smul,smul_add,mul_add]

def observabilityScalarLift (M : Matrix n n R) (P : Matrix m n R)
    (level : n → ℕ) (row : n → m) : SLInput n m → R :=
  (matrixPairEquiv R R n m).symm
    (observabilityScalarX M P (observabilitySelectedMatrix M P level row).adjugate level row,
      observabilityScalarU M (observabilitySelectedMatrix M P level row).adjugate level row)

theorem observabilityScalarLift_derivative_functional
    (M : Matrix n n R[X]) (P : Matrix m n R[X]) (level : n → ℕ) (row : n → m) :
    matrixPairTraceFunctional (M.map Polynomial.derivative) (P.map Polynomial.derivative)
      (observabilityScalarLift M P level row) =
        Polynomial.derivative (observabilitySelectedMatrix M P level row).det := by
  simpa only [matrixPairTraceFunctional,observabilityScalarLift,LinearMap.coe_mk,AddHom.coe_mk,
    LinearEquiv.apply_symm_apply] using
      (observabilitySelectedMatrix_det_derivative M P level row).symm

variable {K : Type*} [Field K]

theorem observabilityScalarLift_equation
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (level : n → ℕ) (row : n → m)
    (hLower : ∀ k s, s<level k → ∀ a, ∃ l, level l=s ∧ row l=a) :
    glEquationMatrix M P *ᵥ observabilityScalarLift M P level row =
      (-(observabilitySelectedMatrix M P level row).det) • glScalarVector K[X] n m := by
  apply (glEquationMatrix_scalar_iff M P _ _).mpr
  obtain ⟨hP,_,hc⟩ := observability_adjugate_scalar_equations M P level row hLower
  simp only [observabilityScalarLift,LinearEquiv.apply_symm_apply]
  refine ⟨hP,?_⟩
  change M*_ - _*M - _*P = _
  rw [hc,add_sub_cancel_left]

theorem slHilbert_zero_of_separable_observability
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (i₀ : n) (d : ℕ)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (level : n → ℕ) (row : n → m)
    (hLower : ∀ k s, s<level k → ∀ a, ∃ l, level l=s ∧ row l=a)
    (hs : (observabilitySelectedMatrix M P level row).det.Separable)
    (hdegree : d+1 < (observabilitySelectedMatrix M P level row).det.natDegree)
    (hinj : Function.Injective (glEquationMatrix M P).mulVec) : slHilbert M P d = 0 := by
  apply slHilbert_zero_of_scalar_divisibility M P i₀ d hM hP
    (observabilityScalarLift M P level row) (-(observabilitySelectedMatrix M P level row).det)
    (Polynomial.derivative (observabilitySelectedMatrix M P level row).det)
    (matrixPairTraceFunctional (M.map Polynomial.derivative) (P.map Polynomial.derivative))
    (observabilityScalarLift_equation M P level row hLower)
    (observabilityScalarLift_derivative_functional M P level row) hs.neg_left hinj
  simpa only [Polynomial.natDegree_neg] using hdegree

end FD56
