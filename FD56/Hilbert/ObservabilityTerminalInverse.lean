/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialKernelSplitting
import FD56.Stabilizer.ObservabilityMatrix

/-! Polynomial splitting of the terminal restriction follows from the two
neighboring observability inverses. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m r : Type*} [Field K]
  [Fintype n] [Fintype m] [Fintype r]
  [DecidableEq n] [DecidableEq m] [DecidableEq r]

theorem observability_terminal_factor_of_left_inverse
    (q : ℕ) (M : Matrix n n K[X]) (P : Matrix m n K[X]) (V : Matrix n r K[X])
    (U : Matrix n (Fin (q+1) × m) K[X])
    (hU : U*observabilityMatrix M P (q+1)=1)
    (hV : observabilityMatrix M P q*V=0) :
    (show Matrix n m K[X] from fun i j => U i (Fin.last q,j))*(P*M^q*V)=V := by
  have he : U*(observabilityMatrix M P (q+1)*V)=
      (show Matrix n m K[X] from fun i j => U i (Fin.last q,j))*(P*M^q*V) := by
    funext x k
    change (∑ ij : Fin (q+1) × m,
      U x ij*(observabilityMatrix M P (q+1)*V) ij k)=_
    rw [Fintype.sum_prod_type,Fin.sum_univ_castSucc]
    have hz (i : Fin q) :
        (∑ y : m, U x (i.castSucc,y)*(observabilityMatrix M P (q+1)*V) (i.castSucc,y) k)=0 := by
      apply Finset.sum_eq_zero
      intro y _
      have h : (observabilityMatrix M P (q+1)*V) (i.castSucc,y) k=0 :=
        congrFun (congrFun hV (i,y)) k
      rw [h,mul_zero]
    simp only [hz,Finset.sum_const_zero,zero_add]
    rfl
  rw [← Matrix.mul_assoc,hU,Matrix.one_mul] at he
  exact he.symm

theorem observability_terminal_kernel_left_inverse
    (q : ℕ) (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P q))))
    (R : Matrix n (Fin q × m) K[X]) (hR : observabilityMatrix M P q*R=1)
    (U : Matrix n (Fin (q+1) × m) K[X])
    (hU : U*observabilityMatrix M P (q+1)=1) :
    ∃ L : Matrix r m K[X],
      L*(P*M^q*polynomialKernelBasisMatrix (observabilityMatrix M P q) B)=1 := by
  obtain ⟨L,hL⟩ := polynomial_kernel_basis_left_inverse_of_right_inverse
    (observabilityMatrix M P q) R hR B
  refine ⟨L*(show Matrix n m K[X] from fun i j => U i (Fin.last q,j)),?_⟩
  rw [Matrix.mul_assoc,observability_terminal_factor_of_left_inverse q M P _ U hU
    (polynomialKernelBasisMatrix_mul _ B),hL]

end FD56
