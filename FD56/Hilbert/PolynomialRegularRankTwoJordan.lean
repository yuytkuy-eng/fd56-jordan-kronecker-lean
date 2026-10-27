/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.PolynomialPrimaryJordan
import FD56.LinearAlgebra.PolynomialPencilEigenvalues
import FD56.LinearAlgebra.PolynomialPrimaryBlockAssembly

/-! Global Jordan blocks for a regular alternating pencil with rank-two primary shifts. -/

noncomputable section
set_option maxHeartbeats 2000000
namespace FD56
open Matrix Polynomial
variable {K n : Type*} [Field K] [IsAlgClosed K] [Fintype n] [DecidableEq n]
local instance : DecidableEq K := Classical.decEq K

theorem polynomial_regular_rank_two_jordan_decomposition
    (H : Matrix n n K[X]) (hH : DegreeBound H 1)
    (hA : ∀ v, v ⬝ᵥ ((fun r s => (H r s).coeff 0) *ᵥ v)=0)
    (hB : ∀ v, v ⬝ᵥ ((fun r s => (H r s).coeff 1) *ᵥ v)=0)
    (hd : Matrix.det (fun r s => (H r s).coeff 1)≠0)
    (m : ℕ)
    (hlocal : ∀ x, H.det.eval x=0 →
      Module.finrank K ((polynomialPencilOperator H).maxGenEigenspace x)=2*m ∧
      Module.finrank K (LinearMap.range (primaryShift (polynomialPencilOperator H) x))=2) :
    ∃ T : Matrix n (Σ _a : (polynomialPencilOperator H).Eigenvalues, rankTwoJordanIndex (m-2)) K,
    ∃ U : Matrix (Σ _a : (polynomialPencilOperator H).Eigenvalues, rankTwoJordanIndex (m-2)) n K,
      T*U=1 ∧ U*T=1 ∧
      (T.map C).transpose*H*T.map C=
        Matrix.blockDiagonal' (fun a : (polynomialPencilOperator H).Eigenvalues =>
          rankTwoJordanPencil a.val (m-2)) := by
  classical
  let f := polynomialPencilOperator H
  have hdata (a : f.Eigenvalues) : Module.finrank K (f.maxGenEigenspace a.val)=2*m ∧
      Module.finrank K (LinearMap.range (primaryShift f a.val))=2 :=
    hlocal a.val (polynomial_pencil_eigenvalue_det_root H hH hd a.val a.property)
  let e (a : f.Eigenvalues) : Basis (Fin (2*m)) K (f.maxGenEigenspace a.val) :=
    Module.finBasisOfFinrankEq K _ (hdata a).1
  have hcong (a : f.Eigenvalues) :
      ∃ T : Matrix (Fin (2*m)) (rankTwoJordanIndex (m-2)) K,
      ∃ U : Matrix (rankTwoJordanIndex (m-2)) (Fin (2*m)) K,
        T*U=1 ∧ U*T=1 ∧
        (((subspaceBasisColumns _ (e a))*T).map C).transpose*H*
          ((subspaceBasisColumns _ (e a))*T).map C=rankTwoJordanPencil a.val (m-2) :=
    polynomial_primary_jordan_decomposition H hH hA hB hd a.val m
      (Fintype.card_fin _) (hdata a).2 (e a)
  choose T U hTU hUT hJ using hcong
  exact polynomial_primary_local_congruence_assembly H hH hA hB hd e T U
    (fun a => rankTwoJordanPencil a.val (m-2)) hTU hUT hJ

end FD56
