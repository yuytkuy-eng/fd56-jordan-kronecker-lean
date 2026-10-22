/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialMatrix
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Polynomial.FieldDivision

/-! Polynomial kernels have finite bases. Their basis matrices have full
column rank at every evaluation point because the kernels are saturated. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K a b k : Type*} [Field K] [Fintype b] [DecidableEq b]

def polynomialKernelBasisMatrix (A : Matrix a b K[X])
    (B : Basis k K[X] (LinearMap.ker (Matrix.toLin' A))) : Matrix b k K[X] :=
  fun i j => (B j).val i

theorem polynomialKernelBasisMatrix_mul (A : Matrix a b K[X])
    (B : Basis k K[X] (LinearMap.ker (Matrix.toLin' A))) :
    A * polynomialKernelBasisMatrix A B = 0 := by
  funext i j
  exact congrFun (B j).property i

theorem polynomialKernelBasisMatrix_mulVec [Fintype k] (A : Matrix a b K[X])
    (B : Basis k K[X] (LinearMap.ker (Matrix.toLin' A))) (c : k → K[X]) :
    polynomialKernelBasisMatrix A B *ᵥ c = (B.equivFun.symm c).val := by
  funext i
  simp [polynomialKernelBasisMatrix, Matrix.mulVec, dotProduct,
    Basis.equivFun_symm_apply, mul_comm]

theorem polynomialKernelBasisMatrix_pointwise_injective [Fintype k]
    (A : Matrix a b K[X]) (B : Basis k K[X] (LinearMap.ker (Matrix.toLin' A))) (x : K) :
    Function.Injective ((polynomialKernelBasisMatrix A B).map (Polynomial.evalRingHom x)).mulVec := by
  classical
  let Z := polynomialKernelBasisMatrix A B
  change Function.Injective (Matrix.toLin' (Z.map (Polynomial.evalRingHom x)))
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro c hc
  let y := B.equivFun.symm (fun j => Polynomial.C (c j))
  have hyeval (i : b) : (y.val i).eval x = 0 := by
    have hy : y.val = Z *ᵥ (fun j => Polynomial.C (c j)) :=
      (polynomialKernelBasisMatrix_mulVec A B _).symm
    rw [hy]
    have hh := congrFun hc i
    simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Polynomial.eval_finset_sum] using hh
  have hdvd (i : b) : Polynomial.X - Polynomial.C x ∣ y.val i :=
    Polynomial.dvd_iff_isRoot.mpr (hyeval i)
  choose w hw using hdvd
  have hy : (Polynomial.X - Polynomial.C x) • w = y.val := by
    funext i
    exact (hw i).symm
  have hwker : A *ᵥ w = 0 := by
    have hh : (Polynomial.X - Polynomial.C x) • (A *ᵥ w) = 0 := by
      rw [← Matrix.mulVec_smul, hy]
      exact y.property
    exact (smul_eq_zero.mp hh).resolve_left (Polynomial.X_sub_C_ne_zero x)
  let w' : LinearMap.ker (Matrix.toLin' A) := ⟨w, hwker⟩
  have hys : y = (Polynomial.X - Polynomial.C x) • w' := Subtype.ext hy.symm
  have hcoord : (fun j => Polynomial.C (c j)) =
      (Polynomial.X - Polynomial.C x) • B.equivFun w' := by
    have hh := congrArg B.equivFun hys
    simpa only [y, LinearEquiv.apply_symm_apply, map_smul] using hh
  funext j
  have hh := congrArg (Polynomial.eval x) (congrFun hcoord j)
  simpa using hh

theorem polynomial_kernel_has_finite_basis (A : Matrix a b K[X]) :
    ∃ r : ℕ, Nonempty (Basis (Fin r) K[X] (LinearMap.ker (Matrix.toLin' A))) :=
  Submodule.nonempty_basis_of_pid (Pi.basisFun K[X] b) _

end FD56
