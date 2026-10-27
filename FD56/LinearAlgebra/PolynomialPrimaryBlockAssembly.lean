/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PrimaryBlockAssembly
import FD56.LinearAlgebra.PrimaryPencilCoordinates

/-! Assembly of actual affine-pencil congruences on all primary spaces. -/

noncomputable section
set_option maxHeartbeats 2000000
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K]

local instance : DecidableEq K := Classical.decEq K

theorem affineMatrixPencil_blockDiagonal_dependent {a : Type*} [DecidableEq a]
    {i : a → Type*} (A B : ∀ a, Matrix (i a) (i a) K) :
    affineMatrixPencil (Matrix.blockDiagonal' A) (Matrix.blockDiagonal' B)=
      Matrix.blockDiagonal' (fun a => affineMatrixPencil (A a) (B a)) := by
  ext ⟨a,i⟩ ⟨b,j⟩
  by_cases h : a=b
  · subst b
    simp [affineMatrixPencil]
  · simp [affineMatrixPencil,Matrix.blockDiagonal'_apply_ne _ _ _ h]

theorem polynomial_primary_local_congruence_assembly
    [IsAlgClosed K] {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n K[X]) (hdeg : DegreeBound H 1)
    (hA : ∀ v : n → K, v ⬝ᵥ ((fun i j => (H i j).coeff 0) *ᵥ v)=0)
    (hB : ∀ v : n → K, v ⬝ᵥ ((fun i j => (H i j).coeff 1) *ᵥ v)=0)
    (hd : Matrix.det (fun i j => (H i j).coeff 1)≠0)
    {α β : (polynomialPencilOperator H).Eigenvalues → Type*}
    [∀ a, Fintype (α a)] [∀ a, DecidableEq (α a)]
    [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)]
    (e : ∀ a, Basis (α a) K ((polynomialPencilOperator H).maxGenEigenspace a.val))
    (T : ∀ a, Matrix (α a) (β a) K) (S : ∀ a, Matrix (β a) (α a) K)
    (J : ∀ a, Matrix (β a) (β a) K[X])
    (hTS : ∀ a, T a*S a=1) (hST : ∀ a, S a*T a=1)
    (hJ : ∀ a : (polynomialPencilOperator H).Eigenvalues,
      ((subspaceBasisColumns ((polynomialPencilOperator H).maxGenEigenspace a.val)
        (e a)*T a).map C).transpose * H *
      (subspaceBasisColumns ((polynomialPencilOperator H).maxGenEigenspace a.val)
        (e a)*T a).map C=J a) :
    ∃ U : Matrix n (Σ a, β a) K, ∃ W : Matrix (Σ a, β a) n K,
      U*W=1 ∧ W*U=1 ∧
      (U.map C).transpose*H*U.map C=Matrix.blockDiagonal' J := by
  classical
  let A : Matrix n n K := fun i j => (H i j).coeff 0
  let B : Matrix n n K := fun i j => (H i j).coeff 1
  let f := polynomialPencilOperator H
  let Q (a : f.Eigenvalues) := subspaceBasisColumns (f.maxGenEigenspace a.val) (e a)
  let G (a : f.Eigenvalues) := (T a).transpose * (Q a).transpose * B * Q a * T a
  let L (a : f.Eigenvalues) := (T a).transpose * (Q a).transpose * A * Q a * T a
  have hf : ∀ x y, B.toBilin' (f x) y=B.toBilin' x (f y) :=
    (alternating_pencil_operator_forms A B hA hB hd).2.2.2
  have hBF : B.toBilin'.compRight f = -A.toBilin' := by
    have hBA : B*(-B⁻¹*A) = -A := by
      rw [← Matrix.mul_assoc,Matrix.mul_neg,
        Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hd),Matrix.neg_mul,Matrix.one_mul]
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change B.toBilin' x (Matrix.toLin' (-B⁻¹*A) y)=-(A.toBilin' x y)
    simp only [Matrix.toBilin'_apply',Matrix.toLin'_apply]
    rw [Matrix.mulVec_mulVec,hBA,Matrix.neg_mulVec,dotProduct_neg]
  have hG (a : f.Eigenvalues) : (T a).transpose *
      BilinForm.toMatrix (e a) (B.toBilin'.restrict (f.maxGenEigenspace a.val)) * T a=G a := by
    rw [subspace_basis_bilinear_matrix]
    simp only [G,Q,f,Matrix.mul_assoc]
  have hL (a : f.Eigenvalues) : (T a).transpose *
      BilinForm.toMatrix (e a) ((B.toBilin'.compRight f).restrict
        (f.maxGenEigenspace a.val)) * T a=(-L) a := by
    rw [hBF]
    have he : BilinForm.toMatrix (e a) ((-A.toBilin').restrict
        (f.maxGenEigenspace a.val)) =
        -BilinForm.toMatrix (e a) (A.toBilin'.restrict (f.maxGenEigenspace a.val)) := by
      ext i j
      simp only [BilinForm.toMatrix_apply,Matrix.neg_apply]
      rfl
    rw [he,Matrix.mul_neg,Matrix.neg_mul,subspace_basis_bilinear_matrix]
    simp only [L,Q,f,Pi.neg_apply,Matrix.mul_assoc]
  obtain ⟨U,W,hUW,hWU,hUG,hUL⟩ := primary_local_congruence_assembly
    B.toBilin' f hf (Pi.basisFun K n) e T S G (-L) hTS hST hG hL
  have hUB : U.transpose*B*U=Matrix.blockDiagonal' G := by
    simpa only [BilinForm.toMatrix_basisFun,LinearMap.BilinForm.toMatrix'_toBilin'] using hUG
  have hUA : U.transpose*A*U=Matrix.blockDiagonal' L := by
    have hneg : BilinForm.toMatrix (Pi.basisFun K n) (-A.toBilin') = -A := by
      ext i j
      simp [BilinForm.toMatrix_apply,Pi.basisFun_apply]
    rw [hBF,hneg,Matrix.mul_neg,Matrix.neg_mul,Matrix.blockDiagonal'_neg] at hUL
    exact neg_injective hUL
  have hlocal (a : f.Eigenvalues) : affineMatrixPencil (L a) (G a)=J a := by
    calc
      _ = ((Q a*T a).map C).transpose*affineMatrixPencil A B*(Q a*T a).map C := by
        rw [affine_pencil_rectangular_congruence,Matrix.transpose_mul]
        simp only [L,G,Matrix.mul_assoc]
      _ = ((Q a*T a).map C).transpose*H*(Q a*T a).map C :=
        congrArg (fun P => ((Q a*T a).map C).transpose*P*(Q a*T a).map C)
          (affineMatrixPencil_coefficients H hdeg)
      _ = J a := hJ a
  refine ⟨U,W,hUW,hWU,?_⟩
  calc
    _ = (U.map C).transpose*affineMatrixPencil A B*U.map C :=
      congrArg (fun P => (U.map C).transpose*P*U.map C)
        (affineMatrixPencil_coefficients H hdeg).symm
    _ = _ := by
      rw [affine_pencil_rectangular_congruence,hUA,hUB,affineMatrixPencil_blockDiagonal_dependent]
      exact congrArg (fun M : ∀ a, Matrix (β a) (β a) K[X] => Matrix.blockDiagonal' M)
        (funext hlocal)

end FD56
