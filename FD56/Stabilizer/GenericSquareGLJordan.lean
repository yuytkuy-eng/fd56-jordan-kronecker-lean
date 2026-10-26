/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.IndependentSquareGLJordan
import FD56.Stabilizer.SquareGLCoefficientExtension

/-! The original generic square GL pencil has the claimed Jordan blocks after
an injective row-coefficient extension with a simple eigenbasis. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem glKirillovMatrix_map {R E n m : Type*} [CommRing R] [CommRing E]
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (phi : R →+* E) (M : Matrix n n R) (P : Matrix m n R) :
    (glKirillovMatrix M P).map phi = glKirillovMatrix (M.map phi) (P.map phi) := by
  rw [glKirillovMatrix,← Matrix.submatrix_map,glEquationMatrix_map]
  rfl

variable {K L n : Type*} [Field K] [Field L] [Fintype n] [DecidableEq n] [Nontrivial n]

def genericSquareRowConstant (phi : MvPolynomial ((n × n) ⊕ (n × n)) K →+* L) : Matrix n n L :=
  fun i j => phi (MvPolynomial.X (.inl (i,j)))

def genericSquareRowLeading (phi : MvPolynomial ((n × n) ⊕ (n × n)) K →+* L) : Matrix n n L :=
  fun i j => phi (MvPolynomial.X (.inr (i,j)))

theorem generic_square_gl_jordan_of_row_diagonalization
    (phi : MvPolynomial ((n × n) ⊕ (n × n)) K →+* L) (hphi : Function.Injective phi)
    (V S T : Matrix n n L) (hST : S*T=1) (hTS : T*S=1)
    (hP₁V : genericSquareRowLeading phi*V=1) (hVP₁ : V*genericSquareRowLeading phi=1)
    (lam : n → L) (hlam : Function.Injective lam)
    (hdiag : (-V*genericSquareRowConstant phi)*S=S*Matrix.diagonal lam) :
    let kappa : L →+* SquareGLIndependentField L n :=
      (algebraMap (MvPolynomial ((n × n) ⊕ (n × n)) L) (SquareGLIndependentField L n)).comp MvPolynomial.C
    ∃ j : n → n, (∀ i, i≠j i) ∧
    ∃ G : Matrix (SLInput n n) (squareGLJordanIndex j) (SquareGLIndependentField L n),
    ∃ H : Matrix (squareGLJordanIndex j) (SLInput n n) (SquareGLIndependentField L n),
      G*H=1 ∧ H*G=1 ∧
      (G.map C).transpose *
          (glKirillovMatrix (genericAffineSquare K n n) (genericAffineRows K n n)).map
            (Polynomial.mapRingHom (squareGenericFieldMap phi hphi)) * G.map C =
        squareGLJordanTarget (fun i => kappa (lam i)) j := by
  intro kappa
  simp_rw [glKirillovMatrix_map,squareGenericFieldMap_state_pencil,squareGenericFieldMap_row_pencil]
  exact independent_squareGL_jordan_decomposition
    (algebraMap (MvPolynomial ((n × n) ⊕ (n × n)) L) (SquareGLIndependentField L n))
    (IsFractionRing.injective _ _) (genericSquareRowConstant phi) (genericSquareRowLeading phi)
    V S T hST hTS hP₁V hVP₁ lam hlam hdiag

end FD56
