/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.SquareGLDiagonalPoles

/-! A full constant Jordan decomposition of the actual diagonal square GL
Kirillov pencil when every resonant column has a nonzero off-diagonal entry. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

def squareGLJordanIndex (j : n → n) :=
  Σ i : n, (Fin 2 ⊕ Fin 2) ⊕ ((Fin 1 ⊕ Fin 1) × {k : n // k≠i ∧ k≠j i})

instance (j : n → n) : Fintype (squareGLJordanIndex j) := inferInstanceAs (Fintype (Sigma _))
instance (j : n → n) : DecidableEq (squareGLJordanIndex j) := inferInstanceAs (DecidableEq (Sigma _))

def squareGLJordanTarget (lam : n → K) (j : n → n) :
    Matrix (squareGLJordanIndex j) (squareGLJordanIndex j) K[X] :=
  Matrix.blockDiagonal' (fun i => rankTwoRegularTarget (n := {k : n // k≠i ∧ k≠j i}) (lam i))

def squareGLSigmaIndex (n : Type*) : ((n ⊕ n) × n) ≃ (Σ _ : n, n ⊕ n) where
  toFun x := ⟨x.2,x.1⟩
  invFun x := (x.2,x.1)
  left_inv _ := rfl
  right_inv _ := rfl

theorem squareGL_diagonal_jordan_decomposition (lam : n → K) (hlam : Function.Injective lam)
    (A B : Matrix n n K) (j : n → n) (hj : ∀ i, i≠j i)
    (hres : ∀ i, A (j i) i + lam i*B (j i) i ≠ 0) :
    ∃ T : Matrix (SLInput n n) (squareGLJordanIndex j) K,
    ∃ S : Matrix (squareGLJordanIndex j) (SLInput n n) K,
      T*S=1 ∧ S*T=1 ∧
      (T.map C).transpose * glKirillovMatrix (affineMatrixPencil A B)
          (Matrix.diagonal (fun i => X-C (lam i))) * T.map C = squareGLJordanTarget lam j := by
  let H := fun i => pairedCoupling
    ((starCoupling i (fun k => -(A k i+lam i*B k i))).map C) (X-C (lam i))
  have hlocal (i : n) := starCoupling_constant_decomposition i (j i) (hj i)
    (fun k => -(A k i+lam i*B k i)) (neg_ne_zero.mpr (hres i)) (lam i)
  choose U V hUV hVU hlocalCong using hlocal
  let e := squareGLSigmaIndex n
  let P := (Matrix.blockDiagonal' U).submatrix e id
  let Q := (Matrix.blockDiagonal' V).submatrix id e
  have hPQ : P*Q=1 := by
    change (Matrix.blockDiagonal' U).submatrix e (Equiv.refl _) *
      (Matrix.blockDiagonal' V).submatrix (Equiv.refl _) e = 1
    rw [Matrix.submatrix_mul_equiv,← Matrix.blockDiagonal'_mul]
    rw [show (fun k => U k*V k) = (1 : ∀ _ : n, Matrix (n ⊕ n) (n ⊕ n) K)
      from funext hUV,Matrix.blockDiagonal'_one]
    exact Matrix.submatrix_one_equiv e
  have hQP : Q*P=1 := by
    dsimp [P,Q]
    rw [Matrix.submatrix_mul_equiv,← Matrix.blockDiagonal'_mul]
    rw [show (fun k => V k*U k) =
      (1 : ∀ i : n, Matrix ((Fin 2 ⊕ Fin 2) ⊕ ((Fin 1 ⊕ Fin 1) × {k : n // k≠i ∧ k≠j i}))
        ((Fin 2 ⊕ Fin 2) ⊕ ((Fin 1 ⊕ Fin 1) × {k : n // k≠i ∧ k≠j i})) K)
      from funext hVU,Matrix.blockDiagonal'_one,Matrix.submatrix_id_id]
  have hglobal : (P.map C).transpose * Matrix.blockDiagonal H * P.map C =
      squareGLJordanTarget lam j := by
    change ((Matrix.blockDiagonal' U).map C).transpose.submatrix id e *
      (Matrix.blockDiagonal' H).submatrix e e *
      ((Matrix.blockDiagonal' U).map C).submatrix e id = _
    rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv,Matrix.submatrix_id_id,
      Matrix.blockDiagonal'_map _ _ (map_zero C),Matrix.blockDiagonal'_transpose,
      ← Matrix.blockDiagonal'_mul,← Matrix.blockDiagonal'_mul]
    exact congrArg Matrix.blockDiagonal' (funext hlocalCong)
  obtain ⟨T₀,S₀,hTS₀,hST₀,hcong₀⟩ := squareGL_diagonal_pole_decomposition lam hlam A B
  refine ⟨T₀*P,Q*S₀,?_,?_,?_⟩
  · rw [Matrix.mul_assoc,← Matrix.mul_assoc P,hPQ,Matrix.one_mul,hTS₀]
  · rw [Matrix.mul_assoc,← Matrix.mul_assoc S₀,hST₀,Matrix.one_mul,hQP]
  · rw [Matrix.map_mul,Matrix.transpose_mul]
    calc
      _ = (P.map C).transpose *
          ((T₀.map C).transpose * glKirillovMatrix (affineMatrixPencil A B)
            (Matrix.diagonal (fun i => X-C (lam i))) * T₀.map C) * P.map C := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hcong₀]; exact hglobal

end FD56
