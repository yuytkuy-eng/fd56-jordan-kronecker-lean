/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.FourOutputInteriorMinors
import FD56.LinearAlgebra.PluckerOutputActionTransport
import FD56.LinearAlgebra.PolynomialKernelCompletion

/-! A polynomial terminal matrix with a left inverse and an actual two-column
dual kernel basis has the full weighted Plucker output-action image. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem pluckerOutputChange_standard_eq_minors {R : Type*} [CommRing R]
    (Q : Matrix (Fin 4) (Fin 4) R) :
    pluckerOutputChange Q standardPluckerPoint=
      fourOutputPluckerVector (Q.submatrix id (fun j : Fin 2 => j.castAdd 2)) := by
  ext i
  fin_cases i <;>
    simp [pluckerOutputChange,pluckerUpperCoordinates,pluckerSkewMatrix,standardPluckerPoint,
      fourOutputPluckerVector,fourOutputPluckerRows,pluckerMinorVector,
      Matrix.det_fin_two,Matrix.mul_apply,Fin.sum_univ_succ] <;> ring

variable {K : Type*} [Field K]

theorem fourOutputTerminal_completion
    (G : Matrix (Fin 4) (Fin 2) K[X]) (L : Matrix (Fin 2) (Fin 4) K[X])
    (hLG : L*G=1)
    (B : Basis (Fin 2) K[X] (LinearMap.ker (Matrix.toLin' G.transpose))) :
    ∃ Q S : Matrix (Fin 4) (Fin 4) K[X], Q*S=1 ∧ S*Q=1 ∧
      Q.submatrix id (fun j : Fin 2 => j.castAdd 2)=G := by
  have hGL : G.transpose*L.transpose=1 := by
    rw [← Matrix.transpose_mul,hLG,Matrix.transpose_one]
  obtain ⟨U,_,_,_,hJH,hHJ⟩ := polynomial_kernel_basis_completion G.transpose L.transpose hGL B
  let T := polynomialKernelBasisMatrix G.transpose B
  let e : Fin 4 ≃ Fin 2 ⊕ Fin 2 :=
    (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin (2+2)).symm
  let Q : Matrix (Fin 4) (Fin 4) K[X] := (Matrix.fromCols G U.transpose).submatrix id e
  let S : Matrix (Fin 4) (Fin 4) K[X] := (Matrix.fromRows L T.transpose).submatrix e id
  have hraw : Matrix.fromCols G U.transpose*Matrix.fromRows L T.transpose=1 := by
    simpa only [Matrix.transpose_mul,Matrix.transpose_fromRows,Matrix.transpose_fromCols,
      Matrix.transpose_transpose,Matrix.transpose_one] using congrArg Matrix.transpose hHJ
  have hreverse : Matrix.fromRows L T.transpose*Matrix.fromCols G U.transpose=1 := by
    simpa only [Matrix.transpose_mul,Matrix.transpose_fromRows,Matrix.transpose_fromCols,
      Matrix.transpose_transpose,Matrix.transpose_one] using congrArg Matrix.transpose hJH
  refine ⟨Q,S,?_,?_,?_⟩
  · dsimp only [Q,S]
    rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_id_id]
    exact hraw
  · dsimp only [Q,S]
    rw [← Matrix.submatrix_mul _ _ e id e Function.bijective_id,hreverse]
    exact Matrix.submatrix_one_equiv e
  · funext i j
    change Matrix.fromCols G U.transpose i (e (j.castAdd 2))=G i j
    have he : e (j.castAdd 2)=Sum.inl j :=
      finSumFinEquiv_symm_apply_castAdd (n:=2) j
    rw [he]
    rfl

theorem fourOutputTerminal_output_action_range (q : ℕ)
    (G : Matrix (Fin 4) (Fin 2) K[X]) (L : Matrix (Fin 2) (Fin 4) K[X])
    (hLG : L*G=1)
    (B : Basis (Fin 2) K[X] (LinearMap.ker (Matrix.toLin' G.transpose)))
    (H : Fin 6 → K[X]) :
    (∃ A : Matrix (Fin 4) (Fin 4) K[X],
      pluckerOutputAction q (fourOutputPluckerVector G) A=H) ↔
      pluckerQuadricPolar (fourOutputPluckerVector G) H=0 := by
  obtain ⟨Q,S,hQS,hSQ,hQG⟩ := fourOutputTerminal_completion G L hLG B
  have h := pluckerOutputAction_range_of_inverse q Q S hQS hSQ H
  rw [pluckerOutputChange_standard_eq_minors,hQG] at h
  exact h

end FD56
