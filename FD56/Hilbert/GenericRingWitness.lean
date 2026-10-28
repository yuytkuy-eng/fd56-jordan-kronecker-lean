/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericKernelExtension

/-! Generic SL bounds from certificates over another characteristic. The
coefficient ring embeds in the target field; the witness field need not. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {R K F n m : Type*} [CommRing R] [Field K] [Field F]
  [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

theorem slHilbert_le_of_injective_specialization
    (φ : R →+* K) (ψ : R →+* F) (hφ : Function.Injective φ)
    (M : Matrix n n R[X]) (P : Matrix m n R[X])
    (hMK : DegreeBound (M.map (Polynomial.mapRingHom φ)) 1)
    (hPK : DegreeBound (P.map (Polynomial.mapRingHom φ)) 1)
    (hMF : DegreeBound (M.map (Polynomial.mapRingHom ψ)) 1)
    (hPF : DegreeBound (P.map (Polynomial.mapRingHom ψ)) 1)
    (i₀ : n) (d : ℕ) :
    slHilbert (M.map (Polynomial.mapRingHom φ)) (P.map (Polynomial.mapRingHom φ)) d ≤
      slHilbert (M.map (Polynomial.mapRingHom ψ)) (P.map (Polynomial.mapRingHom ψ)) d := by
  rw [slHilbert_eq_matrix_kernel _ _ i₀ d, slHilbert_eq_matrix_kernel _ _ i₀ d]
  have h := polynomial_kernel_finrank_le_of_field_specialization ψ φ hφ
    (slEquationMatrix M P i₀) d
    (by rw [slEquationMatrix_map]; exact slEquationMatrix_degree _ _ i₀ hMF hPF)
    (by rw [slEquationMatrix_map]; exact slEquationMatrix_degree _ _ i₀ hMK hPK)
  rw [slEquationMatrix_map, slEquationMatrix_map] at h
  exact h

theorem generic_slHilbert_le_ring_witness
    (φ : R →+* K) (ψ : R →+* F) (hφ : Function.Injective φ)
    (M : Matrix n n R[X]) (P : Matrix m n R[X])
    (hMK : DegreeBound (M.map (Polynomial.mapRingHom φ)) 1)
    (hPK : DegreeBound (P.map (Polynomial.mapRingHom φ)) 1)
    (hMF : DegreeBound (M.map (Polynomial.mapRingHom ψ)) 1)
    (hPF : DegreeBound (P.map (Polynomial.mapRingHom ψ)) 1)
    (i₀ : n) (d : ℕ) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d ≤
      slHilbert (M.map (Polynomial.mapRingHom ψ)) (P.map (Polynomial.mapRingHom ψ)) d :=
  (generic_slHilbert_le_field_witness (RingHom.id K) _ _ hMK hPK i₀ d).trans
    (slHilbert_le_of_injective_specialization φ ψ hφ M P hMK hPK hMF hPF i₀ d)

theorem affineMatrixPencil_mapRingHom {S a b : Type*} [CommRing S]
    (φ : R →+* S) (A B : Matrix a b R) :
    (affineMatrixPencil A B).map (Polynomial.mapRingHom φ) =
      affineMatrixPencil (A.map φ) (B.map φ) := by
  ext i j
  simp [affineMatrixPencil]

/-- An integral affine witness over any field bounds the generic Hilbert
function in characteristic zero, including when the witness has finite characteristic. -/
theorem generic_slHilbert_le_integer_affine_witness [CharZero K]
    (M₀ M₁ : Matrix n n ℤ) (P₀ P₁ : Matrix m n ℤ) (i₀ : n) (d : ℕ) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d ≤
      slHilbert
        (affineMatrixPencil (M₀.map (Int.castRingHom F)) (M₁.map (Int.castRingHom F)))
        (affineMatrixPencil (P₀.map (Int.castRingHom F)) (P₁.map (Int.castRingHom F))) d := by
  have h := generic_slHilbert_le_ring_witness (Int.castRingHom K) (Int.castRingHom F)
    (show Function.Injective (Int.castRingHom K) from Int.cast_injective)
    (affineMatrixPencil M₀ M₁) (affineMatrixPencil P₀ P₁)
    (by rw [affineMatrixPencil_mapRingHom]; exact affineMatrixPencil_degree _ _)
    (by rw [affineMatrixPencil_mapRingHom]; exact affineMatrixPencil_degree _ _)
    (by rw [affineMatrixPencil_mapRingHom]; exact affineMatrixPencil_degree _ _)
    (by rw [affineMatrixPencil_mapRingHom]; exact affineMatrixPencil_degree _ _) i₀ d
  rw [affineMatrixPencil_mapRingHom, affineMatrixPencil_mapRingHom] at h
  exact h

end FD56
