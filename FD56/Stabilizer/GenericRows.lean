/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericLeading
import FD56.LinearAlgebra.CoefficientMatrix
import FD56.LinearAlgebra.AffineProduct

/-! Generic affine rectangular matrices with more columns than rows have
polynomial right inverses of degree at most the number of rows minus one. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {R K a b : Type*} [CommRing R] [Field K]

def affineMatrixPencil (A B : Matrix a b R) : Matrix a b R[X] :=
  fun i j => Polynomial.C (A i j) + Polynomial.X * Polynomial.C (B i j)

theorem affineMatrixPencil_degree (A B : Matrix a b K) :
    DegreeBound (affineMatrixPencil A B) 1 := by
  intro i j
  apply Polynomial.natDegree_add_le_of_degree_le
  · simp
  · exact Polynomial.natDegree_mul_le.trans (by simp)

theorem affineMatrixPencil_coefficients (P : Matrix a b K[X]) (hP : DegreeBound P 1) :
    affineMatrixPencil (fun i j => (P i j).coeff 0) (fun i j => (P i j).coeff 1) = P := by
  funext i j
  apply Polynomial.ext
  intro k
  rcases k with _ | k
  · simp [affineMatrixPencil]
  · rcases k with _ | k
    · simp [affineMatrixPencil]
    · have hz : (P i j).coeff (k + 2) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hP i j) (by omega))
      simp [affineMatrixPencil, hz]

def universalAffineRows (K n m : Type*) [CommRing K] :
    Matrix m n (MvPolynomial (MatrixParameters n m ⊕ MatrixParameters n m) K)[X] :=
  affineMatrixPencil
    (fun i j => MvPolynomial.X (Sum.inl (Sum.inr (i, j))))
    (fun i j => MvPolynomial.X (Sum.inr (Sum.inr (i, j))))

def affineRowsSpecialization (A B : Matrix a b K) :
    MvPolynomial (MatrixParameters b a ⊕ MatrixParameters b a) K →+* K :=
  MvPolynomial.eval₂Hom (RingHom.id K)
    (Sum.elim (Sum.elim (fun _ => 0) (fun ij => A ij.1 ij.2))
      (Sum.elim (fun _ => 0) (fun ij => B ij.1 ij.2)))

theorem universalAffineRows_specialization (A B : Matrix a b K) :
    (universalAffineRows K b a).map (Polynomial.mapRingHom (affineRowsSpecialization A B)) =
      affineMatrixPencil A B := by
  funext i j
  simp [universalAffineRows, affineMatrixPencil, affineRowsSpecialization]

theorem universalAffineRows_generic (K n m : Type*) [Field K] :
    (universalAffineRows K n m).map (Polynomial.mapRingHom
      (algebraMap (MvPolynomial (MatrixParameters n m ⊕ MatrixParameters n m) K)
        (AffineCoefficientField K (MatrixParameters n m)))) = genericAffineRows K n m := by
  funext i j
  simp [universalAffineRows, affineMatrixPencil, genericAffineRows, universalRows,
    affineParameterMap]

theorem universal_affine_rows_coefficient_of_witness {F : Type*} [Field F]
    [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (P : Matrix a b K[X]) (d : ℕ) (hP : DegreeBound P 1)
    (hs : Function.Surjective (polynomialCoefficientMatrix P d).mulVec)
    (φ : MvPolynomial (MatrixParameters b a ⊕ MatrixParameters b a) K →+* F)
    (hφ : Function.Injective φ) :
    Function.Surjective (polynomialCoefficientMatrix
      ((universalAffineRows K b a).map (Polynomial.mapRingHom φ)) d).mulVec := by
  classical
  let A : Matrix a b K := fun i j => (P i j).coeff 0
  let B : Matrix a b K := fun i j => (P i j).coeff 1
  let ψ := affineRowsSpecialization A B
  have he : (universalAffineRows K b a).map
      (Polynomial.mapRingHom ψ) = P := by
    rw [universalAffineRows_specialization]
    exact affineMatrixPencil_coefficients P hP
  rw [polynomialCoefficientMatrix_map]
  apply matrix_surjective_of_specialization MvPolynomial.C ψ
    (fun c => by simp [ψ, affineRowsSpecialization]) φ hφ
  rw [← polynomialCoefficientMatrix_map, he]
  exact hs

theorem universal_affine_rows_coefficient_of_sizes {F : Type*} [Field F]
    [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (ha : 0 < Fintype.card a) (hab : Fintype.card a < Fintype.card b)
    (φ : MvPolynomial (MatrixParameters b a ⊕ MatrixParameters b a) K →+* F)
    (hφ : Function.Injective φ) :
    Function.Surjective (polynomialCoefficientMatrix
      ((universalAffineRows K b a).map (Polynomial.mapRingHom φ))
        (Fintype.card a - 1)).mulVec := by
  let d := Fintype.card a - 1
  let c := Fintype.card b - (d + 2)
  let er : a ≃ Fin (d + 1) := Fintype.equivOfCardEq (by simp; dsimp [d]; omega)
  let ec : b ≃ (Fin (d + 2) ⊕ Fin c) :=
    Fintype.equivOfCardEq (by simp; dsimp [c, d]; omega)
  let P : Matrix (Fin (d + 1)) (Fin (d + 2) ⊕ Fin c) K[X] :=
    appendColumnMatrix (bidiagonalPencil (d + 1)) 0
  have hP : DegreeBound P 1 := by
    intro i j
    rcases j with j | j
    · exact bidiagonalPencil_degree _ i j
    · exact Nat.zero_le 1
  apply universal_affine_rows_coefficient_of_witness (P.submatrix er ec) d
    (fun i j => hP (er i) (ec j)) _ φ hφ
  apply coefficient_matrix_surjective_reindex P er ec d
  exact coefficient_matrix_surjective_append _ 0 d (bidiagonal_coefficient_matrix_surjective d)

theorem generic_affine_rows_right_inverse_of_sizes (K a b : Type*) [Field K]
    [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (ha : 0 < Fintype.card a) (hab : Fintype.card a < Fintype.card b) :
    ∃ Q : Matrix b a (Polynomial (AffineCoefficientField K (MatrixParameters b a))),
      DegreeBound Q (Fintype.card a - 1) ∧
        (show Matrix a a (Polynomial (AffineCoefficientField K (MatrixParameters b a)))
          from genericAffineRows K b a * Q) = 1 := by
  apply polynomial_right_inverse_of_coefficient_surjective _ (Fintype.card a - 1)
    (genericAffineRows_degree K _ _)
  rw [← universalAffineRows_generic]
  exact universal_affine_rows_coefficient_of_sizes ha hab (algebraMap _ _)
    (IsFractionRing.injective _ _)

theorem generic_affine_rows_pointwise_of_sizes (K a b : Type*) [Field K]
    [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (ha : 0 < Fintype.card a) (hab : Fintype.card a < Fintype.card b)
    {F : Type*} [Field F]
    (φ : Polynomial (AffineCoefficientField K (MatrixParameters b a)) →+* F) :
    Function.Surjective ((genericAffineRows K b a).map φ).mulVec := by
  obtain ⟨Q, _, hQ⟩ := generic_affine_rows_right_inverse_of_sizes K a b ha hab
  exact polynomial_right_inverse_pointwise _ Q hQ φ

theorem universal_rows_surjective_of_sizes {F : Type*} [Field F]
    [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (hab : Fintype.card a ≤ Fintype.card b)
    (φ : MvPolynomial (MatrixParameters b a) K →+* F) (hφ : Function.Injective φ) :
    Function.Surjective ((universalRows K b a).map φ).mulVec := by
  classical
  let e : a ↪ b := Classical.choice (Function.Embedding.nonempty_of_card_le hab)
  let P : Matrix a b K := fun i j => if j = e i then 1 else 0
  have hs : Function.Surjective P.mulVec := by
    intro y
    refine ⟨Function.extend e y 0, ?_⟩
    funext i
    simpa [P, Matrix.mulVec, dotProduct] using e.injective.extend_apply y 0 i
  have he := universal_pair_specialization (0 : Matrix b b K) P
  apply matrix_surjective_of_specialization MvPolynomial.C (matrixSpecialization 0 P)
    (fun c => by simp [matrixSpecialization]) φ hφ
  rw [he.2]
  exact hs

theorem generic_affine_rows_leading_surjective (K a b : Type*) [Field K]
    [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (hab : Fintype.card a ≤ Fintype.card b) :
    Function.Surjective (matrixCoeff (genericAffineRows K b a) 1).mulVec := by
  rw [(genericAffine_leading_pair K b a).2]
  exact universal_rows_surjective_of_sizes hab (affineLeadingParameterMap K _)
    (affineLeadingParameterMap_injective K _)

theorem generic_affine_coefficient_columns_injective (K n m : Type*) [Field K]
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (hnm : 2 * Fintype.card n ≤ Fintype.card m) :
    Function.Injective (affineCoefficientColumns (genericAffineRows K n m)).mulVec := by
  classical
  let e : (n ⊕ n) ↪ m := Classical.choice
    (Function.Embedding.nonempty_of_card_le (by simpa [two_mul] using hnm))
  let E : Matrix (n ⊕ n) m K := fun i j => if j = e i then 1 else 0
  have hs : Function.Surjective E.mulVec := by
    intro y
    refine ⟨Function.extend e y 0, ?_⟩
    funext i
    simpa [E, Matrix.mulVec, dotProduct] using e.injective.extend_apply y 0 i
  let A : Matrix m n K := fun i j => E (.inl j) i
  let B : Matrix m n K := fun i j => E (.inr j) i
  let ψ := affineRowsSpecialization A B
  let J : Matrix m (n ⊕ n)
      (MvPolynomial (MatrixParameters n m ⊕ MatrixParameters n m) K) :=
    fun i j => Sum.elim
      (fun j => MvPolynomial.X (Sum.inl (Sum.inr (i, j))))
      (fun j => MvPolynomial.X (Sum.inr (Sum.inr (i, j)))) j
  have he : J.map ψ = E.transpose := by
    funext i j
    cases j <;> simp [J, ψ, affineRowsSpecialization, A, B, Matrix.transpose_apply]
  have hg : J.map (algebraMap _ (AffineCoefficientField K (MatrixParameters n m))) =
      affineCoefficientColumns (genericAffineRows K n m) := by
    funext i j
    cases j <;> simp [J, affineCoefficientColumns, genericAffineRows, universalRows, affineParameterMap]
  rw [← hg]
  apply matrix_injective_of_specialization MvPolynomial.C ψ
    (fun c => by simp [ψ, affineRowsSpecialization]) (algebraMap _ _)
      (IsFractionRing.injective _ _)
  rw [he]
  exact matrix_transpose_injective_of_surjective E hs

end FD56
