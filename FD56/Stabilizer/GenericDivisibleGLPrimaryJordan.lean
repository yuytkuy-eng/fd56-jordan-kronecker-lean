/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.PolynomialPrimaryJordan
import FD56.Stabilizer.GenericDivisibleGLPrimary

/-! Each primary restriction of the generic divisible GL pencil has explicit Jordan blocks. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K L : Type*} {m : Type} [Field K] [Field L] [Fintype m] [DecidableEq m]

theorem generic_divisible_gl_primary_jordan (q : ℕ) (hm : 2≤Fintype.card m)
    (φ : AffineCoefficientField K (MatrixParameters (Fin (q+1) × m) m) →+* L) (x : L)
    (hx : (glKirillovMatrix (genericAffineSquare K (Fin (q+1) × m) m)
      (genericAffineRows K (Fin (q+1) × m) m)).det.eval₂ φ x=0) :
    let H := (glKirillovMatrix (genericAffineSquare K (Fin (q+1) × m) m)
      (genericAffineRows K (Fin (q+1) × m) m)).map (Polynomial.mapRingHom φ)
    let f := polynomialPencilOperator H
    ∃ b : Basis (Fin (2*Fintype.card m)) L (f.maxGenEigenspace x),
    ∃ T : Matrix (Fin (2*Fintype.card m)) (rankTwoJordanIndex (Fintype.card m-2)) L,
    ∃ U : Matrix (rankTwoJordanIndex (Fintype.card m-2)) (Fin (2*Fintype.card m)) L,
      T*U=1 ∧ U*T=1 ∧
      (((subspaceBasisColumns _ b)*T).map C).transpose*H*((subspaceBasisColumns _ b)*T).map C=
        rankTwoJordanPencil x (Fintype.card m-2) := by
  let M := genericAffineSquare K (Fin (q+1) × m) m
  let P := genericAffineRows K (Fin (q+1) × m) m
  let H := glKirillovMatrix M P
  let H' := H.map (Polynomial.mapRingHom φ)
  let f := polynomialPencilOperator H'
  obtain ⟨hdim,_,hr⟩ := generic_divisible_gl_primary_data q hm φ x hx
  let b : Basis (Fin (2*Fintype.card m)) L (f.maxGenEigenspace x) :=
    Module.finBasisOfFinrankEq L _ hdim
  refine ⟨b,?_⟩
  have hH : DegreeBound H 1 := glKirillovMatrix_degreeBound M P 1
    (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _)
  have hH' : DegreeBound H' 1 := fun i j => Polynomial.natDegree_map_le.trans (hH i j)
  have hc (k : ℕ) : (fun i j => (H' i j).coeff k)=Matrix.map (fun i j => (H i j).coeff k) φ := by
    funext i j
    simp [H',Matrix.map_apply,Polynomial.coe_mapRingHom,Polynomial.coeff_map]
  have halt (k : ℕ) : ∀ v, v ⬝ᵥ ((fun i j => (H' i j).coeff k) *ᵥ v)=0 := by
    rw [hc]
    exact matrix_alternating_map φ _ (glKirillovMatrix_coefficient_alternating M P k)
  have hlead : Matrix.det (fun i j => (H' i j).coeff 1)≠0 := by
    rw [hc]
    have he := φ.map_det (fun i j => (H i j).coeff 1)
    intro hz
    apply generic_divisible_gl_leading_det_ne_zero K m (q+1)
    exact φ.injective ((he.trans hz).trans (map_zero φ).symm)
  exact polynomial_primary_jordan_decomposition H' hH' (halt 0) (halt 1) hlead
    x (Fintype.card m) (Fintype.card_fin _) hr b

end FD56
