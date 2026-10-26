/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.SplittingMatrixDiagonalization
import FD56.Stabilizer.WideObservabilityDiagonalization

/-! Coprimality of maximal column minors of every strictly wide universal observability stack. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K] {n m : ℕ}

theorem universal_wide_observability_common_divisor_isUnit (q : ℕ) (h : q*m < n+1)
    (g : MvPolynomial (MatrixParameters (Fin (n+1)) (Fin m)) K)
    (hd : ∀ r : Fin q × Fin m → Fin (n+1),
      g ∣ ((observabilityMatrix (universalSquare K (Fin (n+1)) (Fin m))
        (universalRows K (Fin (n+1)) (Fin m)) q).submatrix id r).det) : IsUnit g := by
  let R := MvPolynomial (Fin (n+1) × Fin (n+1)) K
  let F := FractionRing R
  let ι : R →+* F := algebraMap R F
  let M : Matrix (Fin (n+1)) (Fin (n+1)) F := (Matrix.mvPolynomialX _ _ K).map ι
  have hsep : M.charpoly.Separable :=
    universal_matrix_charpoly_separable ι (IsFractionRing.injective R F)
  let L := M.charpoly.SplittingField
  let φ : R →+* L := (algebraMap F L).comp ι
  have hφ : Function.Injective φ :=
    (algebraMap F L).injective.comp (IsFractionRing.injective R F)
  obtain ⟨S,T,ev,hev,hST,hTS,hMS⟩ := exists_splitting_field_diagonalization M hsep
  apply universal_wide_coprime_of_diagonalization q h φ hφ S T hST hTS ev hev ?_ g hd
  convert hMS using 1

end FD56
