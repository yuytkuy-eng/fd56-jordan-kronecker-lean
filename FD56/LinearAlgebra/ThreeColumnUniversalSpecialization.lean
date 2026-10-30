/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.ThreeColumnUniversalFrame

/-! Coefficient evaluation realizes every three-column frame within a common
degree bound, together with all of its maximal minors. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
variable {K L n : Type*} [Field K] [Field L] [Algebra K L]

def threeColumnCoefficientEvaluation (h : ℕ) (G : Matrix n (Fin 3) L[X]) :
    ThreeColumnCoefficientRing K n h →ₐ[K] L :=
  MvPolynomial.aeval (fun z => (G z.1 z.2.1).coeff z.2.2.val)

theorem threeColumnCoefficientEvaluation_frame (h : ℕ) (G : Matrix n (Fin 3) L[X])
    (hG : ∀ i j, (G i j).natDegree≤h) (i : n) (j : Fin 3) :
    (threeColumnUniversalFrame K n h i j).map
      (threeColumnCoefficientEvaluation (K:=K) h G).toRingHom=G i j := by
  apply Polynomial.ext
  intro k
  by_cases hk : k≤h
  · have hc := threeColumnUniversalFrame_coeff K n h i j ⟨k,by omega⟩
    rw [Polynomial.coeff_map,hc]
    simp [threeColumnCoefficientEvaluation]
  · have hleft : ((threeColumnUniversalFrame K n h i j).map
        (threeColumnCoefficientEvaluation (K:=K) h G).toRingHom).natDegree≤h :=
      natDegree_map_le.trans (threeColumnUniversalFrame_degree K n h i j)
    rw [coeff_eq_zero_of_natDegree_lt (hleft.trans_lt (by omega)),
      coeff_eq_zero_of_natDegree_lt ((hG i j).trans_lt (by omega))]

theorem threeColumnCoefficientEvaluation_minor (h : ℕ) (G : Matrix n (Fin 3) L[X])
    (hG : ∀ i j, (G i j).natDegree≤h) (row : Fin 3 → n) :
    (pluckerMinorVector (threeColumnUniversalFrame K n h) row).map
      (threeColumnCoefficientEvaluation (K:=K) h G).toRingHom=pluckerMinorVector G row := by
  let φ := (threeColumnCoefficientEvaluation (K:=K) h G).toRingHom
  have he : ((threeColumnUniversalFrame K n h).submatrix row id).map
      (Polynomial.mapRingHom φ)=G.submatrix row id := by
    apply Matrix.ext
    intro i j
    exact threeColumnCoefficientEvaluation_frame (K:=K) h G hG (row i) j
  simpa only [pluckerMinorVector,RingHom.mapMatrix_apply,he] using
    (Polynomial.mapRingHom φ).map_det ((threeColumnUniversalFrame K n h).submatrix row id)

end FD56
