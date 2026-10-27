/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialPencilPrimaryData
import FD56.Stabilizer.GenericDivisibleGLRoot

/-! Every primary component of a divisible generic GL pencil has a rank-two nilpotent shift. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K L : Type*} {m : Type} [Field K] [Field L] [Fintype m] [DecidableEq m]

theorem generic_divisible_gl_primary_data (q : ℕ) (hm : 2≤Fintype.card m)
    (φ : AffineCoefficientField K (MatrixParameters (Fin (q+1) × m) m) →+* L) (x : L)
    (hx : (glKirillovMatrix (genericAffineSquare K (Fin (q+1) × m) m)
      (genericAffineRows K (Fin (q+1) × m) m)).det.eval₂ φ x=0) :
    let H := (glKirillovMatrix (genericAffineSquare K (Fin (q+1) × m) m)
      (genericAffineRows K (Fin (q+1) × m) m)).map (Polynomial.mapRingHom φ)
    let f := polynomialPencilOperator H
    Module.finrank L (f.maxGenEigenspace x)=2*Fintype.card m ∧
      IsNilpotent (primaryShift f x) ∧
      Module.finrank L (LinearMap.range (primaryShift f x))=2 := by
  let H := glKirillovMatrix (genericAffineSquare K (Fin (q+1) × m) m)
    (genericAffineRows K (Fin (q+1) × m) m)
  let H' := H.map (Polynomial.mapRingHom φ)
  have hH : DegreeBound H 1 := glKirillovMatrix_degreeBound _ _ 1
    (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _)
  have hH' : DegreeBound H' 1 := fun i j => Polynomial.natDegree_map_le.trans (hH i j)
  have hc : (fun i j => (H' i j).coeff 1)=Matrix.map (fun i j => (H i j).coeff 1) φ := by
    funext i j
    simp [H',Matrix.map_apply,Polynomial.coe_mapRingHom,Polynomial.coeff_map]
  have hlead : Matrix.det (fun i j => (H' i j).coeff 1)≠0 := by
    rw [hc]
    have he := φ.map_det (fun i j => (H i j).coeff 1)
    intro hz
    apply generic_divisible_gl_leading_det_ne_zero K m (q+1)
    exact φ.injective ((he.trans hz).trans (map_zero φ).symm)
  obtain ⟨hker,hmult⟩ := generic_divisible_gl_pole_nullity_and_order q hm φ x hx
  have hdet : H'.det=H.det.map φ := ((Polynomial.mapRingHom φ).map_det H).symm
  have heval : H'.map (Polynomial.evalRingHom x)=H.map (Polynomial.eval₂RingHom φ x) := by
    funext i j
    simp [H',Matrix.map_apply,Polynomial.eval_map]
  apply polynomial_pencil_primary_rank_two H' hH' hlead x (Fintype.card m) (by omega)
  · rw [hdet]
    exact hmult
  · rw [heval]
    exact hker

end FD56
