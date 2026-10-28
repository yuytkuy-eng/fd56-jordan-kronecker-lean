/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.FourOutputMinorOutputAction
import FD56.Hilbert.PluckerTerminalOutputAction
import FD56.Hilbert.ObservabilityTerminalLeading
import FD56.LinearAlgebra.PluckerActionRowModule
import FD56.Stabilizer.GenericMinorDifferentialImage

/-! The six actual generic observability gradients generate precisely the
polynomial tangent module of their Plucker relation. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxHeartbeats 2000000

variable {K : Type*} [Field K]

theorem generic_four_output_gradient_relation (q : ℕ) :
    pluckerPolarRow (genericFourOutputInteriorMinors (K:=K) q)*
      (fourOutputScalarLiftMatrix q
        (genericAffineSquare K (Fin (4*q+2)) (Fin 4))
        (genericAffineRows K (Fin (4*q+2)) (Fin 4))).transpose=0 := by
  classical
  let L := AffineCoefficientField K (MatrixParameters (Fin (4*q+2)) (Fin 4))
  let F := genericFourOutputInteriorMinors (K:=K) q
  let Z := fourOutputScalarLiftMatrix q
    (genericAffineSquare K (Fin (4*q+2)) (Fin 4))
    (genericAffineRows K (Fin (4*q+2)) (Fin 4))
  have hpolar (k : SLInput (Fin (4*q+2)) (Fin 4)) :
      pluckerQuadricPolar F (fun i => Z k i)=0 := by
    obtain ⟨D,hD⟩ := generic_minor_derivation_realizes_affine_pairing (K:=K)
      (fun _ : Fin 6 => interiorLevel 2 2 q) (fourOutputInteriorRow q)
      (Pi.single k 1) 0
    have hsingle : (fun j : SLInput (Fin (4*q+2)) (Fin 4) =>
        (C ((Pi.single k 1 : SLInput (Fin (4*q+2)) (Fin 4) → L) j) : L[X])+
          X*C ((0 : SLInput (Fin (4*q+2)) (Fin 4) → L) j))=
        Pi.single k (1:L[X]) := by
      funext j
      by_cases hj : j=k
      · subst j; simp
      · simp [Pi.single_apply,hj]
    have hDF (i : Fin 6) : polynomialCoefficientDerivation D (F i)=Z k i := by
      have h := hD i
      rw [hsingle] at h
      simp only [dotProduct_single,mul_one] at h
      rw [four_output_selected_matrix_fromRows] at h
      exact h
    have h := congrArg (polynomialCoefficientDerivation D)
      (generic_four_output_minors_relation (K:=K) q)
    rw [map_zero] at h
    change polynomialCoefficientDerivation D (F 0*F 5-F 1*F 4+F 2*F 3)=0 at h
    simp only [map_add,map_sub,Derivation.leibniz,smul_eq_mul,hDF] at h
    dsimp [pluckerQuadricPolar]
    linear_combination h
  funext i k
  cases i
  change (pluckerPolarRow F *ᵥ (fun j => Z k j)) ()=0
  rw [pluckerPolarRow_mulVec]
  exact hpolar k

theorem generic_four_output_gradient_row_range (q : ℕ)
    (Bv : Basis (Fin 2)
      (AffineCoefficientField K (MatrixParameters (Fin (4*q+2)) (Fin 4)))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K (Fin (4*q+2)) (Fin 4))
        (genericAffineRows K (Fin (4*q+2)) (Fin 4)) q))))
    (Bt : Basis (Fin 2)
      (AffineCoefficientField K (MatrixParameters (Fin (4*q+2)) (Fin 4)))[X]
      (LinearMap.ker (Matrix.toLin'
        (genericAffineRows K (Fin (4*q+2)) (Fin 4)*
          (genericAffineSquare K (Fin (4*q+2)) (Fin 4))^q*
          polynomialKernelBasisMatrix _ Bv).transpose))) :
    LinearMap.range (Matrix.toLin' (fourOutputScalarLiftMatrix q
      (genericAffineSquare K (Fin (4*q+2)) (Fin 4))
      (genericAffineRows K (Fin (4*q+2)) (Fin 4))).transpose)=
    LinearMap.ker (Matrix.toLin' (pluckerPolarRow (genericFourOutputInteriorMinors (K:=K) q))) := by
  classical
  let L := AffineCoefficientField K (MatrixParameters (Fin (4*q+2)) (Fin 4))
  let M := genericAffineSquare K (Fin (4*q+2)) (Fin 4)
  let P := genericAffineRows K (Fin (4*q+2)) (Fin 4)
  let G := P*M^q*polynomialKernelBasisMatrix (observabilityMatrix M P q) Bv
  let F := fourOutputInteriorMinors q M P
  let Z := fourOutputScalarLiftMatrix q M P
  obtain ⟨R,hR⟩ := generic_affine_wide_observability_right_inverse
    (K:=K) (n:=Fin (4*q+2)) (m:=Fin 4) q (by simp only [Fintype.card_fin]; omega)
  obtain ⟨LG,hLG⟩ := generic_terminal_kernel_left_inverse
    (K:=K) (n:=Fin (4*q+2)) (m:=Fin 4) q (by simp)
    (by simp only [Fintype.card_fin]; omega) (by simp only [Fintype.card_fin]; omega) Bv
  change LG*G=1 at hLG
  obtain ⟨c,hc,hF⟩ := fourOutputInteriorMinors_common_scalar q M P R hR Bv
  have hu : IsUnit (C c : L[X]) := Polynomial.isUnit_iff.mpr ⟨c,isUnit_iff_ne_zero.mpr hc,rfl⟩
  obtain ⟨u,hu⟩ := hu
  have hscale : F=(u:L[X]) • fourOutputPluckerVector G := by
    funext i
    rw [hu]
    exact hF i
  have hgen (H : Fin 6 → L[X]) :
      (∃ A : Matrix (Fin 4) (Fin 4) L[X],pluckerOutputAction q F A=H) ↔
        pluckerQuadricPolar F H=0 := by
    rw [hscale]
    exact pluckerOutputAction_unit_smul_range q u (fourOutputPluckerVector G)
      (fourOutputTerminal_output_action_range q G LG hLG Bt) H
  apply plucker_gradient_row_range q F Z (generic_four_output_gradient_relation (K:=K) q) _ hgen
  intro A
  let v := (matrixPairEquiv L[X] L[X] (Fin (4*q+2)) (Fin 4)).symm
    (0,(A*P).transpose)
  refine ⟨v,?_⟩
  rw [← four_output_scalar_lift_output_action q M P R hR Bv A]
  funext i
  have h := matrixPairTraceFunctional_transpose v (fun k => Z k i)
  simpa only [v,LinearEquiv.apply_symm_apply,Matrix.transpose_zero,Matrix.transpose_transpose]
    using h.symm

end FD56
