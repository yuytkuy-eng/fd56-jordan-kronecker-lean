/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.InteriorScalarSelectors
import FD56.Stabilizer.ObservabilityScalarAdjugateMap
import FD56.Stabilizer.ObservabilityMinorGradient
import FD56.Stabilizer.AffineSpecialization
import FD56.LinearAlgebra.RankSpecializationExtension

/-! Independent selected-minor gradients in the generic interior SL kernel.
The shift specialization works in every characteristic. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
variable (r s : ℕ) [NeZero r] [NeZero s]
variable {R : Type*} [CommRing R]

def interiorScalarLiftMatrix (q : ℕ)
    (M : Matrix (Fin ((r+s)*q+r)) (Fin ((r+s)*q+r)) R)
    (P : Matrix (Fin (r+s)) (Fin ((r+s)*q+r)) R) :
    Matrix (SLInput (Fin ((r+s)*q+r)) (Fin (r+s))) (Option (Fin r × Fin s)) R :=
  fun k z => observabilityScalarLift M P (interiorLevel r s q) (interiorSelectorRow r s q z) k

omit [NeZero s] in
theorem interiorScalarLiftMatrix_map {S : Type*} [CommRing S] (φ : R →+* S)
    (q : ℕ) (M : Matrix (Fin ((r+s)*q+r)) (Fin ((r+s)*q+r)) R)
    (P : Matrix (Fin (r+s)) (Fin ((r+s)*q+r)) R) :
    (interiorScalarLiftMatrix r s q M P).map φ=
      interiorScalarLiftMatrix r s q (M.map φ) (P.map φ) := by
  funext k z
  have hC : ((observabilitySelectedMatrix M P (interiorLevel r s q)
      (interiorSelectorRow r s q z)).adjugate).map φ=
      (observabilitySelectedMatrix (M.map φ) (P.map φ) (interiorLevel r s q)
        (interiorSelectorRow r s q z)).adjugate := by
    rw [← RingHom.mapMatrix_apply,φ.map_adjugate,RingHom.mapMatrix_apply,
      observabilitySelectedMatrix_map]
  rcases k with ab|ab
  · have h := observabilityScalarX_map φ M P
      (observabilitySelectedMatrix M P (interiorLevel r s q)
        (interiorSelectorRow r s q z)).adjugate
      (interiorLevel r s q) (interiorSelectorRow r s q z)
    rw [hC] at h
    exact congrFun (congrFun h ab.1) ab.2
  · have h := observabilityScalarU_map φ M
      (observabilitySelectedMatrix M P (interiorLevel r s q)
        (interiorSelectorRow r s q z)).adjugate
      (interiorLevel r s q) (interiorSelectorRow r s q z)
    rw [hC] at h
    exact congrFun (congrFun h ab.1) ab.2

theorem interior_shift_scalar_lift_injective (q : ℕ) :
    Function.Injective (interiorScalarLiftMatrix r s q
      (interiorShiftM (R:=R) r s q) (interiorShiftP r s q)).mulVec := by
  change Function.Injective (Matrix.toLin' (interiorScalarLiftMatrix r s q
    (interiorShiftM (R:=R) r s q) (interiorShiftP r s q)))
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have hU : (∑ z, v z • interiorScalarUFamily (R:=R) r s q z)=0 := by
    funext i b
    have h := congrFun hv (.inr (i,b))
    change (∑ z, interiorScalarUFamily (R:=R) r s q z i b*v z)=0 at h
    simpa only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Matrix.zero_apply,
      mul_comm] using h
  exact funext ((Fintype.linearIndependent_iff.mp
    (interior_shift_scalarU_independent (R:=R) r s q)) v hU)

variable {K : Type*} [Field K]

theorem interiorScalarLiftMatrix_kernel (q : ℕ)
    (M : Matrix (Fin ((r+s)*q+r)) (Fin ((r+s)*q+r)) K[X])
    (P : Matrix (Fin (r+s)) (Fin ((r+s)*q+r)) K[X]) (i₀ : Fin ((r+s)*q+r)) :
    slEquationMatrix M P i₀*interiorScalarLiftMatrix r s q M P=0 := by
  funext k z
  exact congrFun (observabilityScalarLift_sl_kernel M P (interiorLevel r s q)
    (interiorSelectorRow r s q z) (interiorSelector_lower_closed r s q z) i₀) k

theorem generic_interior_scalar_lifts_zero_injective (q : ℕ) :
    Function.Injective ((interiorScalarLiftMatrix r s q
      (genericAffineSquare K (Fin ((r+s)*q+r)) (Fin (r+s)))
      (genericAffineRows K (Fin ((r+s)*q+r)) (Fin (r+s)))).map
        (Polynomial.evalRingHom 0)).mulVec := by
  let φ := (Polynomial.evalRingHom
    (0 : AffineCoefficientField K (MatrixParameters (Fin ((r+s)*q+r)) (Fin (r+s))))).comp
    (affineParameterMap K (MatrixParameters (Fin ((r+s)*q+r)) (Fin (r+s))))
  have hφ : Function.Injective φ := by
    dsimp only [φ]
    rw [affineParameterMap_zero]
    exact (IsFractionRing.injective
      (MvPolynomial (MatrixParameters (Fin ((r+s)*q+r)) (Fin (r+s)) ⊕
        MatrixParameters (Fin ((r+s)*q+r)) (Fin (r+s))) K)
      (AffineCoefficientField K (MatrixParameters (Fin ((r+s)*q+r)) (Fin (r+s))))).comp
      (MvPolynomial.rename_injective (R:=K)
        (Sum.inl : MatrixParameters (Fin ((r+s)*q+r)) (Fin (r+s)) →
          MatrixParameters (Fin ((r+s)*q+r)) (Fin (r+s)) ⊕
            MatrixParameters (Fin ((r+s)*q+r)) (Fin (r+s))) Sum.inl_injective)
  let ψ := matrixSpecialization (interiorShiftM (R:=K) r s q) (interiorShiftP r s q)
  let A := interiorScalarLiftMatrix r s q
    (universalSquare K (Fin ((r+s)*q+r)) (Fin (r+s)))
    (universalRows K (Fin ((r+s)*q+r)) (Fin (r+s)))
  have hA : Function.Injective (A.map ψ).mulVec := by
    dsimp only [A,ψ]
    rw [interiorScalarLiftMatrix_map,
      (universal_pair_specialization (interiorShiftM (R:=K) r s q) (interiorShiftP r s q)).1,
      (universal_pair_specialization (interiorShiftM (R:=K) r s q) (interiorShiftP r s q)).2]
    exact interior_shift_scalar_lift_injective r s q
  have hg := matrix_injective_of_field_specialization ψ φ hφ A hA
  have he : A.map φ=(interiorScalarLiftMatrix r s q
      (genericAffineSquare K (Fin ((r+s)*q+r)) (Fin (r+s)))
      (genericAffineRows K (Fin ((r+s)*q+r)) (Fin (r+s)))).map
        (Polynomial.evalRingHom 0) := by
    dsimp only [A,φ,genericAffineSquare,genericAffineRows]
    rw [← interiorScalarLiftMatrix_map,Matrix.map_map]
    rfl
  rw [he] at hg
  exact hg

set_option maxHeartbeats 1000000 in
theorem generic_interior_scalar_lifts_field_injective {F : Type*} [Field F]
    (q : ℕ)
    (φ : (AffineCoefficientField K (MatrixParameters (Fin ((r+s)*q+r)) (Fin (r+s))))[X] →+* F)
    (hφ : Function.Injective φ) :
    Function.Injective ((interiorScalarLiftMatrix r s q
      (genericAffineSquare K (Fin ((r+s)*q+r)) (Fin (r+s)))
      (genericAffineRows K (Fin ((r+s)*q+r)) (Fin (r+s)))).map φ).mulVec :=
  matrix_injective_of_field_specialization (Polynomial.evalRingHom 0) φ hφ _
    (generic_interior_scalar_lifts_zero_injective (K:=K) r s q)

end FD56
