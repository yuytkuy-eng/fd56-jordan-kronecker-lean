/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.TwoOutputOddSLAdjugate
import FD56.Stabilizer.OddTwoScalarSpecialization
import FD56.Stabilizer.AffineSpecialization

/-! Sparse specialization proves independence of the two generic scalar lifts. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {R : Type*} [CommRing R]

def oddTwoScalarCross (q : ℕ) (M : Matrix (Fin (2*q+1)) (Fin (2*q+1)) R)
    (P : Matrix (Fin 2) (Fin (2*q+1)) R) : SLInput (Fin (2*q+1)) (Fin 2) → R :=
  oddTwoScalarValue q M P 1 • oddTwoScalarLift q M P 0 -
    oddTwoScalarValue q M P 0 • oddTwoScalarLift q M P 1

theorem oddTwoScalarCross_map {S : Type*} [CommRing S] (φ : R →+* S)
    (q : ℕ) (M : Matrix (Fin (2*q+1)) (Fin (2*q+1)) R)
    (P : Matrix (Fin 2) (Fin (2*q+1)) R) :
    (fun k => φ (oddTwoScalarCross q M P k))=oddTwoScalarCross q (M.map φ) (P.map φ) := by
  funext k
  simp only [oddTwoScalarCross,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,map_sub,map_mul,
    oddTwoScalarValue_map]
  rw [congrFun (oddTwoScalarLift_map φ q M P 0) k,
    congrFun (oddTwoScalarLift_map φ q M P 1) k]

theorem oddTwo_shift_scalar_cross_entry (q : ℕ) :
    oddTwoScalarCross q (oddTwoShiftM (R := R) q) (oddTwoShiftP q) (Sum.inr (0,1))=1 := by
  have hU : oddTwoScalarLift q (oddTwoShiftM (R := R) q) (oddTwoShiftP q) 1
      (Sum.inr (0,1))=1 := oddTwo_shift_scalarU_one q
  simp only [oddTwoScalarCross,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
    oddTwoScalarValue,oddTwoScalarMatrix,oddTwo_shift_selected_zero_det,
    oddTwo_shift_selected_one_det,neg_zero,zero_mul,hU,mul_one,zero_sub,neg_neg]

variable {K : Type*} [Field K]

theorem generic_two_output_odd_scalar_cross_ne_zero (q : ℕ) :
    oddTwoScalarValue q (genericAffineSquare K (Fin (2*q+1)) (Fin 2))
        (genericAffineRows K (Fin (2*q+1)) (Fin 2)) 1 •
      oddTwoScalarLift q (genericAffineSquare K (Fin (2*q+1)) (Fin 2))
        (genericAffineRows K (Fin (2*q+1)) (Fin 2)) 0 -
    oddTwoScalarValue q (genericAffineSquare K (Fin (2*q+1)) (Fin 2))
        (genericAffineRows K (Fin (2*q+1)) (Fin 2)) 0 •
      oddTwoScalarLift q (genericAffineSquare K (Fin (2*q+1)) (Fin 2))
        (genericAffineRows K (Fin (2*q+1)) (Fin 2)) 1 ≠ 0 := by
  let M := oddTwoShiftM (R := K[X]) q
  let P := oddTwoShiftP (R := K[X]) q
  have hM : DegreeBound M 1 := by
    intro i j
    dsimp [M,oddTwoShiftM,finiteShiftMatrix]
    split_ifs <;> simp
  have hP : DegreeBound P 1 := by
    intro i j
    dsimp [P,oddTwoShiftP,finiteInitialRows]
    split_ifs <;> simp
  let Mu := universalAffineSquare K (Fin (2*q+1)) (Fin 2)
  let Pu := universalAffineRows K (Fin (2*q+1)) (Fin 2)
  let φ := Polynomial.mapRingHom (algebraMap
    (MvPolynomial (MatrixParameters (Fin (2*q+1)) (Fin 2) ⊕
      MatrixParameters (Fin (2*q+1)) (Fin 2)) K)
    (AffineCoefficientField K (MatrixParameters (Fin (2*q+1)) (Fin 2))))
  have hφ : Function.Injective φ := Polynomial.map_injective _ (IsFractionRing.injective _ _)
  let ψ := Polynomial.mapRingHom (affinePairSpecialization M P)
  have hg := oddTwoScalarCross_map φ q Mu Pu
  rw [universalAffineSquare_generic,universalAffineRows_generic] at hg
  have hs := oddTwoScalarCross_map ψ q Mu Pu
  rw [universalAffineSquare_pair_specialization M P hM,
    universalAffineRows_pair_specialization M P hP] at hs
  intro hz
  change oddTwoScalarCross q _ _=0 at hz
  have hu : oddTwoScalarCross q Mu Pu=0 := by
    funext k
    apply hφ
    change φ (oddTwoScalarCross q Mu Pu k)=φ 0
    rw [map_zero]
    exact (congrFun hg k).trans (congrFun hz k)
  have hzero : oddTwoScalarCross q M P (Sum.inr (0,1))=0 := by
    rw [← congrFun hs (Sum.inr (0,1))]
    simp [hu]
  have hone : oddTwoScalarCross q M P (Sum.inr (0,1))=1 :=
    oddTwo_shift_scalar_cross_entry q
  exact one_ne_zero (hone.symm.trans hzero)

end FD56
