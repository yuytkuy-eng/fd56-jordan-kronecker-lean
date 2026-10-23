/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedGenericWitness
import FD56.Hilbert.MixedThreeScalarWitness

/-! The degree-one high-row obstruction for mixed degrees three and four. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option maxHeartbeats 800000

section AffineRows
variable {R S h m r : Type*} [CommRing R] [CommRing S]

def affineScalarRowLift (G : Matrix m r R[X]) : Matrix (Fin 2 × m) r R[X] :=
  fun i j => if i.1 = 0 then G i.2 j else Polynomial.X * G i.2 j

def affineScalarRowDecode (E : Matrix h (Fin 2 × m) R) : Matrix h m R[X] :=
  fun i x => Polynomial.C (E i (1,x)) * Polynomial.X + Polynomial.C (E i (0,x))

theorem affineScalarRowLift_map (G : Matrix m r R[X]) (φ : R →+* S) :
    (affineScalarRowLift G).map (Polynomial.mapRingHom φ) =
      affineScalarRowLift (G.map (Polynomial.mapRingHom φ)) := by
  funext i j
  by_cases hi : i.1 = 0 <;> simp [affineScalarRowLift, hi]

theorem affineScalarRowDecode_mul [Fintype m] (E : Matrix h (Fin 2 × m) R)
    (G : Matrix m r R[X]) :
    E.map Polynomial.C * affineScalarRowLift G = affineScalarRowDecode E * G := by
  funext i j
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.map_apply, affineScalarRowLift, affineScalarRowDecode,
    Prod.fst, Prod.snd, if_pos rfl, show (1 : Fin 2) ≠ 0 by decide, if_false]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  simp only [if_true]
  ring

theorem affineScalarRowDecode_zero (E : Matrix h (Fin 2 × m) R)
    (hE : affineScalarRowDecode E = 0) : E = 0 := by
  funext i j
  rcases j with ⟨k,x⟩
  have hh := congrFun (congrFun hE i) x
  fin_cases k
  · have hz := congrArg (fun p : R[X] => p.coeff 0) hh
    simpa [affineScalarRowDecode] using hz
  · have hz := congrArg (fun p : R[X] => p.coeff 1) hh
    simpa [affineScalarRowDecode] using hz

end AffineRows

section FieldRows
variable {K h m r : Type*} [Field K]

theorem affineScalarRowDecode_degree (E : Matrix h (Fin 2 × m) K) :
    DegreeBound (affineScalarRowDecode E) 1 := by
  intro i j
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · exact (Polynomial.natDegree_mul_le).trans (by simp)
  · simp

theorem affineScalarRowLift_degree (G : Matrix m r K[X]) (b : ℕ)
    (hG : DegreeBound G b) : DegreeBound (affineScalarRowLift G) (b+1) := by
  intro i j
  by_cases hi : i.1 = 0
  · simpa only [affineScalarRowLift, if_pos hi] using (hG i.2 j).trans (by omega)
  · simp only [affineScalarRowLift, if_neg hi]
    exact Polynomial.natDegree_mul_le.trans (by have := hG i.2 j; simp; omega)

theorem affineScalarRowDecode_coeff (E : Matrix h m K[X]) (hE : DegreeBound E 1) :
    affineScalarRowDecode (fun i x => (E i x.2).coeff x.1.val) = E := by
  funext i j
  exact (Polynomial.eq_X_add_C_of_natDegree_le_one (hE i j)).symm

end FieldRows

variable {K : Type*} [Field K]

theorem genericMixedThreeWitness_scalar_coefficient_injective (u v : ℕ) (hv : 0 < v) :
    Function.Injective (mixedScalarCoefficientMatrix
      (affineScalarRowLift (genericMixedWitness K 3 u v)) 7 (8-u*v)
      (fun k => u*v+k.val)).mulVec := by
  classical
  let e := fun j => mixedKernelDegree 3 u v j + 2
  obtain ⟨W, hW, _, _, hz⟩ := exists_mixed_three_scalar_witness (K := K) u v hv
  have hWe : ∀ j x, (W.transpose j x).natDegree ≤ e j := by
    intro j x
    have hh := hW x j
    cases j <;> simpa [e, mixedKernelDegree, mixedColumnShift] using hh
  have hWb : DegreeBound W 6 := by
    intro x j
    have hh := hWe j x
    cases j <;> simp only [e, mixedKernelDegree_inl, mixedKernelDegree_inr,
      Matrix.transpose_apply] at hh <;> omega
  have hWi : Function.Injective (mixedScalarCoefficientMatrix (affineScalarRowLift W)
      7 (8-u*v) (fun k => u*v+k.val)).mulVec := by
    apply mixedScalarCoefficientMatrix_injective_of_obstruction _ _ _ _
      (affineScalarRowLift_degree W 6 hWb) (fun k => by have := k.isLt; omega)
    intro E c hrel htail
    rw [affineScalarRowDecode_mul] at hrel
    obtain ⟨hE,hc⟩ := hz (affineScalarRowDecode E) c
      (affineScalarRowDecode_degree E) hrel htail
    exact ⟨affineScalarRowDecode_zero E hE,hc⟩
  let ψ := prescribedMatrixSpecialization e (RingHom.id K) W.transpose
  let φ := algebraMap
    (MvPolynomial (PrescribedMatrixParameters (MixedScalarRows 3 (Fin u) (Fin v)) e) K)
    (MixedWitnessField K 3 u v)
  let U := (universalPrescribedMatrix K (MixedScalarRows 3 (Fin u) (Fin v)) e).transpose
  let A := mixedScalarCoefficientMatrix (affineScalarRowLift U) 7 (8-u*v)
    (fun k => u*v+k.val)
  have hU : U.map (Polynomial.mapRingHom ψ) = W := by
    change (universalPrescribedMatrix K _ e).transpose.map _ = _
    rw [Matrix.transpose_map, universalPrescribedMatrix_specialization e (RingHom.id K)
      W.transpose hWe, Matrix.transpose_transpose]
  have hAe : A.map ψ = mixedScalarCoefficientMatrix (affineScalarRowLift W) 7 (8-u*v)
      (fun k => u*v+k.val) := by
    dsimp only [A]
    rw [mixedScalarCoefficientMatrix_map, affineScalarRowLift_map, hU]
  have hAg : A.map φ = mixedScalarCoefficientMatrix
      (affineScalarRowLift (genericMixedWitness K 3 u v)) 7 (8-u*v)
      (fun k => u*v+k.val) := by
    dsimp only [A]
    rw [mixedScalarCoefficientMatrix_map, affineScalarRowLift_map]
    rfl
  rw [← hAg]
  apply matrix_injective_of_field_specialization ψ φ (IsFractionRing.injective _ _) A
  simpa only [hAe] using hWi

theorem genericMixedThreeWitness_scalar_obstruction (u v : ℕ) (hv : 0 < v)
    (E : Matrix (Fin v) (MixedScalarRows 3 (Fin u) (Fin v)) (MixedWitnessField K 3 u v)[X])
    (c : (MixedWitnessField K 3 u v)[X]) (hE : DegreeBound E 1) (hc : c.natDegree ≤ 7)
    (hr : E * genericMixedWitness K 3 u v = (-c) •
      (mixedScalarHighIdentity : Matrix (Fin v) (Fin u ⊕ Fin v) (MixedWitnessField K 3 u v)[X]))
    (ht : ∀ k : Fin (8-u*v), c.coeff (u*v+k.val) = 0) : E = 0 ∧ c = 0 := by
  let E₀ : Matrix (Fin v) (Fin 2 × MixedScalarRows 3 (Fin u) (Fin v))
      (MixedWitnessField K 3 u v) := fun i x => (E i x.2).coeff x.1.val
  have hdecode : affineScalarRowDecode E₀ = E := affineScalarRowDecode_coeff E hE
  have hrel : E₀.map C * affineScalarRowLift (genericMixedWitness K 3 u v) =
      (-c) • (mixedScalarHighIdentity :
        Matrix (Fin v) (Fin u ⊕ Fin v) (MixedWitnessField K 3 u v)[X]) := by
    rw [affineScalarRowDecode_mul, hdecode, hr]
  obtain ⟨hzero,hc0⟩ := mixedScalarCoefficientMatrix_obstruction_of_injective
    (affineScalarRowLift (genericMixedWitness K 3 u v)) 7 (8-u*v) (fun k => u*v+k.val)
    (fun k => by have := k.isLt; dsimp; omega)
    (genericMixedThreeWitness_scalar_coefficient_injective (K := K) u v hv) E₀ c hc hrel ht
  refine ⟨?_,hc0⟩
  rw [← hdecode, hzero]
  funext i j
  simp [affineScalarRowDecode]

end FD56
