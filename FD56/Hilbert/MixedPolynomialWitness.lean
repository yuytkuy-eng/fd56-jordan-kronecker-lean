/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedGenericWitness

/-! Transfer bounded polynomial row obstructions to the prescribed generic matrix. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

section Rows
variable {R S h m r : Type*} [CommRing R] [CommRing S]

def polynomialScalarRowLift (k : ℕ) (G : Matrix m r R[X]) :
    Matrix (Fin (k+1) × m) r R[X] := fun i j => X^i.1.val * G i.2 j

def polynomialScalarRowDecode (k : ℕ) (E : Matrix h (Fin (k+1) × m) R) :
    Matrix h m R[X] := by
  classical
  exact fun i x => Polynomial.ofFn (k+1) (fun l => E i (l,x))

theorem polynomialScalarRowLift_map (k : ℕ) (G : Matrix m r R[X]) (φ : R →+* S) :
    (polynomialScalarRowLift k G).map (Polynomial.mapRingHom φ) =
      polynomialScalarRowLift k (G.map (Polynomial.mapRingHom φ)) := by
  funext i j
  simp [polynomialScalarRowLift]

theorem polynomialScalarRowDecode_mul [Fintype m]
    (k : ℕ) (E : Matrix h (Fin (k+1) × m) R) (G : Matrix m r R[X]) :
    E.map Polynomial.C * polynomialScalarRowLift k G = polynomialScalarRowDecode k E * G := by
  funext i j
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,Matrix.map_apply,
    polynomialScalarRowLift,polynomialScalarRowDecode,Polynomial.ofFn_eq_sum_monomial,
    ← Polynomial.C_mul_X_pow_eq_monomial,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem polynomialScalarRowDecode_zero (k : ℕ) (E : Matrix h (Fin (k+1) × m) R)
    (hE : polynomialScalarRowDecode k E = 0) : E = 0 := by
  funext i j
  have h := congrArg (fun p : R[X] => p.coeff j.1.val) (congrFun (congrFun hE i) j.2)
  simpa [polynomialScalarRowDecode,Polynomial.ofFn_coeff_eq_val_of_lt _ j.1.isLt] using h

end Rows

section FieldRows
variable {K h m r : Type*} [Field K]

theorem polynomialScalarRowDecode_degree (k : ℕ) (E : Matrix h (Fin (k+1) × m) K) :
    DegreeBound (polynomialScalarRowDecode k E) k := by
  intro i j
  classical
  dsimp only [polynomialScalarRowDecode]
  exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega : 1 ≤ k+1) _)

theorem polynomialScalarRowLift_degree (k : ℕ) (G : Matrix m r K[X]) (b : ℕ)
    (hG : DegreeBound G b) : DegreeBound (polynomialScalarRowLift k G) (b+k) := by
  intro i j
  apply Polynomial.natDegree_mul_le.trans
  have hi := i.1.isLt
  have hh := hG i.2 j
  simp only [Polynomial.natDegree_X_pow]
  omega

theorem polynomialScalarRowDecode_coeff (k : ℕ) (E : Matrix h m K[X])
    (hE : DegreeBound E k) :
    polynomialScalarRowDecode k (fun i x => (E i x.2).coeff x.1.val) = E := by
  funext i j
  classical
  dsimp only [polynomialScalarRowDecode]
  exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by have := hE i j; omega)

end FieldRows

variable {K : Type*} [Field K]

set_option maxHeartbeats 800000 in
theorem genericMixedWitness_scalar_obstruction_of_witness
    (a u v k t : ℕ) (f : Fin t → ℕ) (hf : ∀ j, f j ≤ a+3+k)
    (W : Matrix (MixedScalarRows a (Fin u) (Fin v)) (Fin u ⊕ Fin v) K[X])
    (hW : ∀ x j, (W x j).natDegree ≤ mixedKernelDegree a u v j+2)
    (hzero : ∀ (E : Matrix (Fin v) (MixedScalarRows a (Fin u) (Fin v)) K[X])
      (c : K[X]), DegreeBound E k → E*W = (-c) •
        (mixedScalarHighIdentity : Matrix (Fin v) (Fin u ⊕ Fin v) K[X]) →
      (∀ j, c.coeff (f j) = 0) → E = 0 ∧ c = 0)
    (E : Matrix (Fin v) (MixedScalarRows a (Fin u) (Fin v)) (MixedWitnessField K a u v)[X])
    (c : (MixedWitnessField K a u v)[X]) (hE : DegreeBound E k) (hc : c.natDegree ≤ a+3+k)
    (hr : E*genericMixedWitness K a u v = (-c) •
      (mixedScalarHighIdentity : Matrix (Fin v) (Fin u ⊕ Fin v) (MixedWitnessField K a u v)[X]))
    (ht : ∀ j, c.coeff (f j) = 0) : E = 0 ∧ c = 0 := by
  classical
  let e := fun j => mixedKernelDegree a u v j+2
  have hWb : DegreeBound W (a+3) := by
    intro x j
    have h := hW x j
    cases j <;> simp only [mixedKernelDegree_inl,mixedKernelDegree_inr] at h <;> omega
  have hWi : Function.Injective (mixedScalarCoefficientMatrix
      (polynomialScalarRowLift k W) (a+3+k) t f).mulVec := by
    apply mixedScalarCoefficientMatrix_injective_of_obstruction _ _ _ _
      (polynomialScalarRowLift_degree k W (a+3) hWb) hf
    intro F z hrel htail
    rw [polynomialScalarRowDecode_mul] at hrel
    obtain ⟨hF,hz⟩ := hzero (polynomialScalarRowDecode k F) z
      (polynomialScalarRowDecode_degree k F) hrel htail
    exact ⟨polynomialScalarRowDecode_zero k F hF,hz⟩
  let ψ := prescribedMatrixSpecialization e (RingHom.id K) W.transpose
  let φ := algebraMap
    (MvPolynomial (PrescribedMatrixParameters (MixedScalarRows a (Fin u) (Fin v)) e) K)
    (MixedWitnessField K a u v)
  let U := (universalPrescribedMatrix K (MixedScalarRows a (Fin u) (Fin v)) e).transpose
  let A := mixedScalarCoefficientMatrix (polynomialScalarRowLift k U) (a+3+k) t f
  have hU : U.map (Polynomial.mapRingHom ψ) = W := by
    change (universalPrescribedMatrix K _ e).transpose.map _ = _
    rw [Matrix.transpose_map,universalPrescribedMatrix_specialization e (RingHom.id K)
      W.transpose (fun j x => hW x j),Matrix.transpose_transpose]
  have hAe : A.map ψ = mixedScalarCoefficientMatrix
      (polynomialScalarRowLift k W) (a+3+k) t f := by
    dsimp only [A]
    rw [mixedScalarCoefficientMatrix_map,polynomialScalarRowLift_map,hU]
  have hAg : A.map φ = mixedScalarCoefficientMatrix
      (polynomialScalarRowLift k (genericMixedWitness K a u v)) (a+3+k) t f := by
    dsimp only [A]
    rw [mixedScalarCoefficientMatrix_map,polynomialScalarRowLift_map]
    rfl
  have hi : Function.Injective (mixedScalarCoefficientMatrix
      (polynomialScalarRowLift k (genericMixedWitness K a u v)) (a+3+k) t f).mulVec := by
    rw [← hAg]
    apply matrix_injective_of_field_specialization ψ φ (IsFractionRing.injective _ _) A
    simpa only [hAe] using hWi
  let E₀ : Matrix (Fin v) (Fin (k+1) × MixedScalarRows a (Fin u) (Fin v))
      (MixedWitnessField K a u v) := fun i x => (E i x.2).coeff x.1.val
  have hdecode : polynomialScalarRowDecode k E₀ = E := polynomialScalarRowDecode_coeff k E hE
  have hrel : E₀.map C * polynomialScalarRowLift k (genericMixedWitness K a u v) =
      (-c) • (mixedScalarHighIdentity :
        Matrix (Fin v) (Fin u ⊕ Fin v) (MixedWitnessField K a u v)[X]) := by
    rw [polynomialScalarRowDecode_mul,hdecode,hr]
  obtain ⟨hEz,hcz⟩ := mixedScalarCoefficientMatrix_obstruction_of_injective
    _ (a+3+k) t f hf hi E₀ c hc hrel ht
  refine ⟨?_,hcz⟩
  rw [← hdecode,hEz]
  funext i j
  simp [polynomialScalarRowDecode,Polynomial.ofFn_eq_sum_monomial]

end FD56
