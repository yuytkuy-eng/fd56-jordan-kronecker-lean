/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.FourOutputInteriorMinors
import FD56.LinearAlgebra.AugmentedDeterminantDifferential
import FD56.LinearAlgebra.PluckerOutputAction
import FD56.Stabilizer.ObservabilityOutputDifferential

/-! The actual output variation of the six augmented observability minors. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 2000000

variable {R : Type*} [CommRing R]

def fourOutputPrefixAction (q : ℕ) (A : Matrix (Fin 4) (Fin 4) R) :
    Matrix (Fin q × Fin 4) (Fin q × Fin 4) R :=
  fun i j => if i.1=j.1 then A i.2 j.2 else 0

theorem fourOutputPrefixAction_trace (q : ℕ) (A : Matrix (Fin 4) (Fin 4) R) :
    Matrix.trace (fourOutputPrefixAction q A)=(q:R)*Matrix.trace A := by
  simp [Matrix.trace,Matrix.diag,fourOutputPrefixAction,Fintype.sum_prod_type]

theorem four_output_observability_output_mul (q : ℕ)
    (M : Matrix (Fin (4*q+2)) (Fin (4*q+2)) R)
    (P : Matrix (Fin 4) (Fin (4*q+2)) R) (A : Matrix (Fin 4) (Fin 4) R) :
    observabilityMatrix M (A*P) q=fourOutputPrefixAction q A*observabilityMatrix M P q := by
  funext i j
  change (A*P*M^i.1.val) i.2 j=_
  rw [Matrix.mul_assoc]
  simp [Matrix.mul_apply,fourOutputPrefixAction,observabilityMatrix,Fintype.sum_prod_type,
    ite_mul]

theorem fourOutputPluckerVector_directional (q : ℕ)
    (G : Matrix (Fin 4) (Fin 2) R) (A : Matrix (Fin 4) (Fin 4) R) :
    (fun i => (q:R)*Matrix.trace A*fourOutputPluckerVector G i+
      matrixDetDifferential (G.submatrix (fourOutputPluckerRows i) id)
        ((A*G).submatrix (fourOutputPluckerRows i) id))=
      pluckerOutputAction q (fourOutputPluckerVector G) A := by
  have htwo (U V : Matrix (Fin 2) (Fin 2) R) :
      matrixDetDifferential U V=U 1 1*V 0 0-U 0 1*V 1 0-U 1 0*V 0 1+U 0 0*V 1 1 := by
    simp only [matrixDetDifferential,Matrix.trace,Matrix.diag,Matrix.mul_apply,
      Matrix.adjugate_fin_two,Fin.sum_univ_two]
    simp
    ring
  funext i
  fin_cases i <;>
    rw [htwo] <;>
    simp [fourOutputPluckerVector,fourOutputPluckerRows,pluckerMinorVector,
      Matrix.det_fin_two,
      pluckerOutputAction,pluckerUpperCoordinates,pluckerSkewMatrix,Matrix.trace,
      Matrix.mul_apply,Fin.sum_univ_succ,
      Matrix.vecHead,Matrix.vecTail] <;> ring

def fourOutputInteriorDirectional (q : ℕ)
    (M : Matrix (Fin (4*q+2)) (Fin (4*q+2)) R)
    (P Q : Matrix (Fin 4) (Fin (4*q+2)) R) : Fin 6 → R :=
  fun i => matrixDetDifferential
    ((Matrix.fromRows (observabilityMatrix M P q)
      ((P*M^q).submatrix (fourOutputPluckerRows i) id)).submatrix (interiorPrefixEquiv 2 2 q) id)
    ((Matrix.fromRows (observabilityMatrix M Q q)
      ((Q*M^q).submatrix (fourOutputPluckerRows i) id)).submatrix (interiorPrefixEquiv 2 2 q) id)

private theorem pluckerOutputAction_smul_point (q : ℕ) (c : R) (F : Fin 6 → R)
    (A : Matrix (Fin 4) (Fin 4) R) :
    pluckerOutputAction q (c • F) A=c • pluckerOutputAction q F A := by
  have hs : pluckerSkewMatrix (c • F)=c • pluckerSkewMatrix F := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pluckerSkewMatrix,smul_eq_mul]
  simp only [pluckerOutputAction,LinearMap.coe_mk,AddHom.coe_mk,hs,
    Matrix.mul_smul,Matrix.smul_mul,← smul_add,map_smul]
  ext i
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
  ring

theorem four_output_directional_action_of_completion (q : ℕ)
    (M : Matrix (Fin (4*q+2)) (Fin (4*q+2)) R)
    (P : Matrix (Fin 4) (Fin (4*q+2)) R) (A : Matrix (Fin 4) (Fin 4) R)
    (S : Matrix (Fin (4*q+2)) (Fin q × Fin 4) R)
    (V : Matrix (Fin (4*q+2)) (Fin 2) R)
    (hS : observabilityMatrix M P q*S=1) (hV : observabilityMatrix M P q*V=0)
    (hunit : IsUnit ((Matrix.fromCols S V).submatrix id (interiorPrefixEquiv 2 2 q)).det) :
    fourOutputInteriorDirectional q M P (A*P)=
      pluckerOutputAction q (fourOutputInteriorMinors q M P) A := by
  let t := ((Matrix.fromCols S V).submatrix id (interiorPrefixEquiv 2 2 q)).det
  let G := P*M^q*V
  have hscale : t • fourOutputInteriorMinors q M P=fourOutputPluckerVector G := by
    funext i
    have h := augmented_completion_determinant (interiorPrefixEquiv 2 2 q)
      (observabilityMatrix M P q) S V hS hV ((P*M^q).submatrix (fourOutputPluckerRows i) id)
    simpa only [t,fourOutputInteriorMinors,fourOutputPluckerVector,pluckerMinorVector,G,
      Pi.smul_apply,smul_eq_mul,Matrix.submatrix_mul,Matrix.submatrix_id_id] using h
  have hdiff : t • fourOutputInteriorDirectional q M P (A*P)=
      pluckerOutputAction q (fourOutputPluckerVector G) A := by
    rw [← fourOutputPluckerVector_directional]
    funext i
    change t*matrixDetDifferential _ _=_
    rw [four_output_observability_output_mul]
    have h := augmented_completion_differential (interiorPrefixEquiv 2 2 q)
      (observabilityMatrix M P q) S V hS hV (fourOutputPrefixAction q A)
      ((P*M^q).submatrix (fourOutputPluckerRows i) id)
      ((A*P*M^q).submatrix (fourOutputPluckerRows i) id)
    rw [fourOutputPrefixAction_trace q A] at h
    have hrow (T : Matrix (Fin 4) (Fin (4*q+2)) R) :
        T.submatrix (fourOutputPluckerRows i) id*V=(T*V).submatrix (fourOutputPluckerRows i) id := by
      simpa only [Matrix.submatrix_id_id] using
        (Matrix.submatrix_mul T V (fourOutputPluckerRows i) id id Function.bijective_id).symm
    rw [hrow,hrow] at h
    simpa only [t,fourOutputPluckerVector,pluckerMinorVector,G,Matrix.mul_assoc] using h
  rw [← hscale,pluckerOutputAction_smul_point] at hdiff
  funext i
  exact hunit.mul_left_cancel (congrFun hdiff i)

theorem four_output_directional_action {K : Type*} [Field K] (q : ℕ)
    (M : Matrix (Fin (4*q+2)) (Fin (4*q+2)) K[X])
    (P : Matrix (Fin 4) (Fin (4*q+2)) K[X])
    (S : Matrix (Fin (4*q+2)) (Fin q × Fin 4) K[X])
    (hS : observabilityMatrix M P q*S=1)
    (B : Basis (Fin 2) K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P q))))
    (A : Matrix (Fin 4) (Fin 4) K[X]) :
    fourOutputInteriorDirectional q M P (A*P)=
      pluckerOutputAction q (fourOutputInteriorMinors q M P) A := by
  let V := polynomialKernelBasisMatrix (observabilityMatrix M P q) B
  obtain ⟨L,_,_,_,_,hHJ⟩ := polynomial_kernel_basis_completion (observabilityMatrix M P q) S hS B
  let H := (Matrix.fromCols S V).submatrix id (interiorPrefixEquiv 2 2 q)
  let J := (Matrix.fromRows (observabilityMatrix M P q) L).submatrix (interiorPrefixEquiv 2 2 q) id
  have hprod : H*J=1 := by
    dsimp only [H,J]
    rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_id_id]
    exact hHJ
  have hd : H.det*J.det=1 := by rw [← Matrix.det_mul,hprod,Matrix.det_one]
  exact four_output_directional_action_of_completion q M P A S V hS
    (polynomialKernelBasisMatrix_mul _ B) (isUnit_iff_dvd_one.mpr ⟨_,hd.symm⟩)

def fourOutputInteriorRow (q : ℕ) (i : Fin 6) : Fin (4*q+2) → Fin 4 :=
  fun k => Sum.elim (fun t : Fin q × Fin 4 => t.2) (fourOutputPluckerRows i)
    (interiorPrefixEquiv 2 2 q k)

private theorem fourOutputInteriorLevel_prefix (q : ℕ) (t : Fin q) (a : Fin 4) :
    interiorLevel 2 2 q ((interiorPrefixEquiv 2 2 q).symm (Sum.inl (t,a)))=t.val := by
  change (4*t.val+a.val)/4=t.val
  omega

theorem four_output_selected_matrix_fromRows (q : ℕ)
    (M : Matrix (Fin (4*q+2)) (Fin (4*q+2)) R)
    (P : Matrix (Fin 4) (Fin (4*q+2)) R) (i : Fin 6) :
    observabilitySelectedMatrix M P (interiorLevel 2 2 q) (fourOutputInteriorRow q i)=
      (Matrix.fromRows (observabilityMatrix M P q)
        ((P*M^q).submatrix (fourOutputPluckerRows i) id)).submatrix
          (interiorPrefixEquiv 2 2 q) id := by
  funext k j
  obtain ⟨w,rfl⟩ := (interiorPrefixEquiv 2 2 q).symm.surjective k
  rcases w with ⟨t,a⟩|a
  · simp only [observabilitySelectedMatrix,fourOutputInteriorRow,Equiv.apply_symm_apply,
      Sum.elim_inl,fourOutputInteriorLevel_prefix,Matrix.submatrix_apply,
      Matrix.fromRows_apply_inl,observabilityMatrix,id_eq]
  · simp only [observabilitySelectedMatrix,fourOutputInteriorRow,Equiv.apply_symm_apply,
      Sum.elim_inr,interiorPrefixEquiv_symm_inr,interiorLevel_missing,interiorPrefixEquiv_missing,
      Matrix.submatrix_apply,Matrix.fromRows_apply_inr,id_eq]

theorem fourOutputInteriorRow_lower_closed (q : ℕ) (i : Fin 6) :
    ∀ k t, t < interiorLevel 2 2 q k → ∀ a, ∃ l,
      interiorLevel 2 2 q l=t ∧ fourOutputInteriorRow q i l=a := by
  apply interior_lower_closed 2 2 q
  intro k hk
  simp only [fourOutputInteriorRow,interiorPrefixEquiv,Equiv.coe_fn_mk,hk,↓reduceDIte,
    Sum.elim_inl,interiorBaseRow]

def fourOutputScalarLiftMatrix (q : ℕ)
    (M : Matrix (Fin (4*q+2)) (Fin (4*q+2)) R)
    (P : Matrix (Fin 4) (Fin (4*q+2)) R) :
    Matrix (SLInput (Fin (4*q+2)) (Fin 4)) (Fin 6) R :=
  fun k i => observabilityScalarLift M P (interiorLevel 2 2 q) (fourOutputInteriorRow q i) k

theorem four_output_scalar_lift_directional (q : ℕ)
    (M : Matrix (Fin (4*q+2)) (Fin (4*q+2)) R)
    (P Q : Matrix (Fin 4) (Fin (4*q+2)) R) :
    (fun i => matrixPairTraceFunctional 0 Q (fun k => fourOutputScalarLiftMatrix q M P k i))=
      fourOutputInteriorDirectional q M P Q := by
  funext i
  have h := observabilitySelectedMatrix_output_differential M P Q
    (interiorLevel 2 2 q) (fourOutputInteriorRow q i)
  rw [four_output_selected_matrix_fromRows q M P i,four_output_selected_matrix_fromRows q M Q i] at h
  simpa only [fourOutputScalarLiftMatrix,matrixPairTraceFunctional,observabilityScalarLift,
    LinearMap.coe_mk,AddHom.coe_mk,LinearEquiv.apply_symm_apply,Matrix.zero_mul,
    Matrix.trace_zero,zero_add,fourOutputInteriorDirectional,
    four_output_selected_matrix_fromRows] using h.symm

theorem four_output_scalar_lift_output_action {K : Type*} [Field K] (q : ℕ)
    (M : Matrix (Fin (4*q+2)) (Fin (4*q+2)) K[X])
    (P : Matrix (Fin 4) (Fin (4*q+2)) K[X])
    (S : Matrix (Fin (4*q+2)) (Fin q × Fin 4) K[X])
    (hS : observabilityMatrix M P q*S=1)
    (B : Basis (Fin 2) K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P q))))
    (A : Matrix (Fin 4) (Fin 4) K[X]) :
    (fun i => matrixPairTraceFunctional 0 (A*P) (fun k => fourOutputScalarLiftMatrix q M P k i))=
      pluckerOutputAction q (fourOutputInteriorMinors q M P) A := by
  rw [four_output_scalar_lift_directional]
  exact four_output_directional_action q M P S hS B A

theorem fourOutputScalarLiftMatrix_kernel {K : Type*} [Field K] (q : ℕ)
    (M : Matrix (Fin (4*q+2)) (Fin (4*q+2)) K[X])
    (P : Matrix (Fin 4) (Fin (4*q+2)) K[X]) (i₀ : Fin (4*q+2)) :
    slEquationMatrix M P i₀*fourOutputScalarLiftMatrix q M P=0 := by
  funext k i
  exact congrFun (observabilityScalarLift_sl_kernel M P (interiorLevel 2 2 q)
    (fourOutputInteriorRow q i) (fourOutputInteriorRow_lower_closed q i) i₀) k

end FD56
