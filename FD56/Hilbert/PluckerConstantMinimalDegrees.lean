/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PluckerConstantOutputDerivation
import FD56.Hilbert.ConstantEquivalence
import FD56.Hilbert.MinimalProfile

/-! Constant invertible output changes preserve the ordinary six-coordinate
row's polynomial kernel Hilbert function and minimal degrees. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false

private theorem pluckerOutputChange_map {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (Q : Matrix (Fin 4) (Fin 4) A) (F : Fin 6 → A) :
    (fun i => φ (pluckerOutputChange Q F i))=
      pluckerOutputChange (Q.map φ) (fun i => φ (F i)) := by
  have hskew : (pluckerSkewMatrix F).map φ=pluckerSkewMatrix (fun i => φ (F i)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pluckerSkewMatrix]
  have hupper (T : Matrix (Fin 4) (Fin 4) A) :
      (fun i => φ (pluckerUpperCoordinates T i))=pluckerUpperCoordinates (T.map φ) := by
    ext i
    fin_cases i <;> rfl
  change (fun i => φ (pluckerUpperCoordinates (Q*pluckerSkewMatrix F*Q.transpose) i))=_
  rw [hupper,Matrix.map_mul,Matrix.map_mul,hskew]
  rfl

private def pluckerOutputMatrix {A : Type*} [CommRing A]
    (Q : Matrix (Fin 4) (Fin 4) A) : Matrix (Fin 6) (Fin 6) A :=
  LinearMap.toMatrix' (pluckerOutputChange Q)

private theorem pluckerOutputMatrix_map {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (Q : Matrix (Fin 4) (Fin 4) A) :
    (pluckerOutputMatrix Q).map φ=pluckerOutputMatrix (Q.map φ) := by
  ext i j
  simp only [pluckerOutputMatrix,Matrix.map_apply,LinearMap.toMatrix'_apply]
  have h := congrFun (pluckerOutputChange_map φ Q (fun k => if k=j then 1 else 0)) i
  simpa only [apply_ite,map_one,map_zero] using h

private theorem pluckerOutputMatrix_mul {A : Type*} [CommRing A]
    (Q S : Matrix (Fin 4) (Fin 4) A) :
    pluckerOutputMatrix Q*pluckerOutputMatrix S=pluckerOutputMatrix (Q*S) := by
  unfold pluckerOutputMatrix
  rw [← LinearMap.toMatrix'_comp]
  congr 1
  apply LinearMap.ext
  intro F
  exact pluckerOutputChange_mul Q S F

private theorem pluckerOutputMatrix_one {A : Type*} [CommRing A] :
    pluckerOutputMatrix (1 : Matrix (Fin 4) (Fin 4) A)=1 := by
  unfold pluckerOutputMatrix
  have h : pluckerOutputChange (1 : Matrix (Fin 4) (Fin 4) A)=LinearMap.id := by
    apply LinearMap.ext
    intro F
    exact pluckerOutputChange_one F
  rw [h,LinearMap.toMatrix'_id]

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

private theorem constant_output_row_equation (Q : Matrix (Fin 4) (Fin 4) K)
    (F : Fin 6 → L[X]) :
    (show Matrix Unit (Fin 6) L[X] from fun _ => F)*
      ((pluckerOutputMatrix Q).map (algebraMap K L)).transpose.map C=
      (fun _ : Unit => pluckerConstantOutputChange Q F) := by
  rw [← Matrix.transpose_map,Matrix.map_map]
  change (show Matrix Unit (Fin 6) L[X] from fun _ : Unit => F)*
    ((pluckerOutputMatrix Q).map (C.comp (algebraMap K L))).transpose=_
  rw [pluckerOutputMatrix_map]
  have h := congrArg (fun f => f F)
    (Matrix.toLin'_toMatrix' (pluckerOutputChange (Q.map (C.comp (algebraMap K L)))))
  funext u j
  have hj := congrFun h j
  change ∑ k, F k*pluckerOutputMatrix (Q.map (C.comp (algebraMap K L))) j k=_
  change (∑ k, pluckerOutputMatrix (Q.map (C.comp (algebraMap K L))) j k*F k)=_ at hj
  simpa only [mul_comm] using hj

theorem pluckerConstantOutputChange_kernel_hilbert
    (Q S : Matrix (Fin 4) (Fin 4) K) (hQS : Q*S=1) (hSQ : S*Q=1)
    (F : Fin 6 → L[X]) (d : ℕ) :
    Module.finrank L (polynomialKernelAtDegree
      (fun _ : Unit => pluckerConstantOutputChange Q F) d)=
      Module.finrank L (polynomialKernelAtDegree (fun _ : Unit => F) d) := by
  let V := ((pluckerOutputMatrix Q).map (algebraMap K L)).transpose
  let W := ((pluckerOutputMatrix S).map (algebraMap K L)).transpose
  have hVW : V*W=1 := by
    dsimp only [V,W]
    rw [← Matrix.transpose_mul,← Matrix.map_mul,pluckerOutputMatrix_mul,hSQ,
      pluckerOutputMatrix_one,Matrix.map_one,Matrix.transpose_one] <;> simp
  have hWV : W*V=1 := by
    dsimp only [V,W]
    rw [← Matrix.transpose_mul,← Matrix.map_mul,pluckerOutputMatrix_mul,hQS,
      pluckerOutputMatrix_one,Matrix.map_one,Matrix.transpose_one] <;> simp
  have hrow := constant_output_row_equation Q F
  apply constant_equivalence_kernel_hilbert (fun _ : Unit => F)
    (fun _ : Unit => pluckerConstantOutputChange Q F) 1 1 V W
  · simpa using hrow
  · rw [← hrow,Matrix.mul_assoc,← Matrix.map_mul,hVW]
    simp
  · exact hVW
  · exact hWV

theorem pluckerConstantOutputChange_minimal_degrees_iff
    (Q S : Matrix (Fin 4) (Fin 4) K) (hQS : Q*S=1) (hSQ : S*Q=1)
    (F : Fin 6 → L[X]) (xs : List ℕ) :
    HasMinimalKernelDegrees (fun _ : Unit => pluckerConstantOutputChange Q F) xs ↔
      HasMinimalKernelDegrees (fun _ : Unit => F) xs := by
  rw [hasMinimalKernelDegrees_iff_hilbert,hasMinimalKernelDegrees_iff_hilbert]
  simp only [pluckerConstantOutputChange_kernel_hilbert Q S hQS hSQ F]

end FD56
