/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ObservabilityScalarAdjugateDegree
import FD56.Stabilizer.ObservabilityScalarAdjugateMap
import FD56.Stabilizer.OddTwoObservabilitySelectors
import FD56.Hilbert.SLScalarCrossVanishing

/-! Two explicit scalar lifts of the predicted degree in every odd state dimension. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

theorem oddTwo_row_weight (q : ℕ) :
    (∑ k : Fin (2*q+1), (oddTwoLevel q k+1))=q*(q+2)+1 := by
  have haux (r : ℕ) : (∑ k : Fin (2*r), (k.val/2+1))=r*(r+1) := by
    induction r with
    | zero => simp
    | succ r ih =>
      have he : 2*(r+1)=2*r+1+1 := by omega
      rw [he,Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
      simp only [Fin.coe_castSucc,Fin.val_last]
      rw [ih]
      have h₀ : 2*r/2=r := by omega
      have h₁ : (2*r+1)/2=r := by omega
      rw [h₀,h₁]
      ring
  simp only [oddTwoLevel,Fin.sum_univ_castSucc,Fin.coe_castSucc,Fin.val_last]
  rw [haux]
  have h : 2*q/2=q := by omega
  rw [h]
  ring

variable {R : Type*} [CommRing R]

def oddTwoScalarMatrix (q : ℕ) (M : Matrix (Fin (2*q+1)) (Fin (2*q+1)) R)
    (P : Matrix (Fin 2) (Fin (2*q+1)) R) (j : Fin 2) :
    Matrix (Fin (2*q+1)) (Fin (2*q+1)) R :=
  observabilitySelectedMatrix M P (oddTwoLevel q) (oddTwoRow q j)

def oddTwoScalarValue (q : ℕ) (M : Matrix (Fin (2*q+1)) (Fin (2*q+1)) R)
    (P : Matrix (Fin 2) (Fin (2*q+1)) R) (j : Fin 2) : R :=
  -(oddTwoScalarMatrix q M P j).det

def oddTwoScalarLift (q : ℕ) (M : Matrix (Fin (2*q+1)) (Fin (2*q+1)) R)
    (P : Matrix (Fin 2) (Fin (2*q+1)) R) (j : Fin 2) :
    SLInput (Fin (2*q+1)) (Fin 2) → R :=
  (matrixPairEquiv R R (Fin (2*q+1)) (Fin 2)).symm
    (observabilityScalarX M P (oddTwoScalarMatrix q M P j).adjugate (oddTwoLevel q) (oddTwoRow q j),
      observabilityScalarU M (oddTwoScalarMatrix q M P j).adjugate (oddTwoLevel q) (oddTwoRow q j))

theorem oddTwoScalarMatrix_map {S : Type*} [CommRing S] (φ : R →+* S)
    (q : ℕ) (M : Matrix (Fin (2*q+1)) (Fin (2*q+1)) R)
    (P : Matrix (Fin 2) (Fin (2*q+1)) R) (j : Fin 2) :
    (oddTwoScalarMatrix q M P j).map φ=oddTwoScalarMatrix q (M.map φ) (P.map φ) j :=
  observabilitySelectedMatrix_map φ M P (oddTwoLevel q) (oddTwoRow q j)

theorem oddTwoScalarValue_map {S : Type*} [CommRing S] (φ : R →+* S)
    (q : ℕ) (M : Matrix (Fin (2*q+1)) (Fin (2*q+1)) R)
    (P : Matrix (Fin 2) (Fin (2*q+1)) R) (j : Fin 2) :
    φ (oddTwoScalarValue q M P j)=oddTwoScalarValue q (M.map φ) (P.map φ) j := by
  unfold oddTwoScalarValue
  rw [map_neg,φ.map_det,RingHom.mapMatrix_apply,oddTwoScalarMatrix_map]

theorem oddTwoScalarLift_map {S : Type*} [CommRing S] (φ : R →+* S)
    (q : ℕ) (M : Matrix (Fin (2*q+1)) (Fin (2*q+1)) R)
    (P : Matrix (Fin 2) (Fin (2*q+1)) R) (j : Fin 2) :
    (fun k => φ (oddTwoScalarLift q M P j k))=oddTwoScalarLift q (M.map φ) (P.map φ) j := by
  have hC : ((oddTwoScalarMatrix q M P j).adjugate).map φ=
      (oddTwoScalarMatrix q (M.map φ) (P.map φ) j).adjugate := by
    rw [← RingHom.mapMatrix_apply,φ.map_adjugate,RingHom.mapMatrix_apply,oddTwoScalarMatrix_map]
  funext k
  rcases k with ij | ij
  · have h := observabilityScalarX_map φ M P (oddTwoScalarMatrix q M P j).adjugate
      (oddTwoLevel q) (oddTwoRow q j)
    rw [hC] at h
    exact congrFun (congrFun h ij.1) ij.2
  · have h := observabilityScalarU_map φ M (oddTwoScalarMatrix q M P j).adjugate
      (oddTwoLevel q) (oddTwoRow q j)
    rw [hC] at h
    exact congrFun (congrFun h ij.1) ij.2

variable {K : Type*} [Field K]

theorem oddTwoScalarLift_equation (q : ℕ)
    (M : Matrix (Fin (2*q+1)) (Fin (2*q+1)) K[X])
    (P : Matrix (Fin 2) (Fin (2*q+1)) K[X]) (j : Fin 2) :
    glEquationMatrix M P *ᵥ oddTwoScalarLift q M P j =
      oddTwoScalarValue q M P j • glScalarVector K[X] (Fin (2*q+1)) (Fin 2) := by
  apply (glEquationMatrix_scalar_iff _ _ _ _).mpr
  simp only [oddTwoScalarLift,LinearEquiv.apply_symm_apply]
  obtain ⟨hP,_,hc⟩ := observability_adjugate_scalar_equations M P
    (oddTwoLevel q) (oddTwoRow q j) (oddTwo_lower_closed q j)
  refine ⟨hP,?_⟩
  change M*_ - _*M - _*P = _
  dsimp only [oddTwoScalarMatrix,oddTwoScalarValue]
  rw [hc,add_sub_cancel_left]

theorem oddTwoScalarLift_degree (q : ℕ)
    (M : Matrix (Fin (2*q+1)) (Fin (2*q+1)) K[X])
    (P : Matrix (Fin 2) (Fin (2*q+1)) K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (j : Fin 2) :
    (∀ k, (oddTwoScalarLift q M P j k).natDegree ≤ q*(q+2)) ∧
      (oddTwoScalarValue q M P j).natDegree ≤ q*(q+2)+1 := by
  obtain ⟨hX,hU,hF⟩ := observability_adjugate_solution_degree M P hM hP
    (oddTwoLevel q) (oddTwoRow q j) (q*(q+2)) (oddTwo_row_weight q)
  constructor
  · intro k
    rcases k with ij | ij
    · exact hX ij.1 ij.2
    · exact hU ij.1 ij.2
  · simpa only [oddTwoScalarValue,oddTwoScalarMatrix,Polynomial.natDegree_neg] using hF

end FD56
