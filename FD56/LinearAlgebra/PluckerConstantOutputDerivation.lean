/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PluckerOutputActionTransport
import FD56.LinearAlgebra.PolynomialDerivationImage

/-! A constant base-field output change preserves polynomial degree bounds
and the rank of coefficient derivations on the six Plucker coordinates. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

def pluckerConstantOutputChange (Q : Matrix (Fin 4) (Fin 4) K) :
    (Fin 6 → L[X]) →ₗ[L] (Fin 6 → L[X]) :=
  (pluckerOutputChange (Q.map (Polynomial.C.comp (algebraMap K L)))).restrictScalars L

private theorem pluckerConstantOutputChange_inverse
    (Q S : Matrix (Fin 4) (Fin 4) K) (hSQ : S*Q=1) (F : Fin 6 → L[X]) :
    pluckerConstantOutputChange S (pluckerConstantOutputChange Q F)=F := by
  change pluckerOutputChange _ (pluckerOutputChange _ F)=F
  rw [pluckerOutputChange_mul,← Matrix.map_mul,hSQ,Matrix.map_one,
    pluckerOutputChange_one] <;> simp

private def pluckerConstantOutputEquiv
    (Q S : Matrix (Fin 4) (Fin 4) K) (hQS : Q*S=1) (hSQ : S*Q=1) :
    (Fin 6 → L[X]) ≃ₗ[L] (Fin 6 → L[X]) where
  toLinearMap := pluckerConstantOutputChange Q
  invFun := pluckerConstantOutputChange S
  left_inv := pluckerConstantOutputChange_inverse Q S hSQ
  right_inv := pluckerConstantOutputChange_inverse S Q hQS

theorem pluckerConstantOutputChange_derivation
    (Q : Matrix (Fin 4) (Fin 4) K) (F : Fin 6 → L[X]) (D : Derivation K L L) :
    polynomialDerivationImageMap (pluckerConstantOutputChange Q F) D=
      pluckerConstantOutputChange Q (polynomialDerivationImageMap F D) := by
  let Qp := Q.map (Polynomial.C.comp (algebraMap K L))
  let δ := polynomialCoefficientDerivation D
  have hQ : Qp.map δ=0 := by
    ext i j
    simp [Qp,δ,polynomialCoefficientDerivation_C,Derivation.map_algebraMap]
  have hskew : (pluckerSkewMatrix F).map δ=
      pluckerSkewMatrix (fun i => δ (F i)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pluckerSkewMatrix]
  have hprod : (Qp*pluckerSkewMatrix F*Qp.transpose).map δ=
      Qp*pluckerSkewMatrix (fun i => δ (F i))*Qp.transpose := by
    rw [matrix_derivation_mul,matrix_derivation_mul,hQ,hskew]
    simp only [Matrix.transpose_map,hQ,Matrix.transpose_zero,Matrix.zero_mul,
      Matrix.mul_zero,zero_add,add_zero]
  have hupper (A : Matrix (Fin 4) (Fin 4) L[X]) :
      (fun i => δ (pluckerUpperCoordinates A i))=pluckerUpperCoordinates (A.map δ) := by
    funext i
    fin_cases i <;> rfl
  change (fun i => δ (pluckerUpperCoordinates (Qp*pluckerSkewMatrix F*Qp.transpose) i))=
    pluckerUpperCoordinates (Qp*pluckerSkewMatrix (fun i => δ (F i))*Qp.transpose)
  rw [hupper,hprod]

theorem pluckerConstantOutputChange_derivation_rank
    (Q S : Matrix (Fin 4) (Fin 4) K) (hQS : Q*S=1) (hSQ : S*Q=1)
    (F : Fin 6 → L[X]) :
    Module.finrank L (LinearMap.range (polynomialDerivationImageMap
      (pluckerConstantOutputChange Q F) : Derivation K L L →ₗ[L] (Fin 6 → L[X])))=
    Module.finrank L (LinearMap.range (polynomialDerivationImageMap F :
      Derivation K L L →ₗ[L] (Fin 6 → L[X]))) := by
  let E := pluckerConstantOutputEquiv (L:=L) Q S hQS hSQ
  have hmap : polynomialDerivationImageMap (pluckerConstantOutputChange Q F)=
      E.toLinearMap.comp (polynomialDerivationImageMap F :
        Derivation K L L →ₗ[L] (Fin 6 → L[X])) := by
    apply LinearMap.ext
    intro D
    exact pluckerConstantOutputChange_derivation Q F D
  rw [hmap,LinearMap.range_comp]
  exact E.finrank_map_eq _

theorem pluckerConstantOutputChange_degree_bound
    (Q : Matrix (Fin 4) (Fin 4) K) (F : Fin 6 → L[X]) (W : ℕ)
    (hF : ∀ i, (F i).natDegree≤W) :
    ∀ i, (pluckerConstantOutputChange Q F i).natDegree≤W := by
  let Qp := Q.map (Polynomial.C.comp (algebraMap K L))
  have hQ : DegreeBound Qp 0 := by intro i j; simp [Qp]
  have hQt : DegreeBound Qp.transpose 0 := fun i j => hQ j i
  have hskew : DegreeBound (pluckerSkewMatrix F) W := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [pluckerSkewMatrix] <;>
      first | exact hF 0 | exact hF 1 | exact hF 2 | exact hF 3 | exact hF 4 | exact hF 5
  have hprod : DegreeBound (Qp*pluckerSkewMatrix F*Qp.transpose) W := by
    simpa using degreeBound_mul (degreeBound_mul hQ hskew) hQt
  intro i
  fin_cases i <;> exact hprod _ _

theorem pluckerConstantOutputChange_quadric
    (Q : Matrix (Fin 4) (Fin 4) K) (F : Fin 6 → L[X]) :
    pluckerQuadric (pluckerConstantOutputChange Q F)=
      C (algebraMap K L Q.det)*pluckerQuadric F := by
  change pluckerQuadric (pluckerOutputChange _ F)=_
  rw [pluckerOutputChange_quadric]
  exact congrArg (fun x => x*pluckerQuadric F)
    ((Polynomial.C.comp (algebraMap K L)).map_det Q).symm

end FD56
