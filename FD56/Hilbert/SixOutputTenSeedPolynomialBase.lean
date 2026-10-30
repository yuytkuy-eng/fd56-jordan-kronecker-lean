/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputTenSeedData
import FD56.LinearAlgebra.SelectedPolynomialCoefficients
import FD56.LinearAlgebra.RankSpecializationExtension
import FD56.Hilbert.IntegerPolynomial
import FD56.LinearAlgebra.SixOutputPluckerTangent

/-! An integral frame and the actual fifteen-equation Plucker tangent. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
variable {R : Type*} [CommRing R]

def sixOutputTenSeedU : Fin 6 → R[X] := fun i => integerPolynomial (sixOutputTenSeedUData i)
def sixOutputTenSeedV : Fin 6 → R[X] := fun i => integerPolynomial (sixOutputTenSeedVData i)

def sixOutputTenSeedWitness : Matrix (Fin 15) (Fin 15) R[X] :=
  sixOutputPluckerTangent (twoColumnWedge sixOutputTenSeedU sixOutputTenSeedV)

private def wedgeData (i j : Fin 6) : List ℤ :=
  integerPolynomialAdd (integerPolynomialMul (sixOutputTenSeedUData i) (sixOutputTenSeedVData j))
    ((integerPolynomialMul (sixOutputTenSeedUData j) (sixOutputTenSeedVData i)).map (-·))

def sixOutputTenSeedComputedData : Matrix (Fin 15) (Fin 15) (List ℤ) := fun i j =>
  let q := sixOutputQuad i
  let p := sixOutputPair j
  if p=(q 0,q 1) then wedgeData (q 2) (q 3) else
  if p=(q 0,q 2) then (wedgeData (q 1) (q 3)).map (-·) else
  if p=(q 0,q 3) then wedgeData (q 1) (q 2) else
  if p=(q 1,q 2) then wedgeData (q 0) (q 3) else
  if p=(q 1,q 3) then (wedgeData (q 0) (q 2)).map (-·) else
  if p=(q 2,q 3) then wedgeData (q 0) (q 1) else []

def sixOutputTenSeedPolynomialData : Matrix (Fin 15) (Fin 15) (List ℤ) :=
  ![![[0,0,0,0,0,0,0,1],[],[0,0,-1,0,0,0,-1],[],[],[0,0,0,0,0,-1],[],[],[],[-1,0,0,0,-1],[],[],[],[],[]],
    ![[0,0,0,0,0,-1],[0,0,0,1,0,0,0,1],[],[0,0,-1,0,0,0,-1],[],[0,0,0,1],[],[],[],[],[-1,0,0,0,-1],[],[],[],[]],
    ![[0,0,0,0,1],[0,0,0,0,0,1,0,0,0,1],[],[],[0,0,-1,0,0,0,-1],[0,0,-1],[],[],[],[],[],[-1,0,0,0,-1],[],[],[]],
    ![[0,0,0,0,0,0,0,0,-1],[],[0,0,0,1,0,0,0,1],[],[],[],[0,0,0,1],[0,0,0,0,0,1],[],[],[],[],[-1,0,0,0,-1],[],[]],
    ![[0,0,0,0,0,0,0,0,0,0,-1],[],[0,0,0,0,0,1,0,0,0,1],[],[],[],[0,0,-1],[],[0,0,0,0,0,1],[],[],[],[],[-1,0,0,0,-1],[]],
    ![[0,0,0,0,0,1,0,0,1],[],[],[0,0,0,0,0,1,0,0,0,1],[0,0,0,-1,0,0,0,-1],[],[],[0,0,-1],[0,0,0,-1],[],[],[],[],[],[-1,0,0,0,-1]],
    ![[],[0,0,0,0,0,0,0,0,-1],[0,0,0,0,0,1],[0,0,0,0,0,0,0,1],[],[],[],[],[],[0,0,0,1],[0,0,0,0,0,1],[],[],[],[]],
    ![[],[0,0,0,0,0,0,0,0,0,0,-1],[0,0,0,0,-1],[],[0,0,0,0,0,0,0,1],[],[],[],[],[0,0,-1],[],[0,0,0,0,0,1],[],[],[]],
    ![[],[0,0,0,0,0,1,0,0,1],[],[0,0,0,0,-1],[0,0,0,0,0,-1],[],[],[],[],[],[0,0,-1],[0,0,0,-1],[],[],[]],
    ![[],[],[0,0,0,0,0,1,0,0,1],[0,0,0,0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,0,-1],[],[],[],[],[],[],[],[0,0,-1],[0,0,0,-1],[0,0,0,0,0,-1]],
    ![[],[],[],[],[],[0,0,0,0,0,0,0,0,-1],[0,0,0,0,0,1],[0,0,0,0,0,0,0,1],[],[0,0,0,-1,0,0,0,-1],[],[],[0,0,-1,0,0,0,-1],[],[]],
    ![[],[],[],[],[],[0,0,0,0,0,0,0,0,0,0,-1],[0,0,0,0,-1],[],[0,0,0,0,0,0,0,1],[0,0,0,0,0,-1,0,0,0,-1],[],[],[],[0,0,-1,0,0,0,-1],[]],
    ![[],[],[],[],[],[0,0,0,0,0,1,0,0,1],[],[0,0,0,0,-1],[0,0,0,0,0,-1],[],[0,0,0,0,0,-1,0,0,0,-1],[0,0,0,1,0,0,0,1],[],[],[0,0,-1,0,0,0,-1]],
    ![[],[],[],[],[],[],[0,0,0,0,0,1,0,0,1],[0,0,0,0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,0,-1],[],[],[],[0,0,0,0,0,-1,0,0,0,-1],[0,0,0,1,0,0,0,1],[]],
    ![[],[],[],[],[],[],[],[],[],[0,0,0,0,0,1,0,0,1],[0,0,0,0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,0,-1],[0,0,0,0,1],[0,0,0,0,0,1],[0,0,0,0,0,0,0,1]]]

theorem sixOutputTenSeed_computed_polynomial (i j : Fin 15) :
    integerPolynomial (K:=R) (sixOutputTenSeedComputedData i j)=sixOutputTenSeedWitness i j := by
  dsimp only [sixOutputTenSeedComputedData,sixOutputTenSeedWitness,sixOutputPluckerTangent]
  split_ifs <;>
    simp [wedgeData,integerPolynomial_add,integerPolynomial_mul,integerPolynomial_neg,
      sixOutputTenSeedU,sixOutputTenSeedV,twoColumnWedge,sub_eq_add_neg]

end FD56
