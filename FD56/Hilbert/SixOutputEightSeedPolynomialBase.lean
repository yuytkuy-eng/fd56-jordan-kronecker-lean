/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputEightSeedData
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

def sixOutputEightSeedU : Fin 6 → R[X] := fun i => integerPolynomial (sixOutputEightSeedUData i)
def sixOutputEightSeedV : Fin 6 → R[X] := fun i => integerPolynomial (sixOutputEightSeedVData i)

def sixOutputEightSeedWitness : Matrix (Fin 15) (Fin 15) R[X] :=
  sixOutputPluckerTangent (twoColumnWedge sixOutputEightSeedU sixOutputEightSeedV)

private def wedgeData (i j : Fin 6) : List ℤ :=
  integerPolynomialAdd (integerPolynomialMul (sixOutputEightSeedUData i) (sixOutputEightSeedVData j))
    ((integerPolynomialMul (sixOutputEightSeedUData j) (sixOutputEightSeedVData i)).map (-·))

def sixOutputEightSeedComputedData : Matrix (Fin 15) (Fin 15) (List ℤ) := fun i j =>
  let q := sixOutputQuad i
  let p := sixOutputPair j
  if p=(q 0,q 1) then wedgeData (q 2) (q 3) else
  if p=(q 0,q 2) then (wedgeData (q 1) (q 3)).map (-·) else
  if p=(q 0,q 3) then wedgeData (q 1) (q 2) else
  if p=(q 1,q 2) then wedgeData (q 0) (q 3) else
  if p=(q 1,q 3) then (wedgeData (q 0) (q 2)).map (-·) else
  if p=(q 2,q 3) then wedgeData (q 0) (q 1) else []

def sixOutputEightSeedPolynomialData : Matrix (Fin 15) (Fin 15) (List ℤ) :=
  ![![[],[],[],[],[],[0,0,0,0,1],[0,1],[],[],[-1],[],[],[],[],[]],
    ![[0,0,0,1],[0,0,-1],[],[],[],[0,0,0,0,1],[],[0,1],[],[],[-1],[],[],[],[]],
    ![[0,0,0,0,0,-1],[0,0,0,0,1],[],[],[],[0,0,0,1,0,0,-1],[],[],[0,1],[],[],[-1],[],[],[]],
    ![[0,0,0,0,0,0,-1],[],[0,0,-1],[],[],[],[0,0,0,0,1],[0,0,0,0,-1],[],[],[],[],[-1],[],[]],
    ![[0,0,0,0,0,0,0,0,1],[],[0,0,0,0,1],[],[],[],[0,0,0,1,0,0,-1],[],[0,0,0,0,-1],[],[],[],[],[-1],[]],
    ![[0,0,0,0,0,1],[],[],[0,0,0,0,1],[0,0,1],[],[],[0,0,0,1,0,0,-1],[0,0,0,0,-1],[],[],[],[],[],[-1]],
    ![[],[0,0,0,0,0,0,-1],[0,0,0,-1],[],[],[],[],[],[],[0,0,0,0,1],[0,0,0,0,-1],[],[0,-1],[],[]],
    ![[],[0,0,0,0,0,0,0,0,1],[0,0,0,0,0,1],[],[],[],[],[],[],[0,0,0,1,0,0,-1],[],[0,0,0,0,-1],[],[0,-1],[]],
    ![[],[0,0,0,0,0,1],[],[0,0,0,0,0,1],[0,0,0,1],[],[],[],[],[],[0,0,0,1,0,0,-1],[0,0,0,0,-1],[],[],[0,-1]],
    ![[],[],[0,0,0,0,0,1],[0,0,0,0,0,0,0,0,-1],[0,0,0,0,0,0,-1],[],[],[],[],[],[],[],[0,0,0,1,0,0,-1],[0,0,0,0,-1],[0,0,0,0,1]],
    ![[],[],[],[],[],[0,0,0,0,0,0,-1],[0,0,0,-1],[],[],[0,0,1],[],[],[],[],[]],
    ![[],[],[],[],[],[0,0,0,0,0,0,0,0,1],[0,0,0,0,0,1],[],[],[0,0,0,0,-1],[],[],[],[],[]],
    ![[],[],[],[],[],[0,0,0,0,0,1],[],[0,0,0,0,0,1],[0,0,0,1],[],[0,0,0,0,-1],[0,0,-1],[],[],[]],
    ![[],[],[],[],[],[],[0,0,0,0,0,1],[0,0,0,0,0,0,0,0,-1],[0,0,0,0,0,0,-1],[],[],[],[0,0,0,0,-1],[0,0,-1],[]],
    ![[],[],[],[],[],[],[],[],[],[0,0,0,0,0,1],[0,0,0,0,0,0,0,0,-1],[0,0,0,0,0,0,-1],[0,0,0,0,0,-1],[0,0,0,-1],[]]]

theorem sixOutputEightSeed_computed_polynomial (i j : Fin 15) :
    integerPolynomial (K:=R) (sixOutputEightSeedComputedData i j)=sixOutputEightSeedWitness i j := by
  dsimp only [sixOutputEightSeedComputedData,sixOutputEightSeedWitness,sixOutputPluckerTangent]
  split_ifs <;>
    simp [wedgeData,integerPolynomial_add,integerPolynomial_mul,integerPolynomial_neg,
      sixOutputEightSeedU,sixOutputEightSeedV,twoColumnWedge,sub_eq_add_neg]

end FD56
