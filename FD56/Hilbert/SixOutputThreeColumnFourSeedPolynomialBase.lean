/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnFourSeedMinors
import FD56.LinearAlgebra.SelectedPolynomialCoefficients
import FD56.LinearAlgebra.RankSpecializationExtension

/-! Integral coefficients bound to the actual twenty-equation triple tangent. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
variable {R : Type*} [CommRing R]

def sixOutputThreeColumnFourSeedComputedData (r j : Fin 20) : List ℤ :=
  ((sixOutputTriplePluckerTermData r).map fun t =>
    (integerPolynomialAdd
      (if j=t.2.1 then sixOutputThreeColumnFourSeedMinorData t.2.2 else [])
      (if j=t.2.2 then sixOutputThreeColumnFourSeedMinorData t.2.1 else [])).map (t.1*·)).foldr integerPolynomialAdd []

def sixOutputThreeColumnFourSeedPolynomialData : Matrix (Fin 20) (Fin 20) (List ℤ) :=
  ![![[],[0,0,0,0,0,-1,-1,0,0,-1],[],[],[0,0,0,0,0,0,0,0,0,0,-1],[],[],[0,0,0,0,0,0,0,0,0,-1,0,0,-1],[],[],[],[],[],[],[],[],[],[],[],[]],![[],[0,0,0,0,0,0,1,0,1],[],[],[0,0,0,0,0,0,0,0,-1,0,-1],[],[],[],[0,0,0,0,0,0,0,0,0,-1,0,0,-1],[],[],[],[],[],[],[],[],[],[],[]],![[0,0,0,0,-1,-1,-1,-1],[],[0,0,0,0,0,0,1,0,1],[0,0,0,0,0,1,1,0,0,1],[],[0,0,0,0,0,0,0,0,-1,0,-1],[0,0,0,0,0,0,0,0,0,0,1],[],[],[0,0,0,0,0,0,0,0,0,-1,0,0,-1],[],[],[],[],[],[],[],[],[],[]],![[0,0,0,0,0,0,1],[],[0,0,0,0,0,-1,0,0,-1],[],[],[],[],[],[],[],[0,0,0,0,0,0,0,0,0,0,-1],[],[],[0,0,0,0,0,0,0,0,0,-1,0,0,-1],[],[],[],[],[],[]],![[0,0,0,0,1,0,1],[0,0,0,0,0,0,-1,0,0,-1],[],[0,0,0,0,0,-1,0,0,-1],[],[],[],[],[],[],[0,0,0,0,0,0,0,0,-1,0,-1],[],[],[],[0,0,0,0,0,0,0,0,0,-1,0,0,-1],[],[],[],[],[]],![[0,0,0,0,0,0,0,1],[],[0,0,0,0,0,0,-1,0,0,-1],[],[],[],[],[],[],[],[],[0,0,0,0,0,0,0,0,-1,0,-1],[0,0,0,0,0,0,0,0,0,0,1],[],[],[0,0,0,0,0,0,0,0,0,-1,0,0,-1],[],[],[],[]],![[1,1,1,1],[0,0,-1,-1,0,0,-1],[0,0,-1,0,-1],[0,-1,-1,0,0,-1],[],[],[],[],[],[],[],[],[],[],[],[],[0,0,0,0,0,0,0,0,-1,0,-1],[0,0,0,0,0,0,0,0,0,0,1],[],[0,0,0,0,0,0,0,0,0,1,0,0,1]],![[0,-1,-1,0,0,-1],[],[],[],[],[0,0,0,0,0,-1,0,0,-1],[],[],[],[],[0,0,0,0,0,1,1,0,0,1],[],[],[],[],[],[0,0,0,0,0,0,0,0,0,-1,0,0,-1],[],[],[]],![[0,0,1,0,1],[],[],[],[0,0,0,0,0,0,-1,0,0,-1],[],[0,0,0,0,0,-1,0,0,-1],[],[],[],[0,0,0,0,0,0,-1,0,-1],[],[],[],[],[],[],[0,0,0,0,0,0,0,0,0,-1,0,0,-1],[],[]],![[0,0,-1,-1,0,0,-1],[],[],[],[],[0,0,0,0,0,0,-1,0,0,-1],[],[],[],[],[],[0,0,0,0,0,0,-1,0,-1],[0,0,0,0,0,-1,-1,0,0,-1],[],[],[],[],[],[0,0,0,0,0,0,0,0,0,-1,0,0,-1],[]],![[-1,-1,-1,-1],[],[],[0,1,1,0,0,1],[],[],[0,0,0,0,0,0,1],[0,0,0,0,0,0,-1,0,0,-1],[],[],[],[],[],[0,0,0,0,0,0,-1,0,-1],[],[],[0,0,0,0,0,0,0,0,1,0,1],[],[],[0,0,0,0,0,0,0,0,0,-1,0,0,-1]],![[],[-1,-1,-1,-1],[],[],[],[],[],[0,0,0,0,-1,0,-1],[0,0,0,0,0,0,1],[],[],[],[],[],[],[],[],[],[],[]],![[],[],[-1,-1,-1,-1],[],[],[],[],[0,0,0,0,0,0,0,-1],[],[0,0,0,0,0,0,1],[],[],[],[0,0,0,0,-1,-1,-1,-1],[],[],[],[],[],[0,0,0,0,0,0,0,0,0,0,-1]],![[],[],[],[],[-1,-1,-1,-1],[],[],[0,0,-1,0,-1],[0,-1,-1,0,0,-1],[],[],[],[],[],[],[],[],[],[],[]],![[],[],[],[],[],[-1,-1,-1,-1],[],[0,0,1,1,0,0,1],[],[0,-1,-1,0,0,-1],[],[],[],[],[],[],[0,0,0,0,-1,-1,-1,-1],[],[],[0,0,0,0,0,1,1,0,0,1]],![[],[],[],[],[],[],[],[],[],[],[-1,-1,-1,-1],[],[],[0,0,-1,0,-1],[0,-1,-1,0,0,-1],[],[0,0,0,0,1,0,1],[0,0,0,0,0,0,-1],[],[0,0,0,0,0,-1,0,0,-1]],![[],[],[],[],[],[],[],[],[],[],[],[-1,-1,-1,-1],[],[0,0,1,1,0,0,1],[],[0,-1,-1,0,0,-1],[0,0,0,0,0,0,0,1],[],[0,0,0,0,0,0,-1],[]],![[],[],[],[-1,-1,-1,-1],[],[],[],[],[0,0,0,0,0,0,0,-1],[0,0,0,0,1,0,1],[],[],[],[],[0,0,0,0,-1,-1,-1,-1],[],[],[],[],[0,0,0,0,0,0,0,0,-1,0,-1]],![[],[],[],[],[],[],[-1,-1,-1,-1],[],[0,0,1,1,0,0,1],[0,0,1,0,1],[],[],[],[],[],[],[],[0,0,0,0,-1,-1,-1,-1],[],[0,0,0,0,0,0,-1,0,-1]],![[],[],[],[],[],[],[],[],[],[],[],[],[-1,-1,-1,-1],[],[0,0,1,1,0,0,1],[0,0,1,0,1],[],[0,0,0,0,0,0,0,1],[0,0,0,0,-1,0,-1],[0,0,0,0,0,0,1,0,0,1]]]

private theorem integerPolynomial_sum (l : List (List ℤ)) :
    integerPolynomial (K:=R) (l.foldr integerPolynomialAdd [])=
      (l.map (integerPolynomial (K:=R))).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.foldr_cons,integerPolynomial_add,List.map_cons,List.sum_cons,ih]

theorem sixOutputThreeColumnFourSeed_computed_polynomial (r j : Fin 20) :
    integerPolynomial (K:=R) (sixOutputThreeColumnFourSeedComputedData r j)=sixOutputThreeColumnFourSeedWitness r j := by
  unfold sixOutputThreeColumnFourSeedComputedData sixOutputThreeColumnFourSeedWitness sixOutputTriplePluckerTangent
  rw [sixOutputTriplePluckerTerms_eq_data,integerPolynomial_sum]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  dsimp only [Function.comp_apply]
  rw [integerPolynomial_map_mul,integerPolynomial_add]
  split_ifs <;> simp [← sixOutputThreeColumnFourSeedMinors_entry]

end FD56
