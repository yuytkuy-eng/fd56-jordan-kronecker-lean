/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyFourTangentPolynomial
import FD56.Hilbert.BalancedTwentyFourTangentRank

/-! Integral binding of the degree5 selected coefficient certificate. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

def balancedTwentyFourTangentCoefficientRows (i:Fin 60) : Fin 5 × ℕ :=
  let r := (finProdFinEquiv : Fin 5 × Fin 30 ≃ Fin 150).symm (balancedTwentyFourTangentSelectedRows i)
  (r.1,r.2.val)

def balancedTwentyFourTangentSelectedIntegerEntry (i j:Fin 60) : ℤ :=
  let r := balancedTwentyFourTangentCoefficientRows i
  let c := (finProdFinEquiv : Fin 10 × Fin 6 ≃ Fin 60).symm j
  if c.2.val≤r.2 then (balancedTwentyFourTangentPolynomialData r.1 c.1).getD (r.2-c.2.val) 0 else 0

def balancedTwentyFourTangentSelectedCoefficient {K : Type*} [Field K] : Matrix (Fin 60) (Fin 60) K :=
  (selectedPolynomialCoefficientMatrix (balancedTwentyFourTangentWitness (R:=K)) 5
    balancedTwentyFourTangentCoefficientRows).submatrix id
      (finProdFinEquiv : Fin 10 × Fin 6 ≃ Fin 60).symm

end FD56
