/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyThreeTangentPolynomial
import FD56.Hilbert.BalancedTwentyThreeTangentRank

/-! Integral binding of the degree5 selected coefficient certificate. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

def balancedTwentyThreeTangentCoefficientRows (i:Fin 60) : Fin 5 × ℕ :=
  let r := (finProdFinEquiv : Fin 5 × Fin 29 ≃ Fin 145).symm (balancedTwentyThreeTangentSelectedRows i)
  (r.1,r.2.val)

def balancedTwentyThreeTangentSelectedIntegerEntry (i j:Fin 60) : ℤ :=
  let r := balancedTwentyThreeTangentCoefficientRows i
  let c := (finProdFinEquiv : Fin 10 × Fin 6 ≃ Fin 60).symm j
  if c.2.val≤r.2 then (balancedTwentyThreeTangentPolynomialData r.1 c.1).getD (r.2-c.2.val) 0 else 0

def balancedTwentyThreeTangentSelectedCoefficient {K : Type*} [Field K] : Matrix (Fin 60) (Fin 60) K :=
  (selectedPolynomialCoefficientMatrix (balancedTwentyThreeTangentWitness (R:=K)) 5
    balancedTwentyThreeTangentCoefficientRows).submatrix id
      (finProdFinEquiv : Fin 10 × Fin 6 ≃ Fin 60).symm

end FD56
