/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedEighteenTangentPolynomial
import FD56.Hilbert.BalancedEighteenTangentRank

/-! Integral binding of the degree4 selected coefficient certificate. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

def balancedEighteenTangentCoefficientRows (i:Fin 50) : Fin 5 × ℕ :=
  let r := (finProdFinEquiv : Fin 5 × Fin 23 ≃ Fin 115).symm (balancedEighteenTangentSelectedRows i)
  (r.1,r.2.val)

def balancedEighteenTangentSelectedIntegerEntry (i j:Fin 50) : ℤ :=
  let r := balancedEighteenTangentCoefficientRows i
  let c := (finProdFinEquiv : Fin 10 × Fin 5 ≃ Fin 50).symm j
  if c.2.val≤r.2 then (balancedEighteenTangentPolynomialData r.1 c.1).getD (r.2-c.2.val) 0 else 0

def balancedEighteenTangentSelectedCoefficient {K : Type*} [Field K] : Matrix (Fin 50) (Fin 50) K :=
  (selectedPolynomialCoefficientMatrix (balancedEighteenTangentWitness (R:=K)) 4
    balancedEighteenTangentCoefficientRows).submatrix id
      (finProdFinEquiv : Fin 10 × Fin 5 ≃ Fin 50).symm

end FD56
