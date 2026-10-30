/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyFiveTangentPolynomial
import FD56.Hilbert.BalancedTwentyFiveTangentRank

/-! Integral binding of the degree6 selected coefficient certificate. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

def balancedTwentyFiveTangentCoefficientRows (i:Fin 70) : Fin 5 × ℕ :=
  let r := (finProdFinEquiv : Fin 5 × Fin 32 ≃ Fin 160).symm (balancedTwentyFiveTangentSelectedRows i)
  (r.1,r.2.val)

def balancedTwentyFiveTangentSelectedIntegerEntry (i j:Fin 70) : ℤ :=
  let r := balancedTwentyFiveTangentCoefficientRows i
  let c := (finProdFinEquiv : Fin 10 × Fin 7 ≃ Fin 70).symm j
  if c.2.val≤r.2 then (balancedTwentyFiveTangentPolynomialData r.1 c.1).getD (r.2-c.2.val) 0 else 0

def balancedTwentyFiveTangentSelectedCoefficient {K : Type*} [Field K] : Matrix (Fin 70) (Fin 70) K :=
  (selectedPolynomialCoefficientMatrix (balancedTwentyFiveTangentWitness (R:=K)) 6
    balancedTwentyFiveTangentCoefficientRows).submatrix id
      (finProdFinEquiv : Fin 10 × Fin 7 ≃ Fin 70).symm

end FD56
