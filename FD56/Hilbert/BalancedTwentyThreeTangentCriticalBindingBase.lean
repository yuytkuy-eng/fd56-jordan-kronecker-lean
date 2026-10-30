/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyThreeTangentBinding
import FD56.Hilbert.BalancedTwentyThreeTangentCriticalRank

/-! The selected67-column degree6 coefficient minor is integral. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

def balancedTwentyThreeTangentCriticalCoefficientRows (i : Fin 67) : Fin 5 × ℕ :=
  let r := (finProdFinEquiv : Fin 5 × Fin 30 ≃ Fin 150).symm (balancedTwentyThreeTangentCriticalSelectedRows i)
  (r.1,r.2.val)

def balancedTwentyThreeTangentCriticalSelectedIntegerEntry (i j : Fin 67) : ℤ :=
  let r := balancedTwentyThreeTangentCriticalCoefficientRows i
  let c := (finProdFinEquiv : Fin 10 × Fin 7 ≃ Fin 70).symm (balancedTwentyThreeTangentCriticalCoefficientColumns j)
  if c.2.val≤r.2 then (balancedTwentyThreeTangentPolynomialData r.1 c.1).getD (r.2-c.2.val) 0 else 0

def balancedTwentyThreeTangentCriticalSelectedCoefficient {K : Type*} [Field K] : Matrix (Fin 67) (Fin 67) K :=
  (selectedPolynomialCoefficientMatrix (balancedTwentyThreeTangentWitness (R:=K)) 6
    balancedTwentyThreeTangentCriticalCoefficientRows).submatrix id
      (fun j => (finProdFinEquiv : Fin 10 × Fin 7 ≃ Fin 70).symm (balancedTwentyThreeTangentCriticalCoefficientColumns j))

end FD56
