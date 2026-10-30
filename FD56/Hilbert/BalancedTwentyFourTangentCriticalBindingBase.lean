/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyFourTangentBinding
import FD56.Hilbert.BalancedTwentyFourTangentCriticalRank

/-! The selected69-column degree6 coefficient minor is integral. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

def balancedTwentyFourTangentCriticalCoefficientRows (i : Fin 69) : Fin 5 × ℕ :=
  let r := (finProdFinEquiv : Fin 5 × Fin 31 ≃ Fin 155).symm (balancedTwentyFourTangentCriticalSelectedRows i)
  (r.1,r.2.val)

def balancedTwentyFourTangentCriticalSelectedIntegerEntry (i j : Fin 69) : ℤ :=
  let r := balancedTwentyFourTangentCriticalCoefficientRows i
  let c := (finProdFinEquiv : Fin 10 × Fin 7 ≃ Fin 70).symm (balancedTwentyFourTangentCriticalCoefficientColumns j)
  if c.2.val≤r.2 then (balancedTwentyFourTangentPolynomialData r.1 c.1).getD (r.2-c.2.val) 0 else 0

def balancedTwentyFourTangentCriticalSelectedCoefficient {K : Type*} [Field K] : Matrix (Fin 69) (Fin 69) K :=
  (selectedPolynomialCoefficientMatrix (balancedTwentyFourTangentWitness (R:=K)) 6
    balancedTwentyFourTangentCriticalCoefficientRows).submatrix id
      (fun j => (finProdFinEquiv : Fin 10 × Fin 7 ≃ Fin 70).symm (balancedTwentyFourTangentCriticalCoefficientColumns j))

end FD56
