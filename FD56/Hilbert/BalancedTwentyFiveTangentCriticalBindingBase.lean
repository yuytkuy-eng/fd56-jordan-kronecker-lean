/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyFiveTangentBinding
import FD56.Hilbert.BalancedTwentyFiveTangentCriticalRank

/-! The selected74-column degree7 coefficient minor is integral. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

def balancedTwentyFiveTangentCriticalCoefficientRows (i : Fin 74) : Fin 5 × ℕ :=
  let r := (finProdFinEquiv : Fin 5 × Fin 33 ≃ Fin 165).symm (balancedTwentyFiveTangentCriticalSelectedRows i)
  (r.1,r.2.val)

def balancedTwentyFiveTangentCriticalSelectedIntegerEntry (i j : Fin 74) : ℤ :=
  let r := balancedTwentyFiveTangentCriticalCoefficientRows i
  let c := (finProdFinEquiv : Fin 10 × Fin 8 ≃ Fin 80).symm (balancedTwentyFiveTangentCriticalCoefficientColumns j)
  if c.2.val≤r.2 then (balancedTwentyFiveTangentPolynomialData r.1 c.1).getD (r.2-c.2.val) 0 else 0

def balancedTwentyFiveTangentCriticalSelectedCoefficient {K : Type*} [Field K] : Matrix (Fin 74) (Fin 74) K :=
  (selectedPolynomialCoefficientMatrix (balancedTwentyFiveTangentWitness (R:=K)) 7
    balancedTwentyFiveTangentCriticalCoefficientRows).submatrix id
      (fun j => (finProdFinEquiv : Fin 10 × Fin 8 ≃ Fin 80).symm (balancedTwentyFiveTangentCriticalCoefficientColumns j))

end FD56
