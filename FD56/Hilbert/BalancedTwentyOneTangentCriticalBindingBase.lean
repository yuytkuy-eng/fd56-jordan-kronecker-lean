/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyOneTangentBinding
import FD56.Hilbert.BalancedTwentyOneTangentCriticalRank

/-! The selected63-column degree6 coefficient minor is integral. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

def balancedTwentyOneTangentCriticalCoefficientRows (i : Fin 63) : Fin 5 × ℕ :=
  let r := (finProdFinEquiv : Fin 5 × Fin 28 ≃ Fin 140).symm (balancedTwentyOneTangentCriticalSelectedRows i)
  (r.1,r.2.val)

def balancedTwentyOneTangentCriticalSelectedIntegerEntry (i j : Fin 63) : ℤ :=
  let r := balancedTwentyOneTangentCriticalCoefficientRows i
  let c := (finProdFinEquiv : Fin 10 × Fin 7 ≃ Fin 70).symm (balancedTwentyOneTangentCriticalCoefficientColumns j)
  if c.2.val≤r.2 then (balancedTwentyOneTangentPolynomialData r.1 c.1).getD (r.2-c.2.val) 0 else 0

def balancedTwentyOneTangentCriticalSelectedCoefficient {K : Type*} [Field K] : Matrix (Fin 63) (Fin 63) K :=
  (selectedPolynomialCoefficientMatrix (balancedTwentyOneTangentWitness (R:=K)) 6
    balancedTwentyOneTangentCriticalCoefficientRows).submatrix id
      (fun j => (finProdFinEquiv : Fin 10 × Fin 7 ≃ Fin 70).symm (balancedTwentyOneTangentCriticalCoefficientColumns j))

end FD56
