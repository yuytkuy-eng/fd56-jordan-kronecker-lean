/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedEighteenTangentBinding
import FD56.Hilbert.BalancedEighteenTangentCriticalRank

/-! The selected54-column degree5 coefficient minor is integral. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

def balancedEighteenTangentCriticalCoefficientRows (i : Fin 54) : Fin 5 × ℕ :=
  let r := (finProdFinEquiv : Fin 5 × Fin 24 ≃ Fin 120).symm (balancedEighteenTangentCriticalSelectedRows i)
  (r.1,r.2.val)

def balancedEighteenTangentCriticalSelectedIntegerEntry (i j : Fin 54) : ℤ :=
  let r := balancedEighteenTangentCriticalCoefficientRows i
  let c := (finProdFinEquiv : Fin 10 × Fin 6 ≃ Fin 60).symm (balancedEighteenTangentCriticalCoefficientColumns j)
  if c.2.val≤r.2 then (balancedEighteenTangentPolynomialData r.1 c.1).getD (r.2-c.2.val) 0 else 0

def balancedEighteenTangentCriticalSelectedCoefficient {K : Type*} [Field K] : Matrix (Fin 54) (Fin 54) K :=
  (selectedPolynomialCoefficientMatrix (balancedEighteenTangentWitness (R:=K)) 5
    balancedEighteenTangentCriticalCoefficientRows).submatrix id
      (fun j => (finProdFinEquiv : Fin 10 × Fin 6 ≃ Fin 60).symm (balancedEighteenTangentCriticalCoefficientColumns j))

end FD56
