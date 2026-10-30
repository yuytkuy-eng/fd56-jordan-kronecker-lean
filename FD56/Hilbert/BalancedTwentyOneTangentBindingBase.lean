/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyOneTangentPolynomial
import FD56.Hilbert.BalancedTwentyOneTangentRank

/-! Integral binding of the degree5 selected coefficient certificate. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

def balancedTwentyOneTangentCoefficientRows (i:Fin 60) : Fin 5 × ℕ :=
  let r := (finProdFinEquiv : Fin 5 × Fin 27 ≃ Fin 135).symm (balancedTwentyOneTangentSelectedRows i)
  (r.1,r.2.val)

def balancedTwentyOneTangentSelectedIntegerEntry (i j:Fin 60) : ℤ :=
  let r := balancedTwentyOneTangentCoefficientRows i
  let c := (finProdFinEquiv : Fin 10 × Fin 6 ≃ Fin 60).symm j
  if c.2.val≤r.2 then (balancedTwentyOneTangentPolynomialData r.1 c.1).getD (r.2-c.2.val) 0 else 0

def balancedTwentyOneTangentSelectedCoefficient {K : Type*} [Field K] : Matrix (Fin 60) (Fin 60) K :=
  (selectedPolynomialCoefficientMatrix (balancedTwentyOneTangentWitness (R:=K)) 5
    balancedTwentyOneTangentCoefficientRows).submatrix id
      (finProdFinEquiv : Fin 10 × Fin 6 ≃ Fin 60).symm

end FD56
