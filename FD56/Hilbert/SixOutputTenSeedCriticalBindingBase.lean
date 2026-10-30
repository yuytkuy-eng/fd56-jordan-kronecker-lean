/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputTenSeedBinding
import FD56.Hilbert.SixOutputTenSeedCriticalRank

/-! Integral binding of a selected 54-column critical coefficient minor. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

def sixOutputTenSeedCriticalCoefficientRows (i : Fin 54) : Fin 15 × ℕ :=
  let r := (finProdFinEquiv : Fin 15 × Fin 14 ≃ Fin 210).symm (sixOutputTenSeedCriticalSelectedRows i)
  (r.1,r.2.val)

def sixOutputTenSeedCriticalSelectedIntegerEntry (i j : Fin 54) : ℤ :=
  let r := sixOutputTenSeedCriticalCoefficientRows i
  let c := (finProdFinEquiv : Fin 15 × Fin 4 ≃ Fin 60).symm (sixOutputTenSeedCriticalCoefficientColumns j)
  if c.2.val≤r.2 then (sixOutputTenSeedPolynomialData r.1 c.1).getD (r.2-c.2.val) 0 else 0

def sixOutputTenSeedCriticalSelectedCoefficient {K : Type*} [Field K] : Matrix (Fin 54) (Fin 54) K :=
  (selectedPolynomialCoefficientMatrix (sixOutputTenSeedWitness (R:=K)) 3
    sixOutputTenSeedCriticalCoefficientRows).submatrix id
      (fun j => (finProdFinEquiv : Fin 15 × Fin 4 ≃ Fin 60).symm (sixOutputTenSeedCriticalCoefficientColumns j))

attribute [local irreducible] sixOutputTenSeedCriticalCoefficientRows sixOutputTenSeedPolynomialData

end FD56
