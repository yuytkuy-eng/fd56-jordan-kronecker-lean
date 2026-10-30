/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnFourSeedPolynomial
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalRank

/-! Selection of the degree-4 tangent coefficient matrix. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false

def sixOutputThreeColumnFourSeedCriticalCoefficientRows (i : Fin 98) : Fin 20 × ℕ :=
  let r := (finProdFinEquiv : Fin 20 × Fin 17 ≃ Fin 340).symm (sixOutputThreeColumnFourSeedCriticalSelectedRows i)
  (r.1,r.2.val)

def sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry (i j : Fin 98) : ℤ :=
  let r := sixOutputThreeColumnFourSeedCriticalCoefficientRows i
  let c := (finProdFinEquiv : Fin 20 × Fin 5 ≃ Fin 100).symm (sixOutputThreeColumnFourSeedCriticalCoefficientColumns j)
  if c.2.val≤r.2 then (sixOutputThreeColumnFourSeedPolynomialData r.1 c.1).getD (r.2-c.2.val) 0 else 0

def sixOutputThreeColumnFourSeedCriticalSelectedCoefficient {K : Type*} [Field K] : Matrix (Fin 98) (Fin 98) K :=
  (selectedPolynomialCoefficientMatrix (sixOutputThreeColumnFourSeedWitness (R:=K)) 4
    sixOutputThreeColumnFourSeedCriticalCoefficientRows).submatrix id
      (fun j => (finProdFinEquiv : Fin 20 × Fin 5 ≃ Fin 100).symm (sixOutputThreeColumnFourSeedCriticalCoefficientColumns j))

end FD56
