/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnFourSeedPolynomial
import FD56.Hilbert.SixOutputThreeColumnFourSeedRank

/-! Selection of the degree-3 tangent coefficient matrix. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false

def sixOutputThreeColumnFourSeedCoefficientRows (i : Fin 80) : Fin 20 × ℕ :=
  let r := (finProdFinEquiv : Fin 20 × Fin 16 ≃ Fin 320).symm (sixOutputThreeColumnFourSeedSelectedRows i)
  (r.1,r.2.val)

def sixOutputThreeColumnFourSeedSelectedIntegerEntry (i j : Fin 80) : ℤ :=
  let r := sixOutputThreeColumnFourSeedCoefficientRows i
  let c := (finProdFinEquiv : Fin 20 × Fin 4 ≃ Fin 80).symm j
  if c.2.val≤r.2 then (sixOutputThreeColumnFourSeedPolynomialData r.1 c.1).getD (r.2-c.2.val) 0 else 0

def sixOutputThreeColumnFourSeedSelectedCoefficient {K : Type*} [Field K] : Matrix (Fin 80) (Fin 80) K :=
  (selectedPolynomialCoefficientMatrix (sixOutputThreeColumnFourSeedWitness (R:=K)) 3
    sixOutputThreeColumnFourSeedCoefficientRows).submatrix id
      (fun j => (finProdFinEquiv : Fin 20 × Fin 4 ≃ Fin 80).symm j)

end FD56
