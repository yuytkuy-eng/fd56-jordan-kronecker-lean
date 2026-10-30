/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnTailPolynomial
import FD56.Hilbert.SixOutputThreeColumnTailRank

/-! Selection of the degree-five tangent coefficient matrix. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false

def sixOutputThreeColumnTailCoefficientRows (i : Fin 120) : Fin 20 × ℕ :=
  let r := (finProdFinEquiv : Fin 20 × Fin 21 ≃ Fin 420).symm (sixOutputThreeColumnTailSelectedRows i)
  (r.1,r.2.val)

def sixOutputThreeColumnTailSelectedIntegerEntry (i j : Fin 120) : ℤ :=
  let r := sixOutputThreeColumnTailCoefficientRows i
  let c := (finProdFinEquiv : Fin 20 × Fin 6 ≃ Fin 120).symm j
  if c.2.val≤r.2 then (sixOutputThreeColumnTailPolynomialData r.1 c.1).getD (r.2-c.2.val) 0 else 0

def sixOutputThreeColumnTailSelectedCoefficient {K : Type*} [Field K] : Matrix (Fin 120) (Fin 120) K :=
  (selectedPolynomialCoefficientMatrix (sixOutputThreeColumnTailWitness (R:=K)) 5
    sixOutputThreeColumnTailCoefficientRows).submatrix id
      (finProdFinEquiv : Fin 20 × Fin 6 ≃ Fin 120).symm

end FD56
