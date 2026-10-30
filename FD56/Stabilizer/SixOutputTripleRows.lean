/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.SixOutputTriplePluckerTangent
import FD56.Stabilizer.InteriorSelectedMinorFactorization

/-! The selected ten three-column minors occur among the twenty increasing
triple coordinates, with explicit signs. -/

namespace FD56
open Matrix
set_option Elab.async false

def sixOutputTripleSelectedIndex : Option (Fin 3 × Fin 3) → Fin 20
  | none => 0
  | some (i,j) => (![![10,11,12],![4,5,6],![1,2,3]] : Fin 3 → Fin 3 → Fin 20) i j

def sixOutputTripleSelectedSign : Option (Fin 3 × Fin 3) → ℤ
  | none => 1
  | some (i,_) => if i=1 then -1 else 1

theorem six_output_triple_selected_det {R : Type*} [CommRing R]
    (G : Matrix (Fin 6) (Fin 3) R) (z : Option (Fin 3 × Fin 3)) :
    (G.submatrix (interiorTerminalRow 3 3 z) id).det=
      (sixOutputTripleSelectedSign z : R)*
        sixOutputTriplePluckerMinors G (sixOutputTripleSelectedIndex z) := by
  cases z with
  | none =>
    simp [sixOutputTripleSelectedIndex,sixOutputTripleSelectedSign,
      sixOutputTriplePluckerMinors,sixOutputTriple,interiorTerminalRow,
      Matrix.det_fin_three,Matrix.submatrix_apply]
  | some z =>
    rcases z with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [sixOutputTripleSelectedIndex,sixOutputTripleSelectedSign,
        sixOutputTriplePluckerMinors,sixOutputTriple,interiorTerminalRow,
        Matrix.det_fin_three,Matrix.submatrix_apply] <;> ring

end FD56
