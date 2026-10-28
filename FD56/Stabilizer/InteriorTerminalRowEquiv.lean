/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.InteriorSelectedMinorFactorization

/-! The base and single-swap terminal selectors extend to row equivalences.
Their complementary rows are therefore suitable for the complementary-minor
identity without any separate ordering or sign convention. -/

noncomputable section
namespace FD56

variable (r s : ℕ)

def interiorTerminalRowEquiv (z : Option (Fin r × Fin s)) :
    (Fin r ⊕ Fin s) ≃ Fin (r+s) :=
  (match z with
    | none => Equiv.refl (Fin r ⊕ Fin s)
    | some ab => Equiv.swap (Sum.inl ab.1) (Sum.inr ab.2)).trans finSumFinEquiv

theorem interiorTerminalRowEquiv_inl (z : Option (Fin r × Fin s)) (a : Fin r) :
    interiorTerminalRowEquiv r s z (Sum.inl a)=interiorTerminalRow r s z a := by
  cases z with
  | none => rfl
  | some ab =>
    by_cases h : a=ab.1
    · subst a
      simp only [interiorTerminalRowEquiv,Equiv.trans_apply,Equiv.swap_apply_left,
        finSumFinEquiv_apply_right,interiorTerminalRow,↓reduceIte]
      rfl
    · simp only [interiorTerminalRowEquiv,Equiv.trans_apply,Equiv.swap_apply_def,
        Sum.inl.injEq,h,↓reduceIte,Sum.inl_ne_inr,finSumFinEquiv_apply_left,
        interiorTerminalRow]
      rfl

theorem interiorTerminalRowEquiv_inr (z : Option (Fin r × Fin s)) (b : Fin s) :
    interiorTerminalRowEquiv r s z (Sum.inr b)=
      match z with
      | none => Fin.natAdd r b
      | some ab => if b=ab.2 then Fin.castAdd s ab.1 else Fin.natAdd r b := by
  cases z with
  | none => rfl
  | some ab =>
    by_cases h : b=ab.2
    · subst b
      simp only [interiorTerminalRowEquiv,Equiv.trans_apply,Equiv.swap_apply_right,
        finSumFinEquiv_apply_left,↓reduceIte]
    · simp only [interiorTerminalRowEquiv,Equiv.trans_apply,Equiv.swap_apply_def,
        Sum.inr_ne_inl,↓reduceIte,Sum.inr.injEq,h,finSumFinEquiv_apply_right]

end FD56
