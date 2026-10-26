/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.ObservabilityScalarAdjugate

/-! The two terminal-row choices for an odd state dimension and two outputs. -/

namespace FD56

def oddTwoLevel (q : ℕ) (k : Fin (2*q+1)) : ℕ := k.val/2

def oddTwoRow (q : ℕ) (j : Fin 2) (k : Fin (2*q+1)) : Fin 2 :=
  if k.val=2*q then j else ⟨k.val%2,Nat.mod_lt _ (by decide)⟩

theorem oddTwoLevel_le (q : ℕ) (k : Fin (2*q+1)) : oddTwoLevel q k ≤ q := by
  dsimp [oddTwoLevel]
  omega

theorem oddTwo_lower_closed (q : ℕ) (j : Fin 2) :
    ∀ k s, s<oddTwoLevel q k → ∀ a, ∃ l,
      oddTwoLevel q l=s ∧ oddTwoRow q j l=a := by
  intro k s hs a
  have hs' : s<q := lt_of_lt_of_le hs (oddTwoLevel_le q k)
  let l : Fin (2*q+1) := ⟨2*s+a.val,by omega⟩
  refine ⟨l,?_,?_⟩
  · dsimp [oddTwoLevel,l]
    omega
  · have hne : l.val ≠ 2*q := by dsimp [l]; omega
    simp only [oddTwoRow,hne,↓reduceIte]
    apply Fin.ext
    dsimp [l]
    omega

@[simp] theorem oddTwoLevel_last (q : ℕ) : oddTwoLevel q (Fin.last (2*q))=q := by
  simp [oddTwoLevel]

@[simp] theorem oddTwoRow_last (q : ℕ) (j : Fin 2) :
    oddTwoRow q j (Fin.last (2*q))=j := by
  simp [oddTwoRow]

end FD56
