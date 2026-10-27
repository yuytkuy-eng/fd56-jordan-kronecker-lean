/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GLDeterminantReduction
import FD56.Stabilizer.GLKirillovReindex
import FD56.Stabilizer.SquareKirillovDeterminant

/-! The GL Kirillov determinant in observable companion coordinates is one. -/

noncomputable section
namespace FD56
open Matrix

def blockFirstSplit (q : ℕ) (m : Type*) : (m ⊕ (Fin q × m)) ≃ (Fin (q+1) × m) where
  toFun
    | .inl a => (0,a)
    | .inr (i,a) => (i.succ,a)
  invFun x := Fin.cases (.inl x.2) (fun i => .inr (i,x.2)) x.1
  left_inv x := by rcases x with a|⟨i,a⟩ <;> simp
  right_inv x := by
    rcases x with ⟨i,a⟩
    induction i using Fin.cases <;> rfl

variable {R m : Type*} [CommRing R] [Fintype m] [DecidableEq m]

def blockFirstRow (q : ℕ) : Matrix m (Fin (q+1) × m) R :=
  fun a j => if j.1=0 then (1 : Matrix m m R) a j.2 else 0

omit [Fintype m] in
theorem blockFirstRow_split (q : ℕ) :
    (blockFirstRow (R := R) (m := m) q).submatrix (Equiv.refl m) (blockFirstSplit q m)=
      Matrix.fromCols (1 : Matrix m m R) 0 := by
  ext a (b|⟨i,b⟩) <;> simp [blockFirstRow,blockFirstSplit,Matrix.one_apply]

theorem glKirillovMatrix_companion_det (q : ℕ)
    (M : Matrix (Fin (q+1) × m) (Fin (q+1) × m) R)
    (hM : ∀ (i : Fin q) (a : m) (k : Fin (q+1)) (b : m),
      M (i.castSucc,a) (k,b)=if k=i.succ then (1 : Matrix m m R) a b else 0) :
    (glKirillovMatrix M (blockFirstRow q)).det=1 := by
  induction q with
  | zero =>
    let e : m ≃ (Fin 1 × m) :=
      { toFun := fun a => (0,a)
        invFun := fun a => a.2
        left_inv := fun _ => rfl
        right_inv := by intro ⟨i,a⟩; have hi : i=0 := Subsingleton.elim _ _; subst i; rfl }
    have hp : (blockFirstRow (R := R) (m := m) 0).submatrix (Equiv.refl m) e=1 := by
      ext i j; rfl
    rw [← glKirillovMatrix_det_reindex M (blockFirstRow 0) e (Equiv.refl m),hp,
      glKirillovMatrix_square_det,Matrix.det_one,one_pow]
  | succ q ih =>
    let e := blockFirstSplit (q+1) m
    let N := M.submatrix e e
    let A := N.toBlocks₁₁
    let B := N.toBlocks₁₂
    let C := N.toBlocks₂₁
    let D := N.toBlocks₂₂
    have hN : N=Matrix.fromBlocks A B C D := (Matrix.fromBlocks_toBlocks N).symm
    have hB : B=blockFirstRow q := by
      funext a k
      change M (0,a) (k.1.succ,k.2)=_
      have hk : k.1.succ=(1 : Fin (q+2)) ↔ k.1=0 := by
        change k.1.succ=(0 : Fin (q+1)).succ ↔ k.1=0
        exact Fin.succ_inj
      simpa [blockFirstRow,hk] using hM 0 a k.1.succ k.2
    have hD : ∀ (i : Fin q) (a : m) (k : Fin (q+1)) (b : m),
        D (i.castSucc,a) (k,b)=if k=i.succ then (1 : Matrix m m R) a b else 0 := by
      intro i a k b
      change M (i.castSucc.succ,a) (k.succ,b)=_
      simpa [Fin.succ_castSucc,Fin.succ_inj] using hM i.succ a k.succ b
    calc
      _ = (glKirillovMatrix N (Matrix.fromCols (1 : Matrix m m R) 0)).det := by
        rw [← glKirillovMatrix_det_reindex M (blockFirstRow (q+1)) e (Equiv.refl m),blockFirstRow_split]
      _ = (glKirillovMatrix D B).det := by rw [hN,glKirillovMatrix_row_reduction_det]
      _ = 1 := by rw [hB]; exact ih D hD

end FD56
