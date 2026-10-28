/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.InteriorScalarSelectors
import FD56.LinearAlgebra.SelectedMinorFactorization
import FD56.LinearAlgebra.PluckerDifferential

/-! The base and single-swap observability minors are selected Plucker
coordinates of the actual terminal matrix, with one common nonzero scalar. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable (r s : ℕ) [NeZero r]

def interiorPrefixEquiv (q : ℕ) :
    Fin ((r+s)*q+r) ≃ (Fin q × Fin (r+s)) ⊕ Fin r where
  toFun k := if h : k.val<(r+s)*q then
      Sum.inl (⟨k.val/(r+s),(Nat.div_lt_iff_lt_mul
        (by have := NeZero.pos r; omega)).mpr (by nlinarith)⟩,
        ⟨k.val%(r+s),Nat.mod_lt _ (by have := NeZero.pos r; omega)⟩)
    else Sum.inr ⟨k.val-(r+s)*q,by omega⟩
  invFun z := match z with
    | Sum.inl ij => ⟨(r+s)*ij.1.val+ij.2.val,by
        have := ij.1.isLt
        have := ij.2.isLt
        nlinarith⟩
    | Sum.inr a => interiorMissing r s q a
  left_inv k := by
    dsimp only
    split_ifs with h
    · apply Fin.ext
      dsimp only
      have := Nat.mod_add_div k.val (r+s)
      omega
    · apply Fin.ext
      dsimp [interiorMissing]
      omega
  right_inv z := by
    have hm : 0<r+s := by have := NeZero.pos r; omega
    rcases z with ⟨i,a⟩ | a
    · have hi : (r+s)*i.val+a.val<(r+s)*q := by nlinarith [i.isLt,a.isLt]
      simp only [hi,↓reduceDIte,Sum.inl.injEq,Prod.mk.injEq]
      constructor
      · apply Fin.ext
        dsimp only
        rw [Nat.mul_add_div hm,Nat.div_eq_of_lt a.isLt,Nat.add_zero]
      · apply Fin.ext
        simp [Nat.add_mod,Nat.mod_eq_of_lt a.isLt]
    · have ha : ¬(interiorMissing r s q a).val<(r+s)*q := by
        dsimp [interiorMissing]
        omega
      simp only [ha,↓reduceDIte,Sum.inr.injEq]
      apply Fin.ext
      simp [interiorMissing]

def interiorTerminalRow (z : Option (Fin r × Fin s)) (a : Fin r) : Fin (r+s) :=
  match z with
  | none => ⟨a.val,by omega⟩
  | some ab => if a=ab.1 then ⟨r+ab.2.val,by omega⟩ else ⟨a.val,by omega⟩

theorem interiorPrefixEquiv_symm_inl (q : ℕ) (i : Fin q) (a : Fin (r+s)) :
    ((interiorPrefixEquiv r s q).symm (Sum.inl (i,a))).val=(r+s)*i.val+a.val := rfl

theorem interiorPrefixEquiv_symm_inr (q : ℕ) (a : Fin r) :
    (interiorPrefixEquiv r s q).symm (Sum.inr a)=interiorMissing r s q a := rfl

theorem interiorPrefixEquiv_missing (q : ℕ) (a : Fin r) :
    interiorPrefixEquiv r s q (interiorMissing r s q a)=Sum.inr a := by
  exact (interiorPrefixEquiv r s q).apply_symm_apply (Sum.inr a)

private theorem interiorLevel_prefix (q : ℕ) (i : Fin q) (a : Fin (r+s)) :
    interiorLevel r s q ((interiorPrefixEquiv r s q).symm (Sum.inl (i,a)))=i.val := by
  have hm : 0<r+s := by have := NeZero.pos r; omega
  dsimp [interiorLevel,interiorPrefixEquiv]
  rw [Nat.mul_add_div hm,Nat.div_eq_of_lt a.isLt,Nat.add_zero]

private theorem interiorSelectorRow_prefix (q : ℕ) (z : Option (Fin r × Fin s))
    (i : Fin q) (a : Fin (r+s)) :
    interiorSelectorRow r s q z ((interiorPrefixEquiv r s q).symm (Sum.inl (i,a)))=a := by
  have hbase : interiorBaseRow r s q
      ((interiorPrefixEquiv r s q).symm (Sum.inl (i,a)))=a := by
    apply Fin.ext
    simp [interiorBaseRow,interiorPrefixEquiv,Nat.add_mod,Nat.mod_eq_of_lt a.isLt]
  cases z with
  | none => exact hbase
  | some ab =>
    have hn : (interiorPrefixEquiv r s q).symm (Sum.inl (i,a))≠interiorMissing r s q ab.1 := by
      intro he
      have hh := congrArg Fin.val he
      dsimp [interiorPrefixEquiv,interiorMissing] at hh
      nlinarith [i.isLt,a.isLt]
    simp only [interiorSelectorRow,interiorSwapRow,hn,↓reduceIte]
    exact hbase

theorem interiorSelectorRow_terminal (q : ℕ) (z : Option (Fin r × Fin s)) (a : Fin r) :
    interiorSelectorRow r s q z (interiorMissing r s q a)=interiorTerminalRow r s z a := by
  have ha : a.val<r+s := by omega
  have hbase : interiorBaseRow r s q (interiorMissing r s q a)=⟨a.val,ha⟩ := by
    apply Fin.ext
    simp [interiorBaseRow,interiorMissing,Nat.add_mod,Nat.mod_eq_of_lt ha]
  have hmissing (b : Fin r) : interiorMissing r s q a=interiorMissing r s q b ↔ a=b := by
    simp [interiorMissing,Fin.ext_iff]
  cases z with
  | none => exact hbase
  | some ab =>
    simp only [interiorSelectorRow,interiorSwapRow,hmissing,interiorTerminalRow,hbase]

theorem interior_selected_matrix_fromRows {R : Type*} [CommRing R]
    (q : ℕ) (M : Matrix (Fin ((r+s)*q+r)) (Fin ((r+s)*q+r)) R)
    (P : Matrix (Fin (r+s)) (Fin ((r+s)*q+r)) R)
    (z : Option (Fin r × Fin s)) :
    observabilitySelectedMatrix M P (interiorLevel r s q) (interiorSelectorRow r s q z)=
      (Matrix.fromRows (observabilityMatrix M P q)
        ((P*M^q).submatrix (interiorTerminalRow r s z) id)).submatrix
          (interiorPrefixEquiv r s q) id := by
  funext k j
  obtain ⟨w,rfl⟩ := (interiorPrefixEquiv r s q).symm.surjective k
  rcases w with ⟨i,a⟩ | a
  · simp only [Matrix.submatrix_apply,Equiv.apply_symm_apply,Matrix.fromRows_apply_inl,
      observabilitySelectedMatrix,interiorLevel_prefix,interiorSelectorRow_prefix,
      observabilityMatrix,id_eq]
  · simp only [Matrix.submatrix_apply,Equiv.apply_symm_apply,Matrix.fromRows_apply_inr,
      interiorPrefixEquiv_symm_inr,interiorPrefixEquiv_missing,
      observabilitySelectedMatrix,interiorLevel_missing,
      interiorSelectorRow_terminal,id_eq]

theorem interior_selected_minors_common_scalar {K : Type*} [Field K]
    (q : ℕ) (M : Matrix (Fin ((r+s)*q+r)) (Fin ((r+s)*q+r)) K[X])
    (P : Matrix (Fin (r+s)) (Fin ((r+s)*q+r)) K[X])
    (R : Matrix (Fin ((r+s)*q+r)) (Fin q × Fin (r+s)) K[X])
    (hR : observabilityMatrix M P q*R=1)
    (B : Basis (Fin r) K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P q)))) :
    ∃ c : K, c≠0 ∧ ∀ z : Option (Fin r × Fin s),
      (observabilitySelectedMatrix M P (interiorLevel r s q) (interiorSelectorRow r s q z)).det=
        C c*pluckerMinorVector (P*M^q*polynomialKernelBasisMatrix (observabilityMatrix M P q) B)
          (interiorTerminalRow r s z) := by
  obtain ⟨c,hc,h⟩ := selected_augmented_minors_common_scalar_equiv
    (interiorPrefixEquiv r s q) (observabilityMatrix M P q) R hR B (P*M^q)
  refine ⟨c,hc,?_⟩
  intro z
  rw [interior_selected_matrix_fromRows]
  exact h (interiorTerminalRow r s z)

end FD56
