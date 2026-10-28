/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.ResidueOneSelectors

/-! Shift witnesses for all interior remainders. Replacing one terminal row
gives a scalar solution with a single prescribed off-diagonal entry. -/

namespace FD56
open Matrix
open scoped BigOperators
variable (r s : ℕ) [NeZero r] [NeZero s]

def interiorLevel (q : ℕ) (k : Fin ((r+s)*q+r)) : ℕ := k.val/(r+s)

def interiorBaseRow (q : ℕ) (k : Fin ((r+s)*q+r)) : Fin (r+s) :=
  ⟨k.val%(r+s),Nat.mod_lt _ (by have := NeZero.pos r; omega)⟩

def interiorMissing (q : ℕ) (a : Fin r) : Fin ((r+s)*q+r) :=
  ⟨(r+s)*q+a.val,by omega⟩

def interiorSwapRow (q : ℕ) (a : Fin r) (b : Fin s)
    (k : Fin ((r+s)*q+r)) : Fin (r+s) :=
  if k=interiorMissing r s q a then ⟨r+b.val,by omega⟩ else interiorBaseRow r s q k

theorem interior_lower_closed (q : ℕ) (row : Fin ((r+s)*q+r) → Fin (r+s))
    (hrow : ∀ k, k.val<(r+s)*q → row k=interiorBaseRow r s q k) :
    ∀ k t, t < interiorLevel r s q k → ∀ a, ∃ l,
      interiorLevel r s q l=t ∧ row l=a := by
  intro k t ht a
  have hm : 0<r+s := by have := NeZero.pos r; omega
  have hk : k.val/(r+s)≤q :=
    (Nat.div_le_iff_le_mul_add_pred hm).mpr (by have := NeZero.pos s; omega)
  have htq : t<q := by dsimp [interiorLevel] at ht; omega
  let l : Fin ((r+s)*q+r) := ⟨(r+s)*t+a.val,by nlinarith [a.isLt]⟩
  have hl : l.val<(r+s)*q := by dsimp [l]; nlinarith [a.isLt]
  refine ⟨l,?_,?_⟩
  · dsimp [interiorLevel,l]
    rw [Nat.mul_add_div hm,Nat.div_eq_of_lt a.isLt,Nat.add_zero]
  · rw [hrow l hl]
    apply Fin.ext
    simp [interiorBaseRow,l,Nat.add_mod,Nat.mod_eq_of_lt a.isLt]

omit [NeZero s] in
@[simp] theorem interiorLevel_missing (q : ℕ) (a : Fin r) :
    interiorLevel r s q (interiorMissing r s q a)=q := by
  have hm : 0<r+s := by have := NeZero.pos r; omega
  have ha : a.val<r+s := by omega
  dsimp [interiorLevel,interiorMissing]
  rw [Nat.mul_add_div hm,Nat.div_eq_of_lt ha,Nat.add_zero]

omit [NeZero s] in
@[simp] theorem interiorSwapRow_missing (q : ℕ) (a : Fin r) (b : Fin s) :
    interiorSwapRow r s q a b (interiorMissing r s q a)=⟨r+b.val,by omega⟩ := by
  simp [interiorSwapRow]

variable {R : Type*} [CommRing R]

def interiorShiftM (q : ℕ) : Matrix (Fin ((r+s)*q+r)) (Fin ((r+s)*q+r)) R :=
  finiteShiftMatrix ((r+s)*q+r) (r+s)

def interiorShiftP (q : ℕ) : Matrix (Fin (r+s)) (Fin ((r+s)*q+r)) R :=
  finiteInitialRows (r+s) ((r+s)*q+r)

omit [NeZero s] in
theorem interior_shift_selected_base (q : ℕ) :
    observabilitySelectedMatrix (interiorShiftM (R:=R) r s q) (interiorShiftP r s q)
      (interiorLevel r s q) (interiorBaseRow r s q)=1 := by
  ext i j
  simp only [observabilitySelectedMatrix,interiorShiftM,interiorShiftP,
    finiteShiftMatrix_pow,finiteInitialRows_mul_shift]
  rw [finiteInitialRows_mul_shift]
  dsimp only
  have hi : (interiorBaseRow r s q i).val+(r+s)*interiorLevel r s q i=i.val :=
    Nat.mod_add_div _ _
  rw [hi]
  simp [Matrix.one_apply,Fin.ext_iff]

omit [NeZero s] in
theorem interior_shift_selected_swap (q : ℕ) (a : Fin r) (b : Fin s) :
    observabilitySelectedMatrix (interiorShiftM (R:=R) r s q) (interiorShiftP r s q)
      (interiorLevel r s q) (interiorSwapRow r s q a b)=
      Matrix.diagonal (fun i => if i=interiorMissing r s q a then (0 : R) else 1) := by
  ext i j
  simp only [observabilitySelectedMatrix,interiorShiftM,interiorShiftP,
    finiteShiftMatrix_pow,finiteInitialRows_mul_shift]
  rw [finiteInitialRows_mul_shift]
  dsimp only
  by_cases hi : i=interiorMissing r s q a
  · subst i
    have hj : r+b.val+(r+s)*q≠j.val := by omega
    simp [interiorLevel_missing,interiorSwapRow_missing,Matrix.diagonal_apply,hj]
  · have he : (interiorSwapRow r s q a b i).val+(r+s)*interiorLevel r s q i=i.val := by
      simp only [interiorSwapRow,hi,↓reduceIte,interiorBaseRow,interiorLevel]
      exact Nat.mod_add_div _ _
    rw [he]
    have hival : i.val≠(interiorMissing r s q a).val := fun h => hi (Fin.ext h)
    simp [Matrix.diagonal_apply,hi,Fin.ext_iff,hival]

omit [NeZero s] in
theorem interior_shift_selected_adjugate (q : ℕ) (a : Fin r) (b : Fin s) :
    (observabilitySelectedMatrix (interiorShiftM (R:=R) r s q) (interiorShiftP r s q)
      (interiorLevel r s q) (interiorSwapRow r s q a b)).adjugate=
      Matrix.diagonal (fun i => if i=interiorMissing r s q a then (1 : R) else 0) := by
  rw [interior_shift_selected_swap,Matrix.adjugate_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  by_cases hi : i=interiorMissing r s q a
  · subst i; simp
  · rw [if_neg hi]
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hi,Finset.mem_univ _⟩)
    simp

omit [NeZero s] in
theorem interior_shift_scalarU_swap (q : ℕ) (a : Fin r) (b : Fin s)
    (i : Fin ((r+s)*q+r)) (c : Fin (r+s)) :
    observabilityScalarU (interiorShiftM (R:=R) r s q)
      (observabilitySelectedMatrix (interiorShiftM r s q) (interiorShiftP r s q)
        (interiorLevel r s q) (interiorSwapRow r s q a b)).adjugate
      (interiorLevel r s q) (interiorSwapRow r s q a b) i c=
        if i.val=a.val ∧ c.val=r+b.val then 1 else 0 := by
  rw [interior_shift_selected_adjugate]
  simp only [observabilityScalarU,Matrix.sum_apply,Matrix.mul_apply,
    observabilityScalarColumn,Matrix.diagonal_apply]
  rw [Finset.sum_eq_single (interiorMissing r s q a)]
  · simp only [interiorLevel_missing,interiorSwapRow_missing]
    rw [Finset.sum_eq_single (interiorMissing r s q a)]
    · simp [interiorShiftM,finiteShiftMatrix_pow,finiteShiftMatrix,
        interiorMissing,Fin.ext_iff]
      split_ifs <;> simp_all <;> omega
    · intro l _ hl
      simp [hl]
    · simp
  · intro k _ hk
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : l=k
    · subst l; simp [hk]
    · simp [hl]
  · simp

omit [NeZero r] [NeZero s] in
private theorem cyclic_residue_sum (m q a b : ℕ) (ha : a≤m) (hb : b<m) :
    (∑ k ∈ Finset.range (m*q+a), if k%m=b then (1 : R) else 0) =
      (q : R)+(if b<a then 1 else 0) := by
  have hblock (t : ℕ) :
      (∑ k ∈ Finset.range m, if (m*t+k)%m=b then (1 : R) else 0)=1 := by
    have he : (∑ k ∈ Finset.range m, if (m*t+k)%m=b then (1 : R) else 0)=
        ∑ k ∈ Finset.range m, if k=b then (1 : R) else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [Nat.add_mod,Nat.mod_eq_of_lt (Finset.mem_range.mp hk)]
    rw [he]
    simp [hb]
  have hfull : (∑ k ∈ Finset.range (m*q), if k%m=b then (1 : R) else 0)=(q : R) := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ,Finset.sum_range_add,ih,hblock]
      simp
  rw [Finset.sum_range_add,hfull]
  congr 1
  have he : (∑ k ∈ Finset.range a, if (m*q+k)%m=b then (1 : R) else 0)=
      ∑ k ∈ Finset.range a, if k=b then (1 : R) else 0 := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkm : k<m := lt_of_lt_of_le (Finset.mem_range.mp hk) ha
    simp [Nat.add_mod,Nat.mod_eq_of_lt hkm]
  rw [he]
  simp

omit [NeZero s] in
theorem interior_shift_scalarU_base (q : ℕ)
    (i : Fin ((r+s)*q+r)) (c : Fin (r+s)) :
    observabilityScalarU (interiorShiftM (R:=R) r s q)
      (observabilitySelectedMatrix (interiorShiftM r s q) (interiorShiftP r s q)
        (interiorLevel r s q) (interiorBaseRow r s q)).adjugate
      (interiorLevel r s q) (interiorBaseRow r s q) i c=
        if i.val=c.val then (q : R)+(if c.val<r then 1 else 0) else 0 := by
  rw [interior_shift_selected_base,Matrix.adjugate_one]
  have hs : observabilityScalarU (interiorShiftM (R:=R) r s q) 1
      (interiorLevel r s q) (interiorBaseRow r s q) i c=
      ∑ k : Fin ((r+s)*q+r), if c=interiorBaseRow r s q k then
        (if i.val+(r+s)*(k.val/(r+s))=k.val then (1 : R) else 0) else 0 := by
    simp only [observabilityScalarU,Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hc : c=interiorBaseRow r s q k
    · simp [Matrix.mul_apply,observabilityScalarColumn,hc,Matrix.one_apply,
        interiorShiftM,finiteShiftMatrix_pow,finiteShiftMatrix,interiorLevel]
    · simp [Matrix.mul_apply,observabilityScalarColumn,hc]
  rw [hs]
  have hterm (k : Fin ((r+s)*q+r)) :
      (if c=interiorBaseRow r s q k then
        (if i.val+(r+s)*(k.val/(r+s))=k.val then (1 : R) else 0) else 0)=
      if i.val=c.val then (if k.val%(r+s)=c.val then (1 : R) else 0) else 0 := by
    simp only [interiorBaseRow,Fin.ext_iff]
    have hm := Nat.mod_add_div k.val (r+s)
    split_ifs <;> first | rfl | omega
  simp_rw [hterm]
  by_cases hi : i.val=c.val
  · simp only [hi,↓reduceIte]
    exact (Fin.sum_univ_eq_sum_range
      (fun k => if k%(r+s)=c.val then (1 : R) else 0) ((r+s)*q+r)).trans
      (cyclic_residue_sum (r+s) q r c.val (by omega) c.isLt)
  · simp [hi]

def interiorSelectorRow (q : ℕ) (z : Option (Fin r × Fin s)) :
    Fin ((r+s)*q+r) → Fin (r+s) :=
  match z with
  | none => interiorBaseRow r s q
  | some ab => interiorSwapRow r s q ab.1 ab.2

theorem interiorSelector_lower_closed (q : ℕ) (z : Option (Fin r × Fin s)) :
    ∀ k t, t < interiorLevel r s q k → ∀ a, ∃ l,
      interiorLevel r s q l=t ∧ interiorSelectorRow r s q z l=a := by
  apply interior_lower_closed
  intro k hk
  cases z with
  | none => rfl
  | some ab =>
    have hne : k≠interiorMissing r s q ab.1 := by
      intro he
      have := congrArg Fin.val he
      dsimp [interiorMissing] at this
      omega
    simp [interiorSelectorRow,interiorSwapRow,hne]

def interiorScalarUFamily (q : ℕ) (z : Option (Fin r × Fin s)) :
    Matrix (Fin ((r+s)*q+r)) (Fin (r+s)) R :=
  observabilityScalarU (interiorShiftM r s q)
    (observabilitySelectedMatrix (interiorShiftM r s q) (interiorShiftP r s q)
      (interiorLevel r s q) (interiorSelectorRow r s q z)).adjugate
    (interiorLevel r s q) (interiorSelectorRow r s q z)

theorem interior_shift_scalarU_independent (q : ℕ) :
    LinearIndependent R (interiorScalarUFamily (R:=R) r s q) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro w hw
  have he (i : Fin ((r+s)*q+r)) (c : Fin (r+s)) :
      w none*(if i.val=c.val then (q : R)+(if c.val<r then 1 else 0) else 0)+
        (∑ ab : Fin r × Fin s, w (some ab)*
          (if i.val=ab.1.val ∧ c.val=r+ab.2.val then 1 else 0))=0 := by
    have h := congrFun (congrFun hw i) c
    simpa only [Fintype.sum_option,Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply,
      smul_eq_mul,Matrix.zero_apply,interiorScalarUFamily,interiorSelectorRow,
      interior_shift_scalarU_base,interior_shift_scalarU_swap] using h
  have hr : 0<r := NeZero.pos r
  have hs : 0<s := NeZero.pos s
  have hzero : w none*((q : R)+1)=0 := by
    have h := he ⟨0,by omega⟩ ⟨0,by omega⟩
    have hn : ∀ b : Fin s, (0 : ℕ)≠r+b.val := fun b => by omega
    simpa [hn,hr] using h
  have hq : w none*(q : R)=0 := by
    by_cases hqn : q=0
    · simp [hqn]
    · have hi : r<(r+s)*q+r := by
        have hqpos : 0<q := Nat.pos_of_ne_zero hqn
        nlinarith
      have hza : ∀ a : Fin r, r≠a.val := fun a => Ne.symm (Nat.ne_of_lt a.isLt)
      simpa [hza] using he ⟨r,hi⟩ ⟨r,by omega⟩
  have hnone : w none=0 := by
    calc
      w none = w none*((q : R)+1)-w none*(q : R) := by ring
      _ = 0 := by rw [hzero,hq]; simp
  intro z
  cases z with
  | none => exact hnone
  | some ab =>
    have h := he ⟨ab.1.val,by omega⟩ ⟨r+ab.2.val,by omega⟩
    simp only [hnone,zero_mul,zero_add] at h
    have hc (cd : Fin r × Fin s) :
        (ab.1.val=cd.1.val ∧ r+ab.2.val=r+cd.2.val) ↔ cd=ab := by
      constructor
      · intro heq
        apply Prod.ext
        · exact Fin.ext heq.1.symm
        · apply Fin.ext
          omega
      · intro heq
        subst cd
        simp
    simp_rw [hc] at h
    simpa using h

end FD56
