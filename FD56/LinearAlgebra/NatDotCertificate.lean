/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! Natural-number list dot products provide small kernel-checkable
certificates for matrix inverses over a residue ring. -/

namespace FD56
open Matrix
open scoped BigOperators

def natListDot : List ℕ → List ℕ → ℕ
  | [],_ => 0
  | _,[] => 0
  | a::as,b::bs => a*b+natListDot as bs

theorem natListDot_eq_fin_sum (a b : List ℕ) (n : ℕ)
    (ha : a.length=n) (hb : b.length=n) :
    natListDot a b=∑ k : Fin n, a.getD k.val 0*b.getD k.val 0 := by
  induction a generalizing b n with
  | nil => subst n; simp_all [natListDot]
  | cons a as ih =>
    cases b with
    | nil => simp only [List.length_nil] at hb; simp only [List.length_cons] at ha; omega
    | cons b bs =>
      subst n
      have hl : bs.length=as.length := by simpa using hb
      rw [List.length_cons,Fin.sum_univ_succ]
      simp only [natListDot,List.getD_cons_zero,List.getD_cons_succ,Fin.val_zero,
        Fin.val_succ]
      rw [ih bs as.length rfl hl]

theorem matrix_inverse_of_natListDot (p n : ℕ)
    (rows cols : Fin n → List ℕ)
    (hr : ∀ i, (rows i).length=n) (hc : ∀ j, (cols j).length=n)
    (hcert : ∀ i j, natListDot (rows i) (cols j)%p=if i=j then 1 else 0) :
    (show Matrix (Fin n) (Fin n) (ZMod p) from fun i k => ((rows i).getD k.val 0 : ZMod p)) *
      (show Matrix (Fin n) (Fin n) (ZMod p) from fun k j => (cols j).getD k.val 0)=1 := by
  funext i j
  change (∑ k : Fin n, ((rows i).getD k.val 0 : ZMod p)*((cols j).getD k.val 0 : ZMod p))=_
  simp only [← Nat.cast_mul,← Nat.cast_sum]
  rw [← natListDot_eq_fin_sum (rows i) (cols j) n (hr i) (hc j)]
  have h := congrArg (fun a : ℕ => (a : ZMod p)) (hcert i j)
  simpa only [ZMod.natCast_mod,apply_ite,Nat.cast_one,Nat.cast_zero,Matrix.one_apply] using h

end FD56
