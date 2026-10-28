/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericAllDepthGL
import FD56.Hilbert.GLBalancedFormula
import FD56.Hilbert.AboveGLKronecker
import FD56.Arithmetic.SpectrumArithmetic

/-! The explicit three-level GL formula is the actual generic degree list at
every positive nondivisible size. The whole pencil has a constant Kronecker
congruence over the generic coefficient field. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem interiorGLDegreeList_perm_formula (r s q : ℕ) (hr : 0<r) (hs : 0<s) :
    (interiorGLDegreeList r s q).Perm (glFormula ((r+s)*(q+1)+r) (r+s)) := by
  have hm : 0<r+s := by omega
  have hlt : r<r+s := by omega
  have hdiv : ((r+s)*(q+1)+r)/(r+s)=q+1 := by
    rw [Nat.mul_add_div hm,Nat.div_eq_of_lt hlt,Nat.add_zero]
  have hmod : ((r+s)*(q+1)+r)%(r+s)=r := by
    simp [Nat.add_mod,Nat.mod_eq_of_lt hlt]
  have h := balanced_degreeConvolution_perm ((r+s)*(q+1)*(q+2)/2)
    ((r+s)*(q+1)*(q+2)/2+(q+2)*r) r s q
  simpa only [interiorGLDegreeList,glFormula,hdiv,hmod,Nat.add_sub_cancel_left,
    show q+1+1=q+2 by omega,Nat.mul_comm r (q+2),Nat.add_assoc] using h

private theorem minimal_degrees_of_perm {K a b : Type*} [Field K]
    [Fintype b] [DecidableEq b] {A : Matrix a b K[X]} {xs ys : List ℕ}
    (h : HasMinimalKernelDegrees A xs) (hperm : xs.Perm ys) :
    HasMinimalKernelDegrees A ys := by
  obtain ⟨k,B,d,hd,hl,hp⟩ := h
  exact ⟨k,B,d,hd,hl,hp.trans hperm⟩

private theorem kronecker_decomposition_of_perm {K b : Type*} [Field K]
    [Fintype b] [DecidableEq b] {A : Matrix b b K[X]} {xs ys : List ℕ}
    (h : HasKroneckerDecomposition A xs) (hperm : xs.Perm ys) :
    HasKroneckerDecomposition A ys := by
  obtain ⟨k,d,hp,T,S,hTS,hST,hcanon⟩ := h
  exact ⟨k,d,hp.trans hperm,T,S,hTS,hST,hcanon⟩

theorem generic_positive_depth_gl_formula {K : Type*} [Field K]
    (n m : ℕ) (hm : 0<m) (hmn : m<n) (hrem : n%m≠0) :
    HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K (Fin n) (Fin m)) (genericAffineRows K (Fin n) (Fin m)))
      (glFormula n m) ∧
    HasKroneckerDecomposition (glKirillovMatrix
      (genericAffineSquare K (Fin n) (Fin m)) (genericAffineRows K (Fin n) (Fin m)))
      (glFormula n m) := by
  obtain ⟨q,hq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.div_pos hmn.le hm))
  change n/m=q+1 at hq
  let r := n%m
  let s := m-r
  have hr : 0<r := Nat.pos_of_ne_zero hrem
  have hs : 0<s := Nat.sub_pos_of_lt (Nat.mod_lt n hm)
  letI : NeZero r := ⟨Nat.ne_of_gt hr⟩
  letI : NeZero s := ⟨Nat.ne_of_gt hs⟩
  have hsplit : r+s=m := Nat.add_sub_of_le (Nat.mod_lt n hm).le
  have hn : (r+s)*(q+1)+r=n := by
    rw [hsplit,← hq]
    exact Nat.div_add_mod n m
  have hp := interiorGLDegreeList_perm_formula r s q hr hs
  rw [hn,hsplit] at hp
  have hmin := generic_interior_gl_minimal_degrees (K:=K) r s q
  have hcanon := generic_interior_gl_kronecker (K:=K) r s q
  rw [hn,hsplit] at hmin hcanon
  exact ⟨minimal_degrees_of_perm hmin hp,kronecker_decomposition_of_perm hcanon hp⟩

private theorem above_formula_perm (n m : ℕ) (hnm : n<m) :
    (List.replicate (n*(n%(m-n))) (n/(m-n)+1) ++
      List.replicate (n*((m-n)-n%(m-n))) (n/(m-n))).Perm (glFormula n m) := by
  simp only [glFormula,Nat.div_eq_of_lt hnm,Nat.mod_eq_of_lt hnm,Nat.mul_zero,
    Nat.zero_mul,Nat.zero_div,Nat.zero_mod,Nat.zero_add,Nat.add_zero,Nat.mul_one,
    Nat.sub_zero,List.replicate_zero,List.append_nil]
  exact List.perm_append_comm

theorem generic_nondivisible_gl_formula {K : Type*} [Field K]
    (n m : ℕ) (hm : 0<m) (hrem : n%m≠0) :
    HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K (Fin n) (Fin m)) (genericAffineRows K (Fin n) (Fin m)))
      (glFormula n m) ∧
    HasKroneckerDecomposition (glKirillovMatrix
      (genericAffineSquare K (Fin n) (Fin m)) (genericAffineRows K (Fin n) (Fin m)))
      (glFormula n m) := by
  rcases lt_trichotomy n m with hnm | heq | hmn
  · have hsize : Fintype.card (Fin n)<Fintype.card (Fin m) := by
      simpa only [Fintype.card_fin] using hnm
    have hmin := generic_above_gl_minimal_degrees (K:=K) hsize
    have hcanon := generic_above_gl_kronecker_decomposition (K:=K) hsize
    simp only [Fintype.card_fin] at hmin hcanon
    exact ⟨minimal_degrees_of_perm hmin (above_formula_perm n m hnm),
      kronecker_decomposition_of_perm hcanon (above_formula_perm n m hnm)⟩
  · subst n
    exact (hrem (Nat.mod_self m)).elim
  · exact generic_positive_depth_gl_formula n m hm hmn hrem

end FD56
