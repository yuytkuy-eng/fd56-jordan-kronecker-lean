/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.TwoColumnInteriorGradients
import FD56.Hilbert.GenericInteriorScalarFrame
import FD56.Hilbert.ResidueOneAllDepthFrame

/-! Uniform degrees and the independent selected frame inside all ordered
two-row observability gradients. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false

variable (s q : ℕ) [NeZero s]

def twoColumnInteriorWeight : ℕ := ((2+s)*q*(q+1)+4*(q+1))/2

theorem two_column_interior_row_weight :
    (∑ k : Fin ((2+s)*q+2), (interiorLevel 2 s q k+1))=twoColumnInteriorWeight s q := by
  have hs : 2*(∑ k : Fin ((2+s)*q+2), (interiorLevel 2 s q k+1))=
      (2+s)*q*(q+1)+4*(q+1) := by
    simp only [interiorLevel]
    rw [Fin.sum_univ_add]
    simp only [Fin.coe_castAdd,Fin.coe_natAdd]
    have ht (i : Fin 2) : ((2+s)*q+i.val)/(2+s)=q := by
      rw [Nat.mul_add_div (by omega : 0<2+s),Nat.div_eq_of_lt (by have := i.isLt; omega),Nat.add_zero]
    simp_rw [ht]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
    letI : NeZero (2+s) := ⟨by omega⟩
    nlinarith [residueOne_prefix_row_weight (2+s) q]
  unfold twoColumnInteriorWeight
  omega

theorem twoColumnInteriorWeight_pos : 0<twoColumnInteriorWeight s q := by
  unfold twoColumnInteriorWeight
  omega

theorem twoColumnInteriorScalarGradients_degree {K : Type*} [Field K]
    (M : Matrix (Fin ((2+s)*q+2)) (Fin ((2+s)*q+2)) K[X])
    (P : Matrix (Fin (2+s)) (Fin ((2+s)*q+2)) K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) :
    DegreeBound (twoColumnInteriorScalarGradients s q M P) (twoColumnInteriorWeight s q-1) := by
  intro k ij
  have he : (∑ k : Fin ((2+s)*q+2), (interiorLevel 2 s q k+1))=
      twoColumnInteriorWeight s q-1+1 := by
    rw [two_column_interior_row_weight]
    have := twoColumnInteriorWeight_pos s q
    omega
  obtain ⟨hX,hU,_⟩ := observability_adjugate_solution_degree M P hM hP
    (interiorLevel 2 s q) (twoColumnInteriorRow s q ij) (twoColumnInteriorWeight s q-1) he
  rcases k with ab|ab
  · exact hX ab.1 ab.2
  · exact hU ab.1 ab.2

theorem generic_two_column_scalar_gradients_degree {K : Type*} [Field K] :
    DegreeBound (genericTwoColumnInteriorScalarGradients (K:=K) s q) (twoColumnInteriorWeight s q-1) :=
  twoColumnInteriorScalarGradients_degree s q _ _ (genericAffineSquare_degree K _ _)
    (genericAffineRows_degree K _ _)

theorem twoColumnInteriorRow_selected (z : Option (Fin 2 × Fin s)) :
    twoColumnInteriorRow s q (interiorTerminalRow 2 s z 0,interiorTerminalRow 2 s z 1)=
      interiorSelectorRow 2 s q z := by
  funext k
  obtain ⟨w,rfl⟩ := (interiorPrefixEquiv 2 s q).symm.surjective k
  rcases w with ⟨t,a⟩|a
  · have hn (b : Fin 2) : (interiorPrefixEquiv 2 s q).symm (Sum.inl (t,a))≠interiorMissing 2 s q b := by
      intro he
      have hh := congrArg Fin.val he
      dsimp [interiorPrefixEquiv,interiorMissing] at hh
      nlinarith [t.isLt,a.isLt]
    have hbase : interiorBaseRow 2 s q ((interiorPrefixEquiv 2 s q).symm (Sum.inl (t,a)))=a := by
      apply Fin.ext
      simp [interiorBaseRow,interiorPrefixEquiv,Nat.add_mod,Nat.mod_eq_of_lt a.isLt]
    cases z with
    | none => simpa [twoColumnInteriorRow,interiorSelectorRow] using hbase.symm
    | some ab => simpa [twoColumnInteriorRow,interiorSelectorRow,interiorSwapRow,hn] using hbase.symm
  · simp only [twoColumnInteriorRow,Equiv.apply_symm_apply,Sum.elim_inr,
      interiorPrefixEquiv_symm_inr,interiorSelectorRow_terminal,interiorPrefixEquiv_missing]
    fin_cases a <;> rfl

theorem twoColumnInteriorScalarGradients_selected {R : Type*} [CommRing R]
    (M : Matrix (Fin ((2+s)*q+2)) (Fin ((2+s)*q+2)) R)
    (P : Matrix (Fin (2+s)) (Fin ((2+s)*q+2)) R) :
    (twoColumnInteriorScalarGradients s q M P).submatrix id
      (fun z => (interiorTerminalRow 2 s z 0,interiorTerminalRow 2 s z 1))=
        interiorScalarLiftMatrix 2 s q M P := by
  funext k z
  simp only [Matrix.submatrix_apply,id_eq,twoColumnInteriorScalarGradients,
    interiorScalarLiftMatrix,twoColumnInteriorRow_selected]

end FD56

