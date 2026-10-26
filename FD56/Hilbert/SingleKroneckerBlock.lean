/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedGLKronecker

/-! A singleton Kronecker decomposition has a specified single-block index. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K a : Type*} [Field K] [Fintype a] [DecidableEq a]

theorem single_kronecker_block_congruence (P : Matrix a a K[X]) (e : ℕ)
    (hP : HasKroneckerDecomposition P [e]) :
    ∃ T : Matrix a (Fin e ⊕ Fin (e+1)) K,
    ∃ S : Matrix (Fin e ⊕ Fin (e+1)) a K,
      T*S=1 ∧ S*T=1 ∧ (T.map C).transpose*P*T.map C=kroneckerBlockPencil e := by
  obtain ⟨r,d,hp,T,S,hTS,hST,hcong⟩ := hP
  have hr : r=1 := by simpa using hp.length_eq
  subst r
  have hd : d=fun _ => e := by
    apply List.ofFn_injective
    simpa using List.perm_singleton.mp hp
  subst d
  let f : (Fin e ⊕ Fin (e+1)) ≃ (Σ _ : Fin 1, Fin e ⊕ Fin (e+1)) :=
    { toFun := fun k => ⟨0,k⟩
      invFun := fun k => k.2
      left_inv := fun _ => rfl
      right_inv := by intro ⟨i,k⟩; have hi : i=0 := Subsingleton.elim _ _; subst i; rfl }
  refine ⟨T.submatrix id f,S.submatrix f id,?_,?_,?_⟩
  · rw [Matrix.submatrix_mul_equiv,hTS,Matrix.submatrix_id_id]
  · change S.submatrix f (Equiv.refl _) * T.submatrix (Equiv.refl _) f=1
    rw [Matrix.submatrix_mul_equiv,hST]
    exact Matrix.submatrix_one_equiv f
  · simp only [← Matrix.submatrix_map,Matrix.transpose_submatrix]
    change (T.map C).transpose.submatrix f (Equiv.refl a) *
      P.submatrix (Equiv.refl a) (Equiv.refl a) * (T.map C).submatrix (Equiv.refl a) f=_
    rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv,hcong]
    funext i j
    exact Matrix.blockDiagonal'_apply_eq (fun _ : Fin 1 => kroneckerBlockPencil (K := K) e) 0 i j

end FD56
