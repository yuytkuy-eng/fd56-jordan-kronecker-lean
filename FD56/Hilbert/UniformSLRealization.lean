/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformSLWitness
import FD56.Hilbert.FamilySLRealization

/-! An affine SL witness with zero bounded kernel at degree five in
dimensions `(n,m) = (5r,4r)`, for `r ≥ 2`. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K : Type*} [Field K]

theorem middle_boundedSLKernel_eq_bot_of_weighted_obstruction
    {n m r : Type*} [Fintype n] [Fintype m] [Fintype r]
    [DecidableEq n] [DecidableEq m] [DecidableEq r] [Nonempty n]
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec)
    (a : r → ℕ) (hP : DegreeBound P 1)
    (hB : ∀ x i, (polynomialKernelBasisMatrix P B x i).natDegree ≤ a i)
    (hBL : Function.Injective
      (Matrix.mulVec (fun x i => (polynomialKernelBasisMatrix P B x i).coeff (a i))))
    (hPL : Function.Injective (matrixCoeff P 1).transpose.mulVec) (d : ℕ)
    (hzero : ∀ (E : Matrix r m K[X]) (c : K[X]),
      (∀ i j, E i j = 0 ∨ (a i + 1 ≤ d ∧ (E i j).natDegree ≤ d - (a i + 1))) →
        E * (P * M * polynomialKernelBasisMatrix P B) = (-c) • 1 → E = 0 ∧ c = 0) :
    boundedSLKernel M P d = ⊥ := by
  apply le_antisymm
  · intro z hz
    obtain ⟨E, c, hrel, hX, hU⟩ :=
      (middle_sl_radical_iff M P B R hPR hG (entries z.1) (entries z.2)).mp hz
    have hED := (middle_product_degree_iff (polynomialKernelBasisMatrix P B) P E a d
      hB hBL hP hPL).mp (by
        change DegreeBound (middleSLX P B E) d
        rw [← hX]
        exact entries_degree z.1)
    obtain ⟨hE, hc⟩ := hzero E c hED hrel
    have hzX : entries z.1 = 0 := by simpa [middleSLX, hE] using hX
    have hzU : entries z.2 = 0 := by
      simpa [middleSLTranslation, middleSLX, hE, hc] using hU
    change z = 0
    apply Prod.ext
    · funext i j
      apply Subtype.ext
      exact congrFun (congrFun hzX i) j
    · funext i j
      apply Subtype.ext
      exact congrFun (congrFun hzU i) j
  · exact bot_le

abbrev UniformSLRows (r : ℕ) := Σ _i : Fin r, Fin 4
abbrev UniformSLColumns (r : ℕ) := Σ _i : Fin r, Fin 5

def uniformSLRowEquiv (r : ℕ) : UniformSLRows r ≃ Fin 4 × Fin r where
  toFun x := (x.2, x.1)
  invFun x := ⟨x.2, x.1⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

theorem exists_uniform_sl_block_degree_five_witness (r : ℕ) (hr : 2 ≤ r) :
    ∃ M : Matrix (UniformSLColumns r) (UniformSLColumns r) K[X],
      DegreeBound M 1 ∧
        slHilbert M (rectangularBlockPencil (fun _ : Fin r => 4)) 5 = 0 := by
  let p : Fin r := ⟨0, by omega⟩
  let q : Fin r := ⟨1, by omega⟩
  have hpq : p ≠ q := by intro h; have := congrArg Fin.val h; dsimp [p, q] at this; omega
  let e : Fin r → ℕ := fun _ => 4
  let P : Matrix (UniformSLRows r) (UniformSLColumns r) K[X] := rectangularBlockPencil e
  let G : Matrix (UniformSLRows r) (Fin r) K[X] :=
    (uniformSLWitness (K := K) p q).submatrix (uniformSLRowEquiv r) (Equiv.refl _)
  let B := rectangularBlockKernelBasis (K := K) e
  have hGdeg : ∀ x j, (G x j).natDegree ≤ e j + 2 := by
    intro x j
    exact uniformSLWitness_degree p q (uniformSLRowEquiv r x) j
  obtain ⟨M, hM, hPMG⟩ := rectangularBlockPencil_affine_middle_lift e
    (fun _ _ => by norm_num [e]) G hGdeg
  obtain ⟨R, hPR⟩ := rectangularBlockPencil_right_inverse (K := K) e
  have hVB : polynomialKernelBasisMatrix P B = blockMonomialKernel e :=
    polynomialKernelBasisMatrix_rectangularBlock e
  have hGM : P * M * polynomialKernelBasisMatrix P B = G := by rw [hVB]; exact hPMG
  have hGi : Function.Injective G.mulVec := by
    intro u v h
    apply uniformSLWitness_injective p q
    funext x
    have hh := congrFun h ((uniformSLRowEquiv r).symm x)
    simpa only [G, Matrix.submatrix_mulVec_equiv, Function.comp_apply,
      Equiv.refl_symm, Equiv.refl_apply, Equiv.apply_symm_apply] using hh
  have hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec := by
    rw [hGM]
    exact hGi
  have hV : ∀ x i, (polynomialKernelBasisMatrix P B x i).natDegree ≤ e i := by
    rw [hVB]
    exact blockMonomialKernel_column_degree e
  have hVL : Function.Injective (Matrix.mulVec
      (fun x i => (polynomialKernelBasisMatrix P B x i).coeff (e i))) := by
    rw [hVB]
    exact blockMonomialKernel_leading_injective e
  letI : Nonempty (UniformSLColumns r) := ⟨⟨p, 0⟩⟩
  have hz : boundedSLKernel M P 5 = ⊥ := by
    apply middle_boundedSLKernel_eq_bot_of_weighted_obstruction M P B R hPR hG e
      (rectangularBlockPencil_degree e) hV hVL
      (rectangularBlockPencil_leading_transpose_injective e) 5
    intro E c hE hrel
    let E' := E.submatrix (Equiv.refl _) (uniformSLRowEquiv r).symm
    have hE' : ∀ i j, (E' i j).natDegree ≤ 0 := by
      intro i j
      rcases hE i ((uniformSLRowEquiv r).symm j) with he | ⟨_, he⟩
      · simp [E', he]
      · exact he
    have hrel' : E' * uniformSLWitness p q = (-c) • (1 : Matrix (Fin r) (Fin r) K[X]) := by
      rw [hGM] at hrel
      change E * (uniformSLWitness p q).submatrix (uniformSLRowEquiv r) (Equiv.refl _) = _ at hrel
      have hEE : E'.submatrix (Equiv.refl _) (uniformSLRowEquiv r) = E := by
        funext i j
        simp [E']
      rw [← hEE, Matrix.submatrix_mul_equiv] at hrel
      simpa only [Matrix.submatrix_id_id, Equiv.coe_refl] using hrel
    obtain ⟨hzE, hzc⟩ := uniformSLWitness_constant_scalar_obstruction p q hpq E' c hE' hrel'
    refine ⟨?_, hzc⟩
    funext i j
    have hh := congrFun (congrFun hzE i) (uniformSLRowEquiv r j)
    simpa [E'] using hh
  refine ⟨M, hM, ?_⟩
  change Module.finrank K (boundedSLKernel M P 5) = 0
  rw [hz, finrank_bot]

theorem exists_uniform_sl_degree_five_witness (r : ℕ) (hr : 2 ≤ r) :
    ∃ (M : Matrix (Fin (5 * r)) (Fin (5 * r)) K[X])
      (P : Matrix (Fin (4 * r)) (Fin (5 * r)) K[X]),
      DegreeBound M 1 ∧ DegreeBound P 1 ∧ slHilbert M P 5 = 0 := by
  obtain ⟨M, hM, hH⟩ := exists_uniform_sl_block_degree_five_witness (K := K) r hr
  let en : Fin (5 * r) ≃ UniformSLColumns r :=
    Fintype.equivOfCardEq (by simp [UniformSLColumns, Nat.mul_comm])
  let em : Fin (4 * r) ≃ UniformSLRows r :=
    Fintype.equivOfCardEq (by simp [UniformSLRows, Nat.mul_comm])
  refine ⟨M.submatrix en en,
    (rectangularBlockPencil (fun _ : Fin r => 4)).submatrix em en,
    (fun i j => hM (en i) (en j)),
    (fun i j => rectangularBlockPencil_degree _ (em i) (en j)), ?_⟩
  rw [slHilbert_reindex]
  exact hH

end FD56
