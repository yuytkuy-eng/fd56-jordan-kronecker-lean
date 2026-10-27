/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.RectangularCongruenceDeterminant
import FD56.Hilbert.SeparableCrossPencil
import FD56.LinearAlgebra.WeightedDeterminantDegree

/-! A simple square determinant determines the cross determinant of an isotropic block form. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem isotropic_cross_determinant_separable {K a n : Type*} [Field K]
    [Fintype a] [Fintype n] [DecidableEq a] [DecidableEq n]
    (e : (n ⊕ n) ≃ a) (S : Matrix a (n ⊕ n) K) (T : Matrix (n ⊕ n) a K)
    (hST : S*T=1) (P : Matrix a a K[X]) (A W : Matrix n n K[X])
    (hcong : (S.map C).transpose*P*S.map C=Matrix.fromBlocks A W (-W.transpose) 0)
    (hW : DegreeBound W 1) (g : K[X]) (hP : P.det=g^2)
    (hg : g.Separable) (hd : g.natDegree=Fintype.card n) :
    W.det.Separable ∧ Matrix.det (fun i j => (W i j).coeff 1)≠0 := by
  obtain ⟨c,hc,hdet⟩ := constant_rectangular_congruence_det e S T hST P
  rw [hcong,alternating_cross_block_det,hP] at hdet
  have he : W.det^2=(C c*g)^2 := by rw [mul_pow]; exact hdet
  have hs := separable_of_square_eq_scaled_square W.det g c hc hg he
  refine ⟨hs,?_⟩
  have hdW : W.det.natDegree=Fintype.card n := by
    have h := congrArg Polynomial.natDegree he
    rw [Polynomial.natDegree_pow,Polynomial.natDegree_pow,Polynomial.natDegree_C_mul hc,hd] at h
    omega
  have hcoeff := polynomial_det_coefficient_row_sum W (fun _ => 1) hW
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hcoeff
  rw [← hcoeff,← hdW]
  exact Polynomial.leadingCoeff_ne_zero.mpr hs.ne_zero

end FD56
