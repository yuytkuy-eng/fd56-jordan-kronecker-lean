/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.SquareSLRestrictedPencil
import FD56.LinearAlgebra.GenericResonantColumn

/-! Independent state coefficients discharge the resonances in the square SL restriction. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K L n : Type*} [Field K] [Field L] [Fintype n] [DecidableEq n] [Nontrivial n]

theorem independent_squareSL_separated_decomposition
    (phi : MvPolynomial ((n × n) ⊕ (n × n)) K →+* L) (hphi : Function.Injective phi)
    (P₀ P₁ V S T : Matrix n n K) (hST : S*T=1) (hTS : T*S=1)
    (hP₁V : P₁*V=1) (hVP₁ : V*P₁=1)
    (lam : n → K) (hlam : Function.Injective lam)
    (hdiag : (-V*P₀)*S=S*Matrix.diagonal lam) (i₀ : n) :
    let psi : K →+* L := phi.comp MvPolynomial.C
    ∃ j : n → n, (∀ i, i≠j i) ∧
    ∃ G : Matrix (SLChartInput n n i₀) (squareSLGroupedIndex j i₀) L,
    ∃ H : Matrix (squareSLGroupedIndex j i₀) (SLChartInput n n i₀) L,
      G*H=1 ∧ H*G=1 ∧
      (G.map C).transpose * slKirillovMatrix
          (affineMatrixPencil (independentMatrixConstant.map phi) (independentMatrixLeading.map phi))
          (affineMatrixPencil (P₀.map psi) (P₁.map psi)) i₀ * G.map C =
        squareSLSeparatedTarget (fun i => psi (lam i)) j i₀ := by
  intro psi
  have hp (A B : Matrix n n K) (h : A*B=1) : A.map psi * B.map psi = 1 := by
    rw [← Matrix.map_mul,h,Matrix.map_one _ (map_zero psi) (map_one psi)]
  have hdiag' : (-V.map psi*P₀.map psi)*S.map psi = S.map psi*Matrix.diagonal (fun i => psi (lam i)) := by
    have h := congrArg (fun M => M.map psi) hdiag
    have hn : (-V).map psi = -V.map psi := by ext i j; simp
    have hd : (Matrix.diagonal lam).map psi = Matrix.diagonal (fun i => psi (lam i)) := by
      ext i j
      by_cases hij : i=j <;> simp [Matrix.diagonal_apply,hij]
    simpa only [Matrix.map_mul,hn,hd] using h
  choose j hj using fun i : n => exists_ne i
  refine ⟨j,fun i => Ne.symm (hj i),?_⟩
  apply squareSL_normalized_separated_decomposition
    (independentMatrixConstant.map phi) (independentMatrixLeading.map phi)
    (P₀.map psi) (P₁.map psi) (V.map psi) (S.map psi) (T.map psi)
    (hp S T hST) (hp T S hTS) (hp P₁ V hP₁V) (hp V P₁ hVP₁)
    (fun i => psi (lam i)) (psi.injective.comp hlam) hdiag' j (fun i => Ne.symm (hj i))
  intro i
  exact mapped_independent_resonant_entry_ne_zero phi hphi S T hTS (lam i) (j i) i

end FD56
