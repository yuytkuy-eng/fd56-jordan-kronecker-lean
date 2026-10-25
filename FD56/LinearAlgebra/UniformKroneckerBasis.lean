/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.DualNormalization
import FD56.LinearAlgebra.UniformKroneckerCongruence

/-! A full-dimensional coefficient span and its independent pairing functionals
give an actual simultaneous constant congruence for uniform Kronecker chains.
The coefficient and pairing identities remain explicit hypotheses.
-/

noncomputable section
namespace FD56
open Matrix
open scoped BigOperators

variable {K n w f : Type*} [Field K]
  [Fintype n] [Fintype w] [Fintype f]
  [DecidableEq n] [DecidableEq w] [DecidableEq f]

/-- Choose a dual complement using the full dimension budget, with no given
coordinate chart on the ambient space. -/
theorem exists_dual_complement_of_cardEq
    (W : Matrix n w K) (L : Matrix f n K)
    (hcard : Fintype.card n = Fintype.card w + Fintype.card f)
    (hLW : L * W = 0) (hW : Function.Injective W.mulVec)
    (hL : Function.Surjective L.mulVec) :
    ∃ Q : Matrix n f K, ∃ J : Matrix (w ⊕ f) n K,
      Matrix.fromCols W Q * J = 1 ∧ J * Matrix.fromCols W Q = 1 ∧ L * Q = 1 := by
  let c : n ≃ w ⊕ f := Fintype.equivOfCardEq (by simpa using hcard)
  let W' := W.submatrix c.symm id
  let L' := L.submatrix id c.symm
  have hLW' : L' * W' = 0 := by
    simp [L', W', Matrix.submatrix_mul_equiv, hLW]
  have hW' : Function.Injective W'.mulVec := by
    intro x y hxy
    apply hW
    funext i
    simpa [W', Matrix.mulVec, Matrix.submatrix] using congrFun hxy (c i)
  have hL' : Function.Surjective L'.mulVec := by
    intro y
    obtain ⟨x, hx⟩ := hL y
    refine ⟨x ∘ c.symm, ?_⟩
    rw [← hx]
    funext i
    exact c.symm.sum_comp (fun j => L i j * x j)
  obtain ⟨H', J', hHJ', hJH', _, hLH', hHW'⟩ :=
    exists_dual_matrix_normalization W' L' hLW' hW' hL'
  let H : Matrix n (w ⊕ f) K := H'.submatrix c id
  let J : Matrix (w ⊕ f) n K := J'.submatrix id c
  have hHJ : H * J = 1 := by
    change H'.submatrix c (Equiv.refl _) * J'.submatrix (Equiv.refl _) c = 1
    rw [Matrix.submatrix_mul_equiv, hHJ', Matrix.submatrix_one_equiv]
  have hJH : J * H = 1 := by
    change J'.submatrix id c * H'.submatrix c id = 1
    rw [Matrix.submatrix_mul_equiv, hJH', Matrix.submatrix_id_id]
  have hLH : L * H = Matrix.fromCols (0 : Matrix f w K) (1 : Matrix f f K) := by
    have h := Matrix.submatrix_mul_equiv L' H' id c id
    have hc : L'.submatrix id c = L := by
      funext i j
      simp [L']
    rw [hc, hLH', Matrix.submatrix_id_id] at h
    exact h
  have hHW : H * Matrix.fromRows (1 : Matrix w w K) (0 : Matrix f w K) = W := by
    have h := Matrix.submatrix_mul_equiv H'
      (Matrix.fromRows (1 : Matrix w w K) (0 : Matrix f w K)) c (Equiv.refl _) id
    simp only [Equiv.refl_apply, Matrix.submatrix_id_id] at h
    rw [hHW'] at h
    simpa [H, W'] using h
  let Q : Matrix n f K := H.submatrix id Sum.inr
  have hHsplit : H = Matrix.fromCols (H.submatrix id Sum.inl) Q := by
    funext i j
    cases j <;> rfl
  have hleft : H.submatrix id Sum.inl = W := by
    rw [hHsplit, Matrix.fromCols_mul_fromRows] at hHW
    simpa using hHW
  have hH : H = Matrix.fromCols W Q := by rw [hHsplit, hleft]
  refine ⟨Q, J, ?_, ?_, ?_⟩
  · simpa only [← hH] using hHJ
  · simpa only [← hH] using hJH
  · rw [hH, Matrix.mul_fromCols] at hLH
    exact congrArg (fun M => M.submatrix id Sum.inr) hLH

omit [Fintype w] [DecidableEq n] [DecidableEq w] in
/-- A dual complement exposes the prescribed cross block. -/
theorem dual_complement_congruence
    (A : Matrix n n K) (W : Matrix n w K) (L : Matrix f n K)
    (Q : Matrix n f K) (C : Matrix w f K)
    (hA : A.transpose = -A) (hLW : L * W = 0) (hLQ : L * Q = 1)
    (hWA : W.transpose * A = C * L) :
    (Matrix.fromCols W Q).transpose * A * Matrix.fromCols W Q =
      Matrix.fromBlocks 0 C (-C.transpose) (Q.transpose * A * Q) := by
  have hleft : W.transpose * A * W = 0 := by
    rw [hWA, Matrix.mul_assoc, hLW, Matrix.mul_zero]
  have hright : W.transpose * A * Q = C := by
    rw [hWA, Matrix.mul_assoc, hLQ, Matrix.mul_one]
  have hbottom : Q.transpose * A * W = -C.transpose := by
    calc
      _ = -(W.transpose * A * Q).transpose := by
        simp [Matrix.transpose_mul, hA, Matrix.mul_assoc]
      _ = _ := by rw [hright]
  rw [Matrix.transpose_fromCols, Matrix.fromRows_mul,
    Matrix.fromRows_mul_fromCols, hleft, hright, hbottom]

omit [Fintype f] [DecidableEq n] [DecidableEq f] in
/-- Alternation, including the diagonal condition in characteristic two,
is preserved by the complement restriction. -/
theorem complement_restriction_alternating
    (A : Matrix n n K) (Q : Matrix n f K)
    (hA : A.transpose = -A) (hAlt : ∀ x : n → K, x ⬝ᵥ (A *ᵥ x) = 0) :
    (Q.transpose * A * Q).transpose = -(Q.transpose * A * Q) ∧
      ∀ i, (Q.transpose * A * Q) i i = 0 := by
  constructor
  · simp [Matrix.transpose_mul, hA, Matrix.mul_assoc]
  · intro i
    rw [Matrix.mul_assoc]
    exact hAlt (fun j => Q j i)

/-- Assemble the actual constant congruence from independent coefficients,
independent pairing functionals, and their chain pairing identities. -/
theorem exists_uniform_kronecker_basis
    {e r : ℕ} (A B : Matrix n n K)
    (W : Matrix n (Fin (e+1) × Fin r) K)
    (L : Matrix (Fin e × Fin r) n K)
    (hcard : Fintype.card n = (e+1)*r + e*r)
    (hW : Function.Injective W.mulVec) (hL : Function.Surjective L.mulVec)
    (hLW : L * W = 0)
    (hWA : W.transpose * A = uniformCrossFirst * L)
    (hWB : W.transpose * B = uniformCrossSecond * L)
    (hA : A.transpose = -A) (hB : B.transpose = -B)
    (hAltA : ∀ x : n → K, x ⬝ᵥ (A *ᵥ x) = 0)
    (hAltB : ∀ x : n → K, x ⬝ᵥ (B *ᵥ x) = 0) :
    ∃ G : Matrix n ((Fin (e+1) × Fin r) ⊕ (Fin e × Fin r)) K,
    ∃ J : Matrix ((Fin (e+1) × Fin r) ⊕ (Fin e × Fin r)) n K,
      G * J = 1 ∧ J * G = 1 ∧
      G.transpose * A * G =
        Matrix.fromBlocks 0 uniformCrossFirst (-uniformCrossFirst.transpose) 0 ∧
      G.transpose * B * G =
        Matrix.fromBlocks 0 uniformCrossSecond (-uniformCrossSecond.transpose) 0 := by
  obtain ⟨Q, J, hHJ, hJH, hLQ⟩ := exists_dual_complement_of_cardEq W L
    (by simpa using hcard) hLW hW hL
  let H := Matrix.fromCols W Q
  let S := Q.transpose * A * Q
  let T := Q.transpose * B * Q
  have hHA : H.transpose * A * H =
      Matrix.fromBlocks 0 uniformCrossFirst (-uniformCrossFirst.transpose) S :=
    dual_complement_congruence A W L Q uniformCrossFirst hA hLW hLQ hWA
  have hHB : H.transpose * B * H =
      Matrix.fromBlocks 0 uniformCrossSecond (-uniformCrossSecond.transpose) T :=
    dual_complement_congruence B W L Q uniformCrossSecond hB hLW hLQ hWB
  obtain ⟨hS, hSd⟩ := complement_restriction_alternating A Q hA hAltA
  obtain ⟨hT, hTd⟩ := complement_restriction_alternating B Q hB hAltB
  obtain ⟨hXY, hYX, hAS, hBT⟩ :=
    uniform_kronecker_block_congruence S T hS hSd hT hTd
  let X := complementShift (uniformFiniteCorrection S T)
  let Y := complementShift (-uniformFiniteCorrection S T)
  refine ⟨H * X, Y * J, ?_, ?_, ?_, ?_⟩
  · calc
      H * X * (Y * J) = H * (X * Y) * J := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hXY, Matrix.mul_one]; exact hHJ
  · calc
      Y * J * (H * X) = Y * (J * H) * X := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJH, Matrix.mul_one]; exact hYX
  · calc
      (H * X).transpose * A * (H * X) = X.transpose * (H.transpose * A * H) * X := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hHA]; exact hAS
  · calc
      (H * X).transpose * B * (H * X) = X.transpose * (H.transpose * B * H) * X := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hHB]; exact hBT

end FD56
