/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic

/-! Independent affine matrix coefficients remain nonzero at every prescribed
resonance after an invertible change of state coordinates. -/

noncomputable section
namespace FD56
open Matrix

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

def independentMatrixConstant : Matrix n n (MvPolynomial ((n × n) ⊕ (n × n)) K) :=
  fun i j => MvPolynomial.X (.inl (i,j))

def independentMatrixLeading : Matrix n n (MvPolynomial ((n × n) ⊕ (n × n)) K) :=
  fun i j => MvPolynomial.X (.inr (i,j))

theorem independent_resonant_entry_ne_zero (S T : Matrix n n K)
    (hTS : T*S=1) (lam : K) (i j : n) :
    (T.map (MvPolynomial.C (σ := (n × n) ⊕ (n × n))) * (independentMatrixConstant (K := K) (n := n)) * S.map (MvPolynomial.C (σ := (n × n) ⊕ (n × n)))) i j +
      MvPolynomial.C lam *
        (T.map (MvPolynomial.C (σ := (n × n) ⊕ (n × n))) * (independentMatrixLeading (K := K) (n := n)) * S.map (MvPolynomial.C (σ := (n × n) ⊕ (n × n)))) i j ≠ 0 := by
  let E : Matrix n n K := Matrix.stdBasisMatrix i j 1
  let A := S*E*T
  let phi : MvPolynomial ((n × n) ⊕ (n × n)) K →+* K :=
    MvPolynomial.eval₂Hom (RingHom.id K) (Sum.elim (fun ij => A ij.1 ij.2) (fun _ => 0))
  have hconst (U : Matrix n n K) : (U.map MvPolynomial.C).map phi = U := by
    ext u v
    simp [phi]
  have hA : (independentMatrixConstant (K := K) (n := n)).map phi = A := by
    ext u v
    simp [independentMatrixConstant,phi]
  have hB : (independentMatrixLeading (K := K) (n := n)).map phi = 0 := by
    ext u v
    simp [independentMatrixLeading,phi]
  have hconj : T*A*S = E := by
    dsimp [A]
    simp only [Matrix.mul_assoc,← Matrix.mul_assoc T S,hTS,Matrix.one_mul,Matrix.mul_one]
  intro hz
  have he := congrArg phi hz
  simp only [map_add,map_mul,map_zero] at he
  change ((T.map (MvPolynomial.C (σ := (n × n) ⊕ (n × n))) * (independentMatrixConstant (K := K) (n := n)) * S.map (MvPolynomial.C (σ := (n × n) ⊕ (n × n)))).map phi) i j +
    phi (MvPolynomial.C lam) *
      ((T.map (MvPolynomial.C (σ := (n × n) ⊕ (n × n))) * (independentMatrixLeading (K := K) (n := n)) * S.map (MvPolynomial.C (σ := (n × n) ⊕ (n × n)))).map phi) i j = 0 at he
  simp only [Matrix.map_mul,hconst,hA,hB,hconj,Matrix.mul_zero,Matrix.zero_mul,
    Matrix.zero_apply,mul_zero,add_zero] at he
  simp [E,Matrix.stdBasisMatrix] at he

theorem mapped_independent_resonant_entry_ne_zero {L : Type*} [Field L]
    (phi : MvPolynomial ((n × n) ⊕ (n × n)) K →+* L) (hphi : Function.Injective phi)
    (S T : Matrix n n K) (hTS : T*S=1) (lam : K) (i j : n) :
    (((T.map (MvPolynomial.C (σ := (n × n) ⊕ (n × n)))).map phi) * (independentMatrixConstant (K := K) (n := n)).map phi *
        ((S.map (MvPolynomial.C (σ := (n × n) ⊕ (n × n)))).map phi)) i j +
      phi (MvPolynomial.C lam) *
        (((T.map (MvPolynomial.C (σ := (n × n) ⊕ (n × n)))).map phi) * (independentMatrixLeading (K := K) (n := n)).map phi *
          ((S.map (MvPolynomial.C (σ := (n × n) ⊕ (n × n)))).map phi)) i j ≠ 0 := by
  have h := independent_resonant_entry_ne_zero S T hTS lam i j
  have hn := (map_ne_zero_iff phi hphi).mpr h
  simpa only [map_add,map_mul,← Matrix.map_mul,Matrix.map_apply] using hn

end FD56
