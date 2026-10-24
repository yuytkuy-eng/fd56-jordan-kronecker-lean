/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.CubicScalarInduction

/-! Completions with uniform kernel degree and their cubic extensions. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K m r q : Type*} [Field K] [Fintype m] [Fintype r] [Fintype q]
  [DecidableEq m] [DecidableEq r] [DecidableEq q]

theorem polynomial_completion_of_left_inverse
    (G : Matrix m r K[X]) (S : Matrix m q K[X])
    (R : Matrix r m K[X]) (V : Matrix q m K[X]) (W : Matrix q q K[X])
    (hcard : Fintype.card m=Fintype.card r+Fintype.card q)
    (hRG : R*G=1) (hRS : R*S=0) (hVG : V*G=0) (hWA : W*(V*S)=1) :
    G*R+S*W*V=1 := by
  let e : (r ⊕ q) ≃ m := Fintype.equivOfCardEq (by simpa using hcard.symm)
  have hleft : Matrix.fromRows R (W*V)*Matrix.fromCols G S=1 := by
    rw [Matrix.fromRows_mul_fromCols]
    simp only [hRG,hRS,Matrix.mul_assoc,hVG,hWA,Matrix.mul_zero,Matrix.fromBlocks_one]
  have hright := (Matrix.mul_eq_one_comm_of_equiv e).mp hleft
  simpa only [Matrix.fromCols_mul_fromRows,← Matrix.mul_assoc] using hright

structure UniformCubicCompletion (alpha : r → ℕ) (b : ℕ)
    (W : Matrix q q K[X]) where
  G : Matrix m r K[X]
  S : Matrix m q K[X]
  R : Matrix r m K[X]
  V : Matrix q m K[X]
  gDegree : ∀ x j, (G x j).natDegree ≤ alpha j+2
  sDegree : DegreeBound S 0
  vDegree : ∀ j x, (V j x).natDegree ≤ b
  leading : Function.Injective (Matrix.mulVec
    (fun x j => (V j x).coeff (b)))
  rg : R*G=1
  rs : R*S=0
  vg : V*G=0
  wa : W*(V*S)=1
  completion : G*R+S*W*V=1

namespace UniformCubicCompletion

variable {alpha : r → ℕ} {b : ℕ} {W : Matrix q q K[X]}

def extend (C : UniformCubicCompletion (m := m) alpha b W) :
    UniformCubicCompletion (m := q ⊕ m) (Sum.elim (fun _ : q => 1) alpha)
      (b+3) W where
  G := cubicRowExtension C.G C.S
  S := Matrix.fromRows 1 0
  R := cubicRowExtensionRight C.R W C.V
  V := cubicRowExtensionKernel C.V C.S
  gDegree := by
    intro x j
    cases x with
    | inl x =>
      cases j with
      | inl j =>
        change ((X^3 : K[X]) * (if x=j then 1 else 0)).natDegree ≤ 3
        split_ifs <;> simp
      | inr j => simp [cubicRowExtension, Matrix.fromBlocks]
    | inr x =>
      cases j with
      | inl j => exact (by simpa using C.sDegree x j :
          (-C.S x j).natDegree ≤ 0).trans (by simp)
      | inr j => exact C.gDegree x j
  sDegree := by
    intro x j
    cases x <;> simp [Matrix.fromRows, Matrix.one_apply]
    split_ifs <;> simp
  vDegree := cubic_kernel_degree_of_constant_selector C.V C.S b C.vDegree C.sDegree
  leading := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      cubicRowExtensionKernel_leading C.V C.S (fun j => b) C.leading
  rg := cubicRowExtension_right C.G C.S C.R C.V W C.rg C.rs C.vg C.wa
  rs := by
    simp [cubicRowExtensionRight, Matrix.fromBlocks_mul_fromRows]
  vg := cubicRowExtension_kernel C.G C.S C.V C.vg
  wa := by
    simpa [cubicRowExtensionKernel, Matrix.fromCols_mul_fromRows] using C.wa
  completion := cubicRowExtension_completion C.G C.S C.R C.V W C.completion C.wa

theorem injective (C : UniformCubicCompletion (m := m) alpha b W) :
    Function.Injective C.G.mulVec := by
  intro u v h
  have hh := congrArg (fun z => C.R *ᵥ z) h
  simpa only [Matrix.mulVec_mulVec, C.rg, Matrix.one_mulVec] using hh

theorem coordinates {h : Type*} (C : UniformCubicCompletion (m := m) alpha b W)
    (Z : Matrix h m K[X]) (hZ : Z*C.G=0) : Z=(Z*C.S*W)*C.V := by
  calc
    Z = Z*(C.G*C.R+C.S*W*C.V) := by rw [C.completion, Matrix.mul_one]
    _ = (Z*C.S*W)*C.V := by simp [Matrix.mul_add, ← Matrix.mul_assoc, hZ]

theorem coordinate_degree {h : Type*} (C : UniformCubicCompletion (m := m) alpha b W)
    (Q : Matrix h q K[X]) (d : ℕ)
    (hQ : DegreeBound (Q*C.V) d) :
    ∀ i j, Q i j=0 ∨ (b≤d ∧ (Q i j).natDegree≤d-(b)) := by
  intro i
  apply (polynomial_combination_degree_iff C.V.transpose (fun j => b)
    (Q i) d (fun x j => C.vDegree j x) C.leading).mp
  intro x
  have hh := hQ i x
  simpa [Matrix.mulVec, Matrix.mul_apply, dotProduct, Matrix.transpose_apply, mul_comm] using hh

theorem kernel_hilbert_zero (C : UniformCubicCompletion (m := m) alpha b W)
    (d : ℕ) (hd : d<b) :
    Module.finrank K (polynomialKernelAtDegree C.G.transpose d)=0 := by
  have hbot : polynomialKernelAtDegree C.G.transpose d=⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    let Z : Matrix Unit m K[X] := fun _ j => (x j).val
    have hZG : Z*C.G=0 := by
      apply Matrix.ext
      intro i j
      have hh := congrFun hx j
      simpa [polynomialKernelAtDegree, boundedKernelMap, Z, Matrix.mul_apply,
        Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm] using hh
    let Q : Matrix Unit q K[X] := Z*C.S*W
    have hQV : Z=Q*C.V := C.coordinates Z hZG
    have hQd := C.coordinate_degree Q d (by
      rw [← hQV]
      intro i j
      exact boundedPoly_degree d (x j))
    have hQ : Q=0 := by
      apply Matrix.ext
      intro i j
      rcases hQd i j with hz | ⟨hh,_⟩
      · exact hz
      · omega
    have hZ : Z=0 := by rw [hQV,hQ,Matrix.zero_mul]
    funext j
    apply Subtype.ext
    exact congrArg (fun A : Matrix Unit m K[X] => A () j) hZ
  rw [hbot]
  exact finrank_bot K _

def ScalarZero (C : UniformCubicCompletion (m := m) alpha b W) (d : ℕ) : Prop :=
  ∀ (E : Matrix r m K[X]) (c : K[X]),
    (∀ i x, (E i x).natDegree≤d-(alpha i+1)) → c.natDegree≤d+1 →
    E*C.G=(-c) • 1 → c=0

def ScalarSelector {t : Type*} (C : UniformCubicCompletion (m := m) alpha b W)
    (d : ℕ) (f : t → ℕ) : Prop :=
  ∀ (E : Matrix r m K[X]) (c : K[X]),
    (∀ i x, (E i x).natDegree≤d-(alpha i+1)) → c.natDegree≤d+1 →
    E*C.G=(-c) • 1 → (∀ j, c.coeff (f j)=0) → c=0

theorem scalar_zero_extend (C : UniformCubicCompletion (m := m) alpha b W)
    (hd : ∀ i, alpha i+1≤b)
    (hjet : Function.Injective (Matrix.mulVec
      (fun (ij : q × q) (k : Fin 3) => (W ij.1 ij.2).coeff (2-k.val))))
    (hzero : C.ScalarZero b) : C.extend.ScalarZero (b+3) := by
  exact cubic_scalar_zero_extend C.G C.S C.R C.V W C.completion alpha b hd
    C.vDegree C.leading hjet hzero

theorem scalar_selector_extend {t : Type*}
    (C : UniformCubicCompletion (m := m) alpha b W)
    (d : ℕ) (hd : ∀ i, alpha i+1≤d) (f : t → ℕ)
    (hzero : C.ScalarSelector d f) :
    C.extend.ScalarSelector (d+3)
      (Sum.elim (fun k : Fin 3 => k.val) (fun j => f j+3)) := by
  exact cubic_scalar_selector_extend C.G C.S C.R C.V W C.completion alpha d hd f hzero

end UniformCubicCompletion
end FD56
