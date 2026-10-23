/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedOneTwoJets

/-! Reduced two-row completions and their cubic extensions. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K m r : Type*} [Field K] [Fintype m] [Fintype r]
  [DecidableEq m] [DecidableEq r]

structure CubicTwoCompletion (alpha : r → ℕ) (b eps : ℕ)
    (W : Matrix (Fin 2) (Fin 2) K[X]) where
  G : Matrix m r K[X]
  S : Matrix m (Fin 2) K[X]
  R : Matrix r m K[X]
  V : Matrix (Fin 2) m K[X]
  gDegree : ∀ x j, (G x j).natDegree ≤ alpha j+2
  sDegree : DegreeBound S 0
  vDegree : ∀ j x, (V j x).natDegree ≤ b+eps*j.val
  leading : Function.Injective (Matrix.mulVec
    (fun x j => (V j x).coeff (b+eps*j.val)))
  rg : R*G=1
  rs : R*S=0
  vg : V*G=0
  wa : W*(V*S)=1
  completion : G*R+S*W*V=1
  aDegree : DegreeBound (V*S) 2

namespace CubicTwoCompletion

variable {alpha : r → ℕ} {b eps : ℕ} {W : Matrix (Fin 2) (Fin 2) K[X]}

def extend (C : CubicTwoCompletion (m := m) alpha b eps W) :
    CubicTwoCompletion (m := Fin 2 ⊕ m) (Sum.elim (fun _ : Fin 2 => 1) alpha)
      (b+3) eps W where
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
  vDegree := by
    intro j x
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      cubicRowExtensionKernel_degree C.V C.S (fun j => b+eps*j.val)
        C.vDegree C.aDegree j x
  leading := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      cubicRowExtensionKernel_leading C.V C.S (fun j => b+eps*j.val) C.leading
  rg := cubicRowExtension_right C.G C.S C.R C.V W C.rg C.rs C.vg C.wa
  rs := by
    simp [cubicRowExtensionRight, Matrix.fromBlocks_mul_fromRows]
  vg := cubicRowExtension_kernel C.G C.S C.V C.vg
  wa := by
    simpa [cubicRowExtensionKernel, Matrix.fromCols_mul_fromRows] using C.wa
  completion := cubicRowExtension_completion C.G C.S C.R C.V W C.completion C.wa
  aDegree := by
    simpa [cubicRowExtensionKernel, Matrix.fromCols_mul_fromRows] using C.aDegree

theorem injective (C : CubicTwoCompletion (m := m) alpha b eps W) :
    Function.Injective C.G.mulVec := by
  intro u v h
  have hh := congrArg (fun z => C.R *ᵥ z) h
  simpa only [Matrix.mulVec_mulVec, C.rg, Matrix.one_mulVec] using hh

theorem coordinates {h : Type*} (C : CubicTwoCompletion (m := m) alpha b eps W)
    (Z : Matrix h m K[X]) (hZ : Z*C.G=0) : Z=(Z*C.S*W)*C.V := by
  calc
    Z = Z*(C.G*C.R+C.S*W*C.V) := by rw [C.completion, Matrix.mul_one]
    _ = (Z*C.S*W)*C.V := by simp [Matrix.mul_add, ← Matrix.mul_assoc, hZ]

theorem coordinate_degree {h : Type*} (C : CubicTwoCompletion (m := m) alpha b eps W)
    (Q : Matrix h (Fin 2) K[X]) (d : ℕ)
    (hQ : DegreeBound (Q*C.V) d) :
    ∀ i j, Q i j=0 ∨ (b+eps*j.val≤d ∧ (Q i j).natDegree≤d-(b+eps*j.val)) := by
  intro i
  apply (polynomial_combination_degree_iff C.V.transpose (fun j => b+eps*j.val)
    (Q i) d (fun x j => C.vDegree j x) C.leading).mp
  intro x
  have hh := hQ i x
  simpa [Matrix.mulVec, Matrix.mul_apply, dotProduct, Matrix.transpose_apply, mul_comm] using hh

theorem kernel_hilbert_zero (C : CubicTwoCompletion (m := m) alpha b eps W)
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
    let Q : Matrix Unit (Fin 2) K[X] := Z*C.S*W
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

theorem new_coordinate_degree (C : CubicTwoCompletion (m := m) alpha b eps W)
    (E : Matrix (Fin 2 ⊕ r) (Fin 2 ⊕ m) K[X]) (c : K[X]) (d : ℕ)
    (hrel : E*C.extend.G=(-c) • 1)
    (hE : ∀ i x, (E (Sum.inl i) (Sum.inr x)).natDegree≤d) :
    ∃ Q : Matrix (Fin 2) (Fin 2) K[X],
      Q=((X^3 : K[X]) • E.submatrix Sum.inl Sum.inl+c • 1)*W ∧
      ∀ i j, Q i j=0 ∨ (b+eps*j.val≤d ∧ (Q i j).natDegree≤d-(b+eps*j.val)) := by
  obtain ⟨Q,hQV,hQ⟩ := cubicRowExtension_new_coordinates C.G C.S C.R C.V W
    C.completion E c hrel
  refine ⟨Q,hQ,C.coordinate_degree Q d ?_⟩
  rw [← hQV]
  exact hE

def ScalarZero (C : CubicTwoCompletion (m := m) alpha b eps W) (d : ℕ) : Prop :=
  ∀ (E : Matrix r m K[X]) (c : K[X]),
    (∀ i x, (E i x).natDegree≤d-(alpha i+1)) → c.natDegree≤d+1 →
    E*C.G=(-c) • 1 → c=0

def ScalarSelector {t : Type*} (C : CubicTwoCompletion (m := m) alpha b eps W)
    (d : ℕ) (f : t → ℕ) : Prop :=
  ∀ (E : Matrix r m K[X]) (c : K[X]),
    (∀ i x, (E i x).natDegree≤d-(alpha i+1)) → c.natDegree≤d+1 →
    E*C.G=(-c) • 1 → (∀ j, c.coeff (f j)=0) → c=0

theorem scalar_descent (C : CubicTwoCompletion (m := m) alpha b eps W)
    (d : ℕ) (hd : ∀ i, alpha i+1≤d)
    (E : Matrix (Fin 2 ⊕ r) (Fin 2 ⊕ m) K[X]) (c c' : K[X])
    (hE : ∀ i x, (E i x).natDegree≤d+3-(Sum.elim (fun _ : Fin 2 => 1) alpha i+1))
    (hc : c.natDegree≤d+4) (hfactor : c=X^3*c')
    (hrel : E*C.extend.G=(-c) • 1) :
    ∃ F : Matrix r m K[X],
      (∀ i x, (F i x).natDegree≤d-(alpha i+1)) ∧ c'.natDegree≤d+1 ∧
      F*C.G=(-c') • 1 := by
  obtain ⟨F,hF,hFG⟩ := cubicRowExtension_scalar_descent C.G C.S C.R C.V W
    C.completion E c hrel c' hfactor
  refine ⟨F,?_,?_,hFG⟩
  · intro i x
    apply polynomial_cubic_factor_degree (E (Sum.inr i) (Sum.inr x)) (F i x)
      (d-(alpha i+1))
    · exact congrArg (fun A : Matrix r m K[X] => A i x) hF
    · have hh := hE (Sum.inr i) (Sum.inr x)
      have hi := hd i
      simpa only [Sum.elim_inr] using (show (E (Sum.inr i) (Sum.inr x)).natDegree ≤
        d-(alpha i+1)+3 from by simp only [Sum.elim_inr] at hh; omega)
  · apply polynomial_cubic_factor_degree c c' (d+1) hfactor
    simpa [Nat.add_assoc] using hc

end CubicTwoCompletion
end FD56
