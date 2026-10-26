/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.CofactorMinimalDegree

/-! The corank-one row-sum degree for arbitrary finite coordinate types. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K a b : Type*} [Field K] [Fintype a] [Fintype b]
  [DecidableEq a] [DecidableEq b]

theorem corank_one_polynomial_minimal_degree (A : Matrix a b K[X])
    (hcard : Fintype.card b = Fintype.card a+1) (e : a → ℕ)
    (hA : ∀ i j, (A i j).natDegree ≤ e i)
    (hL : Function.Injective (Matrix.mulVec
      ((Matrix.of fun i k => (A i k).coeff (e i)).transpose)))
    (hp : ∀ d : K[X], (∀ r : a → b, d ∣ (A.submatrix id r).det) → IsUnit d) :
    HasMinimalKernelDegrees A [∑ i, e i] := by
  classical
  let α : Fin (Fintype.card a) ≃ a := (Fintype.equivFin a).symm
  let β : Fin (Fintype.card a+1) ≃ b := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let B := A.submatrix α β
  let e' : Fin (Fintype.card a) → ℕ := e ∘ α
  have hB : ∀ i j, (B i j).natDegree ≤ e' i := fun i j => hA (α i) (β j)
  let L : Matrix b a K := fun j i => (A i j).coeff (e i)
  have hL' : Function.Injective (L.submatrix β α).mulVec := by
    intro u v huv
    have hu := Matrix.submatrix_mulVec_equiv L u β α
    have hv := Matrix.submatrix_mulVec_equiv L v β α
    rw [hu,hv] at huv
    have hh : L *ᵥ (u ∘ α.symm) = L *ᵥ (v ∘ α.symm) := by
      funext j
      simpa using congrFun huv (β.symm j)
    have hh' := hL hh
    funext i
    simpa using congrFun hh' (α i)
  have hpB : ∀ d : K[X],
      (∀ r : Fin (Fintype.card a) → Fin (Fintype.card a+1),
        d ∣ (B.submatrix id r).det) → IsUnit d := by
    intro d hd
    apply hp d
    intro r
    have hh := hd (fun i => β.symm (r (α i)))
    have he : B.submatrix id (fun i => β.symm (r (α i))) =
        (A.submatrix id r).submatrix α α := by
      funext i j
      simp [B]
    simpa only [he,Matrix.det_submatrix_equiv_self] using hh
  let c₀ := rectangularCofactors B.transpose
  have hgenB (y : Fin (Fintype.card a+1) → K[X]) :
      B *ᵥ y = 0 ↔ ∃! h : K[X], y = h • c₀ := by
    simpa only [Matrix.transpose_transpose] using
      rectangularCofactors_kernel_iff_unique_of_maximal_minors_units B.transpose
        (fun d hd => hpB d (fun r => by
          have hh := hd r
          have he : B.transpose.submatrix r id = (B.submatrix id r).transpose := rfl
          simpa only [he,Matrix.det_transpose] using hh)) y
  let c : b → K[X] := c₀ ∘ β.symm
  have hker (y : b → K[X]) : B *ᵥ (y ∘ β) = 0 ↔ A *ᵥ y = 0 := by
    have he := Matrix.submatrix_mulVec_equiv A (y ∘ β) α β
    simp only [Function.comp_assoc,Equiv.self_comp_symm,Function.comp_id] at he
    change B *ᵥ (y ∘ β) = (A *ᵥ y) ∘ α at he
    rw [he]
    constructor
    · intro h
      funext i
      simpa using congrFun h (α.symm i)
    · intro h; rw [h]; rfl
  have hcc : c ∘ β = c₀ := by funext i; simp [c]
  have hcz : A *ᵥ c = 0 := by
    apply (hker c).mp
    rw [hcc]
    simpa only [Matrix.transpose_transpose] using rectangularCofactors_relation B.transpose
  have hgen (y : b → K[X]) : A *ᵥ y = 0 ↔ ∃! h : K[X], y = h • c := by
    rw [← hker y,hgenB]
    constructor
    · rintro ⟨h,hh,hu⟩
      refine ⟨h,?_,?_⟩
      · funext j
        simpa [c,Function.comp_def] using congrFun hh (β.symm j)
      · intro k hk
        apply hu k
        funext i
        simpa [c] using congrFun hk (β i)
    · rintro ⟨h,hh,hu⟩
      refine ⟨h,?_,?_⟩
      · funext i
        simpa [c] using congrFun hh (β i)
      · intro k hk
        apply hu k
        funext j
        simpa [c,Function.comp_def] using congrFun hk (β.symm j)
  have hsum : (∑ i, e' i) = ∑ i, e i := α.sum_comp e
  apply hasMinimalKernelDegrees_singleton_of_generator A c hcz hgen _
  · intro j
    have hh := right_rectangularCofactor_degree B e' hB (β.symm j)
    simpa only [hsum] using hh
  · obtain ⟨j,hj⟩ := right_rectangularCofactors_nonzero_top B e' hB hL'
    refine ⟨β j,?_⟩
    simpa only [c,Function.comp_apply,Equiv.symm_apply_apply,← hsum] using hj

end FD56
