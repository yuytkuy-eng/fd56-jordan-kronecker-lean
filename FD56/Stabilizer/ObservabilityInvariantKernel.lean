/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.KrylovSpan
import FD56.Stabilizer.ObservabilityMatrix

/-! A dependent unobservable orbit produces a nonzero invariant subspace. -/

namespace FD56
open Matrix
variable {F n m : Type*} [Field F] [Fintype n] [DecidableEq n]

theorem observability_kernel_iterates (M : Matrix n n F) (P : Matrix m n F)
    (q : ℕ) (v : n → F) (h : observabilityMatrix M P q *ᵥ v = 0) :
    ∀ j : Fin q, P *ᵥ (M ^ j.val *ᵥ v) = 0 := by
  intro j
  funext i
  exact (observabilityMatrix_mulVec M P q v j i).symm.trans (congrFun h (j, i))

theorem exists_invariant_subspace_of_dependent_observability_kernel
    (M : Matrix n n F) (P : Matrix m n F) (q : ℕ) (hq : 0 < q)
    (v : n → F) (hv : v ≠ 0)
    (hker : ∀ j : Fin q, P *ᵥ (M ^ j.val *ᵥ v) = 0)
    (hdep : ¬ LinearIndependent F (fun j : Fin q => M ^ j.val *ᵥ v)) :
    ∃ W : Submodule F (n → F), W ≠ ⊥ ∧
      (∀ w ∈ W, M *ᵥ w ∈ W) ∧ (∀ w ∈ W, P *ᵥ w = 0) := by
  let f := Matrix.toLinAlgEquiv' M
  have hp (j : ℕ) : (f ^ j) v = M ^ j *ᵥ v := by
    rw [← map_pow]
    rfl
  have hd : ¬ LinearIndependent F (fun j : Fin q => (f ^ j.val) v) := by
    simpa only [hp] using hdep
  refine ⟨krylovSpan f v q, krylovSpan_ne_bot f v hq hv, ?_, ?_⟩
  · exact krylovSpan_invariant_of_dependent f v q hd
  · intro w hw
    apply krylovSpan_le_ker f v q (Matrix.toLin' P) ?_ hw
    intro j hj
    simpa only [hp, Matrix.toLin'_apply] using hker ⟨j, hj⟩

end FD56
