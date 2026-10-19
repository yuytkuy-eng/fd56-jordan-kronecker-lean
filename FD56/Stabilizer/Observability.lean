/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.ChangeBasis
import FD56.LinearAlgebra.RowNormalization

/-! Observability kernels and their reduction in full-row-rank coordinates. -/

noncomputable section
namespace FD56
open Matrix
variable {K n m r : Type*} [Field K] [Fintype n] [Fintype m] [Fintype r]
  [DecidableEq n] [DecidableEq m] [DecidableEq r]

def unobservableSpace (M : Matrix n n K) (P : Matrix m n K) : ℕ → Submodule K (n → K)
  | 0 => ⊤
  | q + 1 => LinearMap.ker P.mulVecLin ⊓
      (unobservableSpace M P q).comap M.mulVecLin

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
theorem mem_unobservableSpace_succ (M : Matrix n n K) (P : Matrix m n K)
    (q : ℕ) (v : n → K) :
    v ∈ unobservableSpace M P (q + 1) ↔ P *ᵥ v = 0 ∧ M *ᵥ v ∈ unobservableSpace M P q := Iff.rfl

omit [Fintype m] [DecidableEq m] in
theorem mem_unobservableSpace_iff (M : Matrix n n K) (P : Matrix m n K)
    (q : ℕ) (v : n → K) :
    v ∈ unobservableSpace M P q ↔ ∀ i < q, P *ᵥ (M ^ i *ᵥ v) = 0 := by
  induction q generalizing v with
  | zero => simp [unobservableSpace]
  | succ q ih =>
    rw [mem_unobservableSpace_succ, ih]
    constructor
    · rintro ⟨hP, h⟩ i hi
      cases i with
      | zero => simpa using hP
      | succ i => simpa only [pow_succ, Matrix.mulVec_mulVec] using h i (by omega)
    · intro h
      refine ⟨by simpa using h 0 (by omega), ?_⟩
      intro i hi
      simpa only [pow_succ, Matrix.mulVec_mulVec] using h (i + 1) (by omega)

def observabilityMap (M : Matrix n n K) (P : Matrix m n K) (q : ℕ) :
    (n → K) →ₗ[K] (Fin q → m → K) where
  toFun v i := P *ᵥ (M ^ i.val *ᵥ v)
  map_add' v w := by ext i j; simp [Matrix.mulVec_add]
  map_smul' c v := by ext i j; simp [Matrix.mulVec_smul]

omit [Fintype m] [DecidableEq m] in
theorem observabilityMap_ker (M : Matrix n n K) (P : Matrix m n K) (q : ℕ) :
    LinearMap.ker (observabilityMap M P q) = unobservableSpace M P q := by
  ext v
  rw [mem_unobservableSpace_iff]
  change (fun i : Fin q => P *ᵥ (M ^ i.val *ᵥ v)) = 0 ↔ _
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    funext i
    exact h i.val i.isLt

omit [DecidableEq r] in
theorem unobservable_block_coordinates (A : Matrix m m K) (B : Matrix m r K)
    (C : Matrix r m K) (D : Matrix r r K) (q : ℕ) (x : m → K) (y : r → K) :
    Sum.elim x y ∈ unobservableSpace (Matrix.fromBlocks A B C D)
      (Matrix.fromCols (1 : Matrix m m K) 0) (q + 1) ↔
      x = 0 ∧ y ∈ unobservableSpace D B q := by
  induction q generalizing x y with
  | zero => simp [unobservableSpace, Matrix.toLin'_apply]
  | succ q ih =>
    rw [mem_unobservableSpace_succ]
    simp only [Matrix.fromCols_mulVec_sumElim, Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]
    constructor
    · rintro ⟨rfl, h⟩
      have hm : Matrix.fromBlocks A B C D *ᵥ Sum.elim 0 y = Sum.elim (B *ᵥ y) (D *ᵥ y) := by
        rw [Matrix.fromBlocks_mulVec]
        change Sum.elim (A *ᵥ (0 : m → K) + B *ᵥ y) (C *ᵥ (0 : m → K) + D *ᵥ y) = _
        simp
      rw [hm, ih] at h
      exact ⟨rfl, h⟩
    · rintro ⟨rfl, h⟩
      refine ⟨rfl, ?_⟩
      have hm : Matrix.fromBlocks A B C D *ᵥ Sum.elim 0 y = Sum.elim (B *ᵥ y) (D *ᵥ y) := by
        rw [Matrix.fromBlocks_mulVec]
        change Sum.elim (A *ᵥ (0 : m → K) + B *ᵥ y) (C *ᵥ (0 : m → K) + D *ᵥ y) = _
        simp
      rw [hm, ih]
      exact h

def unobservableBlockEquiv (A : Matrix m m K) (B : Matrix m r K)
    (C : Matrix r m K) (D : Matrix r r K) (q : ℕ) :
    unobservableSpace D B q ≃ₗ[K]
      unobservableSpace (Matrix.fromBlocks A B C D) (Matrix.fromCols (1 : Matrix m m K) 0) (q + 1) where
  toFun y := ⟨Sum.elim 0 y.val, (unobservable_block_coordinates A B C D q 0 y.val).mpr ⟨rfl, y.property⟩⟩
  invFun v := ⟨v.val ∘ Sum.inr, by
    have heq : Sum.elim (v.val ∘ Sum.inl) (v.val ∘ Sum.inr) = v.val := by
      funext i; cases i <;> rfl
    exact ((unobservable_block_coordinates A B C D q _ _).mp (heq.symm ▸ v.property)).2⟩
  left_inv y := by apply Subtype.ext; rfl
  right_inv v := by
    have heq : Sum.elim (v.val ∘ Sum.inl) (v.val ∘ Sum.inr) = v.val := by
      funext i; cases i <;> rfl
    have hz := ((unobservable_block_coordinates A B C D q _ _).mp (heq.symm ▸ v.property)).1
    apply Subtype.ext
    simpa only [hz] using heq
  map_add' v w := by apply Subtype.ext; funext i; cases i <;> simp
  map_smul' c v := by apply Subtype.ext; funext i; cases i <;> simp

omit [DecidableEq r] in
theorem unobservable_block_finrank (A : Matrix m m K) (B : Matrix m r K)
    (C : Matrix r m K) (D : Matrix r r K) (q : ℕ) :
    Module.finrank K (unobservableSpace (Matrix.fromBlocks A B C D)
      (Matrix.fromCols (1 : Matrix m m K) 0) (q + 1)) =
      Module.finrank K (unobservableSpace D B q) :=
  (unobservableBlockEquiv A B C D q).finrank_eq.symm

omit [DecidableEq m] in
theorem observabilityMap_surjective_of_finrank (M : Matrix n n K) (P : Matrix m n K)
    (q : ℕ) (hdim : Module.finrank K (unobservableSpace M P q) + q * Fintype.card m = Fintype.card n) :
    Function.Surjective (observabilityMap M P q) := by
  have h := (observabilityMap M P q).finrank_range_add_finrank_ker
  rw [observabilityMap_ker] at h
  simp only [Module.finrank_fintype_fun_eq_card] at h
  have hc : Module.finrank K (Fin q → m → K) = q * Fintype.card m := by
    simp [Module.finrank_pi_fintype]
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_of_le_of_finrank_eq le_top
  rw [finrank_top, hc]
  omega

omit [Fintype m] [DecidableEq m] in
theorem surjective_of_observabilityMap (M : Matrix n n K) (P : Matrix m n K)
    (q : ℕ) (h : Function.Surjective (observabilityMap M P (q + 1))) :
    Function.Surjective P.mulVec := by
  intro y
  obtain ⟨v, hv⟩ := h (fun _ => y)
  refine ⟨v, ?_⟩
  have h₀ := congrFun hv ⟨0, by omega⟩
  simpa [observabilityMap] using h₀

omit [Fintype m] [DecidableEq m] in
theorem unobservable_change_basis_mem {p : Type*} [Fintype p] [DecidableEq p]
    (M : Matrix n n K) (P : Matrix m n K) (S : Matrix n p K) (I : Matrix p n K)
    (hSI : S * I = 1) (q : ℕ) (v : p → K) :
    v ∈ unobservableSpace (I * M * S) (P * S) q ↔ S *ᵥ v ∈ unobservableSpace M P q := by
  induction q generalizing v with
  | zero => simp [unobservableSpace]
  | succ q ih =>
    rw [mem_unobservableSpace_succ, mem_unobservableSpace_succ, ih]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc,
      ← Matrix.mul_assoc S I, hSI, Matrix.one_mul]

def unobservableChangeBasisEquiv {p : Type*} [Fintype p] [DecidableEq p]
    (M : Matrix n n K) (P : Matrix m n K) (S : Matrix n p K) (I : Matrix p n K)
    (hSI : S * I = 1) (hIS : I * S = 1) (q : ℕ) :
    unobservableSpace (I * M * S) (P * S) q ≃ₗ[K] unobservableSpace M P q where
  toFun z := ⟨S *ᵥ z.val, (unobservable_change_basis_mem M P S I hSI q z.val).mp z.property⟩
  invFun z := ⟨I *ᵥ z.val, by
    apply (unobservable_change_basis_mem M P S I hSI q _).mpr
    simpa only [Matrix.mulVec_mulVec, hSI, Matrix.one_mulVec] using z.property⟩
  left_inv z := by
    apply Subtype.ext
    change I *ᵥ (S *ᵥ z.val) = z.val
    rw [Matrix.mulVec_mulVec, hIS, Matrix.one_mulVec]
  right_inv z := by
    apply Subtype.ext
    change S *ᵥ (I *ᵥ z.val) = z.val
    rw [Matrix.mulVec_mulVec, hSI, Matrix.one_mulVec]
  map_add' z w := by apply Subtype.ext; exact Matrix.mulVec_add S z.val w.val
  map_smul' c z := by apply Subtype.ext; exact Matrix.mulVec_smul S c z.val

omit [Fintype m] [DecidableEq m] in
theorem unobservable_change_basis_finrank {p : Type*} [Fintype p] [DecidableEq p]
    (M : Matrix n n K) (P : Matrix m n K) (S : Matrix n p K) (I : Matrix p n K)
    (hSI : S * I = 1) (hIS : I * S = 1) (q : ℕ) :
    Module.finrank K (unobservableSpace (I * M * S) (P * S) q) =
      Module.finrank K (unobservableSpace M P q) :=
  (unobservableChangeBasisEquiv M P S I hSI hIS q).finrank_eq

end FD56
