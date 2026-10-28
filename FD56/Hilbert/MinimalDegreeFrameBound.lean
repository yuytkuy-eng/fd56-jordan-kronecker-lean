/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MinimalProfile

/-! A bounded polynomial frame of full kernel rank bounds every minimal index.
Only independence at one evaluation point is needed. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K a b : Type*} [Field K] [Fintype b] [DecidableEq b]

theorem minimal_degrees_le_of_full_frame_at_point
    (A : Matrix a b K[X]) (xs : List ℕ) (hmin : HasMinimalKernelDegrees A xs)
    (r d : ℕ) (Z : Matrix b (Fin r) K[X]) (hlen : xs.length=r)
    (hAZ : A*Z=0) (hZ : DegreeBound Z d) (x : K)
    (hinj : Function.Injective (Z.map (Polynomial.evalRingHom x)).mulVec) :
    ∀ e ∈ xs, e≤d := by
  classical
  obtain ⟨s,B,e,hB,hlead,hperm⟩ := hmin
  have hrs : s=r := by simpa only [List.length_ofFn,hlen] using hperm.length_eq
  subst s
  let y (j : Fin r) : LinearMap.ker (Matrix.toLin' A) :=
    ⟨fun i => Z i j,by
      change A *ᵥ (fun i => Z i j)=0
      funext i
      exact congrFun (congrFun hAZ i) j⟩
  let W : Matrix (Fin r) (Fin r) K[X] := fun i j => B.equivFun (y j) i
  have hBW : polynomialKernelBasisMatrix A B*W=Z := by
    funext i j
    change (polynomialKernelBasisMatrix A B *ᵥ (B.equivFun (y j))) i=Z i j
    rw [polynomialKernelBasisMatrix_mulVec]
    exact congrArg (fun z : LinearMap.ker (Matrix.toLin' A) => z.val i)
      (B.equivFun.symm_apply_apply (y j))
  let ev := Polynomial.evalRingHom x
  have hWinj : Function.Injective (W.map ev).mulVec := by
    intro u v huv
    apply hinj
    rw [← hBW,Matrix.map_mul]
    simpa only [Matrix.mulVec_mulVec] using
      congrArg ((polynomialKernelBasisMatrix A B).map ev).mulVec huv
  have hWsurj : Function.Surjective (Matrix.toLin' (W.map ev)) :=
    (LinearMap.injective_iff_surjective).mp hWinj
  have he (i : Fin r) : e i≤d := by
    by_contra hgt
    have hz (j : Fin r) : W i j=0 := by
      have hb := (polynomial_combination_degree_iff
        (polynomialKernelBasisMatrix A B) e (fun i => W i j) d hB hlead).mp (by
          intro k
          change ((polynomialKernelBasisMatrix A B*W) k j).natDegree≤d
          rw [hBW]
          exact hZ k j) i
      exact hb.resolve_right (fun h => hgt h.1)
    obtain ⟨v,hv⟩ := hWsurj (Pi.single i 1)
    have h : ((W.map ev) *ᵥ v) i=1 := by
      simpa only [Matrix.toLin'_apply,Pi.single_eq_same] using congrFun hv i
    simp [Matrix.mulVec,dotProduct,Matrix.map_apply,hz] at h
  intro k hk
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp (hperm.mem_iff.mpr hk)
  exact hi ▸ he i

private theorem bounded_degree_list_sum_le (xs : List ℕ) (d : ℕ)
    (h : ∀ e ∈ xs, e≤d) : xs.sum≤xs.length*d := by
  induction xs with
  | nil => simp
  | cons e xs ih =>
    have he := h e (by simp)
    have hx := ih (fun k hk => h k (by simp [hk]))
    simp only [List.sum_cons,List.length_cons,Nat.add_mul,one_mul]
    omega

private theorem bounded_degree_list_eq_replicate (xs : List ℕ) (d : ℕ)
    (h : ∀ e ∈ xs, e≤d) (hs : xs.sum=xs.length*d) :
    xs=List.replicate xs.length d := by
  induction xs with
  | nil => simp
  | cons e xs ih =>
    have he := h e (by simp)
    have hx : ∀ k ∈ xs, k≤d := fun k hk => h k (by simp [hk])
    have hxs := bounded_degree_list_sum_le xs d hx
    simp only [List.sum_cons,List.length_cons,Nat.add_mul,one_mul] at hs
    have hed : e=d := by omega
    have hsum : xs.sum=xs.length*d := by omega
    simpa only [List.length_cons,List.replicate_succ,hed] using
      congrArg (List.cons d) (ih hx hsum)

theorem minimal_degrees_uniform_of_full_frame_at_point
    (A : Matrix a b K[X]) (xs : List ℕ) (hmin : HasMinimalKernelDegrees A xs)
    (r d : ℕ) (Z : Matrix b (Fin r) K[X]) (hlen : xs.length=r)
    (hsum : xs.sum=r*d) (hAZ : A*Z=0) (hZ : DegreeBound Z d) (x : K)
    (hinj : Function.Injective (Z.map (Polynomial.evalRingHom x)).mulVec) :
    HasMinimalKernelDegrees A (List.replicate r d) := by
  have hb := minimal_degrees_le_of_full_frame_at_point A xs hmin r d Z hlen hAZ hZ x hinj
  have he := bounded_degree_list_eq_replicate xs d hb (by simpa only [hlen] using hsum)
  rw [hlen] at he
  exact he ▸ hmin

end FD56
