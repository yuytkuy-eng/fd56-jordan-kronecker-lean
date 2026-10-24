/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.HankelFrame

/-! Hankel coefficient functionals without a truncation cutoff. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {R : Type*} [CommRing R] {b c : ℕ}

def hankelFunctional (a : ℕ → R) (r : ℕ) : R[X] →ₗ[R] R :=
  Polynomial.lsum (fun s => LinearMap.mulLeft R (a (r+s)))

theorem hankelFunctional_monomial (a : ℕ → R) (r k : ℕ) (x : R) :
    hankelFunctional a r (monomial k x)=a (r+k)*x := by
  simp [hankelFunctional,Polynomial.lsum_apply,Polynomial.sum_monomial_index]

theorem hankelFunctional_mul_monomial (a : ℕ → R) (r k : ℕ) (x : R) (p : R[X]) :
    hankelFunctional a r (p*monomial k x)=hankelFunctional a (r+k) p*x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [add_mul,map_add,hp,hq]
  | monomial s y =>
    rw [monomial_mul_monomial,hankelFunctional_monomial,hankelFunctional_monomial]
    rw [show r+(s+k)=r+k+s by omega,mul_assoc]

theorem hankelFunctional_truncated (a : ℕ → R) (r N : ℕ) (p : R[X])
    (hp : p.natDegree<N) :
    hankelFunctional a r p=∑ s : Fin N, a (r+s.val)*p.coeff s.val := by
  change p.sum (fun s x => a (r+s)*x)=_
  rw [Polynomial.sum_over_range' p (fun s => mul_zero _) N hp]
  exact (Fin.sum_univ_eq_sum_range _ N).symm

theorem hankelFunctional_mul_bounded (a : ℕ → R) (r d : ℕ) (p q : R[X])
    (hq : q.natDegree≤d) :
    hankelFunctional a r (p*q)=∑ k : Fin (d+1), hankelFunctional a (r+k.val) p*q.coeff k.val := by
  nth_rw 1 [q.as_sum_range' (d+1) (by omega)]
  rw [Finset.mul_sum,map_sum]
  simp_rw [hankelFunctional_mul_monomial]
  exact (Fin.sum_univ_eq_sum_range _ (d+1)).symm

def fullHankelAction (a : Fin b → Fin c → ℕ → R)
    (p : Fin c → R[X]) (j : Fin b) (r : ℕ) : R :=
  ∑ i, hankelFunctional (a j i) r (p i)

theorem fullHankelAction_truncated (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R) (p : Fin c → R[X])
    (hp : ∀ i, (p i).natDegree<g i) (j : Fin b) (r : ℕ) :
    fullHankelAction a p j r=polynomialHankelAction g a p j r := by
  simp only [fullHankelAction,polynomialHankelAction]
  apply Finset.sum_congr rfl
  intro i _
  exact hankelFunctional_truncated (a j i) r (g i) (p i) (hp i)

theorem fullHankelAction_mulVec {w : Type*} [Fintype w]
    (a : Fin b → Fin c → ℕ → R) (P : Matrix (Fin c) w R[X])
    (x : w → R[X]) (d : ℕ) (hx : ∀ w, (x w).natDegree≤d) (j : Fin b) (r : ℕ) :
    fullHankelAction a (P *ᵥ x) j r =
      ∑ w, ∑ k : Fin (d+1), fullHankelAction a (fun i => P i w) j (r+k.val)*(x w).coeff k.val := by
  simp only [fullHankelAction,Matrix.mulVec,dotProduct,map_sum]
  simp_rw [hankelFunctional_mul_bounded _ _ d _ _ (hx _)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

theorem hankelFrame_bounded_image_relations (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (hHB : blockHankel h g a*B=1)
    (d : ℕ) (x : Fin c ⊕ Fin b → R[X]) (hx : ∀ w, (x w).natDegree≤d)
    (j : Fin b) (r : ℕ) (hr : r+d+1<h j) :
    fullHankelAction a (hankelFrame h g a B *ᵥ x) j r=0 := by
  rw [fullHankelAction_mulVec a _ x d hx]
  apply Finset.sum_eq_zero
  intro w _
  apply Finset.sum_eq_zero
  intro k _
  rw [fullHankelAction_truncated (fun i => g i+1) a _
    (fun i => Nat.lt_succ_of_le (hankelFrame_degree h g a B i w)),
    hankelFrame_action_zero h g a B hHB j (r+k.val) (by have := k.isLt; omega) w,zero_mul]

theorem hankelFrame_bounded_image_degree (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (d : ℕ) (x : Fin c ⊕ Fin b → R[X]) (hx : ∀ w, (x w).natDegree≤d) (i : Fin c) :
    ((hankelFrame h g a B *ᵥ x) i).natDegree≤g i+d := by
  simp only [Matrix.mulVec,dotProduct]
  apply natDegree_sum_le_of_forall_le
  intro w _
  exact natDegree_mul_le.trans (Nat.add_le_add (hankelFrame_degree h g a B i w) (hx w))

end FD56
