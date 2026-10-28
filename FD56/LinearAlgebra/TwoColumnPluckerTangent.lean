/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

/-! The full linearized Plucker system for a split two-column frame.
Equations are imposed on every ordered quadruple, including repetitions.
Thus the kernel includes alternation without a separate skew-matrix premise.
There is no division by 2 and the coefficient ring can have any characteristic. -/

noncomputable section
namespace FD56
open Matrix
open scoped BigOperators
variable {R n : Type*} [CommRing R]

def twoColumnWedge (u v : n → R) : Matrix n n R := fun i j => u i*v j-u j*v i

def twoColumnPluckerEquation (u v : n → R) (H : Matrix n n R) (i j k l : n) : R :=
  twoColumnWedge u v i j*H k l-twoColumnWedge u v i k*H j l+
    twoColumnWedge u v i l*H j k+twoColumnWedge u v j k*H i l-
    twoColumnWedge u v j l*H i k+twoColumnWedge u v k l*H i j

def twoColumnWedgeDifferential (u v : n → R) :
    ((n → R) × (n → R)) →ₗ[R] Matrix n n R where
  toFun z := twoColumnWedge z.1 v+twoColumnWedge u z.2
  map_add' x y := by funext i j; dsimp [twoColumnWedge]; ring
  map_smul' c z := by funext i j; dsimp [twoColumnWedge]; ring

def twoColumnPluckerLinearization (u v : n → R) :
    Matrix n n R →ₗ[R] (n → n → n → n → R) where
  toFun H := twoColumnPluckerEquation u v H
  map_add' H J := by funext i j k l; dsimp [twoColumnPluckerEquation]; ring
  map_smul' c H := by funext i j k l; dsimp [twoColumnPluckerEquation]; ring

theorem twoColumnWedgeDifferential_equation (u v x y : n → R) (i j k l : n) :
    twoColumnPluckerEquation u v (twoColumnWedgeDifferential u v (x,y)) i j k l=0 := by
  dsimp [twoColumnPluckerEquation,twoColumnWedgeDifferential,twoColumnWedge]
  ring

private theorem double_sum_product [Fintype n] (f g : n → R) :
    (∑ i, ∑ j, f i*g j)=(∑ i, f i)*(∑ j, g j) := by
  simp only [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem two_column_plucker_contraction [Fintype n]
    (u v p q : n → R) (H : Matrix n n R)
    (hpu : p ⬝ᵥ u=1) (hpv : p ⬝ᵥ v=0) (hqu : q ⬝ᵥ u=0) (hqv : q ⬝ᵥ v=1)
    (hH : ∀ i j k l, twoColumnPluckerEquation u v H i j k l=0) :
    H=twoColumnWedge u (fun j => ∑ i, p i*H i j)+
      twoColumnWedge v (fun j => ∑ i, q i*H i j)-
      (∑ i, ∑ j, p i*q j*H i j) • twoColumnWedge u v := by
  funext k l
  have hzero : (∑ i, ∑ j, p i*q j*twoColumnPluckerEquation u v H i j k l)=0 := by
    simp only [hH,mul_zero,Finset.sum_const_zero]
  have hexpand (i j : n) : p i*q j*twoColumnPluckerEquation u v H i j k l=
      ((p i*u i)*H k l)*(q j*v j)-((p i*v i)*H k l)*(q j*u j)-
      (p i*u i)*((q j*H j l)*v k)+(p i*v i)*((q j*H j l)*u k)+
      (p i*u i)*((q j*H j k)*v l)-(p i*v i)*((q j*H j k)*u l)+
      ((p i*H i l)*v k)*(q j*u j)-((p i*H i l)*u k)*(q j*v j)-
      ((p i*H i k)*v l)*(q j*u j)+((p i*H i k)*u l)*(q j*v j)+
      twoColumnWedge u v k l*(p i*q j*H i j) := by
    dsimp [twoColumnPluckerEquation,twoColumnWedge]
    ring
  simp_rw [hexpand] at hzero
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,double_sum_product,
    ← Finset.sum_mul,← Finset.mul_sum] at hzero
  simp only [dotProduct] at hpu hpv hqu hqv
  rw [hpu,hpv,hqu,hqv] at hzero
  simp only [one_mul,zero_mul,mul_one,mul_zero,zero_add,add_zero,sub_zero] at hzero
  dsimp [twoColumnWedge] at hzero ⊢
  linear_combination hzero

theorem two_column_plucker_kernel_eq_differential_range [Fintype n]
    (u v p q : n → R)
    (hpu : p ⬝ᵥ u=1) (hpv : p ⬝ᵥ v=0) (hqu : q ⬝ᵥ u=0) (hqv : q ⬝ᵥ v=1) :
    LinearMap.ker (twoColumnPluckerLinearization u v)=
      LinearMap.range (twoColumnWedgeDifferential u v) := by
  ext H
  constructor
  · intro hH
    have hzero : ∀ i j k l, twoColumnPluckerEquation u v H i j k l=0 := by
      intro i j k l
      exact congrFun (congrFun (congrFun (congrFun hH i) j) k) l
    let w : n → R := fun j => ∑ i, p i*H i j
    let z : n → R := fun j => ∑ i, q i*H i j
    let t : R := ∑ i, ∑ j, p i*q j*H i j
    refine ⟨((fun i => -z i-t*u i),w),?_⟩
    have he := two_column_plucker_contraction u v p q H hpu hpv hqu hqv hzero
    rw [he]
    funext i j
    dsimp [twoColumnWedgeDifferential,twoColumnWedge,w,z,t]
    ring
  · rintro ⟨⟨x,y⟩,rfl⟩
    apply LinearMap.mem_ker.mpr
    funext i j k l
    exact twoColumnWedgeDifferential_equation u v x y i j k l

theorem two_column_plucker_kernel_eq_range_of_left_inverse [Fintype n]
    (G : Matrix n (Fin 2) R) (L : Matrix (Fin 2) n R) (hLG : L*G=1) :
    LinearMap.ker (twoColumnPluckerLinearization (fun i => G i 0) (fun i => G i 1))=
      LinearMap.range (twoColumnWedgeDifferential (fun i => G i 0) (fun i => G i 1)) := by
  apply two_column_plucker_kernel_eq_differential_range _ _ (L 0) (L 1)
  · simpa [Matrix.mul_apply,dotProduct] using congrFun (congrFun hLG 0) 0
  · simpa [Matrix.mul_apply,dotProduct] using congrFun (congrFun hLG 0) 1
  · simpa [Matrix.mul_apply,dotProduct] using congrFun (congrFun hLG 1) 0
  · simpa [Matrix.mul_apply,dotProduct] using congrFun (congrFun hLG 1) 1

end FD56
