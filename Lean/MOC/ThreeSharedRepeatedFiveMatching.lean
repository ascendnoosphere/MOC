import MOC.ThreeSharedRepeatedFiveData
import MOC.FivePermutations
import MOC.Core
import Mathlib.Tactic.Ring

/-! Expand all order-five matching products with three common signed marks and a repeated first-spectrum value.
The ten coordinates include a constant coordinate. -/

open BigOperators

namespace MOC.ThreeSharedRepeatedFive

noncomputable section

/-- Repeat the fourth mark in the first spectrum. -/
def left (z : Fin 6 → ℂ) : Fin 5 → ℂ := ![z 0, z 1, z 2, z 3, z 3]

/-- The last two signed marks in the partner spectrum are free. -/
def right (z : Fin 6 → ℂ) : Fin 5 → ℂ := ![-z 0, -z 1, -z 2, -z 4, -z 5]

def basis (z : Fin 6 → ℂ) : Fin 10 → ℂ :=
  ![0, ((z 0) - (z 2))*((z 1) - (z 3))*((z 0)*(z 1)*(z 2) - (z 0)*(z 1)*(z 5) + (z 0)*(z 2)*(z 3) - 2*(z 0)*(z 2)*(z 5) - 2*(z 0)*(z 3)*(z 4) + (z 0)*(z 3)*(z 5) + 2*(z 0)*(z 4)*(z 5) - 2*(z 1)*(z 2)*(z 3) - (z 1)*(z 2)*(z 4) + 2*(z 1)*(z 2)*(z 5) + 2*(z 1)*(z 3)*(z 4) - (z 1)*(z 4)*(z 5) + (z 2)*(z 3)*(z 4) - (z 3)*(z 4)*(z 5)), ((z 0) - (z 2))*((z 3) - (z 5))*((z 0)*(z 1)^2 - 2*(z 0)*(z 1)*(z 4) - (z 0)*(z 2)*(z 3) + (z 0)*(z 2)*(z 4) + (z 0)*(z 3)*(z 4) - (z 1)^2*(z 2) - (z 1)^2*(z 3) + (z 1)^2*(z 4) + 2*(z 1)*(z 2)*(z 3) - (z 2)*(z 3)*(z 4)), ((z 0) - (z 2))^2*((z 1) - (z 3))^2*((z 4) - (z 5)), ((z 0) - (z 1))*((z 0)*(z 1)*(z 2)^2 - 2*(z 0)*(z 1)*(z 2)*(z 5) - (z 0)*(z 1)*(z 3)*(z 4) + (z 0)*(z 1)*(z 3)*(z 5) + (z 0)*(z 1)*(z 4)*(z 5) - (z 0)*(z 2)^2*(z 5) - (z 0)*(z 2)*(z 3)^2 - (z 0)*(z 2)*(z 3)*(z 4) + 3*(z 0)*(z 2)*(z 3)*(z 5) + (z 0)*(z 2)*(z 4)*(z 5) + 2*(z 0)*(z 3)^2*(z 4) - (z 0)*(z 3)^2*(z 5) - 2*(z 0)*(z 3)*(z 4)*(z 5) - 2*(z 1)*(z 2)^2*(z 3) - (z 1)*(z 2)^2*(z 4) + 2*(z 1)*(z 2)^2*(z 5) + (z 1)*(z 2)*(z 3)^2 + 3*(z 1)*(z 2)*(z 3)*(z 4) - (z 1)*(z 2)*(z 3)*(z 5) - (z 1)*(z 2)*(z 4)*(z 5) - (z 1)*(z 3)^2*(z 4) + (z 2)^2*(z 3)^2 + (z 2)^2*(z 3)*(z 4) - (z 2)^2*(z 3)*(z 5) - 2*(z 2)*(z 3)^2*(z 4) + (z 3)^2*(z 4)*(z 5)), ((z 0) - (z 1))*((z 0) - (z 2))*((z 1) - (z 3))*((z 2) - (z 4))*((z 3) - (z 5)), ((z 0) - (z 1))*((z 0) - (z 2))*((z 1) - (z 3))*((z 2) - (z 3))*((z 4) - (z 5)), ((z 0) - (z 1))*((z 0) - (z 2))*((z 1) - (z 2))*((z 3) - (z 4))*((z 3) - (z 5)), ((z 0) - (z 1))^2*((z 2) - (z 3))*((z 2) - (z 4))*((z 3) - (z 5)), ((z 0) - (z 1))^2*((z 2) - (z 3))^2*((z 4) - (z 5))]

set_option maxHeartbeats 24000000
set_option maxRecDepth 12000

private theorem product0 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (0 : Fin 120)) =
      ∑ k, (point (labelPoint 0) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (0 : Fin 120)) j = (![0, 1, 2, 3, 4] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 0) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product1 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (1 : Fin 120)) =
      ∑ k, (point (labelPoint 1) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (1 : Fin 120)) j = (![0, 1, 2, 4, 3] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 1) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product2 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (2 : Fin 120)) =
      ∑ k, (point (labelPoint 2) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (2 : Fin 120)) j = (![0, 1, 3, 2, 4] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 2) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product3 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (3 : Fin 120)) =
      ∑ k, (point (labelPoint 3) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (3 : Fin 120)) j = (![0, 1, 3, 4, 2] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 3) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product4 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (4 : Fin 120)) =
      ∑ k, (point (labelPoint 4) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (4 : Fin 120)) j = (![0, 1, 4, 2, 3] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 4) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product5 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (5 : Fin 120)) =
      ∑ k, (point (labelPoint 5) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (5 : Fin 120)) j = (![0, 1, 4, 3, 2] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 5) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product6 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (6 : Fin 120)) =
      ∑ k, (point (labelPoint 6) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (6 : Fin 120)) j = (![0, 2, 1, 3, 4] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 6) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product7 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (7 : Fin 120)) =
      ∑ k, (point (labelPoint 7) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (7 : Fin 120)) j = (![0, 2, 1, 4, 3] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 7) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product8 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (8 : Fin 120)) =
      ∑ k, (point (labelPoint 8) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (8 : Fin 120)) j = (![0, 2, 3, 1, 4] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 8) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product9 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (9 : Fin 120)) =
      ∑ k, (point (labelPoint 9) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (9 : Fin 120)) j = (![0, 2, 3, 4, 1] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 9) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product10 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (10 : Fin 120)) =
      ∑ k, (point (labelPoint 10) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (10 : Fin 120)) j = (![0, 2, 4, 1, 3] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 10) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product11 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (11 : Fin 120)) =
      ∑ k, (point (labelPoint 11) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (11 : Fin 120)) j = (![0, 2, 4, 3, 1] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 11) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product12 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (12 : Fin 120)) =
      ∑ k, (point (labelPoint 12) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (12 : Fin 120)) j = (![0, 3, 1, 2, 4] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 12) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product13 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (13 : Fin 120)) =
      ∑ k, (point (labelPoint 13) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (13 : Fin 120)) j = (![0, 3, 1, 4, 2] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 13) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product14 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (14 : Fin 120)) =
      ∑ k, (point (labelPoint 14) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (14 : Fin 120)) j = (![0, 3, 2, 1, 4] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 14) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product15 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (15 : Fin 120)) =
      ∑ k, (point (labelPoint 15) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (15 : Fin 120)) j = (![0, 3, 2, 4, 1] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 15) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product16 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (16 : Fin 120)) =
      ∑ k, (point (labelPoint 16) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (16 : Fin 120)) j = (![0, 3, 4, 1, 2] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 16) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product17 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (17 : Fin 120)) =
      ∑ k, (point (labelPoint 17) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (17 : Fin 120)) j = (![0, 3, 4, 2, 1] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 17) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product18 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (18 : Fin 120)) =
      ∑ k, (point (labelPoint 18) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (18 : Fin 120)) j = (![0, 4, 1, 2, 3] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 18) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product19 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (19 : Fin 120)) =
      ∑ k, (point (labelPoint 19) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (19 : Fin 120)) j = (![0, 4, 1, 3, 2] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 19) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product20 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (20 : Fin 120)) =
      ∑ k, (point (labelPoint 20) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (20 : Fin 120)) j = (![0, 4, 2, 1, 3] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 20) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product21 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (21 : Fin 120)) =
      ∑ k, (point (labelPoint 21) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (21 : Fin 120)) j = (![0, 4, 2, 3, 1] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 21) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product22 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (22 : Fin 120)) =
      ∑ k, (point (labelPoint 22) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (22 : Fin 120)) j = (![0, 4, 3, 1, 2] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 22) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product23 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (23 : Fin 120)) =
      ∑ k, (point (labelPoint 23) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (23 : Fin 120)) j = (![0, 4, 3, 2, 1] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 23) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product24 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (24 : Fin 120)) =
      ∑ k, (point (labelPoint 24) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (24 : Fin 120)) j = (![1, 0, 2, 3, 4] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 24) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product25 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (25 : Fin 120)) =
      ∑ k, (point (labelPoint 25) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (25 : Fin 120)) j = (![1, 0, 2, 4, 3] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 25) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product26 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (26 : Fin 120)) =
      ∑ k, (point (labelPoint 26) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (26 : Fin 120)) j = (![1, 0, 3, 2, 4] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 26) k = (![1, 0, 0, 0, 0, 0, 0, 0, 1, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product27 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (27 : Fin 120)) =
      ∑ k, (point (labelPoint 27) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (27 : Fin 120)) j = (![1, 0, 3, 4, 2] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 27) k = (![1, 0, 0, 0, 0, 0, 0, 0, 1, -1] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product28 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (28 : Fin 120)) =
      ∑ k, (point (labelPoint 28) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (28 : Fin 120)) j = (![1, 0, 4, 2, 3] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 28) k = (![1, 0, 0, 0, 0, 0, 0, 0, 1, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product29 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (29 : Fin 120)) =
      ∑ k, (point (labelPoint 29) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (29 : Fin 120)) j = (![1, 0, 4, 3, 2] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 29) k = (![1, 0, 0, 0, 0, 0, 0, 0, 1, -1] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product30 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (30 : Fin 120)) =
      ∑ k, (point (labelPoint 30) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (30 : Fin 120)) j = (![1, 2, 0, 3, 4] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 30) k = (![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product31 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (31 : Fin 120)) =
      ∑ k, (point (labelPoint 31) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (31 : Fin 120)) j = (![1, 2, 0, 4, 3] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 31) k = (![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product32 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (32 : Fin 120)) =
      ∑ k, (point (labelPoint 32) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (32 : Fin 120)) j = (![1, 2, 3, 0, 4] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 32) k = (![1, 0, 0, 0, 0, -1, 0, 1, 1, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product33 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (33 : Fin 120)) =
      ∑ k, (point (labelPoint 33) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (33 : Fin 120)) j = (![1, 2, 3, 4, 0] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 33) k = (![1, 0, 0, 0, 0, -1, 1, 1, 1, -1] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product34 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (34 : Fin 120)) =
      ∑ k, (point (labelPoint 34) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (34 : Fin 120)) j = (![1, 2, 4, 0, 3] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 34) k = (![1, 0, 0, 0, 0, -1, 0, 1, 1, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product35 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (35 : Fin 120)) =
      ∑ k, (point (labelPoint 35) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (35 : Fin 120)) j = (![1, 2, 4, 3, 0] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 35) k = (![1, 0, 0, 0, 0, -1, 1, 1, 1, -1] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product36 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (36 : Fin 120)) =
      ∑ k, (point (labelPoint 36) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (36 : Fin 120)) j = (![1, 3, 0, 2, 4] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 36) k = (![1, 0, 0, 0, 0, 1, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product37 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (37 : Fin 120)) =
      ∑ k, (point (labelPoint 37) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (37 : Fin 120)) j = (![1, 3, 0, 4, 2] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 37) k = (![1, 0, 0, 0, 0, 1, -1, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product38 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (38 : Fin 120)) =
      ∑ k, (point (labelPoint 38) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (38 : Fin 120)) j = (![1, 3, 2, 0, 4] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 38) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product39 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (39 : Fin 120)) =
      ∑ k, (point (labelPoint 39) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (39 : Fin 120)) j = (![1, 3, 2, 4, 0] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 39) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product40 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (40 : Fin 120)) =
      ∑ k, (point (labelPoint 40) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (40 : Fin 120)) j = (![1, 3, 4, 0, 2] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 40) k = (![1, 0, 0, 0, -1, 1, 0, 0, 1, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product41 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (41 : Fin 120)) =
      ∑ k, (point (labelPoint 41) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (41 : Fin 120)) j = (![1, 3, 4, 2, 0] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 41) k = (![1, 0, 0, 0, -1, 1, 1, 0, 1, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product42 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (42 : Fin 120)) =
      ∑ k, (point (labelPoint 42) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (42 : Fin 120)) j = (![1, 4, 0, 2, 3] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 42) k = (![1, 0, 0, 0, 0, 1, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product43 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (43 : Fin 120)) =
      ∑ k, (point (labelPoint 43) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (43 : Fin 120)) j = (![1, 4, 0, 3, 2] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 43) k = (![1, 0, 0, 0, 0, 1, -1, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product44 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (44 : Fin 120)) =
      ∑ k, (point (labelPoint 44) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (44 : Fin 120)) j = (![1, 4, 2, 0, 3] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 44) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product45 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (45 : Fin 120)) =
      ∑ k, (point (labelPoint 45) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (45 : Fin 120)) j = (![1, 4, 2, 3, 0] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 45) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product46 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (46 : Fin 120)) =
      ∑ k, (point (labelPoint 46) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (46 : Fin 120)) j = (![1, 4, 3, 0, 2] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 46) k = (![1, 0, 0, 0, -1, 1, 0, 0, 1, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product47 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (47 : Fin 120)) =
      ∑ k, (point (labelPoint 47) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (47 : Fin 120)) j = (![1, 4, 3, 2, 0] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 47) k = (![1, 0, 0, 0, -1, 1, 1, 0, 1, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product48 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (48 : Fin 120)) =
      ∑ k, (point (labelPoint 48) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (48 : Fin 120)) j = (![2, 0, 1, 3, 4] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 48) k = (![1, 0, 0, 0, 0, 0, 0, -1, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product49 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (49 : Fin 120)) =
      ∑ k, (point (labelPoint 49) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (49 : Fin 120)) j = (![2, 0, 1, 4, 3] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 49) k = (![1, 0, 0, 0, 0, 0, 0, -1, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product50 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (50 : Fin 120)) =
      ∑ k, (point (labelPoint 50) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (50 : Fin 120)) j = (![2, 0, 3, 1, 4] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 50) k = (![1, 0, 0, 0, 0, 1, 0, -1, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product51 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (51 : Fin 120)) =
      ∑ k, (point (labelPoint 51) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (51 : Fin 120)) j = (![2, 0, 3, 4, 1] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 51) k = (![1, 0, 0, 0, 0, 1, -1, -1, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product52 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (52 : Fin 120)) =
      ∑ k, (point (labelPoint 52) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (52 : Fin 120)) j = (![2, 0, 4, 1, 3] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 52) k = (![1, 0, 0, 0, 0, 1, 0, -1, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product53 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (53 : Fin 120)) =
      ∑ k, (point (labelPoint 53) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (53 : Fin 120)) j = (![2, 0, 4, 3, 1] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 53) k = (![1, 0, 0, 0, 0, 1, -1, -1, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product54 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (54 : Fin 120)) =
      ∑ k, (point (labelPoint 54) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (54 : Fin 120)) j = (![2, 1, 0, 3, 4] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 54) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product55 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (55 : Fin 120)) =
      ∑ k, (point (labelPoint 55) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (55 : Fin 120)) j = (![2, 1, 0, 4, 3] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 55) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product56 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (56 : Fin 120)) =
      ∑ k, (point (labelPoint 56) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (56 : Fin 120)) j = (![2, 1, 3, 0, 4] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 56) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product57 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (57 : Fin 120)) =
      ∑ k, (point (labelPoint 57) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (57 : Fin 120)) j = (![2, 1, 3, 4, 0] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 57) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product58 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (58 : Fin 120)) =
      ∑ k, (point (labelPoint 58) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (58 : Fin 120)) j = (![2, 1, 4, 0, 3] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 58) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product59 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (59 : Fin 120)) =
      ∑ k, (point (labelPoint 59) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (59 : Fin 120)) j = (![2, 1, 4, 3, 0] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 59) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product60 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (60 : Fin 120)) =
      ∑ k, (point (labelPoint 60) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (60 : Fin 120)) j = (![2, 3, 0, 1, 4] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 60) k = (![1, 0, 1, 0, 0, 0, 0, -1, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product61 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (61 : Fin 120)) =
      ∑ k, (point (labelPoint 61) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (61 : Fin 120)) j = (![2, 3, 0, 4, 1] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 61) k = (![1, 0, 1, -1, 0, 0, 0, -1, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product62 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (62 : Fin 120)) =
      ∑ k, (point (labelPoint 62) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (62 : Fin 120)) j = (![2, 3, 1, 0, 4] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 62) k = (![1, 0, 1, 0, 0, -1, 0, -1, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product63 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (63 : Fin 120)) =
      ∑ k, (point (labelPoint 63) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (63 : Fin 120)) j = (![2, 3, 1, 4, 0] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 63) k = (![1, 0, 1, -1, 0, -1, 1, -1, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product64 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (64 : Fin 120)) =
      ∑ k, (point (labelPoint 64) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (64 : Fin 120)) j = (![2, 3, 4, 0, 1] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 64) k = (![1, -1, 1, 0, 0, 1, 0, -1, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product65 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (65 : Fin 120)) =
      ∑ k, (point (labelPoint 65) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (65 : Fin 120)) j = (![2, 3, 4, 1, 0] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 65) k = (![1, -1, 1, 0, 0, 1, 1, -1, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product66 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (66 : Fin 120)) =
      ∑ k, (point (labelPoint 66) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (66 : Fin 120)) j = (![2, 4, 0, 1, 3] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 66) k = (![1, 0, 1, 0, 0, 0, 0, -1, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product67 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (67 : Fin 120)) =
      ∑ k, (point (labelPoint 67) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (67 : Fin 120)) j = (![2, 4, 0, 3, 1] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 67) k = (![1, 0, 1, -1, 0, 0, 0, -1, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product68 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (68 : Fin 120)) =
      ∑ k, (point (labelPoint 68) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (68 : Fin 120)) j = (![2, 4, 1, 0, 3] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 68) k = (![1, 0, 1, 0, 0, -1, 0, -1, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product69 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (69 : Fin 120)) =
      ∑ k, (point (labelPoint 69) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (69 : Fin 120)) j = (![2, 4, 1, 3, 0] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 69) k = (![1, 0, 1, -1, 0, -1, 1, -1, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product70 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (70 : Fin 120)) =
      ∑ k, (point (labelPoint 70) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (70 : Fin 120)) j = (![2, 4, 3, 0, 1] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 70) k = (![1, -1, 1, 0, 0, 1, 0, -1, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product71 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (71 : Fin 120)) =
      ∑ k, (point (labelPoint 71) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (71 : Fin 120)) j = (![2, 4, 3, 1, 0] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 71) k = (![1, -1, 1, 0, 0, 1, 1, -1, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product72 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (72 : Fin 120)) =
      ∑ k, (point (labelPoint 72) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (72 : Fin 120)) j = (![3, 0, 1, 2, 4] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 72) k = (![1, 0, 0, 0, 0, -1, 0, 0, 1, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product73 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (73 : Fin 120)) =
      ∑ k, (point (labelPoint 73) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (73 : Fin 120)) j = (![3, 0, 1, 4, 2] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 73) k = (![1, 0, 0, 0, 0, -1, 1, 0, 1, -1] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product74 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (74 : Fin 120)) =
      ∑ k, (point (labelPoint 74) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (74 : Fin 120)) j = (![3, 0, 2, 1, 4] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 74) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product75 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (75 : Fin 120)) =
      ∑ k, (point (labelPoint 75) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (75 : Fin 120)) j = (![3, 0, 2, 4, 1] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 75) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product76 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (76 : Fin 120)) =
      ∑ k, (point (labelPoint 76) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (76 : Fin 120)) j = (![3, 0, 4, 1, 2] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 76) k = (![1, 0, 0, 0, 1, -1, 0, 0, 0, -1] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product77 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (77 : Fin 120)) =
      ∑ k, (point (labelPoint 77) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (77 : Fin 120)) j = (![3, 0, 4, 2, 1] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 77) k = (![1, 0, 0, 0, 1, -1, -1, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product78 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (78 : Fin 120)) =
      ∑ k, (point (labelPoint 78) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (78 : Fin 120)) j = (![3, 1, 0, 2, 4] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 78) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product79 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (79 : Fin 120)) =
      ∑ k, (point (labelPoint 79) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (79 : Fin 120)) j = (![3, 1, 0, 4, 2] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 79) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product80 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (80 : Fin 120)) =
      ∑ k, (point (labelPoint 80) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (80 : Fin 120)) j = (![3, 1, 2, 0, 4] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 80) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product81 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (81 : Fin 120)) =
      ∑ k, (point (labelPoint 81) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (81 : Fin 120)) j = (![3, 1, 2, 4, 0] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 81) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product82 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (82 : Fin 120)) =
      ∑ k, (point (labelPoint 82) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (82 : Fin 120)) j = (![3, 1, 4, 0, 2] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 82) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product83 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (83 : Fin 120)) =
      ∑ k, (point (labelPoint 83) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (83 : Fin 120)) j = (![3, 1, 4, 2, 0] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 83) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product84 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (84 : Fin 120)) =
      ∑ k, (point (labelPoint 84) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (84 : Fin 120)) j = (![3, 2, 0, 1, 4] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 84) k = (![1, 0, 1, 0, 0, -1, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product85 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (85 : Fin 120)) =
      ∑ k, (point (labelPoint 85) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (85 : Fin 120)) j = (![3, 2, 0, 4, 1] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 85) k = (![1, 0, 1, -1, 0, -1, 1, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product86 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (86 : Fin 120)) =
      ∑ k, (point (labelPoint 86) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (86 : Fin 120)) j = (![3, 2, 1, 0, 4] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 86) k = (![1, 0, 1, 0, 0, -2, 0, 0, 1, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product87 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (87 : Fin 120)) =
      ∑ k, (point (labelPoint 87) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (87 : Fin 120)) j = (![3, 2, 1, 4, 0] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 87) k = (![1, 0, 1, -1, 0, -2, 2, 0, 1, -1] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product88 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (88 : Fin 120)) =
      ∑ k, (point (labelPoint 88) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (88 : Fin 120)) j = (![3, 2, 4, 0, 1] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 88) k = (![1, -1, 1, 0, 1, -1, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product89 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (89 : Fin 120)) =
      ∑ k, (point (labelPoint 89) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (89 : Fin 120)) j = (![3, 2, 4, 1, 0] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 89) k = (![1, -1, 1, 0, 1, -1, 1, 0, 0, -1] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product90 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (90 : Fin 120)) =
      ∑ k, (point (labelPoint 90) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (90 : Fin 120)) j = (![3, 4, 0, 1, 2] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 90) k = (![1, 1, 0, 0, 0, -1, -1, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product91 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (91 : Fin 120)) =
      ∑ k, (point (labelPoint 91) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (91 : Fin 120)) j = (![3, 4, 0, 2, 1] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 91) k = (![1, 1, 0, -1, 0, -1, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product92 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (92 : Fin 120)) =
      ∑ k, (point (labelPoint 92) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (92 : Fin 120)) j = (![3, 4, 1, 0, 2] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 92) k = (![1, 1, 0, 0, -1, -1, 0, 0, 1, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product93 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (93 : Fin 120)) =
      ∑ k, (point (labelPoint 93) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (93 : Fin 120)) j = (![3, 4, 1, 2, 0] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 93) k = (![1, 1, 0, -1, -1, -1, 1, 0, 1, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product94 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (94 : Fin 120)) =
      ∑ k, (point (labelPoint 94) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (94 : Fin 120)) j = (![3, 4, 2, 0, 1] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 94) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product95 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (95 : Fin 120)) =
      ∑ k, (point (labelPoint 95) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (95 : Fin 120)) j = (![3, 4, 2, 1, 0] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 95) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product96 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (96 : Fin 120)) =
      ∑ k, (point (labelPoint 96) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (96 : Fin 120)) j = (![4, 0, 1, 2, 3] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 96) k = (![1, 0, 0, 0, 0, -1, 0, 0, 1, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product97 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (97 : Fin 120)) =
      ∑ k, (point (labelPoint 97) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (97 : Fin 120)) j = (![4, 0, 1, 3, 2] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 97) k = (![1, 0, 0, 0, 0, -1, 1, 0, 1, -1] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product98 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (98 : Fin 120)) =
      ∑ k, (point (labelPoint 98) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (98 : Fin 120)) j = (![4, 0, 2, 1, 3] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 98) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product99 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (99 : Fin 120)) =
      ∑ k, (point (labelPoint 99) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (99 : Fin 120)) j = (![4, 0, 2, 3, 1] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 99) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product100 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (100 : Fin 120)) =
      ∑ k, (point (labelPoint 100) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (100 : Fin 120)) j = (![4, 0, 3, 1, 2] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 100) k = (![1, 0, 0, 0, 1, -1, 0, 0, 0, -1] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product101 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (101 : Fin 120)) =
      ∑ k, (point (labelPoint 101) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (101 : Fin 120)) j = (![4, 0, 3, 2, 1] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 101) k = (![1, 0, 0, 0, 1, -1, -1, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product102 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (102 : Fin 120)) =
      ∑ k, (point (labelPoint 102) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (102 : Fin 120)) j = (![4, 1, 0, 2, 3] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 102) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product103 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (103 : Fin 120)) =
      ∑ k, (point (labelPoint 103) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (103 : Fin 120)) j = (![4, 1, 0, 3, 2] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 103) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product104 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (104 : Fin 120)) =
      ∑ k, (point (labelPoint 104) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (104 : Fin 120)) j = (![4, 1, 2, 0, 3] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 104) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product105 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (105 : Fin 120)) =
      ∑ k, (point (labelPoint 105) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (105 : Fin 120)) j = (![4, 1, 2, 3, 0] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 105) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product106 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (106 : Fin 120)) =
      ∑ k, (point (labelPoint 106) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (106 : Fin 120)) j = (![4, 1, 3, 0, 2] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 106) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product107 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (107 : Fin 120)) =
      ∑ k, (point (labelPoint 107) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (107 : Fin 120)) j = (![4, 1, 3, 2, 0] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 107) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product108 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (108 : Fin 120)) =
      ∑ k, (point (labelPoint 108) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (108 : Fin 120)) j = (![4, 2, 0, 1, 3] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 108) k = (![1, 0, 1, 0, 0, -1, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product109 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (109 : Fin 120)) =
      ∑ k, (point (labelPoint 109) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (109 : Fin 120)) j = (![4, 2, 0, 3, 1] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 109) k = (![1, 0, 1, -1, 0, -1, 1, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product110 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (110 : Fin 120)) =
      ∑ k, (point (labelPoint 110) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (110 : Fin 120)) j = (![4, 2, 1, 0, 3] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 110) k = (![1, 0, 1, 0, 0, -2, 0, 0, 1, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product111 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (111 : Fin 120)) =
      ∑ k, (point (labelPoint 111) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (111 : Fin 120)) j = (![4, 2, 1, 3, 0] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 111) k = (![1, 0, 1, -1, 0, -2, 2, 0, 1, -1] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product112 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (112 : Fin 120)) =
      ∑ k, (point (labelPoint 112) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (112 : Fin 120)) j = (![4, 2, 3, 0, 1] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 112) k = (![1, -1, 1, 0, 1, -1, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product113 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (113 : Fin 120)) =
      ∑ k, (point (labelPoint 113) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (113 : Fin 120)) j = (![4, 2, 3, 1, 0] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 113) k = (![1, -1, 1, 0, 1, -1, 1, 0, 0, -1] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product114 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (114 : Fin 120)) =
      ∑ k, (point (labelPoint 114) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (114 : Fin 120)) j = (![4, 3, 0, 1, 2] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 114) k = (![1, 1, 0, 0, 0, -1, -1, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product115 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (115 : Fin 120)) =
      ∑ k, (point (labelPoint 115) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (115 : Fin 120)) j = (![4, 3, 0, 2, 1] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 115) k = (![1, 1, 0, -1, 0, -1, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product116 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (116 : Fin 120)) =
      ∑ k, (point (labelPoint 116) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (116 : Fin 120)) j = (![4, 3, 1, 0, 2] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 116) k = (![1, 1, 0, 0, -1, -1, 0, 0, 1, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product117 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (117 : Fin 120)) =
      ∑ k, (point (labelPoint 117) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (117 : Fin 120)) j = (![4, 3, 1, 2, 0] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 117) k = (![1, 1, 0, -1, -1, -1, 1, 0, 1, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product118 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (118 : Fin 120)) =
      ∑ k, (point (labelPoint 118) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (118 : Fin 120)) j = (![4, 3, 2, 0, 1] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 118) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

private theorem product119 (z : Fin 6 → ℂ) :
    matchingProduct (left z) (right z) (FivePermutations.perm (119 : Fin 120)) =
      ∑ k, (point (labelPoint 119) k : ℂ) * basis z k := by
  have hp : ∀ j, (FivePermutations.perm (119 : Fin 120)) j = (![4, 3, 2, 1, 0] : Fin 5 → Fin 5) j := by decide +kernel
  have hx : ∀ k, point (labelPoint 119) k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 10 → ℤ) k := by decide +kernel
  simp only [matchingProduct, hp, hx]
  simp [left, right, basis, Fin.prod_univ_succ, Fin.sum_univ_succ] <;> ring

/-- Evaluation of the ten coefficient coordinates recovers each matching product. -/
theorem matching_eq (z : Fin 6 → ℂ) (p : Fin 120) :
    matchingProduct (left z) (right z) (FivePermutations.perm p) =
      ∑ k, (point (labelPoint p) k : ℂ) * basis z k := by
  fin_cases p
  · exact product0 z
  · exact product1 z
  · exact product2 z
  · exact product3 z
  · exact product4 z
  · exact product5 z
  · exact product6 z
  · exact product7 z
  · exact product8 z
  · exact product9 z
  · exact product10 z
  · exact product11 z
  · exact product12 z
  · exact product13 z
  · exact product14 z
  · exact product15 z
  · exact product16 z
  · exact product17 z
  · exact product18 z
  · exact product19 z
  · exact product20 z
  · exact product21 z
  · exact product22 z
  · exact product23 z
  · exact product24 z
  · exact product25 z
  · exact product26 z
  · exact product27 z
  · exact product28 z
  · exact product29 z
  · exact product30 z
  · exact product31 z
  · exact product32 z
  · exact product33 z
  · exact product34 z
  · exact product35 z
  · exact product36 z
  · exact product37 z
  · exact product38 z
  · exact product39 z
  · exact product40 z
  · exact product41 z
  · exact product42 z
  · exact product43 z
  · exact product44 z
  · exact product45 z
  · exact product46 z
  · exact product47 z
  · exact product48 z
  · exact product49 z
  · exact product50 z
  · exact product51 z
  · exact product52 z
  · exact product53 z
  · exact product54 z
  · exact product55 z
  · exact product56 z
  · exact product57 z
  · exact product58 z
  · exact product59 z
  · exact product60 z
  · exact product61 z
  · exact product62 z
  · exact product63 z
  · exact product64 z
  · exact product65 z
  · exact product66 z
  · exact product67 z
  · exact product68 z
  · exact product69 z
  · exact product70 z
  · exact product71 z
  · exact product72 z
  · exact product73 z
  · exact product74 z
  · exact product75 z
  · exact product76 z
  · exact product77 z
  · exact product78 z
  · exact product79 z
  · exact product80 z
  · exact product81 z
  · exact product82 z
  · exact product83 z
  · exact product84 z
  · exact product85 z
  · exact product86 z
  · exact product87 z
  · exact product88 z
  · exact product89 z
  · exact product90 z
  · exact product91 z
  · exact product92 z
  · exact product93 z
  · exact product94 z
  · exact product95 z
  · exact product96 z
  · exact product97 z
  · exact product98 z
  · exact product99 z
  · exact product100 z
  · exact product101 z
  · exact product102 z
  · exact product103 z
  · exact product104 z
  · exact product105 z
  · exact product106 z
  · exact product107 z
  · exact product108 z
  · exact product109 z
  · exact product110 z
  · exact product111 z
  · exact product112 z
  · exact product113 z
  · exact product114 z
  · exact product115 z
  · exact product116 z
  · exact product117 z
  · exact product118 z
  · exact product119 z

end
end MOC.ThreeSharedRepeatedFive
