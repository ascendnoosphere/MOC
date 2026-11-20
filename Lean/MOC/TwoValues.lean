import MOC.Weights
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! A permutation image of a single subset has a nonnegative signed mass.
This suffices when one spectrum takes at most two values. -/

open BigOperators Matrix Finset
open scoped ComplexOrder

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem matchingProduct_subset_marker (I J : Finset ι) (hc : I.card = J.card)
    (σ : Equiv.Perm ι) :
    matchingProduct (fun i => if i ∈ I then 0 else 1) (fun j => if j ∈ J then 1 else 0) σ =
      if J.map σ.toEmbedding = I then 1 else 0 := by
  classical
  by_cases h : J.map σ.toEmbedding = I
  · rw [if_pos h]
    unfold matchingProduct
    apply Finset.prod_eq_one
    intro j _
    have hm : σ j ∈ I ↔ j ∈ J := by rw [← h, Finset.mem_map_equiv, Equiv.symm_apply_apply]
    by_cases hj : j ∈ J <;> simp [hj, hm]
  · rw [if_neg h]
    have hns : ¬ I ⊆ J.map σ.toEmbedding := by
      intro hs
      exact h (Finset.eq_of_subset_of_card_le hs (by rw [Finset.card_map, hc])).symm
    obtain ⟨i, hi, hni⟩ := Finset.not_subset.mp hns
    unfold matchingProduct
    apply Finset.prod_eq_zero (Finset.mem_univ (σ.symm i))
    have hj : σ.symm i ∉ J := by rwa [Finset.mem_map_equiv] at hni
    simp [hi, hj]

/-- The signed mass of the permutations taking (J) to (I) is real and nonnegative. -/
theorem sum_signedWeight_image_nonneg (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (I J : Finset ι) (hc : I.card = J.card) :
    0 ≤ ∑ σ ∈ univ.filter (fun σ : Equiv.Perm ι => J.map σ.toEmbedding = I), signedWeight U σ := by
  classical
  let p (i : ι) : ℂ := if i ∈ I then 0 else 1
  let q (i : ι) : ℂ := if i ∈ J then 1 else 0
  have hm : (∑ σ ∈ univ.filter (fun σ : Equiv.Perm ι => J.map σ.toEmbedding = I),
      signedWeight U σ) = determinantValue p q U := by
    rw [← signed_determinant p q U hU, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro σ _
    rw [matchingProduct_subset_marker I J hc σ]
    split_ifs <;> simp
  rw [hm]
  have hp : (diagonal p).PosSemidef := Matrix.PosSemidef.diagonal (fun i => by
    by_cases hi : i ∈ I <;> simp [p, hi])
  have hq : (diagonal q).PosSemidef := Matrix.PosSemidef.diagonal (fun i => by
    by_cases hi : i ∈ J <;> simp [q, hi])
  have hM : (diagonal p + U * diagonal q * Uᴴ).PosSemidef :=
    hp.add (hq.mul_mul_conjTranspose_same U)
  unfold determinantValue
  rw [hM.1.det_eq_prod_eigenvalues]
  exact Finset.prod_nonneg (fun i _ => Complex.zero_le_real.mpr (hM.eigenvalues_nonneg i))

/-- A two-valued second spectrum needs only the image of one subset under the permutation. -/
theorem holds_two_values (a : ι → ℂ) (J : Finset ι) (c d : ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    Holds a (fun j => if j ∈ J then c else d) U := by
  classical
  let b (j : ι) := if j ∈ J then c else d
  let g (σ : Equiv.Perm ι) := J.map σ.toEmbedding
  let T := (univ : Finset (Equiv.Perm ι)).image g
  let m (I : Finset ι) := ∑ σ ∈ univ.filter (fun σ => g σ = I), signedWeight U σ
  let w (I : Finset ι) := (m I).re
  let v (I : Finset ι) := ∏ i, (a i + if i ∈ I then c else d)
  have hmap (σ : Equiv.Perm ι) (_ : σ ∈ univ) : g σ ∈ T := Finset.mem_image_of_mem g (mem_univ σ)
  have hv (σ : Equiv.Perm ι) : matchingProduct a b σ = v (g σ) := by
    unfold matchingProduct v
    rw [← Equiv.prod_comp σ (fun i => a i + if i ∈ g σ then c else d)]
    simp [b, g, Finset.mem_map_equiv]
  have hn (I : Finset ι) (hI : I ∈ T) : 0 ≤ m I := by
    obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hI
    apply sum_signedWeight_image_nonneg U hU
    exact card_map _
  have hvtx (I : Finset ι) (hI : I ∈ T) : v I ∈ Set.range (matchingProduct a b) := by
    obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hI
    exact ⟨σ, hv σ⟩
  have hsumC : ∑ I ∈ T, m I = 1 := by
    rw [Finset.sum_fiberwise_of_maps_to hmap, sum_signedWeight U (det_ne_zero_of_unitary hU)]
  have hsum : ∑ I ∈ T, w I = 1 := by
    simpa only [Complex.re_sum, Complex.one_re] using congrArg Complex.re hsumC
  have hdet : ∑ I ∈ T, w I • v I = determinantValue a b U := calc
    _ = ∑ I ∈ T, m I * v I := by
      apply Finset.sum_congr rfl
      intro I hI
      have he : (w I : ℂ) = m I := Complex.ext rfl (Complex.nonneg_iff.mp (hn I hI)).2
      rw [Complex.real_smul, he]
    _ = ∑ σ, signedWeight U σ * matchingProduct a b σ := by
      rw [← Finset.sum_fiberwise_of_maps_to hmap]
      apply Finset.sum_congr rfl
      intro I _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [hv, (Finset.mem_filter.mp hσ).2]
    _ = _ := signed_determinant a b U hU
  change determinantValue a b U ∈ convexHull ℝ (Set.range (matchingProduct a b))
  rw [← hdet, ← T.centerMass_eq_of_sum_1 v hsum]
  exact T.centerMass_mem_convexHull (fun I hI => (Complex.nonneg_iff.mp (hn I hI)).1)
    (hsum.symm ▸ zero_lt_one) hvtx

theorem holds_of_two_values (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (c d : ℂ) (hb : ∀ j, b j = c ∨ b j = d) : Holds a b U := by
  classical
  let J := (univ : Finset ι).filter (fun j => b j = c)
  have h : b = fun j => if j ∈ J then c else d := by
    funext j
    have hm : j ∈ J ↔ b j = c := by simp [J]
    by_cases hj : b j = c
    · rw [if_pos (hm.mpr hj), hj]
    · rw [if_neg (mt hm.mp hj)]
      exact (hb j).resolve_left hj
  rw [h]
  exact holds_two_values a J c d U hU

theorem holds_of_two_values_left (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (c d : ℂ) (ha : ∀ i, a i = c ∨ a i = d) : Holds a b U := by
  have hU' : IsUnitary Uᴴ := ⟨by simpa using hU.2, by simpa using hU.1⟩
  exact (holds_swap_iff a b hU).mp (holds_of_two_values b a Uᴴ hU' c d ha)

end

end MOC
