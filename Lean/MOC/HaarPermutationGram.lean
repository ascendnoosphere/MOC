import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.Ring

/-! The finite Gram matrix for integration of permutation monomials on the unitary group. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def coloringGram (f : ι → ι) : Matrix (Equiv.Perm ι) (Equiv.Perm ι) ℝ := by
  classical
  exact Matrix.of fun p q => if f ∘ p = f ∘ q then 1 else 0

/-- The Gram entry for two permutations counts the colorings for which their
two color words agree. The set of colors is the label set. -/
def permutationColorGram : Matrix (Equiv.Perm ι) (Equiv.Perm ι) ℝ :=
  ∑ f : ι → ι, coloringGram f

private theorem coloringGram_posSemidef (f : ι → ι) : (coloringGram f).PosSemidef := by
  classical
  let X : Matrix (ι → ι) (Equiv.Perm ι) ℝ := Matrix.of fun w p => if f ∘ p = w then 1 else 0
  have hX : coloringGram f = Xᴴ * X := by
    ext p q
    simp only [coloringGram, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      X, star_trivial]
    rw [Finset.sum_eq_single (f ∘ p)]
    · simp only [if_pos rfl, one_mul, eq_comm (a := f ∘ p) (b := f ∘ q)]
    · intro w _ hw
      rw [if_neg hw.symm, zero_mul]
    · simp
  rw [hX]
  exact Matrix.posSemidef_conjTranspose_mul_self X

private theorem coloringGram_of_perm (r : Equiv.Perm ι) : coloringGram (r : ι → ι) = 1 := by
  classical
  ext p q
  have he : (r : ι → ι) ∘ p = (r : ι → ι) ∘ q ↔ p = q := by
    constructor
    · intro h
      exact Equiv.ext fun i => r.injective (congrFun h i)
    · rintro rfl
      rfl
  simp only [coloringGram, Matrix.of_apply, he, Matrix.one_apply]

private theorem coloringGram_sum_posSemidef (s : Finset (ι → ι)) :
    (∑ f ∈ s, coloringGram f).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using
      (Matrix.PosSemidef.zero : (0 : Matrix (Equiv.Perm ι) (Equiv.Perm ι) ℝ).PosSemidef)
  | insert f s hf ih =>
      rw [Finset.sum_insert hf]
      exact (coloringGram_posSemidef f).add ih

/-- The permutation colorings already contribute a factorial multiple of the identity. -/
theorem permutationColorGram_sub_card_posSemidef :
    (permutationColorGram - (Fintype.card (Equiv.Perm ι) : ℝ) • 1).PosSemidef := by
  classical
  let e : Equiv.Perm ι ↪ (ι → ι) := ⟨fun p => p, fun _ _ h => Equiv.ext (congrFun h)⟩
  let s : Finset (ι → ι) := Finset.univ.map e
  have hs : (∑ f ∈ s, coloringGram f) =
      (Fintype.card (Equiv.Perm ι) : ℝ) • 1 := by
    change (∑ f ∈ Finset.univ.map e, coloringGram f) = _
    rw [Finset.sum_map]
    simp only [e, Function.Embedding.coeFn_mk, coloringGram_of_perm, Finset.sum_const,
      Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have hsplit := Finset.sum_sdiff (f := coloringGram) (Finset.subset_univ s)
  rw [hs] at hsplit
  rw [permutationColorGram, ← hsplit, add_sub_cancel_right]
  exact coloringGram_sum_posSemidef (Finset.univ \ s)

private def invariantColoringEquiv (p : Equiv.Perm ι) :
    {f : ι → ι // ∀ i, f (p i) = f i} ≃ (Quotient p.SameCycle.setoid → ι) where
  toFun f := Quotient.lift f.val (by
    intro i j h
    obtain ⟨k, hk⟩ : p.SameCycle i j := h
    let H : Subgroup (Equiv.Perm ι) := {
      carrier := {q | ∀ x, f.val (q x) = f.val x}
      one_mem' := fun _ => rfl
      mul_mem' := fun hq hr x => (hq _).trans (hr x)
      inv_mem' := fun {q} hq x => by
        have he := hq (q⁻¹ x)
        simpa only [Equiv.Perm.apply_inv_self] using he.symm }
    have hp : p ∈ H := f.property
    have hpow : ∀ x, f.val ((p ^ k) x) = f.val x := H.zpow_mem hp k
    exact (hpow i).symm.trans (congrArg f.val hk))
  invFun g := ⟨fun i => g ⟦i⟧, fun i =>
    congrArg g (Quotient.sound (show p.SameCycle (p i) i from
      (show p.SameCycle i (p i) from ⟨1, by rw [zpow_one]⟩).symm))⟩
  left_inv f := by apply Subtype.ext; rfl
  right_inv g := funext fun q => Quotient.inductionOn q (fun _ => rfl)

/-- An entry counts one free color for each cycle of the relative permutation.
The quotient includes singleton cycles. -/
theorem permutationColorGram_apply (p q : Equiv.Perm ι) :
    permutationColorGram p q = (Fintype.card ι : ℝ) ^
      Nat.card (Quotient (q * p⁻¹).SameCycle.setoid) := by
  classical
  let t := q * p⁻¹
  have ht (f : ι → ι) : f ∘ p = f ∘ q ↔ ∀ i, f (t i) = f i := by
    constructor
    · intro h i
      simpa only [Function.comp_apply, t, Equiv.Perm.mul_apply, Equiv.Perm.apply_inv_self] using
        (congrFun h (p⁻¹ i)).symm
    · intro h
      funext i
      simpa only [Function.comp_apply, t, Equiv.Perm.mul_apply, Equiv.Perm.inv_apply_self] using
        (h (p i)).symm
  letI : Fintype (Quotient t.SameCycle.setoid) := Fintype.ofFinite _
  have hcard : Fintype.card {f : ι → ι // ∀ i, f (t i) = f i} =
      Fintype.card ι ^ Nat.card (Quotient t.SameCycle.setoid) := by
    rw [Fintype.card_congr (invariantColoringEquiv t), Fintype.card_fun, Nat.card_eq_fintype_card]
  change _ = (Fintype.card ι : ℝ) ^ Nat.card (Quotient t.SameCycle.setoid)
  unfold permutationColorGram
  simp only [Matrix.sum_apply, coloringGram, Matrix.of_apply, ht, Finset.sum_boole]
  rw [← Fintype.card_subtype, hcard, Nat.cast_pow]

private theorem permutationColorGram_quadratic_lower (x : Equiv.Perm ι → ℝ) :
    0 ≤ x ⬝ᵥ (permutationColorGram *ᵥ x) -
      (Fintype.card (Equiv.Perm ι) : ℝ) * (x ⬝ᵥ x) := by
  have hstar : star x = x := funext fun i => by simp only [Pi.star_apply, star_trivial]
  simpa only [hstar, Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] using
    (permutationColorGram_sub_card_posSemidef (ι := ι)).2 x

theorem permutationColorGram_det_ne_zero :
    (permutationColorGram (ι := ι)).det ≠ 0 := by
  intro hdet
  obtain ⟨x, hx, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hlow := permutationColorGram_quadratic_lower x
  rw [hzero, dotProduct_zero, zero_sub, neg_nonneg] at hlow
  have hcard : (0 : ℝ) < Fintype.card (Equiv.Perm ι) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Equiv.Perm ι))
  have hsum : (∑ i, x i ^ 2) ≤ 0 := by
    simpa only [dotProduct, pow_two] using nonpos_of_mul_nonpos_right hlow hcard
  apply hx
  funext i
  apply sq_eq_zero_iff.mp
  have hi : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  exact le_antisymm (hi.trans hsum) (sq_nonneg _)

/-- The quadratic form of the inverse permutation Gram matrix is bounded by the
mean of the squared coordinates. This real inequality applies separately to
the real and imaginary parts of the monomial coefficients. -/
theorem permutationColorGram_inverse_quadratic_le (c : Equiv.Perm ι → ℝ) :
    (permutationColorGram⁻¹ *ᵥ c) ⬝ᵥ c ≤
      (c ⬝ᵥ c) / (Fintype.card (Equiv.Perm ι) : ℝ) := by
  let d : ℝ := Fintype.card (Equiv.Perm ι)
  let x := permutationColorGram⁻¹ *ᵥ c
  have hd : 0 < d := by
    change (0 : ℝ) < Fintype.card (Equiv.Perm ι)
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Equiv.Perm ι))
  have hx : permutationColorGram *ᵥ x = c := by
    change permutationColorGram *ᵥ (permutationColorGram⁻¹ *ᵥ c) = c
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv
      (isUnit_iff_ne_zero.mpr (permutationColorGram_det_ne_zero (ι := ι))), Matrix.one_mulVec]
  have hl : 0 ≤ x ⬝ᵥ c - d * (x ⬝ᵥ x) := by
    simpa only [d, hx] using permutationColorGram_quadratic_lower x
  have hs : 0 ≤ c ⬝ᵥ c - (2 * d) * (x ⬝ᵥ c) + d ^ 2 * (x ⬝ᵥ x) := by
    have he : c ⬝ᵥ c - (2 * d) * (x ⬝ᵥ c) + d ^ 2 * (x ⬝ᵥ x) =
        ∑ i, (c i - d * x i) ^ 2 := by
      simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [he]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  change x ⬝ᵥ c ≤ (c ⬝ᵥ c) / d
  apply (le_div_iff₀ hd).2
  have he : c ⬝ᵥ c - (x ⬝ᵥ c) * d =
      (c ⬝ᵥ c - (2 * d) * (x ⬝ᵥ c) + d ^ 2 * (x ⬝ᵥ x)) +
        d * (x ⬝ᵥ c - d * (x ⬝ᵥ x)) := by ring
  exact sub_nonneg.mp (he.symm ▸ add_nonneg hs (mul_nonneg hd.le hl))

/-- The sum of the inverse Gram quadratic forms on the real and imaginary
parts is at most the mean squared modulus of the input coefficients. -/
theorem permutationColorGram_inverse_complex_quadratic_le (c : Equiv.Perm ι → ℂ) :
    ((permutationColorGram⁻¹ *ᵥ (Complex.re ∘ c)) ⬝ᵥ (Complex.re ∘ c)) +
      ((permutationColorGram⁻¹ *ᵥ (Complex.im ∘ c)) ⬝ᵥ (Complex.im ∘ c)) ≤
      (∑ p, Complex.normSq (c p)) / (Fintype.card (Equiv.Perm ι) : ℝ) := by
  have h := add_le_add (permutationColorGram_inverse_quadratic_le (Complex.re ∘ c))
    (permutationColorGram_inverse_quadratic_le (Complex.im ∘ c))
  rw [← add_div] at h
  simpa only [dotProduct, Function.comp_apply, Complex.normSq_apply, Finset.sum_add_distrib] using h

/-- The dimension estimate at the order-four mixer and power 185 is strictly
smaller than the corresponding power of the point evaluation. -/
theorem orderFour_unrestricted_moment_evaluation_arithmetic :
    2401 ^ 370 * Nat.choose 755 15 < (2913 : ℕ) ^ 370 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

end

end MOC
