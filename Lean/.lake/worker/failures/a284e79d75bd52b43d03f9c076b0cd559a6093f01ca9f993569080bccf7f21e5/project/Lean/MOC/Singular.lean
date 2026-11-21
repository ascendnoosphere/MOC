import MOC.Small
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! The singular determinant case, by the shared spectral moments argument
of Drury and Cload. The two probability laws need at most five labels in total. -/

open BigOperators Matrix

namespace MOC

noncomputable section

private structure SharedMoments {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℂ) (c : κ → ℂ) (p : ι → ℝ) (q : κ → ℝ) : Prop where
  left_nonneg : ∀ i, 0 ≤ p i
  right_nonneg : ∀ j, 0 ≤ q j
  left_mass : ∑ i, p i = 1
  right_mass : ∑ j, q j = 1
  first : ∑ i, (p i : ℂ) * a i = ∑ j, (q j : ℂ) * c j
  second : ∑ i, p i * Complex.normSq (a i) = ∑ j, q j * Complex.normSq (c j)

private theorem exists_sparse_weights {β : Type*} [Fintype β] [DecidableEq β]
    (f : β → Fin 4 → ℝ) {x : Fin 4 → ℝ} (hx : x ∈ convexHull ℝ (Set.range f)) :
    ∃ w : β → ℝ, (∀ j, 0 ≤ w j) ∧ (∑ j, w j) = 1 ∧ (∑ j, w j • f j) = x ∧
      (Finset.univ.filter (fun j => w j ≠ 0)).card ≤ 5 := by
  classical
  obtain ⟨η, hη, z, v, hz, hInd, hv, hmass, hsum⟩ := eq_pos_convex_span_of_mem_convexHull hx
  letI : Fintype η := hη
  have hle : Fintype.card η ≤ 5 := by
    calc
      Fintype.card η ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range z)) + 1 :=
        hInd.card_le_finrank_succ
      _ ≤ Module.finrank ℝ (Fin 4 → ℝ) + 1 := Nat.add_le_add_right (Submodule.finrank_le _) _
      _ = 5 := by simp [Module.finrank_fin_fun]
  choose g hg using fun i => hz (Set.mem_range_self i)
  let w (j : β) : ℝ := ∑ i, if g i = j then v i else 0
  refine ⟨w, fun j => Finset.sum_nonneg (fun i _ => by split <;> simp_all [(hv i).le]), ?_, ?_, ?_⟩
  · simpa [w, Finset.sum_comm (f := fun j i => if g i = j then v i else 0)] using hmass
  · calc
      ∑ j, w j • f j = ∑ j, ∑ i, (if g i = j then v i else 0) • f j := by
        simp only [w, Finset.sum_smul]
      _ = ∑ i, v i • f (g i) := by rw [Finset.sum_comm]; simp [ite_smul]
      _ = x := by simpa only [hg] using hsum
  · have hs : Finset.univ.filter (fun j => w j ≠ 0) ⊆ Finset.univ.image g := by
      intro j hj
      by_contra hnj
      have hall (i : η) : g i ≠ j := fun he => hnj (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he⟩)
      exact (Finset.mem_filter.mp hj).2 (by simp [w, hall])
    calc
      _ ≤ (Finset.univ.image g).card := Finset.card_le_card hs
      _ ≤ Fintype.card η := Finset.card_image_le
      _ ≤ 5 := hle

private def taggedLift {ι κ : Type*} (a : ι → ℂ) (c : κ → ℂ) :
    ι ⊕ κ → Fin 4 → ℝ :=
  Sum.elim (fun i => ![(a i).re, (a i).im, Complex.normSq (a i), 1])
    (fun j => ![-(c j).re, -(c j).im, -Complex.normSq (c j), 0])

private theorem taggedLift_barycenter {ι κ : Type*} [Fintype ι] [Fintype κ]
    {a : ι → ℂ} {c : κ → ℂ} {p : ι → ℝ} {q : κ → ℝ}
    (h : SharedMoments a c p q) :
    ![0, 0, 0, (1 / 2 : ℝ)] ∈ convexHull ℝ (Set.range (taggedLift a c)) := by
  let w := Sum.elim (fun i => p i / 2) (fun j => q j / 2)
  apply mem_convexHull_of_exists_fintype w (taggedLift a c)
  · intro k
    cases k with
    | inl i => exact div_nonneg (h.left_nonneg _) (by norm_num)
    | inr j => exact div_nonneg (h.right_nonneg _) (by norm_num)
  · simp only [Fintype.sum_sum_type, w, Sum.elim_inl, Sum.elim_inr, ← Finset.sum_div,
      h.left_mass, h.right_mass]
    norm_num
  · exact fun k => Set.mem_range_self k
  · ext k
    have hre := congrArg Complex.re h.first
    have him := congrArg Complex.im h.first
    simp only [Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, zero_add] at hre him
    fin_cases k <;>
      simp only [Finset.sum_apply, Fintype.sum_sum_type, w, taggedLift, Sum.elim_inl,
        Sum.elim_inr, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_succ] <;>
      simp_rw [div_mul_eq_mul_div, mul_neg, Finset.sum_neg_distrib, ← Finset.sum_div,
        mul_one, mul_zero, Finset.sum_const_zero, hre, him, h.second, h.left_mass] <;>
      ring

private theorem exists_sparse_sharedMoments {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {a : ι → ℂ} {c : κ → ℂ} {p : ι → ℝ} {q : κ → ℝ}
    (h : SharedMoments a c p q) :
    ∃ p' q', SharedMoments a c p' q' ∧
      (Finset.univ.filter (fun i => p' i ≠ 0)).card +
        (Finset.univ.filter (fun j => q' j ≠ 0)).card ≤ 5 := by
  classical
  obtain ⟨w, hw, hmass, hb, hcard⟩ := exists_sparse_weights _ (taggedLift_barycenter h)
  let p' (i : ι) := 2 * w (.inl i)
  let q' (j : κ) := 2 * w (.inr j)
  have he (k : Fin 4) := congrFun hb k
  have hleft := he 3
  simp only [Finset.sum_apply, Fintype.sum_sum_type, taggedLift, Sum.elim_inl, Sum.elim_inr,
    Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_succ, mul_one, mul_zero,
    Finset.sum_const_zero, add_zero] at hleft
  rw [Fintype.sum_sum_type] at hmass
  refine ⟨p', q', ⟨fun i => mul_nonneg (by norm_num) (hw _), fun j => mul_nonneg (by norm_num) (hw _),
    ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [show ∑ i, p' i = 2 * ∑ i, w (.inl i) by unfold p'; rw [Finset.mul_sum], hleft]; norm_num
  · unfold q'
    rw [← Finset.mul_sum]
    linarith
  · apply Complex.ext
    · have hr := he 0
      simp only [Finset.sum_apply, Fintype.sum_sum_type, taggedLift, Sum.elim_inl, Sum.elim_inr,
        Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, mul_neg, Finset.sum_neg_distrib] at hr
      simp only [p', q', Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, mul_assoc, ← Finset.mul_sum]
      linarith
    · have hi := he 1
      simp only [Finset.sum_apply, Fintype.sum_sum_type, taggedLift, Sum.elim_inl, Sum.elim_inr,
        Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_succ, mul_neg,
        Finset.sum_neg_distrib] at hi
      simp only [p', q', Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero, mul_assoc, ← Finset.mul_sum]
      linarith
  · have hs := he 2
    simp only [Finset.sum_apply, Fintype.sum_sum_type, taggedLift, Sum.elim_inl, Sum.elim_inr,
      Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_succ, mul_neg,
      Finset.sum_neg_distrib] at hs
    simp only [p', q', mul_assoc, ← Finset.mul_sum]
    linarith
  · have h₁ : Fintype.card {i : ι // p' i ≠ 0} = (Finset.univ.filter (fun i => p' i ≠ 0)).card := by
      simp [Fintype.card_subtype]
    have h₂ : Fintype.card {j : κ // q' j ≠ 0} = (Finset.univ.filter (fun j => q' j ≠ 0)).card := by
      simp [Fintype.card_subtype]
    have h₃ : Fintype.card {k : ι ⊕ κ // w k ≠ 0} =
        (Finset.univ.filter (fun k => w k ≠ 0)).card := by simp [Fintype.card_subtype]
    let e : ({i // p' i ≠ 0} ⊕ {j // q' j ≠ 0}) ≃ {k : ι ⊕ κ // w k ≠ 0} :=
      { toFun := fun s => match s with
          | .inl i => ⟨.inl i, by simpa [p'] using i.property⟩
          | .inr j => ⟨.inr j, by simpa [q'] using j.property⟩
        invFun := fun s => match s with
          | ⟨.inl i, hi⟩ => .inl ⟨i, by simpa [p'] using hi⟩
          | ⟨.inr j, hj⟩ => .inr ⟨j, by simpa [q'] using hj⟩
        left_inv := by rintro (i | j) <;> rfl
        right_inv := by rintro ⟨i | j, h⟩ <;> rfl }
    rw [← h₁, ← h₂, ← Fintype.card_sum, Fintype.card_congr e, h₃]
    exact hcard

end

end MOC
