import MOC.FourKleinNegativeCompression

/-! The scalar completion of squares for a normal Klein-four cap. -/

open BigOperators Matrix

namespace MOC

noncomputable section

abbrev KleinPrismSpace := (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ)

def kleinPrismOff (p x : Fin 3 → ℝ) : ℝ :=
  p 0 * x 1 * x 2 + p 1 * x 0 * x 2 + p 2 * x 0 * x 1

/-- The chart's symmetric pencil, in its three diagonal and two
three-cycle coordinate groups. This scalar convention represents eight
times the inverse quadratic pencil in the research note. -/
def kleinPrismForm (β p q : Fin 3 → ℝ) (c₋ : ℝ) (x : KleinPrismSpace) : ℝ :=
  let w := x.1
  let r := x.2.1
  let s := x.2.2
  let c₊ := (∑ i, β i) - c₋
  (∑ i, (-β i * w i ^ 2 - 2 * q i * w i * r i - 2 * p i * w i * s i +
    (c₊ - β i) * r i ^ 2 + (c₋ - β i) * s i ^ 2)) +
    2 * kleinPrismOff p r + 2 * kleinPrismOff q s

private def kleinInverseMix : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
  (Matrix.of ![![-(1 / 2 : ℝ), 1 / 2, 1 / 2], ![1 / 2, -(1 / 2), 1 / 2],
    ![1 / 2, 1 / 2, -(1 / 2)]]).mulVecLin

private def kleinSplitThree : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x i := x (Fin.castAdd 2 i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def kleinSplitTwo : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun x i := x (Fin.natAdd 3 i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem kleinBilinear_mixed_reverse (u x : Fin 3 → ℝ) (t : ℝ) :
    let r := kleinInverseMix x
    let c := (t + ∑ i, u i) / 2
    let p := fun i => (t + u i) / 2
    (∑ i, (c - p i) * r i ^ 2) + 2 * kleinPrismOff p r =
      kleinBudgetForm u t x / 2 := by
  simp only [kleinInverseMix, kleinPrismOff, kleinBudgetForm,
    Matrix.mulVecLin_apply, Matrix.mulVec, Matrix.of_apply, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
  ring

private theorem kleinSquareComplete (β p q c z r : ℝ) (hβ : β ≠ 0) :
    -β * (z - q / β * r) ^ 2 - 2 * q * (z - q / β * r) * r +
      (c - β) * r ^ 2 =
      -β * z ^ 2 + (c - p) * r ^ 2 - (β - p - q ^ 2 / β) * r ^ 2 := by
  field_simp [hβ] <;> ring

/-- A positive mixed coefficient beyond the strong threshold gives five
strictly negative real directions in the prism, including zero-budget cases. -/
theorem kleinPrism_negative_five (a b c t : ℝ) (β q : Fin 3 → ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : b ≤ a) (hac : c ≤ a)
    (ht : 0 < t) (hthreshold : a * (b + c) - b * c < t)
    (hβ : ∀ i, (t + (![a ^ 2, b ^ 2, c ^ 2] : Fin 3 → ℝ) i) / 2 + |q i| ≤ β i) :
    let u : Fin 3 → ℝ := ![a ^ 2, b ^ 2, c ^ 2]
    let p := fun i => (t + u i) / 2
    let c₊ := (t + ∑ i, u i) / 2
    let c₋ := (∑ i, β i) - c₊
    ∃ L : (Fin 5 → ℝ) →ₗ[ℝ] KleinPrismSpace,
      ∀ x ≠ 0, kleinPrismForm β p q c₋ (L x) < 0 := by
  let u : Fin 3 → ℝ := ![a ^ 2, b ^ 2, c ^ 2]
  let p := fun i => (t + u i) / 2
  let c₊ := (t + ∑ i, u i) / 2
  let c₋ := (∑ i, β i) - c₊
  have hu (i : Fin 3) : 0 ≤ u i := by
    fin_cases i <;> exact sq_nonneg _
  have hp (i : Fin 3) : 0 < p i := div_pos (add_pos_of_pos_of_nonneg ht (hu i)) (by norm_num)
  have hβpos (i : Fin 3) : 0 < β i :=
    (add_pos_of_pos_of_nonneg (hp i) (abs_nonneg (q i))).trans_le (hβ i)
  have hδ (i : Fin 3) : 0 ≤ β i - p i - q i ^ 2 / β i := by
    have hs : |q i| ≤ β i - p i := by
      have h := hβ i
      change p i + |q i| ≤ β i at h
      linarith only [h]
    have hs0 : 0 ≤ β i - p i := (abs_nonneg (q i)).trans hs
    have habs := mul_nonneg (sub_nonneg.mpr hs) (add_nonneg hs0 (abs_nonneg (q i)))
    have hsq : q i ^ 2 ≤ (β i - p i) ^ 2 := by
      have he : (β i - p i - |q i|) * (β i - p i + |q i|) =
          (β i - p i) ^ 2 - |q i| ^ 2 := by ring
      rw [he, sq_abs] at habs
      exact sub_nonneg.mp habs
    have hprod := mul_nonneg hs0 (hp i).le
    apply sub_nonneg.mpr
    apply (div_le_iff₀ (hβpos i)).2
    nlinarith only [hsq, hprod]
  obtain ⟨B, hB⟩ := kleinBudgetForm_negative_plane a b c t hb hc hab hac ht hthreshold
  let R := kleinInverseMix.comp (B.comp kleinSplitTwo)
  let diagonalMap : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
    (diagonal (fun i => q i / β i)).mulVecLin
  let W := kleinSplitThree - diagonalMap.comp R
  let L := W.prod (R.prod (0 : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)))
  refine ⟨L, fun x hx => ?_⟩
  let r := R x
  let z := kleinSplitThree x
  let y := kleinSplitTwo x
  have hW (i : Fin 3) : W x i = z i - q i / β i * r i := by
    simp only [W, LinearMap.sub_apply, LinearMap.comp_apply, Pi.sub_apply, diagonalMap,
      Matrix.mulVecLin_apply, Matrix.mulVec_diagonal, z, r]
  have hsum : (∑ i, β i) - c₋ = c₊ := by simp only [c₋, sub_sub_cancel]
  have hcomp (i : Fin 3) := kleinSquareComplete (β i) (p i) (q i) c₊ (z i) (r i) (hβpos i).ne'
  have hcong := kleinBilinear_mixed_reverse u (B y) t
  change (∑ i, (c₊ - p i) * r i ^ 2) + 2 * kleinPrismOff p r =
    kleinBudgetForm u t (B y) / 2 at hcong
  have heq : kleinPrismForm β p q c₋ (L x) =
      -(∑ i, β i * z i ^ 2) + kleinBudgetForm u t (B y) / 2 -
        ∑ i, (β i - p i - q i ^ 2 / β i) * r i ^ 2 := by
    change kleinPrismForm β p q c₋ (W x, r, 0) = _
    simp only [kleinPrismForm, hsum, hW, Pi.zero_apply, zero_pow (by decide : (2 : ℕ) ≠ 0),
      mul_zero, sub_zero, add_zero, kleinPrismOff, zero_add]
    simp only [Fin.sum_univ_three, kleinPrismOff] at hcong ⊢
    linear_combination hcomp 0 + hcomp 1 + hcomp 2 + hcong
  rw [heq]
  have hz0 : 0 ≤ ∑ i, β i * z i ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hβpos i).le (sq_nonneg (z i))
  have hd0 : 0 ≤ ∑ i, (β i - p i - q i ^ 2 / β i) * r i ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hδ i) (sq_nonneg (r i))
  by_cases hy : y = 0
  · have hz : z ≠ 0 := by
      intro hz
      apply hx
      funext i
      refine Fin.addCases (m := 3) (n := 2) (fun j => ?_) (fun j => ?_) i
      · exact congrFun hz j
      · exact congrFun hy j
    obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
      by_contra! h
      exact hz (funext h)
    have hstrict : 0 < ∑ i, β i * z i ^ 2 :=
      Finset.sum_pos' (fun j _ => mul_nonneg (hβpos j).le (sq_nonneg (z j)))
        ⟨i, Finset.mem_univ i, mul_pos (hβpos i) (sq_pos_of_ne_zero hi)⟩
    have hBzero : kleinBudgetForm u t (B y) = 0 := by
      simp only [hy, map_zero, kleinBudgetForm, Pi.zero_apply,
        zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, Finset.sum_const_zero, add_zero]
    linarith only [hstrict, hBzero, hd0]
  · have hstrict : kleinBudgetForm u t (B y) < 0 := hB y hy
    linarith only [hz0, hd0, hstrict]

end
end MOC
