import MOC.FourT5Minor
import MOC.FourT5Source
import MOC.ProjectivePole
import MOC.FourCoincidence
import MOC.TwoExceptions

/-! The order-four support inequality on the T5 contact set. -/

namespace MOC

private theorem t5LowerSupport_of_holds (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (h : Holds a b U)
    (hn : ∀ i, H ≤ (η * matchingProduct a b (fourPerm i).symm).re) :
    H ≤ (η * determinantValue a b U).re := by
  obtain ⟨σ, hσ⟩ := (holds_iff_directional a b U).mp h (-η)
  obtain ⟨i, hi⟩ := fourPerm_surjective σ.symm
  have hi' : (fourPerm i).symm = σ := by simp [hi]
  have he := hn i
  rw [hi'] at he
  simp only [neg_mul, Complex.neg_re, neg_le_neg_iff] at hσ
  exact he.trans hσ

set_option maxHeartbeats 2000000 in
/-- The T5 lower support bound holds for every order-four unitary eigenbasis
when the prescribed six matchings make contact. Extra contacts are allowed. -/
theorem fourT5_support (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct a b (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourT5ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    H ≤ (η * determinantValue a b U).re := by
  by_cases hna : ¬ Function.Injective a
  · exact t5LowerSupport_of_holds a b η H U
      (holds_four_of_repeated_spectrum a b U hU (Or.inl hna)) hn
  have ha : Function.Injective a := not_not.mp hna
  by_cases hnb : ¬ Function.Injective b
  · exact t5LowerSupport_of_holds a b η H U
      (holds_four_of_repeated_spectrum a b U hU (Or.inr hnb)) hn
  have hb : Function.Injective b := not_not.mp hnb
  by_cases hnab : ¬ (∀ i j, a i + b j ≠ 0)
  · push_neg at hnab
    obtain ⟨i, j, hij⟩ := hnab
    exact t5LowerSupport_of_holds a b η H U (holds_four_of_opposite_entries a b U hU hij) hn
  have hab : ∀ i j, a i + b j ≠ 0 := not_not.mp hnab
  by_cases hη : η = 0
  · simpa [hη] using hn (0 : Fin 24)
  apply fourT5_support_of_capacity a b η H hn hc U hU
  intro g d hd
  obtain ⟨c, X, Y, hcn, hX₂, hX₁, hX, hY, hXY, hprod⟩ :=
    exists_projective_pole_chart a b 2 1 2 (by decide) ha hb hab
  let z := X 0
  let x := X 3
  let w := Y 0
  let v := Y 1
  let t := Y 3 / v
  let ξ := η * c
  let F := fourT5PoleProduct z x w v t
  have hξ : ξ ≠ 0 := mul_ne_zero hη hcn
  have hv : v ≠ 0 := by
    intro h
    exact hXY 2 1 (by decide) (hX₂.trans h.symm)
  have htv : t * v = Y 3 := div_mul_cancel₀ _ hv
  have hz : z ≠ 0 := by
    intro h
    exact (by decide : (0 : Fin 4) ≠ 2) (hX (h.trans hX₂.symm))
  have hzv : z ≠ v := hXY 0 1 (by decide)
  have hzw : z ≠ w := hXY 0 0 (by decide)
  have hvw : v ≠ w := fun h =>
    (by decide : (1 : Fin 4) ≠ 0) (hY (by decide) (by decide) h)
  have htx : x ≠ t * v := by rw [htv]; exact hXY 3 3 (by decide)
  have ht₀ : t ≠ 0 := by
    intro he
    have h : Y 3 = 0 := by rw [← htv, he, zero_mul]
    exact hXY 2 3 (by decide) (hX₂.trans h.symm)
  have ht₁ : t ≠ 1 := by
    intro he
    have h : Y 3 = Y 1 := by rw [← htv, he, one_mul] <;> rfl
    exact (by decide : (3 : Fin 4) ≠ 1) (hY (by decide) (by decide) h)
  have hx₁ : x ≠ 1 := by
    intro he
    exact (by decide : (3 : Fin 4) ≠ 1) (hX (he.trans hX₁.symm))
  have hX' : X = ![z, 1, 0, x] := by
    funext i
    fin_cases i <;> first | rfl | exact hX₁ | exact hX₂
  have hscale (i : Fin 24) : η * matchingProduct a b (fourPerm i).symm = ξ * F i := by
    rw [hprod, show (Finset.univ : Finset (Fin 4)).erase 2 = {0, 1, 3} by decide +kernel,
      Finset.prod_insert (by decide : (0 : Fin 4) ∉ ({1, 3} : Finset (Fin 4))),
      Finset.prod_insert (by decide : (1 : Fin 4) ∉ ({3} : Finset (Fin 4))), Finset.prod_singleton]
    dsimp only [F, fourT5PoleProduct, ξ]
    rw [htv, hX']
    dsimp only [w, v]
    ring
  have hpc : ∀ i ∈ ({1, 2, 3, 4, 6, 8} : Finset (Fin 24)), (ξ * F i).re = H := by
    intro i hi
    rw [← hscale i]
    exact hc i hi
  have hg' (i : Fin 24) : g i = (ξ * (F i - F 1)).re := by
    rw [mul_sub, Complex.sub_re, ← hscale i, ← hscale 1, hc 1 (by decide)]
    rfl
  obtain ⟨hti, hxi, hdir, r, u, hr, hu, hG, hP, hzEq, hwEq⟩ :=
    fourT5_normalized_chart z x w v t ξ H hz hzv hzw hv hvw htx ht₁ hx₁ hξ hpc
  have htC : (t.re : ℂ) = t := Complex.ext (by simp) (by simpa using hti.symm)
  have hxC : (x.re : ℂ) = x := Complex.ext (by simp) (by simpa using hxi.symm)
  have htR : t.re ≠ 0 := fun he => ht₀ (Complex.ext (by simpa using he) (by simpa using hti))
  have htR₁ : t.re ≠ 1 := fun he => ht₁ (Complex.ext (by simpa using he) (by simpa using hti))
  have hcap := fourT5_projective_capacity x.re t.re r u z w v ξ hv htR htR₁
    (Complex.ofReal_ne_zero.mp hr) (Complex.ofReal_ne_zero.mp hu) hzw
  simp only [htC, hxC] at hcap
  obtain ⟨h11, h17⟩ := fourT5_gap_eleven_seventeen a b η H hc
  have hA : g 16 - g 0 < 0 := by dsimp only [d] at hd; linarith only [hd]
  have hh := hcap (sub_ne_zero.mpr htx) hG hP hzEq hwEq hdir
    (fun i => (hg' i) ▸ (sub_nonneg.mpr (hn i) : 0 ≤ g i))
    (by simpa only [← hg'] using h11) (by simpa only [← hg'] using h17) (by simpa only [← hg'] using hA)
  simp only [← hg'] at hh
  rcases hh with hh | hh
  · left
    convert hh using 1 <;> dsimp only [d] <;> ring
  · right
    convert hh using 1 <;> dsimp only [d] <;> ring

end MOC
