import MOC.FourT15Minor
import MOC.FourT15Source
import MOC.ProjectivePole
import MOC.FourCoincidence
import MOC.TwoExceptions

/-! The order-four support inequality on the T15 contact set. -/

namespace MOC

set_option maxHeartbeats 2000000 in
/-- The T15 lower support bound holds for every order-four unitary
eigenbasis at the prescribed six contacts. Extra contacts are allowed. -/
theorem fourT15_support (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct a b (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourT15ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    H ≤ (η * determinantValue a b U).re := by
  by_cases hna : ¬ Function.Injective a
  · exact four_lower_support_of_holds a b η H U
      (holds_four_of_repeated_spectrum a b U hU (Or.inl hna)) hn
  have ha : Function.Injective a := not_not.mp hna
  by_cases hnb : ¬ Function.Injective b
  · exact four_lower_support_of_holds a b η H U
      (holds_four_of_repeated_spectrum a b U hU (Or.inr hnb)) hn
  have hb : Function.Injective b := not_not.mp hnb
  by_cases hnab : ¬ (∀ i j, a i + b j ≠ 0)
  · push_neg at hnab
    obtain ⟨i, j, hij⟩ := hnab
    exact four_lower_support_of_holds a b η H U (holds_four_of_opposite_entries a b U hU hij) hn
  have hab : ∀ i j, a i + b j ≠ 0 := not_not.mp hnab
  by_cases hη : η = 0
  · simpa [hη] using hn (0 : Fin 24)
  apply fourT15_support_of_budget a b η H hn hc U hU
  intro g d hd
  obtain ⟨c, X, Y, hcn, hX₂, hX₁, hX, hY, hXY, hprod⟩ :=
    exists_projective_pole_chart a b 2 1 2 (by decide) ha hb hab
  let z := X 0
  let x := X 3
  let w := Y 0
  let v := Y 1
  let t := Y 3 / v
  let ζ := η * c
  let ξ := -ζ
  let F := fourT5PoleProduct z x w v t
  have hζ : ζ ≠ 0 := mul_ne_zero hη hcn
  have hv : v ≠ 0 := by
    intro h
    exact hXY 2 1 (by decide) (hX₂.trans h.symm)
  have htv : t * v = Y 3 := div_mul_cancel₀ _ hv
  have hzw : z ≠ w := hXY 0 0 (by decide)
  have hw₁ : w ≠ 1 := fun he => hXY 1 0 (by decide) (hX₁.trans he.symm)
  have hwv : w ≠ v := fun h =>
    (by decide : (0 : Fin 4) ≠ 1) (hY (by decide) (by decide) h)
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
  have hscale (i : Fin 24) : η * matchingProduct a b (fourPerm i).symm = ζ * F i := by
    rw [hprod, show (Finset.univ : Finset (Fin 4)).erase 2 = {0, 1, 3} by decide +kernel,
      Finset.prod_insert (by decide : (0 : Fin 4) ∉ ({1, 3} : Finset (Fin 4))),
      Finset.prod_insert (by decide : (1 : Fin 4) ∉ ({3} : Finset (Fin 4))), Finset.prod_singleton]
    dsimp only [F, fourT5PoleProduct, ζ]
    rw [htv, hX']
    dsimp only [w, v]
    ring
  have hpc : ∀ i ∈ ({1, 2, 3, 4} : Finset (Fin 24)), (ζ * F i).re = H := by
    have hsub : ({1, 2, 3, 4} : Finset (Fin 24)) ⊆ fourT15ContactIndices := by decide
    intro i hi
    rw [← hscale i]
    exact hc i (hsub hi)
  have hg' (i : Fin 24) : g i = (ξ * (F 1 - F i)).re := by
    rw [show ξ * (F 1 - F i) = ζ * F i - ζ * F 1 by dsimp only [ξ]; ring,
      Complex.sub_re, ← hscale i, ← hscale 1, hc 1 (by decide)]
  obtain ⟨hti, hxi, hdir⟩ := fourT5_pole_line_parameters z x w v t ζ H hzw hv ht₁ hx₁ hζ hpc
  have hdir' : (ξ * (v * (z - w))).re = 0 := by simpa only [ξ, neg_mul, Complex.neg_re, neg_eq_zero] using hdir
  have htC : (t.re : ℂ) = t := Complex.ext (by simp) (by simpa using hti.symm)
  have hxC : (x.re : ℂ) = x := Complex.ext (by simp) (by simpa using hxi.symm)
  have htR : t.re ≠ 0 := fun he => ht₀ (Complex.ext (by simpa using he) (by simpa using hti))
  have hcap := fourT15_projective_capacity x.re t.re z w v ξ hv hw₁ hwv hzw htR
  simp only [htC, hxC] at hcap
  obtain ⟨h11, h19⟩ := fourT15_gap_eleven_nineteen a b η H hc
  have h6 : g 6 = 0 := sub_eq_zero.mpr (hc 6 (by decide))
  have h7 : g 7 = 0 := sub_eq_zero.mpr (hc 7 (by decide))
  have h := hcap (sub_ne_zero.mpr htx) hdir'
    (fun i => (hg' i) ▸ (sub_nonneg.mpr (hn i) : 0 ≤ g i))
    (by simpa only [← hg'] using h6) (by simpa only [← hg'] using h7)
    (by simpa only [← hg'] using h11) (by simpa only [← hg'] using h19)
    (by dsimp only [d] at hd; simpa only [← hg'] using hd)
  simpa only [← hg', d] using h

end MOC
