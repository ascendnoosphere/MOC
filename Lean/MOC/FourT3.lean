import MOC.FourT3Source
import MOC.ProjectivePole
import MOC.FourCoincidence
import MOC.TwoExceptions

/-! The order-four support inequality on the T3 contact set. -/

namespace MOC

private theorem t3LowerSupport_of_holds (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
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
/-- The T3 lower support bound holds for all order-four unitary eigenbases
when the prescribed six matchings make contact. Extra contacts are allowed. -/
theorem fourT3_support (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct a b (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourT3ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    H ≤ (η * determinantValue a b U).re := by
  by_cases hna : ¬ Function.Injective a
  · exact t3LowerSupport_of_holds a b η H U
      (holds_four_of_repeated_spectrum a b U hU (Or.inl hna)) hn
  have ha : Function.Injective a := not_not.mp hna
  by_cases hnb : ¬ Function.Injective b
  · exact t3LowerSupport_of_holds a b η H U
      (holds_four_of_repeated_spectrum a b U hU (Or.inr hnb)) hn
  have hb : Function.Injective b := not_not.mp hnb
  by_cases hnab : ¬ (∀ i j, a i + b j ≠ 0)
  · push_neg at hnab
    obtain ⟨i, j, hij⟩ := hnab
    exact t3LowerSupport_of_holds a b η H U (holds_four_of_opposite_entries a b U hU hij) hn
  have hab : ∀ i j, a i + b j ≠ 0 := not_not.mp hnab
  by_cases hη : η = 0
  · simpa [hη] using hn (0 : Fin 24)
  apply fourT3_support_of_budget a b η H hn hc U hU
  intro g hA
  obtain ⟨c, X, Y, hcn, hX₁, hX₂, hX, hY, hXY, hprod⟩ :=
    exists_projective_pole_chart a b 1 2 3 (by decide) ha hb hab
  let z := X 0
  let x := X 3
  let w := Y 0
  let v := Y 1
  let t := Y 2 / v
  let ξ := η * c
  let F := fourT3PoleProduct z x w v t
  have hξ : ξ ≠ 0 := mul_ne_zero hη hcn
  have hv : v ≠ 0 := by
    intro h
    exact hXY 1 1 (by decide) (hX₁.trans h.symm)
  have htv : t * v = Y 2 := div_mul_cancel₀ _ hv
  have hz : z ≠ 0 := by
    intro h
    exact (by decide : (0 : Fin 4) ≠ 1) (hX (h.trans hX₁.symm))
  have hz₁ : z ≠ 1 := by
    intro h
    exact (by decide : (0 : Fin 4) ≠ 2) (hX (h.trans hX₂.symm))
  have hzv : z ≠ v := hXY 0 1 (by decide)
  have hzw : z ≠ w := hXY 0 0 (by decide)
  have hvw : v ≠ w := fun h =>
    (by decide : (1 : Fin 4) ≠ 0) (hY (by decide) (by decide) h)
  have htx : x ≠ t * v := by rw [htv]; exact hXY 3 2 (by decide)
  have ht₀ : t ≠ 0 := by
    intro he
    have h : Y 2 = 0 := by rw [← htv, he, zero_mul]
    exact hXY 1 2 (by decide) (hX₁.trans h.symm)
  have ht₁ : t ≠ 1 := by
    intro he
    have h : Y 2 = Y 1 := by rw [← htv, he, one_mul] <;> rfl
    exact (by decide : (2 : Fin 4) ≠ 1) (hY (by decide) (by decide) h)
  have hx₁ : x ≠ 1 := by
    intro he
    exact (by decide : (3 : Fin 4) ≠ 2) (hX (he.trans hX₂.symm))
  have hX' : X = ![z, 0, 1, x] := by
    funext i
    fin_cases i <;> first | rfl | exact hX₁ | exact hX₂
  have hscale (i : Fin 24) : η * matchingProduct a b (fourPerm i).symm = ξ * F i := by
    rw [hprod, show (Finset.univ : Finset (Fin 4)).erase 3 = {0, 1, 2} by decide +kernel,
      Finset.prod_insert (by decide : (0 : Fin 4) ∉ ({1, 2} : Finset (Fin 4))),
      Finset.prod_insert (by decide : (1 : Fin 4) ∉ ({2} : Finset (Fin 4))), Finset.prod_singleton]
    dsimp only [F, fourT3PoleProduct, ξ]
    rw [htv, hX']
    dsimp only [w, v]
    ring
  have hpc : ∀ i ∈ ({0, 1, 2, 3, 7, 8} : Finset (Fin 24)), (ξ * F i).re = H := by
    intro i hi
    rw [← hscale i]
    exact hc i hi
  have hg' (i : Fin 24) : g i = (ξ * (F i - F 0)).re := by
    rw [mul_sub, Complex.sub_re, ← hscale i, ← hscale 0, hc 0 (by decide)]
    rfl
  obtain ⟨hti, hxi, hdir, r, u, _, _, hG, hK, hzEq, hwEq⟩ :=
    fourT3_normalized_chart z x w v t ξ H hz hz₁ hzv hzw hv hvw htx ht₀ ht₁ hx₁ hξ hpc
  have htC : (t.re : ℂ) = t := Complex.ext (by simp) (by simpa using hti.symm)
  have hxC : (x.re : ℂ) = x := Complex.ext (by simp) (by simpa using hxi.symm)
  have htR : t.re ≠ 0 := fun he => ht₀ (Complex.ext (by simpa using he) (by simpa using hti))
  have hcap := fourT3_projective_capacity x.re t.re r u z w v ξ hv hzw
  simp only [htC, hxC] at hcap
  have hh := hcap (sub_ne_zero.mpr htx) htR hG hK hzEq hwEq hdir
    (fun i => (hg' i) ▸ (sub_nonneg.mpr (hn i) : 0 ≤ g i))
    (by simpa only [← hg'] using fourT3_gap_twenty_one a b η H hc)
    (by simpa only [← hg'] using hA)
  simpa only [← hg'] using hh

end MOC
