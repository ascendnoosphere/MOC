import MOC.ZhengStabilizerSupport
import MOC.FractionalFiniteNormalization
import MOC.RealizableContactConsequences
import MOC.TwoExceptions

/-! Direct algebra for T1 in Zheng, DOI 10.13140/RG.2.2.36790.25923.
The normalized cross ratios recover the real spectator chart without a
classification of contact cones. -/

open BigOperators Matrix

namespace MOC.ZhengT1

noncomputable section

abbrev Perm4 := Equiv.Perm (Fin 4)
def s₁ : Perm4 := Equiv.swap 2 3
def s₂ : Perm4 := Equiv.swap 1 2
def s₃ : Perm4 := Equiv.swap 1 2 * Equiv.swap 1 3
def s₆ : Perm4 := Equiv.swap 0 1
def s₇ : Perm4 := s₁*s₆

private def P (a c : Fin 4 → ℂ) (p : Perm4) : ℂ :=
  matchingProduct a (fun i => -c i) p

private theorem product_one (a c : Fin 4 → ℂ) :
    P a c 1 = (a 0-c 0)*(a 1-c 1)*(a 2-c 2)*(a 3-c 3) := by
  simp [P,matchingProduct,Fin.prod_univ_four,sub_eq_add_neg]

private theorem three_swap_factors (a c : Fin 4 → ℂ) :
    (P a c s₁ - P a c 1 =
      (a 0-c 0)*(a 1-c 1)*(a 2-a 3)*(c 3-c 2)) ∧
    (P a c s₃ - P a c s₂ =
      (a 0-c 0)*(a 1-c 2)*(a 2-a 3)*(c 3-c 1)) ∧
    (P a c s₂ - P a c 1 =
      (a 0-c 0)*(a 3-c 3)*(a 1-a 2)*(c 2-c 1)) := by
  simp [P,matchingProduct,Fin.prod_univ_four,s₁,s₂,s₃,Equiv.Perm.mul_apply,Equiv.swap_apply_def]
  exact ⟨by ring,by ring,by ring⟩

private theorem product_s₁ (a c : Fin 4 → ℂ) :
    P a c s₁ = (a 0-c 0)*(a 1-c 1)*(a 2-c 3)*(a 3-c 2) := by
  simp [P,matchingProduct,Fin.prod_univ_four,s₁,Equiv.swap_apply_def,sub_eq_add_neg]
  ring

private theorem real_div_of_real {p q : ℂ} (hp : p.im = 0) (hq : q.im = 0) :
    (p/q).im = 0 := by
  simp [Complex.div_im,hp,hq]

private theorem real_ratio {η p q : ℂ} (hη : η ≠ 0)
    (hp : (η*p).re = 0) (hq : (η*q).re = 0) : (p/q).im = 0 := by
  have he : p/q = (η*p)/(η*q) := by
    rw [mul_div_mul_left _ _ hη]
  rw [he,Complex.div_im,hp,hq]
  simp

private theorem real_from_product {a b : ℂ} (ha : a.im = 0) (hn : a ≠ 0)
    (h : (a*b).im = 0) : b.im = 0 := by
  have har : a.re ≠ 0 := fun e => hn (Complex.ext (by simpa using e) (by simpa using ha))
  simp only [Complex.mul_im,ha,zero_mul,add_zero] at h
  exact (mul_eq_zero.mp h).resolve_left har

private theorem real_difference_ratio {z s t : ℂ}
    (hs : s.im = 0) (ht : t.im = 0) (hst : s ≠ t) (hzt : z ≠ t)
    (h : ((z-s)/(z-t)).im = 0) : z.im = 0 := by
  let q := (z-s)/(z-t)
  have hq : q*(z-t)=z-s := div_mul_cancel₀ _ (sub_ne_zero.mpr hzt)
  have hqi := congrArg Complex.im hq
  change q.im = 0 at h
  simp only [Complex.mul_im,Complex.sub_im,hs,ht,h,sub_zero,zero_mul,add_zero] at hqi
  by_contra hz
  have har : q.re = 1 := by
    apply mul_right_cancel₀ hz
    simpa using hqi
  have he : q = 1 := Complex.ext (by simpa using har) (by simpa using h)
  have hc : z-t=z-s := by simpa [he] using hq
  exact hst (by linear_combination hc)

private theorem real_mul {z w : ℂ} (hz : z.im = 0) (hw : w.im = 0) :
    (z*w).im = 0 := by simp [Complex.mul_im,hz,hw]

private theorem spectator_cross_ratios (a c : Fin 4 → ℂ)
    (ha : Function.Injective a) (hc : Function.Injective c)
    (hn : ∀ i j, a i ≠ c j) (η : ℂ) (hη : η ≠ 0)
    (h₁ : (c 1).im = 0) (h₂ : (c 2).im = 0) (h₃ : (c 3).im = 0)
    (z₀ : (η*P a c 1).re = 0) (z₁ : (η*P a c s₁).re = 0)
    (z₂ : (η*P a c s₂).re = 0) (z₃ : (η*P a c s₃).re = 0) :
    (a 1).im = 0 ∧ (a 2).im = 0 ∧ (a 3).im = 0 := by
  obtain ⟨f₁,f₂,f₃⟩ := three_swap_factors a c
  have ha12 : a 1 ≠ a 2 := ha.ne (by decide)
  have ha23 : a 2 ≠ a 3 := ha.ne (by decide)
  have hc12 : c 1 ≠ c 2 := hc.ne (by decide)
  have hc13 : c 1 ≠ c 3 := hc.ne (by decide)
  have hc23 : c 2 ≠ c 3 := hc.ne (by decide)
  have real_of_contacts {p q : Perm4} (hp : (η*P a c p).re = 0)
      (hq : (η*P a c q).re = 0) : (η*(P a c p-P a c q)).re = 0 := by
    simp [mul_sub,Complex.sub_re,hp,hq]
  have R₁ := real_ratio hη (real_of_contacts z₃ z₂) (real_of_contacts z₁ z₀)
  have R₂ := real_ratio hη (real_of_contacts z₂ z₀) (real_of_contacts z₁ z₀)
  have R₃ := real_ratio hη z₁ z₀
  rw [f₂,f₁,show
    ((a 0-c 0)*(a 1-c 2)*(a 2-a 3)*(c 3-c 1)) /
        ((a 0-c 0)*(a 1-c 1)*(a 2-a 3)*(c 3-c 2))
    = ((c 3-c 1)/(c 3-c 2))*((a 1-c 2)/(a 1-c 1)) by
      field_simp [sub_ne_zero.mpr (hn 0 0),sub_ne_zero.mpr (hn 1 1),
        sub_ne_zero.mpr ha23,sub_ne_zero.mpr hc23.symm]
      ring] at R₁
  have hreal (p q : ℂ) (hp : p.im = 0) (hq : q.im = 0) : (p-q).im = 0 := by
    simp [Complex.sub_im,hp,hq]
  have a₁ := real_difference_ratio h₂ h₁ hc12.symm (hn 1 1)
    (real_from_product (real_div_of_real (hreal (c 3) (c 1) h₃ h₁) (hreal (c 3) (c 2) h₃ h₂))
      (div_ne_zero (sub_ne_zero.mpr hc13.symm) (sub_ne_zero.mpr hc23.symm)) R₁)
  let M (z : ℂ) := (z-c 2)/(z-c 3)
  let X := M (a 2)
  let Y := M (a 3)
  let Z := M (a 1)
  have hZ : Z.im = 0 := real_div_of_real (hreal _ _ a₁ h₂) (hreal _ _ a₁ h₃)
  have hZn : Z ≠ 0 := div_ne_zero (sub_ne_zero.mpr (hn 1 2)) (sub_ne_zero.mpr (hn 1 3))
  have hXn : X ≠ 0 := div_ne_zero (sub_ne_zero.mpr (hn 2 2)) (sub_ne_zero.mpr (hn 2 3))
  have mdiff (p q : ℂ) (hp : p ≠ c 3) (hq : q ≠ c 3) :
      M p-M q = (c 2-c 3)*(p-q)/((p-c 3)*(q-c 3)) := by
    dsimp only [M]
    field_simp [sub_ne_zero.mpr hp,sub_ne_zero.mpr hq]
    ring
  have eXY : X-Y = (c 2-c 3)*(a 2-a 3)/((a 2-c 3)*(a 3-c 3)) :=
    mdiff _ _ (hn 2 3) (hn 3 3)
  have eZX : Z-X = (c 2-c 3)*(a 1-a 2)/((a 1-c 3)*(a 2-c 3)) :=
    mdiff _ _ (hn 1 3) (hn 2 3)
  have hXY : X-Y ≠ 0 := by
    rw [eXY]
    exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr hc23) (sub_ne_zero.mpr ha23))
      (mul_ne_zero (sub_ne_zero.mpr (hn 2 3)) (sub_ne_zero.mpr (hn 3 3)))
  have eS' : (Z-X)/(X-Y) =
      ((a 1-a 2)*(a 3-c 3))/((a 1-c 3)*(a 2-a 3)) := by
    rw [eZX,eXY]
    field_simp [sub_ne_zero.mpr hc23,sub_ne_zero.mpr ha23,
      sub_ne_zero.mpr (hn 1 3),sub_ne_zero.mpr (hn 2 3),sub_ne_zero.mpr (hn 3 3)]
    ring
  have hS : ((Z-X)/(X-Y)).im = 0 := by
    rw [f₃,f₁,show
      ((a 0-c 0)*(a 3-c 3)*(a 1-a 2)*(c 2-c 1)) /
        ((a 0-c 0)*(a 1-c 1)*(a 2-a 3)*(c 3-c 2)) =
      (((c 2-c 1)*(a 1-c 3))/((c 3-c 2)*(a 1-c 1)))*((Z-X)/(X-Y)) by
        rw [eS']
        field_simp [sub_ne_zero.mpr (hn 0 0),sub_ne_zero.mpr (hn 1 1),
          sub_ne_zero.mpr (hn 1 3),sub_ne_zero.mpr ha23,sub_ne_zero.mpr hc23.symm]
        ring] at R₂
    apply real_from_product _ _ R₂
    · exact real_div_of_real (real_mul (hreal _ _ h₂ h₁) (hreal _ _ a₁ h₃))
        (real_mul (hreal _ _ h₃ h₂) (hreal _ _ a₁ h₁))
    · exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr hc12.symm) (sub_ne_zero.mpr (hn 1 3)))
        (mul_ne_zero (sub_ne_zero.mpr hc23.symm) (sub_ne_zero.mpr (hn 1 1)))
  have hT : (Y/X).im = 0 := by
    rw [product_s₁,product_one,show
      ((a 0-c 0)*(a 1-c 1)*(a 2-c 3)*(a 3-c 2)) /
        ((a 0-c 0)*(a 1-c 1)*(a 2-c 2)*(a 3-c 3)) = Y/X by
        dsimp [Y,X,M]
        field_simp [sub_ne_zero.mpr (hn 0 0),sub_ne_zero.mpr (hn 1 1),
          sub_ne_zero.mpr (hn 2 3),sub_ne_zero.mpr (hn 2 2),sub_ne_zero.mpr (hn 3 3)]
        ring] at R₃
    exact R₃
  let T := Y/X
  let S := (Z-X)/(X-Y)
  have eT : T*X = Y := div_mul_cancel₀ _ hXn
  have eS : S*(X-Y) = Z-X := div_mul_cancel₀ _ hXY
  let K := 1+S*(1-T)
  have eK : K*X = Z := by
    dsimp only [K]
    calc
      _ = X+S*(X-T*X) := by ring
      _ = Z := by rw [eT,eS]; ring
  have hk : K.im = 0 := by
    change S.im = 0 at hS
    change T.im = 0 at hT
    simp [K,Complex.add_im,Complex.mul_im,Complex.sub_im,hS,hT]
  have hkn : K ≠ 0 := fun e => hZn (by simpa [e] using eK.symm)
  have hX : X.im = 0 := real_from_product hk hkn (by rw [eK,hZ])
  have hY : Y.im = 0 := by rw [←eT]; exact real_mul hT hX
  exact ⟨a₁,real_difference_ratio h₂ h₃ hc23 (hn 2 3) hX,
    real_difference_ratio h₂ h₃ hc23 (hn 3 3) hY⟩

/-- The entire T1 pattern has the order-four determinant support bound.
The proof uses the projective spectator chart and the zero-pair common
weights, independently of the contact-cone classification. -/
theorem support (a c : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (η : ℂ) (H : ℝ)
    (h₀ : (η*P a c 1).re = H) (h₁ : (η*P a c s₁).re = H)
    (h₂ : (η*P a c s₂).re = H) (h₃ : (η*P a c s₃).re = H)
    (h₆ : (η*P a c s₆).re = H) (h₇ : (η*P a c s₇).re = H)
    (hs : ∀ p, (η*P a c p).re ≤ H) :
    (η*determinantValue a (fun i => -c i) U).re ≤ H := by
  classical
  let b : Fin 4 → ℂ := fun i => -c i
  by_cases hη : η = 0
  · simp [hη] at h₀ ⊢
    exact h₀.le
  have from_holds (h : Holds a b U) :
      (η*determinantValue a b U).re ≤ H := by
    obtain ⟨p,hp⟩ := (holds_iff_directional _ _ _).mp h η
    exact hp.trans (hs p)
  by_cases hrep : ¬ Function.Injective a ∨ ¬ Function.Injective b
  · exact from_holds (holds_four_of_repeated_spectrum _ _ _ hU hrep)
  have ha : Function.Injective a := not_or.mp hrep |>.1 |> not_not.mp
  have hb : Function.Injective b := not_or.mp hrep |>.2 |> not_not.mp
  have hc : Function.Injective c := fun _ _ e => hb (congrArg Neg.neg e)
  by_cases hcoin : ∃ i j, a i = c j
  · obtain ⟨i,j,e⟩ := hcoin
    exact from_holds (holds_four_of_opposite_entries a b U hU
      (show a i+b j = 0 by simp [b,e]))
  have hn (i j : Fin 4) : a i ≠ c j := fun e => hcoin ⟨i,j,e⟩
  have mpn (p : Perm4) : matchingProduct a b p ≠ 0 := by
    unfold matchingProduct
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro j _
    simpa [b,sub_eq_add_neg] using sub_ne_zero.mpr (hn (p j) j)
  have hdisj (i : Fin 4) : Equiv.swap (2 : Fin 4) 3 i = i ∨ Equiv.swap 0 1 i = i := by
    fin_cases i <;> simp [Equiv.swap_apply_def]
  have hH : H = 0 := by
    apply matchingProduct_disjoint_swap_rectangle_height_zero_of_simple a b ha hb mpn
      1 2 3 0 1 (by decide) (by decide) hdisj η hη H h₀
    · simpa [P,b,s₁] using h₁
    · simpa [P,b,s₆] using h₆
    · simpa [P,b,s₇,s₁,s₆] using h₇
  rw [hH] at h₀ h₁ h₂ h₃ hs ⊢
  let T : Set ℂ := Set.range a ∪ Set.range c
  obtain ⟨α,β,γ,δ,hdet,havoid,t₁,t₂,R,_,t₃⟩ :=
    exists_pole_avoiding_three_point_approximation T
      ((Set.finite_range a).union (Set.finite_range c))
      (c 1) (c 2) (c 3) (hc.ne (by decide)) (hc.ne (by decide)) (hc.ne (by decide)) 0
  let f := fractionalMap α β γ δ
  let a' := f ∘ a
  let c' := f ∘ c
  have hna (i : Fin 4) : γ*a i+δ ≠ 0 := havoid _ (Or.inl ⟨i,rfl⟩)
  have hnc (i : Fin 4) : γ*c i+δ ≠ 0 := havoid _ (Or.inr ⟨i,rfl⟩)
  obtain ⟨K,hK,hp,hd⟩ := exists_fractional_factor a b U hU α β γ δ hdet hna
    (fun i => by simpa [b] using hnc i)
  let η' := η/K
  have hη' : η' ≠ 0 := div_ne_zero hη hK
  have eqP (p : Perm4) : η'*P a' c' p = η*P a c p := by
    have ee : P a' c' p = K*P a c p := by
      simpa [P,a',c',f,b] using hp p
    rw [ee]
    dsimp [η']
    field_simp [hK]
    ring
  have hfi := fractionalMap_injOn α β γ δ hdet
  have ha' : Function.Injective a' := fun i j e => ha
    (hfi (by exact hna i) (by exact hna j) e)
  have hc' : Function.Injective c' := fun i j e => hc
    (hfi (by exact hnc i) (by exact hnc j) e)
  have hn' (i j : Fin 4) : a' i ≠ c' j := fun e => hn i j
    (hfi (by exact hna i) (by exact hnc j) e)
  have c₁ : (c' 1).im = 0 := by simp [c',f,t₁]
  have c₂ : (c' 2).im = 0 := by simp [c',f,t₂]
  have c₃ : (c' 3).im = 0 := by simp [c',f,t₃]
  obtain ⟨a₁,a₂,a₃⟩ := spectator_cross_ratios a' c' ha' hc' hn' η' hη' c₁ c₂ c₃
    (by rwa [eqP]) (by rwa [eqP]) (by rwa [eqP]) (by rwa [eqP])
  have hspeca (i : Fin 4) (hi : i ≠ 0) : (a' i).im = 0 := by
    fin_cases i
    · exact (hi rfl).elim
    · exact a₁
    · exact a₂
    · exact a₃
  have hspecc (i : Fin 4) (hi : i ≠ 0) : (-c' i).im = 0 := by
    rw [Complex.neg_im,neg_eq_zero]
    fin_cases i
    · exact (hi rfl).elim
    · exact c₁
    · exact c₂
    · exact c₃
  let S := (a' 1-c' 1)*(a' 2-c' 2)*(a' 3-c' 3)
  have hS : S.im = 0 := by
    dsimp only [S]
    apply real_mul
    · apply real_mul <;> simp [Complex.sub_im,a₁,a₂,c₁,c₂]
    · simp [Complex.sub_im,a₃,c₃]
  have hnS : S ≠ 0 := mul_ne_zero
    (mul_ne_zero (sub_ne_zero.mpr (hn' 1 1)) (sub_ne_zero.mpr (hn' 2 2)))
    (sub_ne_zero.mpr (hn' 3 3))
  have hrS : S.re ≠ 0 := fun e => hnS (Complex.ext (by simpa using e) (by simpa using hS))
  have hOut : (η'*(a' 0 + -c' 0)).re = 0 := by
    have e : η'*P a' c' 1 = (η'*(a' 0 + -c' 0))*S := by
      rw [product_one]
      dsimp only [S]
      ring
    have he := congrArg Complex.re e
    rw [eqP,h₀,Complex.mul_re,hS,mul_zero,sub_zero] at he
    exact (mul_eq_zero.mp he.symm).resolve_right hrS
  have hq := four_real_spectators_zero_height_support U hU a' (fun i => -c' i) η'
    hspeca hspecc hOut (fun p => by
      change (η'*P a' c' p).re ≤ 0
      rw [eqP]
      exact hs p)
  have ed : determinantValue a' (fun i => -c' i) U = K*determinantValue a b U := by
    simpa [a',c',f,b] using hd
  rw [ed,show η'*(K*determinantValue a b U) = η*determinantValue a b U by
    dsimp [η']
    field_simp [hK]
    ring] at hq
  exact hq

end
end MOC.ZhengT1
