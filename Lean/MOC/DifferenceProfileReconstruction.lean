import MOC.MatchingQuartet
import MOC.Weights
import MOC.Small
import MOC.GeneralContactReduction

/-! Exact pivot differences determine every possible strict matching profile.
This uses a nonzero disjoint-swap rectangle, not genericity of the spectra. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem exists_outside_three (hcard : 4 ≤ Fintype.card ι) (i j k : ι) :
    ∃ l : ι, l ≠ i ∧ l ≠ j ∧ l ≠ k := by
  classical
  by_contra! h
  have hall : (Finset.univ : Finset ι) ⊆ {i, j, k} := by
    intro l _
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hi : l = i
    · exact Or.inl hi
    by_cases hj : l = j
    · exact Or.inr (Or.inl hj)
    exact Or.inr (Or.inr (h l hi hj))
  have hb := Finset.card_le_card hall
  have hc : ({i, j, k} : Finset ι).card ≤ 3 := by
    have h₁ := Finset.card_insert_le i ({j, k} : Finset ι)
    have h₂ := Finset.card_insert_le j ({k} : Finset ι)
    simp only [Finset.card_singleton] at h₂
    omega
  rw [Finset.card_univ] at hb
  omega

omit [Fintype ι] [DecidableEq ι] in
private theorem const_off_of_not_edge {A B : Type*}
    (h₀ : Nonempty ι) (a : ι → A) (b : ι → B) (c : ι)
    (h : ∀ x y, x ≠ c → y ≠ c → ¬ (a x ≠ a y ∧ b x ≠ b y)) :
    (∃ z, ∀ x, x ≠ c → a x = z) ∨ (∃ z, ∀ x, x ≠ c → b x = z) := by
  classical
  by_cases hdiff : ∃ x y, x ≠ c ∧ y ≠ c ∧ a x ≠ a y
  · obtain ⟨x, y, hx, hy, hxy⟩ := hdiff
    have hbxy : b x = b y := not_ne_iff.mp (fun hb => h x y hx hy ⟨hxy, hb⟩)
    refine Or.inr ⟨b x, fun z hzc => ?_⟩
    by_contra! hzx
    have hzya : b z ≠ b y := by simpa only [← hbxy] using hzx
    have ha₁ : a z = a x := not_ne_iff.mp (fun ha => h z x hzc hx ⟨ha, hzx⟩)
    have ha₂ : a z = a y := not_ne_iff.mp (fun ha => h z y hzc hy ⟨ha, hzya⟩)
    exact hxy (ha₁.symm.trans ha₂)
  · by_cases hxc : ∃ x, x ≠ c
    · obtain ⟨x, hx⟩ := hxc
      exact Or.inl ⟨a x, fun y hy => not_ne_iff.mp (fun hxy => hdiff ⟨y, x, hy, hx, hxy⟩)⟩
    · exact Or.inl ⟨a (Classical.choice h₀), fun y hy => (hxc ⟨y, hy⟩).elim⟩

omit [DecidableEq ι] in
private theorem one_outlier_or_disjoint_edges {A B : Type*}
    (hcard : 4 ≤ Fintype.card ι) (a : ι → A) (b : ι → B) :
    (∃ c z, ∀ x, x ≠ c → a x = z) ∨ (∃ c z, ∀ x, x ≠ c → b x = z) ∨
      ∃ i j k l, i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧
        a i ≠ a j ∧ b i ≠ b j ∧ a k ≠ a l ∧ b k ≠ b l := by
  classical
  have h₀ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  let E := fun i j => a i ≠ a j ∧ b i ≠ b j
  have hsymm {x y} : E x y → E y x := fun h => ⟨h.1.symm, h.2.symm⟩
  have hne {x y} : E x y → x ≠ y := fun h he => h.1 (congrArg a he)
  by_cases hdis : ∃ i j k l, i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧
      k ≠ l ∧ E i j ∧ E k l
  · obtain ⟨i, j, k, l, h₁, h₂, h₃, h₄, h₅, h₆, he, hf⟩ := hdis
    exact Or.inr (Or.inr ⟨i, j, k, l, h₁, h₂, h₃, h₄, h₅, h₆, he.1, he.2, hf.1, hf.2⟩)
  have hinter {i j k l} (hij : E i j) (hkl : E k l) :
      i = k ∨ i = l ∨ j = k ∨ j = l := by
    by_contra! h
    exact hdis ⟨i, j, k, l, hne hij, h.1, h.2.1, h.2.2.1, h.2.2.2, hne hkl, hij, hkl⟩
  have htri {i j k} (hij : E i j) (hik : E i k) (hjk : E j k) : False := by
    obtain ⟨l, hli, hlj, hlk⟩ := exists_outside_three hcard i j k
    have hi : ¬ E l i := by
      intro he
      rcases hinter he hjk with h | h | h | h
      · exact hlj h
      · exact hlk h
      · exact hne hij h
      · exact hne hik h
    have hj : ¬ E l j := by
      intro he
      rcases hinter he hik with h | h | h | h
      · exact hli h
      · exact hlk h
      · exact hne hij h.symm
      · exact hne hjk h
    have hk : ¬ E l k := by
      intro he
      rcases hinter he hij with h | h | h | h
      · exact hli h
      · exact hlj h
      · exact hne hik h.symm
      · exact hne hjk h.symm
    dsimp [E] at hi hj hk
    push_neg at hi hj hk
    have hor (s : ι) (h : a l ≠ a s → b l = b s) : a l = a s ∨ b l = b s := by
      by_cases he : a l = a s
      · exact Or.inl he
      · exact Or.inr (h he)
    rcases hor i hi with hai | hbi <;> rcases hor j hj with haj | hbj <;>
      rcases hor k hk with hak | hbk
    all_goals first
      | exact hij.1 (hai.symm.trans haj)
      | exact hik.1 (hai.symm.trans hak)
      | exact hjk.1 (haj.symm.trans hak)
      | exact hij.2 (hbi.symm.trans hbj)
      | exact hik.2 (hbi.symm.trans hbk)
      | exact hjk.2 (hbj.symm.trans hbk)
  have hcenter : ∃ c, ∀ x y, x ≠ c → y ≠ c → ¬ E x y := by
    by_cases hE : ∃ i j, E i j
    · obtain ⟨i, j, hij⟩ := hE
      by_cases histar : ∀ x y, x ≠ i → y ≠ i → ¬ E x y
      · exact ⟨i, histar⟩
      push_neg at histar
      obtain ⟨x, y, hxi, hyi, hxy⟩ := histar
      have hjk : ∃ k, k ≠ i ∧ E j k := by
        rcases hinter hij hxy with h | h | h | h
        · exact (hxi h.symm).elim
        · exact (hyi h.symm).elim
        · exact ⟨y, hyi, h ▸ hxy⟩
        · exact ⟨x, hxi, h ▸ hsymm hxy⟩
      obtain ⟨k, hki, hjk⟩ := hjk
      refine ⟨j, fun u v huj hvj huv => ?_⟩
      have hui : u = i ∨ v = i := by
        rcases hinter hij huv with h | h | h | h
        · exact Or.inl h.symm
        · exact Or.inr h.symm
        · exact (huj h.symm).elim
        · exact (hvj h.symm).elim
      have huk : u = k ∨ v = k := by
        rcases hinter hjk huv with h | h | h | h
        · exact (huj h.symm).elim
        · exact (hvj h.symm).elim
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      rcases hui with rfl | rfl
      · rcases huk with h | rfl
        · exact hki h.symm
        · exact htri hij huv hjk
      · rcases huk with rfl | h
        · exact htri hij (hsymm huv) hjk
        · exact hki h.symm
    · exact ⟨Classical.choice h₀, fun x y _ _ hxy => hE ⟨x, y, hxy⟩⟩
  obtain ⟨c, hc⟩ := hcenter
  rcases const_off_of_not_edge h₀ a b c hc with ⟨z, hz⟩ | ⟨z, hz⟩
  · exact Or.inl ⟨c, z, hz⟩
  · exact Or.inr (Or.inl ⟨c, z, hz⟩)

/-- A strict profile in arbitrary order at least four has a nonzero mixed
difference on a disjoint-swap rectangle. Opposite pairs are allowed. -/
theorem exists_matching_quartet_of_not_holds
    (hcard : 4 ≤ Fintype.card ι) (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (hbad : ¬ Holds a b U) :
    ∃ σ : Equiv.Perm ι, ∃ i j k l, i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧
      matchingProduct a b σ + matchingProduct a b (σ * Equiv.swap i j * Equiv.swap k l) -
        matchingProduct a b (σ * Equiv.swap i j) - matchingProduct a b (σ * Equiv.swap k l) ≠ 0 := by
  classical
  have hn : ∃ σ, matchingProduct a b σ ≠ 0 := by
    by_contra! hz
    have hd : determinantValue a b U = 0 := by
      rw [← signed_determinant a b U hU]
      simp only [hz, mul_zero, Finset.sum_const_zero]
    apply hbad
    unfold Holds
    rw [hd, ← hz 1]
    exact subset_convexHull ℝ _ ⟨1, rfl⟩
  obtain ⟨σ, hσ⟩ := hn
  rcases one_outlier_or_disjoint_edges hcard (a ∘ σ) b with
    ⟨c, z, hc⟩ | ⟨c, z, hc⟩ | ⟨i, j, k, l, hij, hik, hil, hjk, hjl, hkl, haij, hbij, hakl, hbkl⟩
  · have ha : ∀ x, x ≠ σ c → a x = z := by
      intro x hx
      have hsx : σ.symm x ≠ c := by
        intro he
        apply hx
        rw [← he, Equiv.apply_symm_apply]
      have hh := hc (σ.symm x) hsx
      simpa using hh
    have hUs : IsUnitary Uᴴ := ⟨by simpa using hU.2, by simpa using hU.1⟩
    exact (hbad ((holds_swap_iff a b hU).mp (holds_one_exception b a Uᴴ hUs (σ c) z ha))).elim
  · exact (hbad (holds_one_exception a b U hU c z hc)).elim
  · refine ⟨σ, i, j, k, l, hij, hik, hil, hjk, hjl, hkl, ?_⟩
    rw [matchingProduct_disjoint_swaps_alternating_sum a b σ i j k l hij hik hil hjk hjl hkl]
    have hfactor (m : ι) : a (σ m) + b m ≠ 0 :=
      Finset.prod_ne_zero_iff.mp hσ m (Finset.mem_univ _)
    exact mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun m _ => hfactor m)
      (mul_ne_zero (sub_ne_zero.mpr haij) (sub_ne_zero.mpr hbij.symm)))
      (mul_ne_zero (sub_ne_zero.mpr hakl) (sub_ne_zero.mpr hbkl.symm))


/-- The translation-invariant mixed difference of four ordered coordinates. -/
def quartetMixed {α : Type*} (p : α → ℂ) (q₀ q₁ q₂ q₃ : α) : ℂ :=
  p q₀ + p q₃ - p q₁ - p q₂

/-- The pivot coordinate is a rational function of four pivot differences.
The formula does not require a nonzero matching product at the pivot. -/
theorem quartet_pivot_eq_of_differences {α : Type*} (p : α → ℂ) (r q₀ q₁ q₂ q₃ : α)
    (he : p q₀ * p q₃ = p q₁ * p q₂)
    (hn : quartetMixed p q₀ q₁ q₂ q₃ ≠ 0) :
    let d := fun q => p q - p r
    p r = (d q₁ * d q₂ - d q₀ * d q₃) / quartetMixed d q₀ q₁ q₂ q₃ := by
  intro d
  have hd : quartetMixed d q₀ q₁ q₂ q₃ = quartetMixed p q₀ q₁ q₂ q₃ := by
    unfold quartetMixed d
    ring
  apply (eq_div_iff (hd ▸ hn)).mpr
  rw [hd]
  unfold quartetMixed d
  linear_combination he

/-- For every possibly violating pair, *all* pivot differences determine the
exact profile uniquely, even among pairs whose spectra have collisions. -/
theorem matchingProfile_eq_of_pivot_differences_of_not_holds
    (hcard : 4 ≤ Fintype.card ι) (a b c d : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (hbad : ¬ Holds a b U) (r : Equiv.Perm ι)
    (h : ∀ q, matchingProduct a b q - matchingProduct a b r =
      matchingProduct c d q - matchingProduct c d r) :
    matchingProduct a b = matchingProduct c d := by
  obtain ⟨σ, i, j, k, l, hij, hik, hil, hjk, hjl, hkl, hΓ⟩ :=
    exists_matching_quartet_of_not_holds hcard a b U hU hbad
  let t := matchingProduct c d r - matchingProduct a b r
  have ht (q : Equiv.Perm ι) :
      matchingProduct c d q = matchingProduct a b q + t := by
    unfold t
    linear_combination -(h q)
  have h₁ := matchingProduct_disjoint_swaps_identity a b σ i j k l hij hik hil hjk hjl hkl
  have h₂ := matchingProduct_disjoint_swaps_identity c d σ i j k l hij hik hil hjk hjl hkl
  simp only [ht] at h₂
  have hz := eq_zero_of_matching_quartet_translation h₁ hΓ h₂
  funext q
  simp [ht q, hz]

/-- After absorbing the support direction, reflection across the imaginary
axis keeps every complex contact difference and reverses the real gap.
Thus a strict profile cannot be the globally unique point of its
contact-difference fiber, even when the point is isolated there. -/
theorem exists_distinct_matchingProfile_of_contact_differences
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (r : Equiv.Perm ι) (hU : IsUnitary U)
    (hstrict : 0 < (determinantValue a b U - matchingProduct a b r).re)
    (S : Set (Equiv.Perm ι))
    (hS : ∀ q ∈ S, (matchingProduct a b q - matchingProduct a b r).re = 0) :
    ∃ c d : ι → ℂ, matchingProduct c d ≠ matchingProduct a b ∧
      (∀ q ∈ S, matchingProduct c d q - matchingProduct c d r =
        matchingProduct a b q - matchingProduct a b r) ∧
      (determinantValue c d U - matchingProduct c d r).re =
        -(determinantValue a b U - matchingProduct a b r).re := by
  classical
  have hn : Nonempty ι := by
    by_contra! h
    letI : IsEmpty ι := not_nonempty_iff.mp h
    have hd : determinantValue a b U = matchingProduct a b r := by
      unfold determinantValue matchingProduct
      simp
    simp [hd] at hstrict
  obtain ⟨k, hk⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : ℂ) (Fintype.card_pos_iff.mpr hn)
  let c := fun j => k * star (a j)
  let d := fun j => k * star (b j)
  have hp (q : Equiv.Perm ι) : matchingProduct c d q = -star (matchingProduct a b q) := by
    simp only [c, d, matchingProduct_scale, hk, neg_one_mul]
    unfold matchingProduct
    simp only [star_add, star_prod]
  have hg : (determinantValue c d U - matchingProduct c d r).re =
      -(determinantValue a b U - matchingProduct a b r).re := by
    have h₁ := matchingProfileDetGap_matchingProduct c d U hU 1 r
    have h₂ := matchingProfileDetGap_matchingProduct a b U hU 1 r
    simp only [one_mul] at h₁ h₂
    rw [← h₁, ← h₂]
    simp only [matchingProfileDetGap, hp, Complex.re_sum, one_mul, ← map_sub,
      neg_sub_neg, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.sub_re, Complex.star_def, Complex.conj_re]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro q _
    ring
  refine ⟨c, d, ?_, fun q hq => ?_, hg⟩
  · intro he
    have hsame := congrArg (fun p => (matchingProfileDetGap U 1 r p).re) he
    dsimp only at hsame
    rw [matchingProfileDetGap_matchingProduct c d U hU 1 r,
      matchingProfileDetGap_matchingProduct a b U hU 1 r, one_mul, one_mul, hg] at hsame
    linarith
  · rw [hp, hp]
    apply Complex.ext
    · have hz := hS q hq
      simp only [Complex.sub_re] at hz
      simp only [Complex.sub_re, Complex.neg_re, Complex.star_def, Complex.conj_re]
      linarith
    · simp [Complex.sub_im, Complex.star_def, sub_eq_add_neg]

end

end MOC
