import MOC.OrderFiveContact

open Matrix BigOperators

namespace MOC

private theorem two_dimensional_orthogonality {a b c d e f : ℂ}
    (ha : a ≠ 0) (hc : c ≠ 0) (he : e ≠ 0)
    (h₁ : star a * c + star b * d = 0)
    (h₂ : star a * e + star b * f = 0)
    (h₃ : star c * e + star d * f = 0) : False := by
  have hrel : star a * (c * f - e * d) = 0 := by
    linear_combination f * h₁ - d * h₂
  have hprop : c * f = e * d :=
    sub_eq_zero.mp ((mul_eq_zero.mp hrel).resolve_left (by simpa using ha))
  have hnorm : e * (star c * c + star d * d) = 0 := by
    linear_combination c * h₃ - star d * hprop
  have hzero := (mul_eq_zero.mp hnorm).resolve_left he
  change (starRingEnd ℂ) c * c + (starRingEnd ℂ) d * d = 0 at hzero
  rw [← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self,
    ← Complex.ofReal_add, Complex.ofReal_eq_zero] at hzero
  exact (ne_of_gt (add_pos_of_pos_of_nonneg
    (lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm (mt Complex.normSq_eq_zero.mp hc)))
    (Complex.normSq_nonneg _))) hzero

private theorem sum_on_pair {α K : Type*} [Fintype α] [DecidableEq α] [AddCommMonoid K]
    (f : α → K) {i j : α} (hij : i ≠ j)
    (hzero : ∀ k, k ≠ i → k ≠ j → f k = 0) : ∑ k, f k = f i + f j := by
  have h : ∑ k ∈ ({i,j} : Finset α), f k = ∑ k, f k := by
    apply Finset.sum_subset (Finset.subset_univ _)
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, not_or, true_implies]
    exact fun k hk => hzero k hk.1 hk.2
  simpa [hij] using h.symm

private theorem mem_zeroRow (U : Matrix (Fin 5) (Fin 5) ℂ) (i j : Fin 5) :
    j ∈ (supportColumns U {i})ᶜ ↔ U i j = 0 := by
  simp [supportColumns]

private theorem mem_zeroCol (U : Matrix (Fin 5) (Fin 5) ℂ) (i j : Fin 5) :
    i ∈ (supportColumns Uᴴ {j})ᶜ ↔ U i j = 0 := by
  simp [supportColumns, conjTranspose_apply]

/-- Every three distinct rows in a five-by-five unitary with column degree at
least three contain a row of degree at least four, if all rows have degree at
least three. The argument uses orthogonality, not support-mask enumeration. -/
theorem order_five_not_three_degree_three_rows {U : Matrix (Fin 5) (Fin 5) ℂ}
    (hU : IsUnitary U) (hcols : ∀ j, 3 ≤ (supportColumns Uᴴ {j}).card)
    {i j k : Fin 5} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : (supportColumns U {i}).card = 3)
    (hj : (supportColumns U {j}).card = 3)
    (hk : (supportColumns U {k}).card = 3) : False := by
  classical
  let Z (r : Fin 5) := (supportColumns U {r})ᶜ
  have hmem (r s : Fin 5) : s ∈ Z r ↔ U r s = 0 := mem_zeroRow U r s
  have hzcard (r : Fin 5) (hr : (supportColumns U {r}).card = 3) : (Z r).card = 2 := by
    simp [Z, Finset.card_compl, hr]
  have noTriple (s : Fin 5) (hsi : s ∈ Z i) (hsj : s ∈ Z j) (hsk : s ∈ Z k) : False := by
    have hsub : ({i,j,k} : Finset (Fin 5)) ⊆ (supportColumns Uᴴ {s})ᶜ := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with ht | ht | ht <;> subst t
      · exact (mem_zeroCol U i s).mpr ((hmem i s).mp hsi)
      · exact (mem_zeroCol U j s).mpr ((hmem j s).mp hsj)
      · exact (mem_zeroCol U k s).mpr ((hmem k s).mp hsk)
    have hc := Finset.card_le_card hsub
    simp [hij, hik, hjk, Finset.card_compl] at hc
    have := hcols s
    omega
  have pair (r s : Fin 5) (hrs : r ≠ s) (hr : (Z r).card = 2) (hs : (Z s).card = 2) :
      ∃ t, t ∈ Z r ∧ t ∈ Z s := by
    by_cases hh : ∃ t, t ∈ Z r ∧ t ∈ Z s
    · exact hh
    exfalso
    have hn := hh
    have hd : Disjoint (Z r) (Z s) :=
      Finset.disjoint_left.mpr fun x hx hy => hn ⟨x, hx, hy⟩
    have hcard : ((Z r ∪ Z s)ᶜ).card = 1 := by
      rw [Finset.card_compl, Finset.card_union_of_disjoint hd, hr, hs]
      decide
    obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hcard
    have htn : t ∉ Z r ∧ t ∉ Z s := by
      have htmem : t ∈ (Z r ∪ Z s)ᶜ := by simp [ht]
      simpa using htmem
    have heq := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℂ => M r s) hU.1
    have heq' : ∑ x, U r x * star (U s x) = 0 := by
      simpa [mul_apply, conjTranspose_apply, one_apply, hrs] using heq
    have hsum : ∑ x, U r x * star (U s x) = U r t * star (U s t) := by
      have hsingle : ∑ x ∈ ({t} : Finset (Fin 5)), U r x * star (U s x) =
          ∑ x, U r x * star (U s x) := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro x _ hx
        have hx' : x ∈ Z r ∪ Z s := by
          by_contra h
          exact hx (ht ▸ Finset.mem_compl.mpr h)
        rcases Finset.mem_union.mp hx' with h | h
        · simp [(hmem r x).mp h]
        · simp [(hmem s x).mp h]
      simpa using hsingle.symm
    rw [hsum] at heq'
    exact (mul_ne_zero (mt (hmem r t).mpr htn.1)
      (by simpa using (mt (hmem s t).mpr htn.2))) heq'
  obtain ⟨x, hxi, hxj⟩ := pair i j hij (hzcard i hi) (hzcard j hj)
  obtain ⟨y, hyi, hyk⟩ := pair i k hik (hzcard i hi) (hzcard k hk)
  obtain ⟨z, hzj, hzk⟩ := pair j k hjk (hzcard j hj) (hzcard k hk)
  have hxy : x ≠ y := fun h => noTriple x hxi hxj (h ▸ hyk)
  have hxz : x ≠ z := fun h => noTriple x hxi hxj (h ▸ hzk)
  have hyz : y ≠ z := fun h => noTriple y hyi (h ▸ hzj) hyk
  have hrscard : (({i,j,k} : Finset (Fin 5))ᶜ).card = 2 := by
    simp [Finset.card_compl, hij, hik, hjk]
  obtain ⟨r,s,hrs,hrseq⟩ := Finset.card_eq_two.mp hrscard
  have nr (t : Fin 5) (ht : t ∈ ({r,s} : Finset (Fin 5))) :
      U t x ≠ 0 ∧ U t y ≠ 0 ∧ U t z ≠ 0 := by
    have htc : t ∉ ({i,j,k} : Finset (Fin 5)) := Finset.mem_compl.mp (hrseq ▸ ht)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at htc
    have nn (p q l : Fin 5) (hpq : p ≠ q) (htp : t ≠ p) (htq : t ≠ q)
        (hp : U p l = 0) (hq : U q l = 0) : U t l ≠ 0 := by
      intro ht
      have hsub : ({t,p,q} : Finset (Fin 5)) ⊆ (supportColumns Uᴴ {l})ᶜ := by
        intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl <;>
          exact (mem_zeroCol U _ _).mpr (by assumption)
      have hc := Finset.card_le_card hsub
      simp [htp, htq, hpq, Finset.card_compl] at hc
      have := hcols l
      omega
    exact ⟨nn i j x hij htc.1 htc.2.1 ((hmem i x).mp hxi) ((hmem j x).mp hxj),
      nn i k y hik htc.1 htc.2.2 ((hmem i y).mp hyi) ((hmem k y).mp hyk),
      nn j k z hjk htc.2.1 htc.2.2 ((hmem j z).mp hzj) ((hmem k z).mp hzk)⟩
  have eqn (l m : Fin 5) (hlm : l ≠ m)
      (hzero : ∀ t ∈ ({i,j,k} : Finset (Fin 5)), U t l = 0 ∨ U t m = 0) :
      star (U r l) * U r m + star (U s l) * U s m = 0 := by
    have heq := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℂ => M l m) hU.2
    have heq' : ∑ t, star (U t l) * U t m = 0 := by
      simpa [mul_apply, conjTranspose_apply, one_apply, hlm] using heq
    rw [sum_on_pair _ hrs] at heq'
    · exact heq'
    · intro t htr hts
      have ht : t ∈ ({i,j,k} : Finset (Fin 5)) := by
        by_contra h
        have hm := Finset.mem_compl.mpr h
        rw [hrseq] at hm
        simp [htr, hts] at hm
      rcases hzero t ht with hh | hh <;> simp [hh]
  have hxyz := nr r (by simp)
  apply two_dimensional_orthogonality hxyz.1 hxyz.2.1 hxyz.2.2
  · apply eqn x y hxy
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with ht | ht | ht <;> subst t
    · exact Or.inl ((hmem i x).mp hxi)
    · exact Or.inl ((hmem j x).mp hxj)
    · exact Or.inr ((hmem k y).mp hyk)
  · apply eqn x z hxz
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with ht | ht | ht <;> subst t
    · exact Or.inl ((hmem i x).mp hxi)
    · exact Or.inl ((hmem j x).mp hxj)
    · exact Or.inr ((hmem k z).mp hzk)
  · apply eqn y z hyz
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with ht | ht | ht <;> subst t
    · exact Or.inl ((hmem i y).mp hyi)
    · exact Or.inr ((hmem j z).mp hzj)
    · exact Or.inl ((hmem k y).mp hyk)


theorem order_five_degree_three_rows_card_le_two {U : Matrix (Fin 5) (Fin 5) ℂ}
    (hU : IsUnitary U) (hcols : ∀ j, 3 ≤ (supportColumns Uᴴ {j}).card) :
    (Finset.univ.filter (fun i => (supportColumns U {i}).card = 3)).card ≤ 2 := by
  classical
  let s := Finset.univ.filter (fun i => (supportColumns U {i}).card = 3)
  change s.card ≤ 2
  by_cases hs : s.card ≤ 2
  · exact hs
  exfalso
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq (s := s) (n := 3) (by omega)
  obtain ⟨i,j,k,hij,hik,hjk,rfl⟩ := Finset.card_eq_three.mp htcard
  have hd (l : Fin 5) (hl : l ∈ ({i,j,k} : Finset (Fin 5))) :
      (supportColumns U {l}).card = 3 := (Finset.mem_filter.mp (hts hl)).2
  exact order_five_not_three_degree_three_rows hU hcols hij hik hjk
    (hd i (by simp)) (hd j (by simp)) (hd k (by simp))

/-- If order four holds, every order-five counterexample must have at most seven
zero entries in its mixer, counted by rows. The same bound by columns follows
on applying the row bound to the conjugate transpose. -/
theorem order_five_failure_zero_bound (hfour : Conjecture (Fin 4))
    (a b : Fin 5 → ℂ) {U : Matrix (Fin 5) (Fin 5) ℂ} (hU : IsUnitary U)
    (hfail : ¬ Holds a b U) :
    (∑ i : Fin 5, ((supportColumns U {i})ᶜ).card) ≤ 7 := by
  classical
  obtain ⟨_, hrows, hcols⟩ := order_five_failure_structure hfour a b hU hfail
  have hc := order_five_degree_three_rows_card_le_two hU hcols
  calc
    _ ≤ ∑ i : Fin 5, (1 + if (supportColumns U {i}).card = 3 then 1 else 0) := by
      apply Finset.sum_le_sum
      intro i _
      have hm := hrows i
      rw [Finset.card_compl, Fintype.card_fin]
      split <;> omega
    _ = 5 + (Finset.univ.filter (fun i => (supportColumns U {i}).card = 3)).card := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp
    _ ≤ 7 := by omega


/-- An order-five failure on any mixer with eight or more zero entries
forces failure already in order four. -/
theorem not_conjecture_four_of_eight_zero_mixer {a b : Fin 5 → ℂ}
    {U : Matrix (Fin 5) (Fin 5) ℂ} (hU : IsUnitary U) (hfail : ¬ Holds a b U)
    (hzeros : 8 ≤ ∑ i : Fin 5, ((supportColumns U {i})ᶜ).card) : ¬ Conjecture (Fin 4) := by
  intro hfour
  have := order_five_failure_zero_bound hfour a b hU hfail
  omega

theorem order_five_degree_three_columns_card_le_two {U : Matrix (Fin 5) (Fin 5) ℂ}
    (hU : IsUnitary U) (hrows : ∀ i, 3 ≤ (supportColumns U {i}).card) :
    (Finset.univ.filter (fun j => (supportColumns Uᴴ {j}).card = 3)).card ≤ 2 := by
  have hUT : IsUnitary Uᴴ := by simpa [IsUnitary, and_comm] using hU
  exact order_five_degree_three_rows_card_le_two hUT (by simpa using hrows)

end MOC
