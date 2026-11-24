import MOC.OrderFiveSparseGeometry

open Matrix Finset BigOperators

namespace MOC

/-- Two columns supported on the same three rows, nonzero at each,
force a rigid adjacent rectangle. A zero in that rectangle forces a row
of support at most two. The proof uses a localized linear combination of
the two orthogonal columns. -/
theorem row_degree_le_two_of_zero_in_three_row_corner
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Matrix ι ι ℂ} (hU : IsUnitary U)
    (r s t x y j : ι) (hrs : r ≠ s)
    (hxy : x ≠ y) (hjx : j ≠ x) (hjy : j ≠ y)
    (hzero : ∀ i, i ≠ r → i ≠ s → i ≠ t → U i x = 0 ∧ U i y = 0)
    (hxr : U r x ≠ 0) (hyr : U r y ≠ 0)
    (hjt : U t j = 0)
    (hj : U r j ≠ 0 ∨ U s j ≠ 0) :
    (supportColumns U {t}).card ≤ 2 := by
  classical
  have hd (a b : ι) : (∑ i, star (U i a) * U i b) = if a = b then 1 else 0 := by
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using
      congrArg (fun V : Matrix ι ι ℂ => V a b) hU.2
  have hsum (f : ι → ℂ) (hf : ∀ i, i ≠ r → i ≠ s → f i = 0) :
      ∑ i, f i = f r + f s := by
    have he : ∑ i ∈ ({r,s} : Finset ι), f i = ∑ i, f i := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have hi' : i ≠ r ∧ i ≠ s := by simpa using hi
      exact hf i hi'.1 hi'.2
    simpa [hrs] using he.symm
  have hp (a : ι) (ha : a = x ∨ a = y) (haj : a ≠ j) :
      star (U r a) * U r j + star (U s a) * U s j = 0 := by
    have he := hd a j
    rw [if_neg haj, hsum] at he
    · exact he
    · intro i hir his
      by_cases hit : i = t
      · simp [hit, hjt]
      · rcases ha with ha | ha
        · simp [ha, (hzero i hir his hit).1]
        · simp [ha, (hzero i hir his hit).2]
  have hxj := hp x (Or.inl rfl) hjx.symm
  have hyj := hp y (Or.inr rfl) hjy.symm
  have hsj : U s j ≠ 0 := by
    intro hs
    have hz : star (U r x) * U r j = 0 := by simpa [hs] using hxj
    have hf : U r j = 0 := (mul_eq_zero.mp hz).resolve_left (by simpa using hxr)
    exact hj.elim (fun h => h hf) (fun h => h hs)
  let L (i : ι) := U r y * U i x - U r x * U i y
  have hLs : L s = 0 := by
    have hz : star (L s) * U s j = 0 := by
      unfold L
      simp only [star_sub, StarMul.star_mul]
      linear_combination star (U r y) * hxj - star (U r x) * hyj
    have hh := (mul_eq_zero.mp hz).resolve_right hsj
    simpa using hh
  have hL (i : ι) (hit : i ≠ t) : L i = 0 := by
    by_cases hir : i = r
    · subst i
      dsimp [L]
      ring
    · by_cases his : i = s
      · simpa [his] using hLs
      · obtain ⟨hx,hy⟩ := hzero i hir his hit
        simp [L,hx,hy]
  have hinner (k : ι) :
      (∑ i, star (L i) * U i k) =
        star (U r y) * (∑ i, star (U i x) * U i k) -
        star (U r x) * (∑ i, star (U i y) * U i k) := by
    simp only [L, star_sub, StarMul.star_mul, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
  have hsingle (k : ι) : (∑ i, star (L i) * U i k) = star (L t) * U t k := by
    apply Finset.sum_eq_single t
    · intro i _ hi
      simp [hL i hi]
    · simp
  have hLt : star (L t) ≠ 0 := by
    have h := hinner x
    rw [hsingle, hd, hd, if_pos rfl, if_neg hxy.symm, mul_zero, sub_zero, mul_one] at h
    intro hz
    rw [hz, zero_mul] at h
    exact (by simpa using hyr : star (U r y) ≠ 0) h.symm
  have hsupp : supportColumns U {t} ⊆ {x,y} := by
    intro k hk
    by_cases hn : k ∈ ({x,y} : Finset ι)
    · exact hn
    exfalso
    have hne : k ≠ x ∧ k ≠ y := by simpa using hn
    have h := hinner k
    rw [hsingle, hd, hd, if_neg hne.1.symm, if_neg hne.2.symm, mul_zero, mul_zero,
      sub_zero] at h
    have hh := (mul_eq_zero.mp h).resolve_left hLt
    exact (by simpa [supportColumns] using hk : U t k ≠ 0) hh
  exact (Finset.card_le_card hsupp).trans Finset.card_le_two


/-- With all row and column degrees at least three, a two-by-two zero corner
has an entirely nonzero complementary three-by-three corner. -/
theorem order_five_complement_of_zero_corner_ne_zero
    {U : Matrix (Fin 5) (Fin 5) ℂ} (hU : IsUnitary U)
    (hrows : ∀ i, 3 ≤ (supportColumns U {i}).card)
    (hcols : ∀ j, 3 ≤ (supportColumns Uᴴ {j}).card)
    (r s t x y j : Fin 5) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hxy : x ≠ y) (hjx : j ≠ x) (hjy : j ≠ y)
    (hzero : ∀ i, i ≠ r → i ≠ s → i ≠ t → U i x = 0 ∧ U i y = 0) :
    U t j ≠ 0 := by
  classical
  have hcol (c : Fin 5) (S : Finset (Fin 5)) (hS : S.card ≤ 2)
      (hz : ∀ i ∉ S, U i c = 0) : False := by
    have hsub : supportColumns Uᴴ {c} ⊆ S := by
      intro i hi
      have hn : U i c ≠ 0 := by simpa [supportColumns, conjTranspose_apply] using hi
      by_cases hs : i ∈ S
      · exact hs
      · exact False.elim (hn (hz i hs))
    have hle := (Finset.card_le_card hsub).trans hS
    have := hcols c
    omega
  have hne (c : Fin 5) (hc : c = x ∨ c = y) : U r c ≠ 0 := by
    intro hz
    apply hcol c {s,t} Finset.card_le_two
    intro i hi
    have hi' : i ≠ s ∧ i ≠ t := by simpa using hi
    by_cases hir : i = r
    · simpa [hir] using hz
    · rcases hc with rfl | rfl
      · exact (hzero i hir hi'.1 hi'.2).1
      · exact (hzero i hir hi'.1 hi'.2).2
  intro hz
  have hsome : U r j ≠ 0 ∨ U s j ≠ 0 := by
    by_cases hr : U r j = 0
    · right
      intro hs
      apply hcol j ({r,s,t} : Finset (Fin 5))ᶜ (by
        simp [Finset.card_compl, hrs, hrt, hst])
      intro i hi
      have hmem : i ∈ ({r,s,t} : Finset (Fin 5)) := by
        simpa only [Finset.mem_compl, not_not] using hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with hi | hi | hi <;> subst i <;> assumption
    · exact Or.inl hr
  have hh := row_degree_le_two_of_zero_in_three_row_corner hU r s t x y j hrs hxy hjx hjy
    hzero (hne x (Or.inl rfl)) (hne y (Or.inr rfl)) hz hsome
  have := hrows t
  omega

end MOC
