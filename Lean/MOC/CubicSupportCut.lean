import MOC.SparseUnitarySupport

namespace MOC

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Four rows that meet one cubic row have at most four adjacent columns
when distinct rows and columns cannot meet in exactly one position. -/
theorem cubic_four_neighborhood_card_le {U : Matrix ι ι ℂ} (i : ι)
    (hrow : ∀ r, (supportColumns U {r}).card = 3)
    (hrr : ∀ {r t : ι}, r ≠ t →
      ((supportColumns U {r}) ∩ supportColumns U {t}).card ≠ 1)
    (hcc : ∀ {j k : ι}, j ≠ k →
      ((supportColumns Uᴴ {j}) ∩ supportColumns Uᴴ {k}).card ≠ 1)
    (hfour : (supportColumns Uᴴ (supportColumns U {i})).card = 4) :
    (supportColumns U (supportColumns Uᴴ (supportColumns U {i}))).card ≤ 4 := by
  classical
  let S := supportColumns U {i}
  let R := supportColumns Uᴴ S
  let T := supportColumns U R
  have hiR : i ∈ R := by
    obtain ⟨j, hj⟩ : S.Nonempty := Finset.card_pos.mp (by dsimp [S]; rw [hrow]; decide)
    exact mem_supportColumns_iff.mpr ⟨j, hj, by simpa [Matrix.conjTranspose_apply] using mem_supportColumns_singleton.mp hj⟩
  have rowCapacity (r : ι) (hr : r ∈ R) : ((supportColumns U {r}) \ S).card ≤ 1 := by
    by_cases h : r = i
    · subst r; simp [S]
    obtain ⟨j, hj, hjr⟩ := mem_supportColumns_iff.mp hr
    have hpos : 0 < ((supportColumns U {r}) ∩ S).card := Finset.card_pos.mpr
      ⟨j, Finset.mem_inter.mpr ⟨mem_supportColumns_singleton.mpr (by simpa [Matrix.conjTranspose_apply] using hjr), hj⟩⟩
    have hne := hrr h
    change ((supportColumns U {r}) ∩ S).card ≠ 1 at hne
    have hsum := Finset.card_sdiff_add_card_inter (supportColumns U {r}) S
    rw [hrow] at hsum
    omega
  let outsideRows (d : ι) := R.filter (fun r => U r d ≠ 0)
  have outsideLarge (d : ι) (hd : d ∈ T \ S) : 2 ≤ (outsideRows d).card := by
    obtain ⟨r, hr, hrd⟩ := mem_supportColumns_iff.mp (Finset.mem_sdiff.mp hd).1
    obtain ⟨j, hj, hrj⟩ := mem_supportColumns_iff.mp hr
    have hdj : d ≠ j := fun e => (Finset.mem_sdiff.mp hd).2 (e ▸ hj)
    let I := (supportColumns Uᴴ {d}) ∩ supportColumns Uᴴ {j}
    have hpos : 0 < I.card := Finset.card_pos.mpr ⟨r, Finset.mem_inter.mpr
      ⟨mem_adjoint_supportColumns_singleton.mpr hrd, mem_supportColumns_singleton.mpr hrj⟩⟩
    have hne : I.card ≠ 1 := hcc hdj
    have hsub : I ⊆ outsideRows d := by
      intro x hx
      obtain ⟨hxd, hxj⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_filter.mpr ⟨mem_supportColumns_iff.mpr ⟨j, hj, mem_supportColumns_singleton.mp hxj⟩,
        mem_adjoint_supportColumns_singleton.mp hxd⟩
    have := Finset.card_le_card hsub
    omega
  have outsideSmall : (T \ S).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro d hd e he
    by_contra hde
    have hdis : Disjoint (outsideRows d) (outsideRows e) := by
      apply Finset.disjoint_left.mpr
      intro x hxd hxe
      obtain ⟨hx, hxd⟩ := Finset.mem_filter.mp hxd
      obtain ⟨_, hxe⟩ := Finset.mem_filter.mp hxe
      exact hde ((Finset.card_le_one.mp (rowCapacity x hx)) d
        (Finset.mem_sdiff.mpr ⟨mem_supportColumns_singleton.mpr hxd, (Finset.mem_sdiff.mp hd).2⟩)
        e (Finset.mem_sdiff.mpr ⟨mem_supportColumns_singleton.mpr hxe, (Finset.mem_sdiff.mp he).2⟩))
    have hsub (c : ι) (hc : c ∈ T \ S) : outsideRows c ⊆ R.erase i := by
      intro x hx
      obtain ⟨hx, hxc⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_sdiff.mp hc).2
        (mem_supportColumns_singleton.mpr (h ▸ hxc)), hx⟩
    have hbound := Finset.card_le_card (Finset.union_subset (hsub d hd) (hsub e he))
    rw [Finset.card_union_of_disjoint hdis, Finset.card_erase_of_mem hiR] at hbound
    change R.card = 4 at hfour
    have := outsideLarge d hd
    have := outsideLarge e he
    omega
  have hsum := Finset.card_sdiff_add_card_inter T S
  have hbound := Finset.card_le_card (Finset.inter_subset_right : T ∩ S ⊆ S)
  have hS : S.card = 3 := hrow i
  change T.card ≤ 4
  omega

/-- A neighborhood of the same size as its column set exhausts the index
set of a unitary that has no proper paired block. -/
private theorem index_card_le_of_small_neighborhood {n : ℕ}
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : IsUnitary U)
    (hblocks : ¬ HasProperPairedBlocks U) (R : Finset (Fin n)) (hR : R.Nonempty)
    (hsize : (supportColumns U R).card ≤ R.card) : n ≤ R.card := by
  classical
  by_contra! hlt
  have hne : R ≠ Finset.univ := fun h => by simp [h] at hlt
  have hex : ∃ j, j ∉ R := by
    by_contra! hall
    exact hne (Finset.eq_univ_of_forall hall)
  obtain ⟨j, hj⟩ := hex
  exact (Nat.not_lt_of_ge hsize)
    (card_lt_supportColumns_of_no_paired_blocks hU hblocks R hR ⟨j, hj⟩)

/-- An indecomposable unitary with three nonzero entries in every row and
column has order at most four. -/
theorem cubic_order_le_four_of_no_paired_blocks {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : IsUnitary U) (hrows : ∀ r, (supportColumns U {r}).card = 3)
    (hcols : ∀ c, (supportColumns Uᴴ {c}).card = 3)
    (hblocks : ¬ HasProperPairedBlocks U) : n ≤ 4 := by
  classical
  by_contra! hn
  let i : Fin n := ⟨0, by omega⟩
  let S := supportColumns U {i}
  let R := supportColumns Uᴴ S
  obtain ⟨hlo, hhi, heq⟩ := cubic_row_neighbor_bounds hU hrows hcols i
  change 3 ≤ R.card at hlo
  change R.card ≤ 4 at hhi
  have hcover : (supportColumns U R).card ≤ R.card := by
    by_cases hc : R.card = 3
    · rw [heq hc, hc, hrows]
    · have hc4 : R.card = 4 := by omega
      rw [hc4]
      exact cubic_four_neighborhood_card_le i hrows
        (fun h => row_support_inter_card_ne_one hU h)
        (fun h => col_support_inter_card_ne_one hU h) hc4
  have := index_card_le_of_small_neighborhood hU hblocks R
    (Finset.card_pos.mp (by omega)) hcover
  omega

end MOC
