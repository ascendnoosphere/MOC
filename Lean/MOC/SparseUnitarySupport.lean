import MOC.SupportBlocks

/-! Support incidence bounds for unitary matrices with three nonzero entries per row and column. -/

open BigOperators Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem mem_supportColumns_iff {U : Matrix ι ι ℂ} {s : Finset ι} {j : ι} :
    j ∈ supportColumns U s ↔ ∃ i ∈ s, U i j ≠ 0 := by
  classical
  simp [supportColumns]

omit [DecidableEq ι] in
@[simp] theorem mem_supportColumns_singleton {U : Matrix ι ι ℂ} {i j : ι} :
    j ∈ supportColumns U {i} ↔ U i j ≠ 0 := by
  simp [mem_supportColumns_iff]

omit [DecidableEq ι] in
theorem mem_adjoint_supportColumns_iff {U : Matrix ι ι ℂ} {s : Finset ι} {i : ι} :
    i ∈ supportColumns Uᴴ s ↔ ∃ j ∈ s, U i j ≠ 0 := by
  simp [mem_supportColumns_iff, conjTranspose_apply]

omit [DecidableEq ι] in
@[simp] theorem mem_adjoint_supportColumns_singleton {U : Matrix ι ι ℂ} {i j : ι} :
    i ∈ supportColumns Uᴴ {j} ↔ U i j ≠ 0 := by
  simp [conjTranspose_apply]

/-- Orthogonality excludes a unique common nonzero entry in distinct rows. -/
theorem row_support_inter_card_ne_one {U : Matrix ι ι ℂ} (hU : IsUnitary U)
    {i j : ι} (hij : i ≠ j) : (supportColumns U {i} ∩ supportColumns U {j}).card ≠ 1 := by
  intro h
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp h
  have horth : ∑ l, U i l * star (U j l) = 0 := by
    simpa [mul_apply, conjTranspose_apply, one_apply, hij] using
      congrArg (fun M : Matrix ι ι ℂ => M i j) hU.1
  have hsum : ∑ l ∈ ({k} : Finset ι), U i l * star (U j l) =
      ∑ l, U i l * star (U j l) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro l _ hl
    by_contra hn
    have hne := mul_ne_zero_iff.mp hn
    have hm : l ∈ supportColumns U {i} ∩ supportColumns U {j} := by
      simpa using hne
    exact hl (hk ▸ hm)
  have hm : k ∈ supportColumns U {i} ∩ supportColumns U {j} := by simp [hk]
  have hne : U i k ≠ 0 ∧ U j k ≠ 0 := by simpa using hm
  rw [horth, Finset.sum_singleton] at hsum
  exact mul_ne_zero hne.1 (by simpa using hne.2) hsum

/-- Orthogonality excludes a unique common nonzero entry in distinct columns. -/
theorem col_support_inter_card_ne_one {U : Matrix ι ι ℂ} (hU : IsUnitary U)
    {i j : ι} (hij : i ≠ j) : (supportColumns Uᴴ {i} ∩ supportColumns Uᴴ {j}).card ≠ 1 :=
  row_support_inter_card_ne_one (U := Uᴴ)
    ⟨by simpa only [conjTranspose_conjTranspose] using hU.2,
      by simpa only [conjTranspose_conjTranspose] using hU.1⟩ hij

/-- The rows meeting the three columns of a cubic unitary row number three or four.
If there are three, their column neighborhood is the original three columns. -/
theorem cubic_row_neighbor_bounds {U : Matrix ι ι ℂ} (hU : IsUnitary U)
    (hrows : ∀ i, (supportColumns U {i}).card = 3)
    (hcols : ∀ j, (supportColumns Uᴴ {j}).card = 3) (i : ι) :
    let S := supportColumns U {i}
    let R := supportColumns Uᴴ S
    3 ≤ R.card ∧ R.card ≤ 4 ∧ (R.card = 3 → supportColumns U R = S) := by
  classical
  let S := supportColumns U {i}
  let R := supportColumns Uᴴ S
  have hS : S.card = 3 := hrows i
  obtain ⟨c, hc⟩ := Finset.card_pos.mp (show 0 < S.card by rw [hS]; decide)
  have hiR : i ∈ R :=
    mem_adjoint_supportColumns_iff.mpr ⟨c, hc, mem_supportColumns_singleton.mp hc⟩
  have hsub (j : ι) (hj : j ∈ S) : supportColumns Uᴴ {j} ⊆ R := by
    intro r hr
    exact mem_adjoint_supportColumns_iff.mpr ⟨j, hj, mem_adjoint_supportColumns_singleton.mp hr⟩
  have hge := Finset.card_le_card (hsub c hc)
  rw [hcols c] at hge
  refine ⟨hge, ?_, ?_⟩
  · let edge (r j : ι) : ℕ := if U r j ≠ 0 then 1 else 0
    have hcolsum (j : ι) (hj : j ∈ S) : ∑ r ∈ R, edge r j = 3 := by
      have hfilter : R.filter (fun r => U r j ≠ 0) = supportColumns Uᴴ {j} := by
        ext r
        simp only [Finset.mem_filter, mem_adjoint_supportColumns_singleton]
        exact ⟨And.right, fun hr => ⟨hsub j hj (mem_adjoint_supportColumns_singleton.mpr hr), hr⟩⟩
      rw [show (∑ r ∈ R, edge r j) = (R.filter (fun r => U r j ≠ 0)).card by
        simp only [edge, Finset.sum_boole, Nat.cast_id], hfilter, hcols j]
    have hrowsum (r : ι) : ∑ j ∈ S, edge r j = (supportColumns U {r} ∩ S).card := by
      have hfilter : S.filter (fun j => U r j ≠ 0) = supportColumns U {r} ∩ S := by
        ext j
        simp [and_comm]
      simp only [edge, Finset.sum_boole, hfilter, Nat.cast_id]
    have htotal : ∑ r ∈ R, (supportColumns U {r} ∩ S).card = 9 := by
      simp_rw [← hrowsum]
      rw [Finset.sum_comm]
      calc
        _ = ∑ j ∈ S, (3 : ℕ) := Finset.sum_congr rfl hcolsum
        _ = 9 := by simp [hS]
    have hmin (r : ι) (hr : r ∈ R.erase i) : 2 ≤ (supportColumns U {r} ∩ S).card := by
      obtain ⟨hri, hr⟩ := Finset.mem_erase.mp hr
      obtain ⟨j, hjS, hrj⟩ := mem_adjoint_supportColumns_iff.mp hr
      have hpos : 0 < (supportColumns U {r} ∩ S).card :=
        Finset.card_pos.mpr ⟨j, Finset.mem_inter.mpr ⟨mem_supportColumns_singleton.mpr hrj, hjS⟩⟩
      have hne := row_support_inter_card_ne_one hU hri
      change (supportColumns U {r} ∩ S).card ≠ 1 at hne
      omega
    have hlower : 2 * (R.erase i).card ≤ ∑ r ∈ R.erase i, (supportColumns U {r} ∩ S).card := by
      calc
        _ = ∑ r ∈ R.erase i, (2 : ℕ) := by simp [Nat.mul_comm]
        _ ≤ _ := Finset.sum_le_sum hmin
    have herase := Finset.sum_erase_add R (fun r => (supportColumns U {r} ∩ S).card) hiR
    change (∑ r ∈ R.erase i, (supportColumns U {r} ∩ S).card) +
      (S ∩ S).card = ∑ r ∈ R, (supportColumns U {r} ∩ S).card at herase
    rw [Finset.inter_self, hS, htotal] at herase
    rw [Finset.card_erase_of_mem hiR] at hlower
    change R.card ≤ 4
    omega
  · intro hR
    have hceq (j : ι) (hj : j ∈ S) : supportColumns Uᴴ {j} = R :=
      Finset.eq_of_subset_of_card_le (hsub j hj) (by rw [hcols j, hR])
    have hreq (r : ι) (hr : r ∈ R) : supportColumns U {r} = S := by
      apply (Finset.eq_of_subset_of_card_le _ (by rw [hrows r, hS])).symm
      intro j hj
      exact mem_supportColumns_singleton.mpr
        (mem_adjoint_supportColumns_singleton.mp (by rw [hceq j hj]; exact hr))
    ext j
    constructor
    · intro hj
      obtain ⟨r, hr, hrj⟩ := mem_supportColumns_iff.mp hj
      have hjr : j ∈ supportColumns U {r} := mem_supportColumns_singleton.mpr hrj
      rwa [hreq r hr] at hjr
    · intro hj
      exact mem_supportColumns_iff.mpr ⟨i, hiR, mem_supportColumns_singleton.mp hj⟩

end MOC
