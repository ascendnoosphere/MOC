import MOC.MatchingTriangle
import MOC.MatchingProfileClosed

open Set
namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- On any three chosen columns, a nonzero exact matching profile has a
second nonzero label in the same matching fibre.  No limiting argument
or ordering of complex phases is needed for this local obstruction. -/
theorem exists_nonzero_matching_agree_outside_triple
    (a b : ι → ℂ) (σ : Equiv.Perm ι) (hσ : matchingProduct a b σ ≠ 0)
    (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ τ : Equiv.Perm ι, τ ≠ σ ∧ matchingProduct a b τ ≠ 0 ∧
      ∀ m, m ≠ i → m ≠ j → m ≠ k → τ m = σ m := by
  classical
  have h (ν : Equiv.Perm ι) (hν : ν ≠ 1)
      (hfix : ∀ m, m ≠ i → m ≠ j → m ≠ k → ν m = m) :
      matchingProduct a b (σ * ν) = 0 ∨
      ∃ τ : Equiv.Perm ι, τ ≠ σ ∧ matchingProduct a b τ ≠ 0 ∧
        ∀ m, m ≠ i → m ≠ j → m ≠ k → τ m = σ m := by
    by_cases hp : matchingProduct a b (σ * ν) = 0
    · exact Or.inl hp
    · exact Or.inr ⟨σ * ν, fun h => hν (mul_left_cancel (h.trans (mul_one σ).symm)), hp,
        fun m hi hj hk => by rw [Equiv.Perm.mul_apply, hfix m hi hj hk]⟩
  have hn (u v : ι) (huv : u ≠ v) : Equiv.swap u v ≠ (1 : Equiv.Perm ι) := by
    intro he
    exact huv.symm (by simpa using congrFun (congrArg DFunLike.coe he) u)
  rcases h (Equiv.swap i j) (hn i j hij)
    (fun _ hi hj _ => Equiv.swap_apply_of_ne_of_ne hi hj) with h1 | h1
  · rcases h (Equiv.swap i k) (hn i k hik)
      (fun _ hi _ hk => Equiv.swap_apply_of_ne_of_ne hi hk) with h2 | h2
    · rcases h (Equiv.swap j k) (hn j k hjk)
        (fun _ _ hj hk => Equiv.swap_apply_of_ne_of_ne hj hk) with h3 | h3
      · have hc1 : Equiv.swap i j * Equiv.swap j k ≠ (1 : Equiv.Perm ι) := by
          intro he
          have hh := congrArg (fun ν : Equiv.Perm ι => ν i) he
          simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hij hik, hij.symm] at hh
        have hc2 : Equiv.swap j k * Equiv.swap i j ≠ (1 : Equiv.Perm ι) := by
          intro he
          have hh := congrArg (fun ν : Equiv.Perm ι => ν i) he
          simp [Equiv.Perm.mul_apply, hik.symm] at hh
        rcases h (Equiv.swap i j * Equiv.swap j k) hc1 (fun m hi hj hk => by
          simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hi hj,
            Equiv.swap_apply_of_ne_of_ne hj hk]) with h4 | h4
        · rcases h (Equiv.swap j k * Equiv.swap i j) hc2 (fun m hi hj hk => by
            simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hi hj,
              Equiv.swap_apply_of_ne_of_ne hj hk]) with h5 | h5
          · have ht := matchingProduct_triangle_identity a b σ i j k hij hik hjk
            simp only [mul_assoc, h1, h2, h3, h4, h5, add_zero] at ht
            exact False.elim (hσ ht)
          · exact h5
        · exact h4
      · exact h3
    · exact h2
  · exact h1

/-- If one label is nonzero, and a second candidate label moves a specified
column, three columns other than that column force a third nonzero label.
This applies even when the candidate itself happens to be zero. -/
theorem exists_nonzero_matching_ne_two_of_four
    (a b : ι → ℂ) (σ ρ : Equiv.Perm ι) (hσ : matchingProduct a b σ ≠ 0)
    (m i j k : ι) (hm : ρ m ≠ σ m) (hmi : m ≠ i) (hmj : m ≠ j) (hmk : m ≠ k)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ τ : Equiv.Perm ι, τ ≠ σ ∧ τ ≠ ρ ∧ matchingProduct a b τ ≠ 0 := by
  obtain ⟨τ, ht, hn, hf⟩ := exists_nonzero_matching_agree_outside_triple a b σ hσ i j k hij hik hjk
  exact ⟨τ, ht, fun he => hm (he ▸ hf m hmi hmj hmk), hn⟩

/-- Every nonzero exact matching profile in order at least four has support
outside any prescribed pair of labels containing a nonzero entry. -/
theorem exists_nonzero_matching_ne_two
    (hcard : 4 ≤ Fintype.card ι) (a b : ι → ℂ)
    (σ ρ : Equiv.Perm ι) (hne : ρ ≠ σ) (hσ : matchingProduct a b σ ≠ 0) :
    ∃ τ : Equiv.Perm ι, τ ≠ σ ∧ τ ≠ ρ ∧ matchingProduct a b τ ≠ 0 := by
  classical
  obtain ⟨m, hm⟩ : ∃ m, ρ m ≠ σ m := by
    by_contra! H
    exact hne (Equiv.ext H)
  let S : Finset ι := Finset.univ.erase m
  have hS : 3 ≤ S.card := by
    dsimp only [S]
    rw [Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ]
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  have hSi : 2 ≤ (S.erase i).card := by
    rw [Finset.card_erase_of_mem hi]
    omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (show 0 < (S.erase i).card by omega)
  have hSij : 1 ≤ ((S.erase i).erase j).card := by
    rw [Finset.card_erase_of_mem hj]
    omega
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hSij
  have hji := Finset.mem_erase.mp hj
  have hkj := Finset.mem_erase.mp hk
  have hki := Finset.mem_erase.mp hkj.2
  exact exists_nonzero_matching_ne_two_of_four a b σ ρ hσ m i j k hm
    (Finset.mem_erase.mp hi).1.symm (Finset.mem_erase.mp hji.2).1.symm
    (Finset.mem_erase.mp hki.2).1.symm hji.1.symm hki.1.symm hkj.1.symm

/-- The obstruction passes to any normalized complex spectral limit whose
approximating profiles are exact. Rescaling by roots is separate from this
closure lemma. -/
theorem exists_nonzero_matching_limit_ne_two {α : Type*} {l : Filter α} [l.NeBot]
    (hcard : 4 ≤ Fintype.card ι)
    (P : α → Equiv.Perm ι → ℂ) (p : Equiv.Perm ι → ℂ)
    (hexact : ∀ᶠ t in l, ∃ a b : ι → ℂ, matchingProduct a b = P t)
    (hlim : Filter.Tendsto P l (nhds p))
    (σ ρ : Equiv.Perm ι) (hne : ρ ≠ σ) (hσ : p σ ≠ 0) :
    ∃ τ : Equiv.Perm ι, τ ≠ σ ∧ τ ≠ ρ ∧ p τ ≠ 0 := by
  obtain ⟨a, b, rfl⟩ := isClosed_additive_matching_profiles.mem_of_tendsto hlim hexact
  exact exists_nonzero_matching_ne_two hcard a b σ ρ hne hσ

end MOC
