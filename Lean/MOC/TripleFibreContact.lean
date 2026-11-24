import MOC.ContactRectangle

/-! A triangle fibre with simple spectra cannot be entirely active on a
nonzero supporting height. No list of permutations is used: translations
give all pairs of leftover row and column labels uniformly. -/

open BigOperators Matrix

namespace MOC
noncomputable section

private theorem triangle_match_expand (a b : Fin 3 → ℂ) (r : Equiv.Perm (Fin 3))
    (j : Fin 3) :
    matchingProduct a b r =
      (a (r j) + b j) * (a (r (j + 1)) + b (j + 1)) * (a (r (j + 2)) + b (j + 2)) := by
  unfold matchingProduct
  rw [← Equiv.prod_comp (Equiv.addLeft j) (fun k => a (r k) + b k), Fin.prod_univ_three]
  simp

private theorem triangle_one_ne_two (j : Fin 3) : j + 1 ≠ j + 2 :=
  fun h => (by decide : (1 : Fin 3) ≠ 2) (add_left_cancel h)

private theorem triangle_self_ne_one (j : Fin 3) : j ≠ j + 1 := by
  intro h
  have he : j + 0 = j + 1 := by simpa only [add_zero] using h
  exact (by decide : (0 : Fin 3) ≠ 1) (add_left_cancel he)

private theorem triangle_self_ne_two (j : Fin 3) : j ≠ j + 2 := by
  intro h
  have he : j + 0 = j + 2 := by simpa only [add_zero] using h
  exact (by decide : (0 : Fin 3) ≠ 2) (add_left_cancel he)

private theorem triangle_translated_swap_difference (a b : Fin 3 → ℂ) (i j : Fin 3) :
    let r := Equiv.addLeft (i - j)
    matchingProduct a b r -
      matchingProduct a b (r * Equiv.swap (j + 1) (j + 2)) =
       (a (i + 1) - a (i + 2)) * (b (j + 2) - b (j + 1)) * (a i + b j) := by
  intro r
  have hr (k : Fin 3) : r k = (i - j) + k := rfl
  have he : (i - j) + j = i := sub_add_cancel i j
  have h₀ : r j = i := (hr j).trans he
  have h₁ : r (j + 1) = i + 1 := by rw [hr, ← add_assoc, he]
  have h₂ : r (j + 2) = i + 2 := by rw [hr, ← add_assoc, he]
  rw [triangle_match_expand a b r j, triangle_match_expand a b
    (r * Equiv.swap (j+1) (j+2)) j]
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (triangle_self_ne_one j)
    (triangle_self_ne_two j), Equiv.swap_apply_left, Equiv.swap_apply_right, h₀, h₁, h₂]
  ring

/-- An entire three-label fibre with simple spectra and a nonzero outside
factor cannot lie on a nonzero supporting line. An arbitrary complex
outside factor and support direction are absorbed into `d`. -/
theorem triangle_fibre_all_contacts_height_zero (a b : Fin 3 → ℂ)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (d : ℂ) (H : ℝ)
    (hcontact : ∀ σ : Equiv.Perm (Fin 3), (d * matchingProduct a b σ).re = H) :
    H = 0 := by
  by_contra hH
  let A (i : Fin 3) := a (i + 1) - a (i + 2)
  let B (j : Fin 3) := b (j + 2) - b (j + 1)
  let z (σ : Equiv.Perm (Fin 3)) := d * matchingProduct a b σ
  have hd : d ≠ 0 := by
    intro h
    exact hH (by simpa [h] using (hcontact 1).symm)
  have hA (i : Fin 3) : A i ≠ 0 := sub_ne_zero.mpr (ha.ne (triangle_one_ne_two i))
  have hB (j : Fin 3) : B j ≠ 0 := sub_ne_zero.mpr (hb.ne (Ne.symm (triangle_one_ne_two j)))
  let K (i j : Fin 3) := d * (A i * B j * (a i + b j))
  have hK (i j : Fin 3) : (K i j).re = 0 := by
    have he := triangle_translated_swap_difference a b i j
    change matchingProduct a b _ - matchingProduct a b _ = A i * B j * (a i + b j) at he
    unfold K
    rw [← he, mul_sub, Complex.sub_re, hcontact, hcontact, sub_self]
  let c := d ^ 2 * ((∏ i, A i) * ∏ j, B j)
  have hc : c ≠ 0 := mul_ne_zero (pow_ne_zero _ hd) (mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr fun i _ => hA i)
    (Finset.prod_ne_zero_iff.mpr fun j _ => hB j))
  have hcz (σ : Equiv.Perm (Fin 3)) : (c * z σ).re = 0 := by
    have hp : (∏ j, K (σ j) j) = c * z σ := by
      simp only [K, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Equiv.prod_comp σ A, c, z, matchingProduct]
      ring
    rw [← hp, Fin.prod_univ_three]
    simp only [Complex.mul_re, Complex.mul_im, hK, zero_mul, mul_zero, zero_add, add_zero, sub_zero]
  let s : Equiv.Perm (Fin 3) := Equiv.swap (0 + 1) (0 + 2)
  have hdiff : z 1 - z s = K 0 0 := by
    have he := triangle_translated_swap_difference a b 0 0
    have hr : Equiv.addLeft ((0 : Fin 3) - 0) = 1 := by ext k; simp
    simp only [hr, one_mul] at he
    change matchingProduct a b 1 - matchingProduct a b s = _ at he
    dsimp only [z, K]
    rw [← mul_sub, he]
  by_cases hentry : a 0 + b 0 = 0
  · have hn : matchingProduct a b 1 = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ 0) (by simpa using hentry)
    exact hH (by simpa [hn] using (hcontact 1).symm)
  · have hne : z 1 - z s ≠ 0 := by
      rw [hdiff]
      exact mul_ne_zero hd (mul_ne_zero (mul_ne_zero (hA 0) (hB 0)) hentry)
    have hre : (z 1 - z s).re = 0 := by
      simp only [Complex.sub_re, z, hcontact, sub_self]
    have him : (z 1 - z s).im ≠ 0 := fun h =>
      hne (Complex.ext (by simpa using hre) (by simpa using h))
    have hz : (c * (z 1 - z s)).re = 0 := by
      rw [mul_sub, Complex.sub_re, hcz, hcz, sub_self]
    rw [Complex.mul_re, hre, mul_zero, zero_sub, neg_eq_zero, mul_eq_zero] at hz
    have hcim := hz.resolve_right him
    have hcre : c.re ≠ 0 := fun h =>
      hc (Complex.ext (by simpa using h) (by simpa using hcim))
    have hf := hcz 1
    change (c * (d * matchingProduct a b 1)).re = 0 at hf
    rw [Complex.mul_re, hcontact, hcim, zero_mul, sub_zero, mul_eq_zero] at hf
    exact hH (hf.resolve_left hcre)

/-- Every parity class of a three-label fibre has the same total deficit.
This is the determinant identity for a rank-two kernel, not a list of
the six products. -/
theorem triangle_fibre_parity_gap_sum (a b : Fin 3 → ℂ) (d : ℂ) (H : ℝ) :
    let gap (σ : Equiv.Perm (Fin 3)) := H - (d * matchingProduct a b σ).re
    ∑ σ ∈ Equiv.Perm.ofSign 1, gap σ = ∑ σ ∈ Equiv.Perm.ofSign (-1), gap σ := by
  intro gap
  let K : Matrix (Fin 3) (Fin 3) ℂ := Matrix.of fun i j => a j + b i
  have hdet : K.det = 0 := by
    simp only [Matrix.det_fin_three, K, Matrix.of_apply]
    ring
  have hsum : ∑ σ ∈ Equiv.Perm.ofSign 1, matchingProduct a b σ =
      ∑ σ ∈ Equiv.Perm.ofSign (-1), matchingProduct a b σ := by
    rw [Matrix.det_eq_detp_sub_detp, sub_eq_zero] at hdet
    exact hdet
  let A : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun _ _ => (1 : ℝ)
  have hcard : ((Equiv.Perm.ofSign (α := Fin 3) 1).card : ℝ) =
      ((Equiv.Perm.ofSign (α := Fin 3) (-1)).card : ℝ) := by
    have ha : A.det = 0 := by
      simp [Matrix.det_fin_three, A]
    rw [Matrix.det_eq_detp_sub_detp, sub_eq_zero] at ha
    simpa [A, Matrix.detp] using ha
  have hreal : ∑ σ ∈ Equiv.Perm.ofSign 1, (d * matchingProduct a b σ).re =
      ∑ σ ∈ Equiv.Perm.ofSign (-1), (d * matchingProduct a b σ).re := by
    simpa only [Finset.mul_sum, map_sum, Complex.reLm_coe] using
      congrArg (fun z : ℂ => Complex.reLm (d * z)) hsum
  simp only [gap, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard, hreal]

/-- At nonzero support height, simple triangle data require an inactive
matching of each parity. This also covers slices with zero complex products. -/
theorem triangle_fibre_inactive_each_parity (a b : Fin 3 → ℂ)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (d : ℂ) (H : ℝ) (hH : H ≠ 0)
    (hs : ∀ σ : Equiv.Perm (Fin 3), (d * matchingProduct a b σ).re ≤ H) :
    (∃ σ : Equiv.Perm (Fin 3), σ.sign = 1 ∧ (d * matchingProduct a b σ).re < H) ∧
    (∃ σ : Equiv.Perm (Fin 3), σ.sign = -1 ∧ (d * matchingProduct a b σ).re < H) := by
  let gap (σ : Equiv.Perm (Fin 3)) := H - (d * matchingProduct a b σ).re
  have hg σ : 0 ≤ gap σ := sub_nonneg.mpr (hs σ)
  have hp := triangle_fibre_parity_gap_sum a b d H
  change ∑ σ ∈ Equiv.Perm.ofSign 1, gap σ = ∑ σ ∈ Equiv.Perm.ofSign (-1), gap σ at hp
  have hz (s : ℤˣ) : (∑ σ ∈ Equiv.Perm.ofSign s, gap σ) = 0 ↔
      ∀ σ, σ.sign = s → gap σ = 0 := by
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun σ _ => hg σ)]
    simp only [Equiv.Perm.mem_ofSign]
  have hsum : (∑ σ ∈ Equiv.Perm.ofSign (α := Fin 3) 1, gap σ) ≠ 0 := by
    intro h
    have he := (hz 1).mp h
    have ho := (hz (-1)).mp (hp.symm.trans h)
    apply hH (triangle_fibre_all_contacts_height_zero a b ha hb d H (fun σ => ?_))
    rcases Int.units_eq_one_or σ.sign with h' | h'
    · exact (sub_eq_zero.mp (he σ h')).symm
    · exact (sub_eq_zero.mp (ho σ h')).symm
  constructor
  · by_contra! h
    apply hsum ((hz 1).mpr fun σ hσ => sub_eq_zero.mpr (le_antisymm (h σ hσ) (hs σ)))
  · by_contra! h
    apply hsum (hp.trans ((hz (-1)).mpr fun σ hσ =>
      sub_eq_zero.mpr (le_antisymm (h σ hσ) (hs σ))))

/-- The number of contacts in a simple three-label fibre is at most four
at nonzero support height. The proof removes one matching of each parity;
it never enumerates the possible contact sets. -/
theorem card_triangle_fibre_contacts_le_four (a b : Fin 3 → ℂ)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (d : ℂ) (H : ℝ) (hH : H ≠ 0)
    (hs : ∀ σ : Equiv.Perm (Fin 3), (d * matchingProduct a b σ).re ≤ H) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 3) =>
      (d * matchingProduct a b σ).re = H)).card ≤ 4 := by
  classical
  obtain ⟨⟨p, hp₁, hp⟩, ⟨q, hq₁, hq⟩⟩ := triangle_fibre_inactive_each_parity a b ha hb d H hH hs
  have hpq : p ≠ q := by
    intro h
    rw [h, hq₁] at hp₁
    exact (by decide : (-1 : ℤˣ) ≠ 1) hp₁
  have hqMem : q ∈ (Finset.univ : Finset (Equiv.Perm (Fin 3))).erase p :=
    Finset.mem_erase.mpr ⟨Ne.symm hpq, Finset.mem_univ _⟩
  have hle : (Finset.univ.filter (fun σ : Equiv.Perm (Fin 3) =>
      (d * matchingProduct a b σ).re = H)) ⊆ (Finset.univ.erase p).erase q := by
    intro σ hσ
    have hh := (Finset.mem_filter.mp hσ).2
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩⟩
    · rintro rfl
      exact hq.ne hh
    · rintro rfl
      exact hp.ne hh
  refine (Finset.card_le_card hle).trans ?_
  rw [Finset.card_erase_of_mem hqMem, Finset.card_erase_of_mem (Finset.mem_univ p),
    Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  decide

end
end MOC
