import MOC.CollinearKernelSupport
import MOC.DisjointContactRectangle
import Mathlib.Data.Matrix.Rank
import Mathlib.GroupTheory.Perm.Cycle.Factors

/-! Rank-two cancellation propagates contact from transpositions to every
cycle at a zero-height support line. No simplicity or genericity is needed. -/

open BigOperators Matrix
open Equiv.Perm

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem det_additiveKernel_zero (a b : ι → ℂ) (h : 2 < Fintype.card ι) :
    (Matrix.of fun i j => a i + b j).det = 0 := by
  let A : Matrix ι ι ℂ := Matrix.of fun i j => a i + b j
  let L : Matrix ι (Fin 2) ℂ := Matrix.of fun i k => ![a i, 1] k
  let R : Matrix (Fin 2) ι ℂ := Matrix.of fun k j => ![1, b j] k
  have he : A = L * R := by
    ext i j
    simp [A, L, R, Matrix.mul_apply, Fin.sum_univ_two]
  change A.det = 0
  by_contra hn
  have hunit : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hn)
  have hA := Matrix.rank_of_isUnit A hunit
  have hr := (Matrix.rank_mul_le_left L R).trans (Matrix.rank_le_card_width L)
  rw [← he, hA, Fintype.card_fin] at hr
  omega

private theorem matchingProduct_ofSubtype (a b : ι → ℂ) (S : Finset ι)
    (τ : Equiv.Perm S) :
    matchingProduct a b (Equiv.Perm.ofSubtype τ) =
      (∏ j ∈ Sᶜ, (a j + b j)) * ∏ j : S, (a (τ j) + b j) := by
  unfold matchingProduct
  rw [← Finset.prod_compl_mul_prod S]
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    rw [Equiv.Perm.ofSubtype_apply_of_not_mem τ (Finset.mem_compl.mp hj)]
  · rw [← Finset.prod_coe_sort S]
    apply Finset.prod_congr rfl
    intro j _
    rw [Equiv.Perm.ofSubtype_apply_of_mem τ j.property]

private theorem sum_alternating_local_matchingProduct (a b : ι → ℂ) (S : Finset ι)
    (hS : 2 < S.card) (η : ℂ) :
    (∑ τ : Equiv.Perm S, (((Equiv.Perm.sign (Equiv.Perm.ofSubtype τ) : ℤ) : ℂ) *
      (η * matchingProduct a b (Equiv.Perm.ofSubtype τ)))) = 0 := by
  have hd := det_additiveKernel_zero (a ∘ Subtype.val : S → ℂ)
    (b ∘ Subtype.val : S → ℂ) (by rwa [Fintype.card_coe])
  rw [Matrix.det_apply'] at hd
  simp only [Matrix.of_apply, Function.comp_apply] at hd
  rw [← mul_zero (η * ∏ j ∈ Sᶜ, (a j + b j)), ← hd, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  rw [matchingProduct_ofSubtype, Equiv.Perm.sign_ofSubtype]
  rw [show @Subtype.fintype ι (fun i => i ∈ S) _ _ = Finset.Subtype.fintype S from
      Subsingleton.elim _ _]
  ring

omit [DecidableEq ι] in
private theorem eq_one_or_cycle_or_disjoint_pair (τ : Equiv.Perm ι) :
    τ = 1 ∨ τ.IsCycle ∨
      ∃ s t : Equiv.Perm ι, s ≠ 1 ∧ t ≠ 1 ∧ s.Disjoint t ∧ τ = s * t := by
  refine Equiv.Perm.cycle_induction_on (fun τ => τ = 1 ∨ τ.IsCycle ∨
    ∃ s t : Equiv.Perm ι, s ≠ 1 ∧ t ≠ 1 ∧ s.Disjoint t ∧ τ = s * t) τ ?_ ?_ ?_
  · exact Or.inl rfl
  · exact fun _ h => Or.inr (Or.inl h)
  · intro s t hd hs _ _
    by_cases ht : t = 1
    · rw [ht, mul_one]
      exact Or.inr (Or.inl hs)
    · exact Or.inr (Or.inr ⟨s, t, hs.ne_one, ht, hd, rfl⟩)

private theorem support_ofSubtype_le (S : Finset ι) (τ : Equiv.Perm S) :
    (Equiv.Perm.ofSubtype τ).support ⊆ S := by
  intro i hi
  by_contra hn
  exact (Equiv.Perm.mem_support.mp hi) (Equiv.Perm.ofSubtype_apply_of_not_mem τ hn)

private theorem re_zero_of_disjoint_change (a b : ι → ℂ) (η : ℂ)
    (s t : Equiv.Perm ι) (hd : s.Disjoint t)
    (hn : η * matchingProduct a b 1 ≠ 0)
    (h₀ : (η * matchingProduct a b 1).re = 0)
    (h₁ : (η * matchingProduct a b s).re = 0)
    (h₂ : (η * matchingProduct a b t).re = 0) :
    (η * matchingProduct a b (s * t)).re = 0 := by
  have h := matchingProduct_disjoint_perms_fourth_gap a b 1 s t hd η 0 h₀
    (by simpa only [one_mul] using h₁) (by simpa only [one_mul] using h₂)
  have him : (η * matchingProduct a b 1).im ≠ 0 :=
    fun he => hn (Complex.ext (by simpa using h₀) (by simpa using he))
  simp only [one_mul, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add, zero_sub, zero_mul] at h
  exact neg_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (pow_ne_zero 2 him))

private theorem matching_line_of_all_transpositions_at_zero_height_one
    (a b : ι → ℂ) (η : ℂ)
    (hn : η * matchingProduct a b 1 ≠ 0)
    (hp : (η * matchingProduct a b 1).re = 0)
    (hs : ∀ i j, i ≠ j → (η * matchingProduct a b (Equiv.swap i j)).re = 0)
    (hmax : ∀ σ, (η * matchingProduct a b σ).re ≤ 0) :
    ∀ σ, (η * matchingProduct a b σ).re = 0 := by
  classical
  let z (σ : Equiv.Perm ι) := (η * matchingProduct a b σ).re
  suffices H : ∀ m : ℕ, ∀ σ : Equiv.Perm ι, σ.support.card = m → z σ = 0 by
    intro σ
    exact H _ σ rfl
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro σ hm
    have hsmall (τ : Equiv.Perm ι) (ht : τ.support.card < m) : z τ = 0 :=
      ih _ ht _ rfl
    by_cases h₀ : m = 0
    · have he := Equiv.Perm.card_support_eq_zero.mp (hm.trans h₀)
      simpa only [he] using hp
    by_cases h₂ : m = 2
    · obtain ⟨i, j, hij, he⟩ := Equiv.Perm.card_support_eq_two.mp (hm.trans h₂)
      simpa only [he] using hs i j hij
    have hm₁ : m ≠ 1 := fun hh => Equiv.Perm.card_support_ne_one σ (hm.trans hh)
    have hbig : 2 < m := by omega
    have hnc (τ : Equiv.Perm ι) (ht : τ.support.card ≤ m) (hc : ¬ τ.IsCycle) : z τ = 0 := by
      rcases eq_one_or_cycle_or_disjoint_pair τ with h | h | ⟨s, t, hs', ht', hd, rfl⟩
      · simpa only [h] using hp
      · exact (hc h).elim
      · rw [hd.card_support_mul] at ht
        have hsc : 0 < s.support.card := by
          have := Equiv.Perm.one_lt_card_support_of_ne_one hs'
          omega
        have htc : 0 < t.support.card := by
          have := Equiv.Perm.one_lt_card_support_of_ne_one ht'
          omega
        exact re_zero_of_disjoint_change a b η s t hd hn hp (hsmall s (by omega)) (hsmall t (by omega))
    by_cases hcycle : σ.IsCycle
    swap
    · exact hnc σ hm.le hcycle
    let S := σ.support
    have hS : S.card = m := hm
    let c : ℤˣ := -(-1) ^ m
    let e (τ : Equiv.Perm S) : Equiv.Perm ι := Equiv.Perm.ofSubtype τ
    have hterm (τ : Equiv.Perm S) :
        ((((Equiv.Perm.sign (e τ) : ℤ) : ℂ) *
          (η * matchingProduct a b (e τ)))).re = ((c : ℤ) : ℝ) * z (e τ) := by
      rw [Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero]
      change (((Equiv.Perm.sign (e τ) : ℤ) : ℝ) * z (e τ)) = _
      have hle : (e τ).support.card ≤ m := hS ▸ Finset.card_le_card (support_ofSubtype_le S τ)
      by_cases hlt : (e τ).support.card < m
      · have hz := hsmall (e τ) hlt
        simp only [hz, mul_zero]
      by_cases hc : (e τ).IsCycle
      · have hcard : (e τ).support.card = m := by omega
        rw [hc.sign, hcard]
      · have hz := hnc (e τ) hle hc
        simp only [hz, mul_zero]
    have hsum := congrArg Complex.re (sum_alternating_local_matchingProduct a b S (hS ▸ hbig) η)
    simp only [Complex.re_sum, Complex.zero_re] at hsum
    change (∑ τ : Equiv.Perm S, ((((Equiv.Perm.sign (e τ) : ℤ) : ℂ) *
          (η * matchingProduct a b (e τ)))).re) = 0 at hsum
    simp_rw [hterm] at hsum
    rw [← Finset.mul_sum] at hsum
    have hs' := (mul_eq_zero.mp hsum).resolve_left (by exact_mod_cast Units.ne_zero c)
    have hz (τ : Equiv.Perm S) : z (e τ) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonpos (fun τ _ => hmax (e τ))).mp hs' τ (Finset.mem_univ _)
    have hσe : e σ.subtypePermOfSupport = σ := by
      exact Equiv.Perm.ofSubtype_subtypePerm _ (fun i hi => Equiv.Perm.mem_support.mpr hi)
    simpa only [hσe] using hz σ.subtypePermOfSupport

/-- At height zero, active transpositions at one nonzero pivot force the
entire matching hull onto the supporting line. Spectral collisions and zero
inactive products are permitted. -/
theorem matching_line_of_all_transpositions_at_zero_height
    (a b : ι → ℂ) (η : ℂ) (r : Equiv.Perm ι)
    (hn : η * matchingProduct a b r ≠ 0)
    (hp : (η * matchingProduct a b r).re = 0)
    (hs : ∀ i j, i ≠ j → (η * matchingProduct a b (r * Equiv.swap i j)).re = 0)
    (hmax : ∀ σ, (η * matchingProduct a b σ).re ≤ 0) :
    ∀ σ, (η * matchingProduct a b σ).re = 0 := by
  let a' := a ∘ r
  have he (σ : Equiv.Perm ι) : matchingProduct a' b σ = matchingProduct a b (r * σ) := rfl
  have hl := matching_line_of_all_transpositions_at_zero_height_one a' b η
    (by simpa only [he, mul_one] using hn) (by simpa only [he, mul_one] using hp)
    (fun i j hij => by simpa only [he] using hs i j hij) (fun σ => by simpa only [he] using hmax (r * σ))
  intro σ
  simpa only [he, ← mul_assoc, mul_inv_cancel, one_mul] using hl (r⁻¹ * σ)

/-- The all-transposition zero-height face is covered for every relative unitary. -/
theorem holds_of_all_transpositions_at_zero_height [Nonempty ι]
    (a b : ι → ℂ) (η : ℂ) (r : Equiv.Perm ι)
    (hn : η * matchingProduct a b r ≠ 0)
    (hp : (η * matchingProduct a b r).re = 0)
    (hs : ∀ i j, i ≠ j → (η * matchingProduct a b (r * Equiv.swap i j)).re = 0)
    (hmax : ∀ σ, (η * matchingProduct a b σ).re ≤ 0)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    Holds a b U :=
  holds_of_matching_line_through_origin a b η
    (fun h => hn (by simp [h]))
    (matching_line_of_all_transpositions_at_zero_height a b η r hn hp hs hmax) U hU


/-- A clique of active swaps at a nonzero, zero-height pivot makes its
entire matching fibre active. No allowed-edge connectivity is assumed. -/
theorem matching_fibre_zero_height_of_transposition_clique
    (a b : ι → ℂ) (η : ℂ) (r : Equiv.Perm ι) (S : Finset ι)
    (hn : η * matchingProduct a b r ≠ 0)
    (hp : (η * matchingProduct a b r).re = 0)
    (hs : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      (η * matchingProduct a b (r * Equiv.swap i j)).re = 0)
    (hmax : ∀ σ, (η * matchingProduct a b σ).re ≤ 0) :
    ∀ τ : Equiv.Perm S, (η * matchingProduct a b (r * Equiv.Perm.ofSubtype τ)).re = 0 := by
  let a' := a ∘ r
  let A : S → ℂ := a' ∘ Subtype.val
  let B : S → ℂ := b ∘ Subtype.val
  let c : ℂ := η * ∏ j ∈ Sᶜ, (a' j + b j)
  have he (τ : Equiv.Perm S) :
      η * matchingProduct a b (r * Equiv.Perm.ofSubtype τ) = c * matchingProduct A B τ := by
    change η * matchingProduct a' b (Equiv.Perm.ofSubtype τ) = _
    rw [matchingProduct_ofSubtype, mul_assoc]
    rfl
  have hz := matching_line_of_all_transpositions_at_zero_height_one A B c
    (by simpa only [← he, MonoidHom.map_one, mul_one] using hn)
    (by simpa only [← he, MonoidHom.map_one, mul_one] using hp)
    (fun i j hij => by
      rw [← he, Equiv.Perm.ofSubtype_swap_eq]
      exact hs i i.property j j.property (fun h => hij (Subtype.ext h)))
    (fun τ => by rw [← he]; exact hmax _)
  intro τ
  rw [he, hz]

/-- A nonzero contact of a strict zero-height profile has an inactive
nonzero transposition neighbor. In particular its nonzero matching graph
component cannot consist entirely of contacts. -/
theorem exists_nonzero_inactive_swap_of_not_holds_at_zero_height
    (a b : ι → ℂ) (η : ℂ) (r : Equiv.Perm ι) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (hbad : ¬ Holds a b U)
    (hn : η * matchingProduct a b r ≠ 0)
    (hp : (η * matchingProduct a b r).re = 0)
    (hmax : ∀ σ, (η * matchingProduct a b σ).re ≤ 0) :
    ∃ i j : ι, i ≠ j ∧ (η * matchingProduct a b (r * Equiv.swap i j)).re < 0 ∧
      matchingProduct a b (r * Equiv.swap i j) ≠ 0 := by
  classical
  haveI : Nonempty ι := by
    by_contra! h
    letI : IsEmpty ι := not_nonempty_iff.mp h
    have hd : determinantValue a b U = matchingProduct a b r := by
      unfold determinantValue matchingProduct
      simp
    apply hbad
    unfold Holds
    rw [hd]
    exact matchingProduct_mem_hull a b r
  by_contra h
  have hs (i j : ι) (hij : i ≠ j) :
      (η * matchingProduct a b (r * Equiv.swap i j)).re = 0 := by
    apply le_antisymm (hmax _)
    by_contra! hlt
    apply h
    refine ⟨i, j, hij, hlt, ?_⟩
    intro hz
    simp [hz] at hlt
  exact hbad (holds_of_all_transpositions_at_zero_height a b η r hn hp hs hmax U hU)

end

end MOC
