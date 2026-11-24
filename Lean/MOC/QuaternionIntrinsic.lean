import MOC.FourParityCorrection
import Mathlib.GroupTheory.Perm.Cycle.Type

/-! Permutation displacement on a Klein four coordinate group, without
a table of signs or permutations. -/

open Finset BigOperators

namespace MOC.QuaternionIntrinsic

variable {G : Type*} [DecidableEq G]

private theorem two_mem_other {S : Finset G} (hc : S.card = 2)
    {x y z : G} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) (hz : z ∈ S) :
    z = x ∨ z = y := by
  have hsub : ({x,y} : Finset G) ⊆ S := by
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl <;> assumption
  have he : ({x,y} : Finset G) = S :=
    eq_of_subset_of_card_le hsub (by simp [hc, hxy])
  rwa [← he, mem_insert, mem_singleton] at hz

variable [Fintype G]

private theorem three_excluded_unique (hc : Fintype.card G = 4)
    {a b c x y : G} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c)
    (hya : y ≠ a) (hyb : y ≠ b) (hyc : y ≠ c) : x = y := by
  let S : Finset G := ({a,b,c} : Finset G)ᶜ
  have hS : S.card ≤ 1 := by
    rw [show S.card = Fintype.card G - ({a,b,c} : Finset G).card from card_compl _]
    simp [hc, hab, hac, hbc]
  exact (card_le_one.mp hS) x (by simp [S, hxa, hxb, hxc])
    y (by simp [S, hya, hyb, hyc])

variable [AddCommGroup G]

/-- Any permutation fixing zero on the Klein-four group is the identity,
a swap, or has bijective displacement. This uses only the number of
available labels and the exponent-two group operation. -/
theorem fixedOrigin_perm_types (hc : Fintype.card G = 4) (h2 : ∀ x : G, x+x=0)
    (f : Equiv.Perm G) (hf : f 0 = 0) :
    f = 1 ∨ (∃ x y : G, x ≠ y ∧ f = Equiv.swap x y) ∨
      Function.Bijective (fun x => f x + x) := by
  classical
  by_cases hfix : ∃ u : G, u ≠ 0 ∧ f u = u
  · obtain ⟨u, hu, hfu⟩ := hfix
    by_cases hid : f = 1
    · exact Or.inl hid
    right
    left
    have hmove : ∃ x : G, f x ≠ x := by
      by_contra! h
      exact hid (Equiv.ext h)
    obtain ⟨x, hx⟩ := hmove
    let y := f x
    have hxy : x ≠ y := Ne.symm hx
    have hxu : x ≠ u := by rintro rfl; exact hx hfu
    have hx0 : x ≠ 0 := by rintro rfl; exact hx hf
    have hyu : y ≠ u := by
      intro he
      exact hxu (f.injective (he.trans hfu.symm))
    have hy0 : y ≠ 0 := by
      intro he
      exact hx0 (f.injective (he.trans hf.symm))
    let S : Finset G := ({0,u} : Finset G)ᶜ
    have hS : S.card = 2 := by
      rw [show S.card = Fintype.card G - ({0,u} : Finset G).card from card_compl _]
      simp [hc, hu.symm]
    have hxS : x ∈ S := by simp [S, hx0, hxu]
    have hyS : y ∈ S := by simp [S, hy0, hyu]
    have hfy0 : f y ≠ 0 := fun h => hy0 (f.injective (h.trans hf.symm))
    have hfyu : f y ≠ u := fun h => hyu (f.injective (h.trans hfu.symm))
    have hfyS : f y ∈ S := by simp [S, hfy0, hfyu]
    have hfy : f y = x :=
      (two_mem_other hS hxS hyS hxy hfyS).resolve_right (fun he =>
        hxy (f.injective he.symm))
    refine ⟨x,y,hxy,Equiv.ext ?_⟩
    intro z
    by_cases hzx : z = x
    · subst z
      rw [Equiv.swap_apply_left]
    by_cases hzy : z = y
    · subst z
      rw [Equiv.swap_apply_right, hfy]
    rw [Equiv.swap_apply_of_ne_of_ne hzx hzy]
    by_cases hz0 : z = 0
    · simpa [hz0] using hf
    by_cases hzu : z = u
    · simpa [hzu] using hfu
    exact False.elim ((two_mem_other hS hxS hyS hxy (by simp [S, hz0, hzu])).elim hzx hzy)
  right
  right
  apply (Finite.injective_iff_bijective).mp
  intro x y hd
  by_contra hxy
  have hnon (z : G) (hz : z ≠ 0) : f z ≠ z :=
    fun h => hfix ⟨z,hz,h⟩
  have hz_imp (z : G) (h : f z + z = 0) : z = 0 := by
    by_contra hn
    apply hnon z hn
    exact add_right_cancel (h.trans (h2 z).symm)
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxy (hz_imp y (by simpa [hf] using hd.symm)).symm
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hxy (hz_imp x (by simpa [hf] using hd))
  let z := f x + x
  have hz0 : z ≠ 0 := fun h => hx0 (hz_imp x h)
  have hzx : z ≠ x := by
    intro h
    exact hx0 (f.injective ((add_right_cancel (h.trans (zero_add x).symm)).trans hf.symm))
  have hzy : z ≠ y := by
    intro h
    have he : f y + y = y := hd.symm.trans h
    exact hy0 (f.injective ((add_right_cancel (he.trans (zero_add y).symm)).trans hf.symm))
  have hfx0 : f x ≠ 0 := fun h => hx0 (f.injective (h.trans hf.symm))
  have hfy0 : f y ≠ 0 := fun h => hy0 (f.injective (h.trans hf.symm))
  have hfxz : f x ≠ z := by
    intro h
    exact hx0 (add_left_cancel (h.symm.trans (add_zero _).symm))
  have hfyz : f y ≠ z := by
    intro h
    have he : f y = f y + y := h.trans hd
    exact hy0 (add_left_cancel (he.symm.trans (add_zero _).symm))
  have hfx : f x = y :=
    three_excluded_unique hc (Ne.symm hx0) (Ne.symm hz0) hzx.symm
      hfx0 (hnon x hx0) hfxz hy0 (Ne.symm hxy) hzy.symm
  have hfy : f y = x :=
    three_excluded_unique hc (Ne.symm hy0) (Ne.symm hz0) hzy.symm
      hfy0 (hnon y hy0) hfyz hx0 hxy hzx.symm
  have hfz : f z = z :=
    three_excluded_unique hc (Ne.symm hx0) (Ne.symm hy0) hxy
      (fun h => hz0 (f.injective (h.trans hf.symm)))
      (fun h => hzy (f.injective (h.trans hfy.symm)))
      (fun h => hzx (f.injective (h.trans hfx.symm))) hz0 hzx hzy
  exact hnon z hz0 hfz


/-- The only three magnitudes occurring in an unsigned Leibniz
product of the Klein-displacement form. -/
theorem displacement_prod_types [CommMonoid M] (hc : Fintype.card G = 4)
    (h2 : ∀ x : G, x+x=0) (σ : Equiv.Perm G) (q : G → M) :
    (∏ j, q (σ j+j)) = q (σ 0)^4 ∨
    (∃ v : G, v ≠ σ 0 ∧ (∏ j, q (σ j+j)) = q (σ 0)^2*q v^2) ∨
      (Function.Bijective (fun j => σ j+j) ∧ (∏ j, q (σ j+j)) = ∏ j, q j) := by
  let p := σ 0
  let f : Equiv.Perm G := σ.trans (Equiv.subRight p)
  have hf (j : G) : f j = σ j-p := rfl
  have hf0 : f 0 = 0 := by simp [hf, p]
  have hdis (j : G) : σ j+j = f j+j+p := by rw [hf]; abel
  rcases fixedOrigin_perm_types hc h2 f hf0 with he | ⟨r,s,hrs,he⟩ | hb
  · left
    have h (j : G) : σ j+j = p := by simp [hdis, he, h2]
    simp_rw [h, Finset.prod_const, Finset.card_univ, hc]; rfl
  · right
    left
    have hne : r+s+p ≠ p := by
      intro h
      have h' : r+s = 0 := add_right_cancel (h.trans (zero_add p).symm)
      exact hrs (add_right_cancel (h'.trans (h2 s).symm))
    refine ⟨r+s+p, hne, ?_⟩
    have hr : σ r+r = r+s+p := by
      rw [hdis, he, Equiv.swap_apply_left]
      abel
    have hs : σ s+s = r+s+p := by rw [hdis, he, Equiv.swap_apply_right]
    have hout (j : G) (hjr : j ≠ r) (hjs : j ≠ s) : σ j+j = p := by
      rw [hdis, he, Equiv.swap_apply_of_ne_of_ne hjr hjs, h2, zero_add]
    let E : Finset G := ((univ : Finset G).erase r).erase s
    have hsE : s ∈ (univ : Finset G).erase r := mem_erase.mpr ⟨hrs.symm, mem_univ s⟩
    have hE : E.card = 2 := by
      simp only [E, card_erase_of_mem hsE, card_erase_of_mem (mem_univ r), card_univ, hc]
    have hprod : (∏ j ∈ E, q (σ j+j)) = q p^2 := by
      calc
        _ = ∏ _j ∈ E, q p := by
          apply Finset.prod_congr rfl
          intro j hj
          exact congrArg q (hout j (mem_erase.mp (mem_erase.mp hj).2).1 (mem_erase.mp hj).1)
        _ = _ := by rw [Finset.prod_const, hE]
    rw [← Finset.mul_prod_erase univ _ (mem_univ r),
      ← Finset.mul_prod_erase (univ.erase r) _ hsE, hr, hs]
    change q (r+s+p)* (q (r+s+p)* (∏ j ∈ E, q (σ j+j))) = _
    rw [hprod]
    simp only [pow_two]
    ac_rfl
  · right
    right
    have hbij : Function.Bijective (fun j => σ j+j) := by
      have h := (Equiv.addRight p).bijective.comp hb
      change Function.Bijective (fun x => f x+x+p) at h
      simpa only [← hdis] using h
    exact ⟨hbij, Equiv.prod_comp (Equiv.ofBijective _ hbij) q⟩


/-- Every translation of the Klein group is even. Nonzero translations
are fixed-point-free involutions, so their cycles are two pairs. -/
theorem klein_translation_even (hc : Fintype.card G = 4) (h2 : ∀ x : G, x+x=0)
    (p : G) : Equiv.Perm.sign (Equiv.addRight p) = 1 := by
  classical
  by_cases hp : p = 0
  · subst p
    have h : (Equiv.addRight (0 : G)) = (1 : Equiv.Perm G) := Equiv.ext (by simp)
    simp [h]
  let τ : Equiv.Perm G := Equiv.addRight p
  have hsup : τ.support = univ := by
    ext x
    simp only [Equiv.Perm.mem_support, mem_univ, iff_true]
    intro hx
    apply hp
    change x+p=x at hx
    exact add_left_cancel (hx.trans (add_zero x).symm)
  have ht : τ ^ 2 = 1 := by
    apply Equiv.ext
    intro x
    change x+p+p=x
    rw [add_assoc, h2 p, add_zero]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hparts := Equiv.Perm.pow_prime_eq_one_iff.mp ht
  have htype : τ.cycleType = Multiset.replicate τ.cycleType.card 2 :=
    Multiset.eq_replicate.mpr ⟨rfl, hparts⟩
  have hsum : τ.cycleType.sum = 4 := by
    rw [Equiv.Perm.sum_cycleType, hsup, card_univ, hc]
  have hcard : τ.cycleType.card = 2 := by
    have hh : τ.cycleType.card * 2 = 4 := by
      calc
        _ = τ.cycleType.sum := by
          conv_rhs => rw [htype]
          simp
        _ = _ := hsum
    omega
  change Equiv.Perm.sign τ = 1
  rw [Equiv.Perm.sign_of_cycleType, hsum, hcard]
  rfl

/-- Bijective displacement at a fixed origin forces a three-cycle and
hence positive parity; no permutation cases are tested. -/
theorem fixedOrigin_even_of_bijective_displacement (hc : Fintype.card G = 4)
    (h2 : ∀ x : G, x+x=0) (f : Equiv.Perm G) (hf : f 0 = 0)
    (h : Function.Bijective (fun x => f x+x)) :
    Equiv.Perm.sign f = 1 := by
  have hs : f.support = (univ : Finset G).erase 0 := by
    ext x
    simp only [Equiv.Perm.mem_support, mem_erase, mem_univ, and_true]
    constructor
    · intro hx h0
      exact hx (h0.symm ▸ hf)
    · intro hx hfx
      apply hx
      apply h.injective
      show f x+x=f 0+0
      rw [hfx, hf, h2, add_zero]
  have hc' : f.support.card = 3 := by
    rw [hs, card_erase_of_mem (mem_univ _), card_univ, hc]
  exact (card_support_eq_three_iff.mp hc').sign

end MOC.QuaternionIntrinsic
