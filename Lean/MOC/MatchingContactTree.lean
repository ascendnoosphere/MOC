import MOC.MatchingTriangle
import Mathlib.Logic.Relation
import Mathlib.Tactic.FieldSimp

/-! A zero support line through all pivot-swap contacts and the contacts
of a connected graph on the other labels contains every matching product. -/

open BigOperators

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
private theorem im_prod_eq_zero (s : Finset ι) (f : ι → ℂ)
    (h : ∀ i ∈ s, (f i).im = 0) : (∏ i ∈ s, f i).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  rw [map_prod]
  exact Finset.prod_congr rfl fun i hi => Complex.conj_eq_iff_im.mpr (h i hi)

private theorem im_eq_zero_of_pure_mul {z w : ℂ} (hz : z.re = 0) (hnz : z ≠ 0)
    (h : (z * w).re = 0) : w.im = 0 := by
  have him : z.im ≠ 0 := fun he => hnz (Complex.ext hz he)
  simp only [Complex.mul_re, hz, zero_mul, zero_sub, neg_eq_zero] at h
  exact (mul_eq_zero.mp h).resolve_left him

private theorem prod_split_perm (F : ι → ι → ℂ) (s : Finset ι) (σ : Equiv.Perm ι)
    (h : ∀ m ∈ sᶜ, σ m = m) :
    (∏ m, F (σ m) m) =
      (∏ m ∈ sᶜ, F m m) * (∏ m ∈ s, F (σ m) m) := by
  rw [← Finset.prod_compl_mul_prod s (fun m => F (σ m) m)]
  congr 1
  exact Finset.prod_congr rfl fun m hm => by rw [h m hm]

/-- A pivot with all incident swaps active, together with connected active
swaps among the other labels, forces all matching projections to vanish
at zero support height. A spanning tree among the nonpivot labels supplies
the connectivity hypothesis using only `2 * Fintype.card ι - 2` contacts
including the reference matching. -/
theorem matchingProduct_re_eq_zero_of_contact_tree
    (a b : ι → ℂ) (η : ℂ) (r : Equiv.Perm ι) (p : ι)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hnz : ∀ i j, a i + b j ≠ 0) (hη : η ≠ 0)
    (href : (η * matchingProduct a b r).re = 0)
    (hsupport : ∀ σ, (η * matchingProduct a b σ).re ≤ 0)
    (hstar : ∀ i, i ≠ p → (η * matchingProduct a b (r * Equiv.swap p i)).re = 0)
    (hconn : ∀ i j : {k : ι // k ≠ p},
      Relation.ReflTransGen (fun x y : {k : ι // k ≠ p} =>
        x.val ≠ y.val ∧ (η * matchingProduct a b (r * Equiv.swap x.val y.val)).re = 0)
        i j) :
    ∀ σ, (η * matchingProduct a b σ).re = 0 := by
  let X (i : ι) : ℂ := (a (r i) - a (r p)) / (a (r i) + b p)
  let Y (j : ι) : ℂ := (b p - b j) / (a (r p) + b j)
  let F (i j : ι) : ℂ := 1 + X i * Y j
  let C : ℂ := (∏ j, (a (r j) + b p)) * (∏ j, (a (r p) + b j) / (a (r p) + b p))
  let P (σ : Equiv.Perm ι) : ℂ := ∏ j, F (σ j) j
  have hrow (j : ι) : F p j = 1 := by simp [F, X]
  have hcol (i : ι) : F i p = 1 := by simp [F, Y]
  have hentry (i j : ι) : a (r i) + b j =
      ((a (r i) + b p) * ((a (r p) + b j) / (a (r p) + b p))) * F i j := by
    dsimp [F, X, Y]
    field_simp [hnz] <;> ring
  have hFne (i j : ι) : F i j ≠ 0 := by
    intro h
    exact hnz (r i) j (by rw [hentry i j, h, mul_zero])
  have hnorm (σ : Equiv.Perm ι) : matchingProduct a b (r * σ) = C * P σ := by
    calc
      _ = ∏ j, ((a (r (σ j)) + b p) * ((a (r p) + b j) / (a (r p) + b p))) *
          F (σ j) j := Finset.prod_congr rfl fun j _ => hentry (σ j) j
      _ = _ := by
        simp only [C, P, Finset.prod_mul_distrib,
          Equiv.prod_comp σ (fun i => a (r i) + b p)]
  have hbase : matchingProduct a b r = C * P 1 := by simpa using hnorm 1
  have hne (σ : Equiv.Perm ι) : η * matchingProduct a b σ ≠ 0 :=
    mul_ne_zero hη (Finset.prod_ne_zero_iff.mpr fun i _ => hnz (σ i) i)
  have hdiag (i : ι) : (F i i).im = 0 := by
    by_cases hi : i = p
    · subst i
      simp [hrow]
    let S : Finset ι := {p, i}
    have hf (m : ι) (hm : m ∈ Sᶜ) : Equiv.swap p i m = m := by
      have hn : m ≠ p ∧ m ≠ i := by simpa [S, not_or] using Finset.mem_compl.mp hm
      exact Equiv.swap_apply_of_ne_of_ne hn.1 hn.2
    have hid : P 1 = (∏ m ∈ Sᶜ, F m m) * F i i := by
      change (∏ m, F ((1 : Equiv.Perm ι) m) m) = _
      rw [prod_split_perm F S 1 (fun _ _ => rfl)]
      change (∏ m ∈ Sᶜ, F m m) * (∏ m ∈ ({p, i} : Finset ι), F m m) = _
      rw [Finset.prod_pair (Ne.symm hi), hrow, one_mul]
    have hswap : P (Equiv.swap p i) = ∏ m ∈ Sᶜ, F m m := by
      change (∏ m, F ((Equiv.swap p i) m) m) = _
      rw [prod_split_perm F S (Equiv.swap p i) hf]
      change (∏ m ∈ Sᶜ, F m m) * (∏ m ∈ ({p, i} : Finset ι), F (Equiv.swap p i m) m) = _
      rw [Finset.prod_pair (Ne.symm hi)]
      simp only [Equiv.swap_apply_left, Equiv.swap_apply_right, hrow, hcol, mul_one]
    have he : (η * matchingProduct a b (r * Equiv.swap p i)) * F i i =
        η * matchingProduct a b r := by
      rw [hnorm (Equiv.swap p i), hbase, hswap, hid]
      ring
    exact im_eq_zero_of_pure_mul (hstar i hi) (hne _) (by rw [he, href])
  have hP : (P 1).im = 0 := im_prod_eq_zero Finset.univ _ fun i _ => hdiag i
  have hPn : (P 1).re ≠ 0 := fun h =>
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hFne i i) : P 1 ≠ 0) (Complex.ext h hP)
  have hCeq (σ : Equiv.Perm ι) :
      η * matchingProduct a b (r * σ) = (η * C) * P σ := by
    rw [hnorm σ, mul_assoc η C (P σ)]
  have hCne : η * C ≠ 0 := by
    intro hn
    exact hne (r * 1) (by rw [hCeq 1, hn, zero_mul])
  have hC : (η * C).re = 0 := by
    have hz : ((η * C) * P 1).re = 0 := by rw [← hCeq 1, mul_one, href]
    simp only [Complex.mul_re, hP, mul_zero, sub_zero] at hz
    exact (mul_eq_zero.mp hz).resolve_right hPn
  have hedge (i j : ι) (hi : i ≠ p) (hj : j ≠ p) (hij : i ≠ j)
      (hij' : (η * matchingProduct a b (r * Equiv.swap i j)).re = 0) :
      (F i j).im = 0 := by
    let τ := Equiv.swap i j * Equiv.swap p i
    let S : Finset ι := {p, i, j}
    let R : ℂ := ∏ m ∈ Sᶜ, F m m
    have hsum := matching_cycle_gap_sum_eq_swaps a b η r p i j hi.symm hj.symm hij
    simp only [matchingGap, href, hstar i hi, hstar j hj, hij', sub_zero, zero_add] at hsum
    have hτ : (η * matchingProduct a b (r * τ)).re = 0 := by
      have h₁ := hsupport (r * Equiv.swap p i * Equiv.swap i j)
      have h₂ := hsupport (r * Equiv.swap i j * Equiv.swap p i)
      unfold τ
      rw [← mul_assoc]
      linarith only [hsum, h₁, h₂]
    have hτfix (m : ι) (hm : m ∈ Sᶜ) : τ m = m := by
      have hout : m ≠ p ∧ m ≠ i ∧ m ≠ j := by
        simpa [S, not_or] using Finset.mem_compl.mp hm
      simp only [τ, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne hout.1 hout.2.1,
        Equiv.swap_apply_of_ne_of_ne hout.2.1 hout.2.2]
    have hτP : P τ = R * F i j := by
      change (∏ m, F (τ m) m) = _
      rw [prod_split_perm F S τ hτfix]
      change R * (∏ m ∈ ({p, i, j} : Finset ι), F (τ m) m) = _
      rw [Finset.prod_insert (show p ∉ ({i, j} : Finset ι) by simp [hi.symm, hj.symm]),
        Finset.prod_insert (show i ∉ ({j} : Finset ι) by simp [hij]), Finset.prod_singleton]
      simp only [τ, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne hi.symm hj.symm,
        Equiv.swap_apply_of_ne_of_ne hj hij.symm, hrow, hcol, one_mul]
    have hRim : R.im = 0 := im_prod_eq_zero Sᶜ _ (fun m _ => hdiag m)
    have hT : (P τ).im = 0 := im_eq_zero_of_pure_mul hC hCne (by rw [← hCeq τ, hτ])
    rw [hτP, Complex.mul_im, hRim, zero_mul, add_zero] at hT
    have hR : R.re ≠ 0 := fun he => (Finset.prod_ne_zero_iff.mpr
      (fun m _ => hFne m m) : R ≠ 0)
      (Complex.ext he hRim)
    exact (mul_eq_zero.mp hT).resolve_left hR
  have hentryReal (i j : {k : ι // k ≠ p}) :
      (X i.val * Y j.val).im = 0 := by
    have hdiag' (k : ι) : (X k * Y k).im = 0 := by
      simpa only [F, Complex.add_im, Complex.one_im, zero_add] using hdiag k
    have h := hconn i j
    induction h with
    | refl => exact hdiag' i.val
    | @tail k l _ hkl ih =>
      have he : (X k.val * Y l.val).im = 0 := by
        simpa only [F, Complex.add_im, Complex.one_im, zero_add] using
          hedge k.val l.val k.property l.property hkl.1 hkl.2
      have hp : (X i.val * Y k.val) * (X k.val * Y l.val) =
          (X i.val * Y l.val) * (X k.val * Y k.val) := by ring
      have him := congrArg Complex.im hp
      rw [Complex.mul_im (X i.val * Y k.val) (X k.val * Y l.val),
        Complex.mul_im (X i.val * Y l.val) (X k.val * Y k.val), ih, he, hdiag' k.val] at him
      simp only [mul_zero, zero_mul, add_zero, zero_add] at him
      have hwnd : (X k.val * Y k.val).re ≠ 0 := fun hz =>
        (mul_ne_zero
          (div_ne_zero (sub_ne_zero.mpr (ha.ne (r.injective.ne k.property))) (hnz _ _))
          (div_ne_zero (sub_ne_zero.mpr (hb.ne k.property.symm)) (hnz _ _)) :
            X k.val * Y k.val ≠ 0)
          (Complex.ext hz (hdiag' k.val))
      exact (mul_eq_zero.mp him.symm).resolve_right hwnd
  have hF (i j : ι) : (F i j).im = 0 := by
    by_cases hi : i = p
    · simp [hi, hrow]
    by_cases hj : j = p
    · simp [hj, hcol]
    simpa only [F, Complex.add_im, Complex.one_im, zero_add] using hentryReal ⟨i, hi⟩ ⟨j, hj⟩
  have hPall (τ : Equiv.Perm ι) : (P τ).im = 0 :=
    im_prod_eq_zero Finset.univ _ (fun j _ => hF _ j)
  intro σ
  have hσ : σ = r * (r.symm * σ) := by
    ext i
    simp only [Equiv.Perm.mul_apply, Equiv.apply_symm_apply]
  rw [hσ, hCeq (r.symm * σ), Complex.mul_re, hC, hPall, zero_mul, mul_zero, sub_self]

/-- The signed determinant identity transfers zero-height contact-tree
equality from the matching products to every unitary eigenbasis. -/
theorem determinantValue_re_eq_zero_of_contact_tree
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (η : ℂ) (r : Equiv.Perm ι) (p : ι)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hnz : ∀ i j, a i + b j ≠ 0) (hη : η ≠ 0)
    (href : (η * matchingProduct a b r).re = 0)
    (hsupport : ∀ σ, (η * matchingProduct a b σ).re ≤ 0)
    (hstar : ∀ i, i ≠ p → (η * matchingProduct a b (r * Equiv.swap p i)).re = 0)
    (hconn : ∀ i j : {k : ι // k ≠ p},
      Relation.ReflTransGen (fun x y : {k : ι // k ≠ p} =>
        x.val ≠ y.val ∧ (η * matchingProduct a b (r * Equiv.swap x.val y.val)).re = 0)
        i j) :
    (η * determinantValue a b U).re = 0 := by
  have hm := matchingProduct_re_eq_zero_of_contact_tree a b η r p
    ha hb hnz hη href hsupport hstar hconn
  have h := support_gap_eq a b U hU η r
  simp only [matchingGap, hm, sub_zero, mul_zero, Finset.sum_const_zero,
    zero_sub, neg_eq_zero] at h
  exact h

end MOC
