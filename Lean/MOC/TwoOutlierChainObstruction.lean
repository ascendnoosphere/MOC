import MOC.NestedRectangleObstruction
import MOC.TwoOutlierZeroSupport
import Mathlib.Data.Finset.Sort

/-! The simple two-outlier terminal profiles also obstruct a single
additive chain, in either orientation. The four spectator columns in
any flag give two separated swaps and a nonzero mixed interaction. -/

open BigOperators

namespace MOC

variable {κ : Type*} [Fintype κ]

/-- A pure imaginary outlier and positive simple spectators in each
spectrum prevent an additive column-prefix certificate. The matching
support has exactly the outlier-fixing contacts if the heights exceed
the crossed spectator products, by `two_outlier_zero_contact_exact`. -/
theorem two_outlier_five_no_prefix_scores
    (x y : Fin 5 → ℝ) (d : Fin 5) (u v : ℝ)
    (hx : ∀ i, i ≠ d → 0 < x i) (hu : 0 < u) (hv : 0 < v)
    (hx' : Function.Injective x) (hy' : Function.Injective y)
    (e : Equiv.Perm (Fin 5)) (cut : κ → ℕ) :
    let J (p : κ) : Finset (Fin 5) := Finset.univ.filter (fun i => (e.symm i).val < cut p)
    ¬ ∃ f : κ → Finset (Fin 5) → ℝ, ∀ q,
      (matchingProduct (withImaginaryOutlier x d u) (withImaginaryOutlier y d v) q).re =
        ∑ p, f p ((J p).map q.toEmbedding) := by
  classical
  let S : Finset (Fin 5) := Finset.univ.erase (e.symm d)
  have hScard : S.card = 4 := by
    unfold S
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  let f := S.orderEmbOfFin hScard
  let c (n : Fin 4) := e (f n)
  let i := c 0
  let j := c 1
  let k := c 2
  let l := c 3
  have hd (n : Fin 4) : c n ≠ d := by
    intro h
    have hm := S.orderEmbOfFin_mem hScard n
    have he : f n = e.symm d := e.injective (h.trans (e.apply_symm_apply d).symm)
    exact (Finset.mem_erase.mp hm).1 he
  have hcinj : Function.Injective c := e.injective.comp f.injective
  have h01 : (0 : Fin 4) < 1 := Nat.zero_lt_one
  have h12 : (1 : Fin 4) < 2 := Nat.lt_succ_self _
  have h23 : (2 : Fin 4) < 3 := Nat.lt_succ_self _
  have nij : i ≠ j := hcinj.ne h01.ne
  have nik : i ≠ k := hcinj.ne (h01.trans h12).ne
  have nil : i ≠ l := hcinj.ne (h01.trans (h12.trans h23)).ne
  have njk : j ≠ k := hcinj.ne h12.ne
  have njl : j ≠ l := hcinj.ne (h12.trans h23).ne
  have nkl : k ≠ l := hcinj.ne h23.ne
  have hpos {a b : Fin 4} (h : a < b) : (e.symm (c a)).val < (e.symm (c b)).val := by
    simpa only [c, Equiv.symm_apply_apply] using f.strictMono h
  have hcards : ({i, j, k, l} : Finset (Fin 5)).card = 4 := by
    simp [nij, nik, nil, njk, njl, nkl, Finset.card_insert_of_not_mem]
  have hset : ({i, j, k, l} : Finset (Fin 5)) = Finset.univ.erase d := by
    apply Finset.eq_of_subset_of_card_le
    · intro m hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with h | h | h | h
      · subst m; exact Finset.mem_erase.mpr ⟨hd 0, Finset.mem_univ _⟩
      · subst m; exact Finset.mem_erase.mpr ⟨hd 1, Finset.mem_univ _⟩
      · subst m; exact Finset.mem_erase.mpr ⟨hd 2, Finset.mem_univ _⟩
      · subst m; exact Finset.mem_erase.mpr ⟨hd 3, Finset.mem_univ _⟩
    · rw [hcards, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hout : ({i, j, k, l} : Finset (Fin 5))ᶜ = {d} := by
    rw [hset]
    ext m
    simp
  let a := withImaginaryOutlier x d u
  let b := withImaginaryOutlier y d v
  let r := Equiv.swap i d
  have hbo : b d = Complex.I * (v : ℂ) := by simp [b, withImaginaryOutlier]
  have hao : a d = Complex.I * (u : ℂ) := by simp [a, withImaginaryOutlier]
  have ha (m : Fin 5) (hm : m ≠ d) : a m = (x m : ℂ) := by simp [a, withImaginaryOutlier, hm]
  have hb (m : Fin 5) (hm : m ≠ d) : b m = (y m : ℂ) := by simp [b, withImaginaryOutlier, hm]
  have hr₁ : r i = d := Equiv.swap_apply_left i d
  have hr₂ : r j = j := Equiv.swap_apply_of_ne_of_ne nij.symm (hd 1)
  have hr₃ : r k = k := Equiv.swap_apply_of_ne_of_ne nik.symm (hd 2)
  have hr₄ : r l = l := Equiv.swap_apply_of_ne_of_ne nil.symm (hd 3)
  have hrd : r d = i := Equiv.swap_apply_right i d
  have hN : -(x i * x j) - u * v ≠ 0 := by
    exact (sub_neg.mpr ((neg_neg_of_pos (mul_pos (hx i (hd 0)) (hx j (hd 1)))).trans
      (mul_pos hu hv))).ne
  have hcore :
      (((x i : ℂ) + Complex.I * (v : ℂ)) * (Complex.I * (u : ℂ) - (x j : ℂ))).re =
        -(x i * x j) - u * v := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have hD₁ : y j - y i ≠ 0 := sub_ne_zero.mpr (hy'.ne nij.symm)
  have hD₂ : x k - x l ≠ 0 := sub_ne_zero.mpr (hx'.ne nkl)
  have hD₃ : y l - y k ≠ 0 := sub_ne_zero.mpr (hy'.ne nkl.symm)
  have res := no_prefix_scores_of_matching_rectangle a b 1 (fun m => (e.symm m).val) cut
    r i j k l (hpos h01) (hpos h12) (hpos h23)
  simp only [one_mul] at res
  apply res
  rw [hout, Finset.prod_singleton, hrd, hr₁, hr₂, hr₃, hr₄, ha i (hd 0),
    hao, ha j (hd 1), ha k (hd 2), ha l (hd 3), hbo, hb i (hd 0), hb j (hd 1),
    hb k (hd 2), hb l (hd 3)]
  simp only [← Complex.ofReal_sub, ← Complex.ofReal_mul, ← mul_assoc,
    Complex.re_mul_ofReal, hcore]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hN hD₁) hD₂) hD₃


/-- The same obstruction holds if a flag of rows is scored by its inverse
images under the matching permutation. -/
theorem two_outlier_five_no_row_prefix_scores
    (x y : Fin 5 → ℝ) (d : Fin 5) (u v : ℝ)
    (hy : ∀ i, i ≠ d → 0 < y i) (hu : 0 < u) (hv : 0 < v)
    (hx' : Function.Injective x) (hy' : Function.Injective y)
    (e : Equiv.Perm (Fin 5)) (cut : κ → ℕ) :
    let J (p : κ) : Finset (Fin 5) := Finset.univ.filter (fun i => (e.symm i).val < cut p)
    ¬ ∃ f : κ → Finset (Fin 5) → ℝ, ∀ q,
      (matchingProduct (withImaginaryOutlier x d u) (withImaginaryOutlier y d v) q).re =
        ∑ p, f p ((J p).map q.symm.toEmbedding) := by
  intro J ⟨f, hf⟩
  apply two_outlier_five_no_prefix_scores y x d v u hy hv hu hy' hx' e cut
  refine ⟨f, fun q => ?_⟩
  have hq := hf q.symm
  rw [matchingProduct_inverse, Equiv.symm_symm] at hq
  simpa only [matchingProduct, add_comm] using hq


/-- The nonzero matching profile is terminal for the zero-height support
direction: the symmetric group of the spectator labels injects into
the contact set. The count does not enumerate matchings. -/
theorem two_outlier_five_terminal_profile
    (x y : Fin 5 → ℝ) (d : Fin 5) (u v : ℝ)
    (hx : ∀ i, i ≠ d → 0 < x i) (hy : ∀ i, i ≠ d → 0 < y i)
    (hu : 0 < u) (hv : 0 < v)
    (hhigh : ∀ i j, i ≠ d → j ≠ d → x i * y j < u * v) :
    let P := matchingProduct (withImaginaryOutlier x d u) (withImaginaryOutlier y d v)
    (∀ q, P q ≠ 0 ∧ (P q).re ≤ 0) ∧
      Nat.factorial 4 ≤
        (Finset.univ.filter fun q : Equiv.Perm (Fin 5) => (P q).re = 0).card := by
  classical
  intro P
  have hcontact := two_outlier_zero_contact_exact x y d u v
    (fun i j hi hj => add_pos (hx i hi) (hy j hj)) hhigh
  refine ⟨fun q => ⟨?_, (hcontact q).1⟩, ?_⟩
  · unfold P matchingProduct
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    let p := q i
    change withImaginaryOutlier x d u p + withImaginaryOutlier y d v i ≠ 0
    by_cases hp : p = d <;> by_cases hi : i = d
    · intro h
      have hh := congrArg Complex.im h
      rw [hp, hi] at hh
      exact (add_pos hu hv).ne' (by simpa [withImaginaryOutlier, hp, hi, Complex.mul_im] using hh)
    · intro h
      have hh := congrArg Complex.re h
      rw [hp] at hh
      exact (hy i hi).ne' (by simpa [withImaginaryOutlier, hp, hi, Complex.mul_re] using hh)
    · intro h
      have hh := congrArg Complex.re h
      rw [hi] at hh
      exact (hx p hp).ne' (by simpa [withImaginaryOutlier, hp, hi, Complex.mul_re] using hh)
    · intro h
      have hh := congrArg Complex.re h
      exact (add_pos (hx p hp) (hy i hi)).ne'
        (by simpa [withImaginaryOutlier, hp, hi] using hh)
  let S : Finset (Fin 5) := Finset.univ.erase d
  let C := Finset.univ.filter fun q : Equiv.Perm (Fin 5) => (P q).re = 0
  have hm (s : Equiv.Perm S) : Equiv.Perm.ofSubtype s ∈ C := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, (hcontact _).2.mpr ?_⟩
    exact Equiv.Perm.ofSubtype_apply_of_not_mem s (Finset.not_mem_erase d _)
  let f (s : Equiv.Perm S) : C := ⟨Equiv.Perm.ofSubtype s, hm s⟩
  have hcard := Fintype.card_le_of_injective f
    (fun s t h => Equiv.Perm.ofSubtype_injective (congrArg Subtype.val h))
  have hScard : S.card = 4 := by
    unfold S
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  simpa only [Fintype.card_perm, Fintype.card_coe, hScard] using hcard

end MOC
