import MOC.MatchingQuartet
import MOC.MatchingTriangleHeight

/-! A triangle and a disjoint-swap rectangle can determine the same
matching value. At a common nonzero height their overlap may force a
collision of distinct matching products. -/

namespace MOC

/-- Six collinear entries meeting the overlapping triangle and rectangle
identities have zero common height under the stated distinctness. -/
theorem contact_height_eq_zero_of_triangle_rectangle
    {a b c d e f p q : ℂ} {H : ℝ}
    (ha : a.re = H) (hb : b.re = H) (hc : c.re = H) (hd : d.re = H)
    (he : e.re = H) (hf : f.re = H)
    (hpq : p ≠ q) (heb : e ≠ b) (hef : e ≠ f)
    (hsum : p + c + d = q + a + b) (hprod : p * c * d = q * a * b)
    (hrect : p * f = a * e) : H = 0 := by
  by_contra hH
  let L := a + b - c - d
  let s := a.im + b.im - c.im - d.im
  let k := c.im * d.im - a.im * b.im
  have ha0 : a ≠ 0 := by
    intro hz
    exact hH (by simpa only [hz, Complex.zero_re] using ha.symm)
  have hdiff : p - q = L := by
    dsimp only [L]
    linear_combination hsum
  have hLre : L.re = 0 := by
    simp only [L, Complex.add_re, Complex.sub_re, ha, hb, hc, hd]
    ring
  have hLim : L.im = s := by simp only [L, s, Complex.add_im, Complex.sub_im]
  have hs : s ≠ 0 := by
    intro hs0
    apply hpq
    apply sub_eq_zero.mp
    exact hdiff.trans (Complex.ext hLre (hLim.trans hs0))
  have hp : p * (a * b - c * d) = L * (a * b) := by
    linear_combination (a * b) * hdiff - hprod
  have hjoin : (a * b - c * d) * e = L * b * f := by
    apply mul_left_cancel₀ ha0
    linear_combination f * hp - (a * b - c * d) * hrect
  have hre := congrArg Complex.re hjoin
  have him := congrArg Complex.im hjoin
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    ha, hb, hc, hd, he, hf, hLre, hLim, zero_mul, mul_zero, sub_zero, zero_sub,
    add_zero, zero_add] at hre him
  have hR₀ : H * (k - s * e.im + s * b.im + s * f.im) = H * 0 := by
    dsimp only [k, s] at hre ⊢
    linear_combination hre
  have hR := mul_left_cancel₀ hH hR₀
  have hI : k * e.im + s * b.im * f.im = 0 := by
    dsimp only [k, s] at him ⊢
    linear_combination him
  have hfactor : s * (e.im - b.im) * (e.im - f.im) = 0 := by
    linear_combination hI - e.im * hR
  have heb' : e.im - b.im ≠ 0 := fun h =>
    heb (Complex.ext (he.trans hb.symm) (sub_eq_zero.mp h))
  have hef' : e.im - f.im ≠ 0 := fun h =>
    hef (Complex.ext (he.trans hf.symm) (sub_eq_zero.mp h))
  exact (mul_ne_zero (mul_ne_zero hs heb') hef') hfactor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Six contacts in the specified overlapping three-label and two-swap
configuration force zero height for distinct matching products. -/
theorem matchingProduct_triangle_rectangle_contact_height_eq_zero
    (a b : ι → ℂ) (r : Equiv.Perm ι) (i j k l : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (η : ℂ) (hη : η ≠ 0) (H : ℝ) (hinj : Function.Injective (matchingProduct a b))
    (hcontact : ∀ σ ∈ ({r * Equiv.swap k l, r * Equiv.swap j k,
      r * Equiv.swap j k * Equiv.swap k l, r * Equiv.swap k l * Equiv.swap j k,
      r * Equiv.swap i j, r * Equiv.swap i j * Equiv.swap k l} : Finset (Equiv.Perm ι)),
      (η * matchingProduct a b σ).re = H) : H = 0 := by
  let z (σ : Equiv.Perm ι) := η * matchingProduct a b σ
  have hz : Function.Injective z := fun _ _ h => hinj (mul_left_cancel₀ hη h)
  refine contact_height_eq_zero_of_triangle_rectangle
    (a := z (r * Equiv.swap k l)) (b := z (r * Equiv.swap j k))
    (c := z (r * Equiv.swap j k * Equiv.swap k l))
    (d := z (r * Equiv.swap k l * Equiv.swap j k))
    (e := z (r * Equiv.swap i j)) (f := z (r * Equiv.swap i j * Equiv.swap k l))
    (p := z r) (q := z (r * Equiv.swap j l))
    (hcontact _ (by simp)) (hcontact _ (by simp)) (hcontact _ (by simp))
    (hcontact _ (by simp)) (hcontact _ (by simp)) (hcontact _ (by simp)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro heq
    have hx := congrArg (fun σ : Equiv.Perm ι => σ j) (hz heq)
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at hx
    exact hjl (r.injective hx)
  · intro heq
    have hx := congrArg (fun σ : Equiv.Perm ι => σ i) (hz heq)
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hij hik] at hx
    exact hij (r.injective hx).symm
  · intro heq
    have hx := congrArg (fun σ : Equiv.Perm ι => σ k) (hz heq)
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hik.symm hjk.symm,
      Equiv.swap_apply_of_ne_of_ne hil.symm hjl.symm] at hx
    exact hkl (r.injective hx)
  · have h := matchingProduct_triangle_identity a b r j k l hjk hjl hkl
    dsimp only [z]
    linear_combination η * h
  · have h := matchingProduct_triangle_product_identity a b r j k l hjk hjl hkl
    dsimp only [z]
    linear_combination η ^ 3 * h
  · have h := matchingProduct_disjoint_swaps_identity a b r i j k l hij hik hil hjk hjl hkl
    dsimp only [z]
    linear_combination η ^ 2 * h

/-- The six-label pattern forces both missing contacts when all matching
products are nonzero. In order four this rules out the exact regular ordered-ratio pattern
contact set, represented in lexicographic indices by `{1,2,3,4,6,7}`. -/
theorem matchingProduct_triangle_rectangle_complete_contacts
    (a b : ι → ℂ) (r : Equiv.Perm ι) (i j k l : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (η : ℂ) (hη : η ≠ 0) (H : ℝ) (hinj : Function.Injective (matchingProduct a b))
    (hnz : ∀ σ, matchingProduct a b σ ≠ 0)
    (hcontact : ∀ σ ∈ ({r * Equiv.swap k l, r * Equiv.swap j k,
      r * Equiv.swap j k * Equiv.swap k l, r * Equiv.swap k l * Equiv.swap j k,
      r * Equiv.swap i j, r * Equiv.swap i j * Equiv.swap k l} : Finset (Equiv.Perm ι)),
      (η * matchingProduct a b σ).re = H) :
    H = 0 ∧ (η * matchingProduct a b r).re = 0 ∧
      (η * matchingProduct a b (r * Equiv.swap j l)).re = 0 := by
  have hH := matchingProduct_triangle_rectangle_contact_height_eq_zero
    a b r i j k l hij hik hil hjk hjl hkl η hη H hinj hcontact
  let z (σ : Equiv.Perm ι) := η * matchingProduct a b σ
  let s := Equiv.swap i j
  let t := Equiv.swap k l
  let u := Equiv.swap j k
  have ht : (z (r * t)).re = 0 := (hcontact _ (by simp [t])).trans hH
  have hs : (z (r * s)).re = 0 := (hcontact _ (by simp [s])).trans hH
  have hst : (z (r * s * t)).re = 0 := (hcontact _ (by simp [s, t])).trans hH
  have hrect : z r * z (r * s * t) = z (r * s) * z (r * t) := by
    have h := matchingProduct_disjoint_swaps_identity a b r i j k l hij hik hil hjk hjl hkl
    dsimp only [z, s, t]
    linear_combination η ^ 2 * h
  have he := congrArg Complex.im hrect
  simp only [Complex.mul_im, ht, hs, hst, mul_zero, zero_mul, add_zero] at he
  have him : (z (r * s * t)).im ≠ 0 := fun h =>
    mul_ne_zero hη (hnz _) (Complex.ext hst h)
  have hbase : (z r).re = 0 := (mul_eq_zero.mp he).resolve_right him
  have hu : (z (r * u)).re = 0 := (hcontact _ (by simp [u])).trans hH
  have hut : (z (r * u * t)).re = 0 := (hcontact _ (by simp [u, t])).trans hH
  have htu : (z (r * t * u)).re = 0 := (hcontact _ (by simp [u, t])).trans hH
  have hsum : z r + z (r * u * t) + z (r * t * u) =
      z (r * u) + z (r * Equiv.swap j l) + z (r * t) := by
    simpa only [z, u, t, mul_add] using
      congrArg (fun w : ℂ => η * w) (matchingProduct_triangle_identity a b r j k l hjk hjl hkl)
  have hlast := congrArg Complex.re hsum
  simp only [Complex.add_re, hbase, hut, htu, hu, ht, add_zero, zero_add] at hlast
  exact ⟨hH, hbase, hlast.symm⟩

end MOC
