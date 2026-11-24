import MOC.QuaternionIntrinsic
import Mathlib.Data.Real.Sqrt

/-! A parity repair for Klein-displacement matrices with the signed
table identities of the quaternion basis. -/

open Finset BigOperators Matrix

namespace MOC.QuaternionIntrinsic

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Only these local identities of the quaternion basis signs are
needed: unit signs, positive translation signs, and a negative
relative sign on each swapped pair. -/
structure BasisSigning (z : G → G → ℝ) : Prop where
  sq : ∀ p j, z p j ^ 2 = 1
  shift : ∀ p, ∏ j, z p j = 1
  pair : ∀ p r s, r ≠ s →
    z (r+s+p) r * z (r+s+p) s * (z p r * z p s) = -1

def signedKleinMixerTable (z : G → G → ℝ) (q : G → ℝ) : Matrix G G ℂ :=
  Matrix.of fun i j => (z (i+j) j * q (i+j) : ℝ)

private theorem parityWeightFormula (U : Matrix G G ℂ)
    (z : G → G → ℝ) (q : G → ℝ)
    (hU : U = signedKleinMixerTable z q) (hdet : U.det = 1)
    (c : G → G → ℝ) (σ : Equiv.Perm G) :
    parityCorrectedWeight U c σ =
      parityReal σ * ((∏ j, z (σ j+j) j * q (σ j+j)) + ∑ j, c (σ j) j) := by
  unfold parityCorrectedWeight realSignedWeight signedWeight leibnizTerm
  rw [hdet, div_one, hU]
  simp only [signedKleinMixerTable, Matrix.of_apply, ← Complex.ofReal_prod,
    ← Complex.ofReal_intCast, ← Complex.ofReal_mul, Complex.ofReal_re, parityReal]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, ← Finset.sum_mul]
  ring

/-- The intrinsic signed-table model has an actual spectrum-independent
MOC certificate whenever the stated scalar parity correction is feasible.
No case table of permutations is involved. -/
theorem holds_signedKleinMixerTable
    (hc : Fintype.card G = 4) (h2 : ∀ x : G, x+x=0)
    (a b : G → ℂ) (z : G → G → ℝ) (q coeff : G → ℝ)
    (hz : BasisSigning z) (hq : ∀ p, 0 ≤ q p)
    (hU : IsUnitary (signedKleinMixerTable z q))
    (hdet : (signedKleinMixerTable z q).det = 1)
    (hs : 1 ≤ ∑ p, coeff p)
    (hshift : ∀ p, 0 ≤ q p ^ 4 + 4 * (∏ l, q l) * coeff p)
    (hpair : ∀ p v, p ≠ v →
      2 * (∏ l, q l) * (coeff p + coeff v) ≤ q p ^ 2 * q v ^ 2) :
    Holds a b (signedKleinMixerTable z q) := by
  classical
  let P : ℝ := ∏ l, q l
  have hP : 0 ≤ P := Finset.prod_nonneg (fun i _ => hq i)
  apply holds_of_nonneg_parityCorrectedWeight (by omega) a b _ hU
    (fun i j => P * coeff (i+j))
  intro σ
  rw [parityWeightFormula _ z q rfl hdet]
  simp only [← Finset.mul_sum]
  let p := σ 0
  let f : Equiv.Perm G := σ.trans (Equiv.subRight p)
  let τ : Equiv.Perm G := Equiv.addRight p
  have hf (j : G) : f j = σ j-p := rfl
  have hf0 : f 0 = 0 := by simp [hf, p]
  have hdis (j : G) : σ j+j = f j+j+p := by rw [hf]; abel
  have hσ : σ = τ * f := by
    ext j
    change σ j = f j+p
    rw [hf, sub_add_cancel]
  have hsign : Equiv.Perm.sign σ = Equiv.Perm.sign f := by
    rw [hσ, Equiv.Perm.sign_mul, klein_translation_even hc h2 p, one_mul]
  rcases fixedOrigin_perm_types hc h2 f hf0 with he | ⟨r,s,hrs,he⟩ | hb
  · have hd (j : G) : σ j+j = p := by simp [hdis, he, h2]
    have hp : parityReal σ = 1 := by simp [parityReal, hsign, he]
    simp only [hd, hp, Finset.prod_mul_distrib, hz.shift, one_mul, Finset.prod_const,
      Finset.card_univ, hc, Finset.sum_const, nsmul_eq_mul, Nat.cast_ofNat]
    convert hshift p using 1
    dsimp [P]
    ring
  · let v := r+s+p
    have hpv : p ≠ v := by
      intro h
      have hg : r+s=0 := add_right_cancel (h.symm.trans (zero_add p).symm)
      exact hrs (add_right_cancel (hg.trans (h2 s).symm))
    have hr : σ r+r=v := by
      rw [hdis, he, Equiv.swap_apply_left]
      dsimp [v]
      abel
    have hs' : σ s+s=v := by rw [hdis, he, Equiv.swap_apply_right]
    have hout (j : G) (hjr : j ≠ r) (hjs : j ≠ s) : σ j+j=p := by
      rw [hdis, he, Equiv.swap_apply_of_ne_of_ne hjr hjs, h2, zero_add]
    have hsE : s ∈ (univ : Finset G).erase r := mem_erase.mpr ⟨hrs.symm, mem_univ s⟩
    let E : Finset G := ((univ : Finset G).erase r).erase s
    have hE : E.card = 2 := by
      simp only [E, card_erase_of_mem hsE, card_erase_of_mem (mem_univ r), card_univ, hc]
    have hprod (g : G → G → ℝ) :
        (∏ j, g (σ j+j) j) = g v r * (g v s * ∏ j ∈ E, g p j) := by
      rw [← Finset.mul_prod_erase univ _ (mem_univ r),
        ← Finset.mul_prod_erase (univ.erase r) _ hsE, hr, hs']
      congr 2
      apply Finset.prod_congr rfl
      intro j hj
      rw [hout j (mem_erase.mp (mem_erase.mp hj).2).1 (mem_erase.mp hj).1]
    have hsum : (∑ j, coeff (σ j+j)) = 2*(coeff p+coeff v) := by
      rw [← Finset.add_sum_erase univ _ (mem_univ r),
        ← Finset.add_sum_erase (univ.erase r) _ hsE, hr, hs']
      have hh : (∑ j ∈ E, coeff (σ j+j)) = 2*coeff p := by
        calc
          _ = ∑ j ∈ E, coeff p := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hout j (mem_erase.mp (mem_erase.mp hj).2).1 (mem_erase.mp hj).1]
          _ = _ := by simp [hE, nsmul_eq_mul]
      rw [hh]
      ring
    have hprodZ : (∏ j, z (σ j+j) j) = -1 := by
      have hbase := hz.shift p
      rw [← Finset.mul_prod_erase univ _ (mem_univ r),
        ← Finset.mul_prod_erase (univ.erase r) _ hsE] at hbase
      rw [hprod z]
      have hmid : (∏ j ∈ E, z p j) = z p r * z p s := by
        nlinarith only [hbase, hz.sq p r, hz.sq p s,
          congrArg (fun u : ℝ => u * (z p r * z p s)) hbase,
          congrArg (fun u : ℝ => u * z p r ^ 2) (hz.sq p s),
          congrArg (fun u : ℝ => u * (∏ j ∈ E, z p j)) (hz.sq p r),
          congrArg (fun u : ℝ => u * (z p r ^ 2 * (∏ j ∈ E, z p j))) (hz.sq p s)]
      rw [hmid]
      linear_combination hz.pair p r s hrs
    have hprodQ : (∏ j, q (σ j+j)) = q p ^ 2 * q v ^ 2 := by
      rw [hprod (fun i _ => q i), Finset.prod_const, hE]
      ring
    have hp : parityReal σ = -1 := by simp [parityReal, hsign, he, Equiv.Perm.sign_swap hrs]
    rw [hp, Finset.prod_mul_distrib, hprodZ, hprodQ, hsum]
    have hh := hpair p v hpv
    change 2 * P * (coeff p + coeff v) ≤ _ at hh
    linarith
  · have hp : parityReal σ = 1 := by
      simp [parityReal, hsign, fixedOrigin_even_of_bijective_displacement hc h2 f hf0 hb]
    have hbij : Function.Bijective (fun j => σ j+j) := by
      have h := τ.bijective.comp hb
      change Function.Bijective (fun x => f x+x+p) at h
      simpa only [← hdis] using h
    let e := Equiv.ofBijective _ hbij
    have hprod : (∏ j, q (σ j+j)) = P := Equiv.prod_comp e q
    have hs' : (∑ j, coeff (σ j+j)) = ∑ j, coeff j := Equiv.sum_comp e coeff
    have hzabs : |∏ j, z (σ j+j) j| = 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_eq_one (fun j _ => by
        have hh := congrArg Real.sqrt (hz.sq (σ j+j) j)
        simpa [Real.sqrt_sq_eq_abs] using hh)
    rw [hp, one_mul, Finset.prod_mul_distrib, hprod, hs']
    have hlow : -1 ≤ ∏ j, z (σ j+j) j := by
      have hh := neg_abs_le (∏ j, z (σ j+j) j)
      rwa [hzabs] at hh
    have h := mul_nonneg hP (show 0 ≤ (∏ j, z (σ j+j) j) + ∑ j, coeff j from by linarith)
    linarith


/-- Actual unrestricted-spectra conclusion for the near-balanced
Klein-displacement signed-table class. The determinant and unitarity
hypotheses concern the mixer itself, not its spectral scores. -/
theorem holds_nearBalanced_signedKleinMixerTable
    (hc : Fintype.card G = 4) (h2 : ∀ x : G, x+x=0)
    (a b : G → ℂ) (z : G → G → ℝ) (hz : BasisSigning z)
    (u : G) {x t : ℝ} (hx : 0 < x) (ht : 0 < t) (ht' : t ≤ 1)
    (htcub : 0 ≤ t^3+3*t-2)
    (hU : IsUnitary (signedKleinMixerTable z (fun l => x * if l = u then t else 1)))
    (hdet : (signedKleinMixerTable z (fun l => x * if l = u then t else 1)).det = 1) :
    Holds a b (signedKleinMixerTable z (fun l => x * if l = u then t else 1)) := by
  classical
  let q : G → ℝ := fun l => x * if l = u then t else 1
  let w : ℝ := (2-t)/4
  let v : ℝ := (3*t-2)/4
  let cf : G → ℝ := fun l => if l = u then v else w
  have hu : u ∈ (univ : Finset G) := mem_univ u
  have hC : ((univ : Finset G).erase u).card = 3 := by
    rw [card_erase_of_mem hu, card_univ, hc]
  have hprod : (∏ l, q l) = x^4*t := by
    rw [← Finset.mul_prod_erase univ q hu]
    have h : (∏ l ∈ univ.erase u, q l) = x^3 := by
      calc
        _ = ∏ _l ∈ (univ : Finset G).erase u, x := by
          apply Finset.prod_congr rfl
          intro j hj
          simp [q, (mem_erase.mp hj).1]
        _ = _ := by rw [Finset.prod_const, hC]
    rw [h]
    simp [q]
    ring
  obtain ⟨hcoef, haxis, haxis', hpair, hpair'⟩ :=
    nearBalancedParityCorrection_signed ht.le ht' htcub
  change 3*w+v = 1 at hcoef
  change 0 ≤ 1+4*t*w at haxis
  change 0 ≤ t^4+4*t*v at haxis'
  change 2*t*(w+w) ≤ 1 at hpair
  change 2*t*(w+v) = t^2 at hpair'
  have hq : ∀ l, 0 ≤ q l := by
    intro l
    unfold q
    split_ifs <;> positivity
  refine holds_signedKleinMixerTable hc h2 a b z q cf hz hq hU hdet ?_ ?_ ?_
  · rw [← Finset.add_sum_erase univ cf hu]
    have h : (∑ l ∈ univ.erase u, cf l) = 3*w := by
      calc
        _ = ∑ _l ∈ (univ : Finset G).erase u, w := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [cf, (mem_erase.mp hj).1]
        _ = _ := by simp [hC, nsmul_eq_mul]
    rw [show cf u = v by simp [cf]]
    rw [h]
    linarith
  · intro p
    rw [hprod]
    by_cases hp : p=u
    · simp [q, cf, hp]
      calc
        0 ≤ x^4 * (t^4+4*t*v) := mul_nonneg (by positivity) haxis'
        _ = _ := by ring
    · simp [q, cf, hp]
      calc
        0 ≤ x^4 * (1+4*t*w) := mul_nonneg (by positivity) haxis
        _ = _ := by ring
  · intro p l hpl
    rw [hprod]
    by_cases hp : p=u
    · have hl : l ≠ u := by rintro rfl; exact hpl hp
      simp [q, cf, hp, hl]
      apply le_of_eq
      calc
        _ = x^4 * (2*t*(w+v)) := by ring
        _ = (x*t)^2*x^2 := by rw [hpair']; ring
    · by_cases hl : l=u
      · simp [q, cf, hp, hl]
        apply le_of_eq
        calc
          _ = x^4 * (2*t*(w+v)) := by ring
          _ = x^2*(x*t)^2 := by rw [hpair']; ring
      · simp [q, cf, hp, hl]
        calc
          _ = x^4 * (2*t*(w+w)) := by ring
          _ ≤ x^4 * 1 := mul_le_mul_of_nonneg_left hpair (by positivity)
          _ = x^2*x^2 := by ring


/-- An anisotropic bicharacter gives the quaternion sign identities.
The sign-product calculation uses a group basis, not a sign table. -/
theorem basisSigning_of_bicharacter (hc : Fintype.card G = 4)
    (h2 : ∀ x : G, x+x=0) (z : G → G → ℝ)
    (hsq : ∀ p j, z p j ^ 2 = 1)
    (hl : ∀ p q j, z (p+q) j = z p j * z q j)
    (hr : ∀ p i j, z p (i+j) = z p i * z p j)
    (hdiag : ∀ p, p ≠ 0 → z p p = -1) : BasisSigning z := by
  classical
  refine ⟨hsq, ?_, ?_⟩
  · intro p
    have hS : ((univ : Finset G).erase (0 : G)).card = 3 := by
      rw [card_erase_of_mem (mem_univ _), card_univ, hc]
    obtain ⟨r, hrmem, s, hsmem, hrs⟩ := Finset.one_lt_card.mp (by rw [hS]; decide)
    have hr0 : r ≠ 0 := (mem_erase.mp hrmem).1
    have hs0 : s ≠ 0 := (mem_erase.mp hsmem).1
    have hd0 : r+s ≠ 0 := by
      intro h
      exact hrs (add_right_cancel (h.trans (h2 s).symm))
    have hdr : r+s ≠ r := by
      intro h
      exact hs0 (add_left_cancel (h.trans (add_zero r).symm))
    have hds : r+s ≠ s := by
      intro h
      exact hr0 (add_right_cancel (h.trans (zero_add s).symm))
    have hE : ({0,r,s,r+s} : Finset G) = univ := by
      apply Finset.eq_univ_of_card
      simp [hc, hr0, hs0, hd0, hrs, hdr, hds, Ne.symm hr0, Ne.symm hs0,
        Ne.symm hd0, Ne.symm hrs, Ne.symm hdr, Ne.symm hds]
    rw [← hE]
    simp [hr0, hs0, hd0, hrs, hdr, hds, Ne.symm hr0, Ne.symm hs0,
      Ne.symm hd0, Ne.symm hrs, Ne.symm hdr, Ne.symm hds]
    have hz0 : z p 0 = 1 := by
      have he : z p 0 = z p 0 * z p 0 := by simpa only [zero_add] using hr p 0 0
      nlinarith only [he, hsq p 0]
    rw [hz0, hr, one_mul]
    calc
      _ = z p r ^ 2 * z p s ^ 2 := by ring
      _ = _ := by rw [hsq, hsq, one_mul]
  · intro p r s hrs
    have hne : r+s ≠ 0 := by
      intro h
      exact hrs (add_right_cancel (h.trans (h2 s).symm))
    rw [hl (r+s) p r, hl (r+s) p s]
    calc
      _ = (z p r ^ 2 * z p s ^ 2) * (z (r+s) r * z (r+s) s) := by ring
      _ = z (r+s) (r+s) := by rw [hsq, hsq, one_mul, one_mul, hr]
      _ = -1 := hdiag _ hne

end

end MOC.QuaternionIntrinsic
