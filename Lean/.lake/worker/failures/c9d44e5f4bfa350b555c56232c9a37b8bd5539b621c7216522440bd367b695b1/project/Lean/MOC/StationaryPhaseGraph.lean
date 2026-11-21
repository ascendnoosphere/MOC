import MOC.PhaseMove

/-! Scalar constraints on two consecutive couplings at a normal support maximum. -/

open BigOperators Matrix

namespace MOC

private theorem star_eq_neg_of_re_eq_zero (c : ℂ) (h : c.re = 0) : star c = -c := by
  apply Complex.ext <;> simp [Complex.star_def, h]

private theorem normSq_eq_one_of_mul_star (c : ℂ) (h : c * star c = 1) :
    Complex.normSq c = 1 := by
  simpa only [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.one_re] using
    congrArg Complex.re h

private theorem phase_factorization (x y p s t : ℂ) (hp : p ≠ 0)
    (hs : s * star s = 1) (ht : t * star t = 1)
    (hsy : (p * s * y).re = 0) (htx : (p * t * x).re = 0)
    (hmixed : p * (x + y) = -(star (p * (x + y)) * star (s * t))) :
    s = t ∨ s * y = t * x := by
  have hu := star_eq_neg_of_re_eq_zero _ hsy
  have hv := star_eq_neg_of_re_eq_zero _ htx
  simp only [star_mul'] at hu hv
  have hy : star p * star y + p * s ^ 2 * y = 0 := by
    linear_combination s * hu - (star p * star y) * hs
  have hx : star p * star x + p * t ^ 2 * x = 0 := by
    linear_combination t * hv - (star p * star x) * ht
  have hst : (s * t) * (star s * star t) = 1 := by
    linear_combination (t * star t) * hs + ht
  simp only [star_mul', star_add] at hmixed
  have hm : p * (x + y) * (s * t) + star p * (star x + star y) = 0 := by
    linear_combination (s * t) * hmixed - (star p * (star x + star y)) * hst
  have hfactor : p * ((s - t) * (s * y - t * x)) = 0 := by
    linear_combination hy + hx - hm
  simpa only [sub_eq_zero] using mul_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left hp)

/-- The pair and mixed phase identities force a path with two nonzero couplings
to have equal endpoint eigenvalues when the real support is nonzero. Here
`p` is the support multiplier divided by the product of the three eigenvalues. -/
theorem endpoints_eq_of_mixed_phase (x y z p s t : ℂ) (hxz : x ≠ z)
    (hκ : (p * x * y * z).re ≠ 0)
    (hs : s * star s = 1) (ht : t * star t = 1)
    (hsphase : s * (star x - star z) = x - z)
    (htphase : t * (star z - star y) = z - y)
    (hsy : (p * s * y).re = 0) (htx : (p * t * x).re = 0)
    (hmixed : p * (x + y) = -(star (p * (x + y)) * star (s * t))) :
    x = y := by
  by_contra hxy
  have hp : p ≠ 0 := fun h => hκ (by simp [h])
  rcases phase_factorization x y p s t hp hs ht hsy htx hmixed with hst | hst
  · subst t
    have hsnz : s ≠ 0 := fun h => by simp [h] at hs
    have hu := star_eq_neg_of_re_eq_zero _ hsy
    have hv := star_eq_neg_of_re_eq_zero _ htx
    rw [star_mul'] at hu hv
    have hcancel : star (p * s) * (x * star y - star x * y) = 0 := by
      linear_combination x * hu - y * hv
    have hpstar : star (p * s) ≠ 0 :=
      fun h => mul_ne_zero hp hsnz (star_eq_zero.mp h)
    have hxyphase : x * star y = star x * y :=
      sub_eq_zero.mp ((mul_eq_zero.mp hcancel).resolve_left hpstar)
    have hphase : s * (star x - star y) = x - y := by
      linear_combination hsphase + htphase
    have hfactor : (star x - star y) * (s * star x - x) = 0 := by
      linear_combination star x * hphase + hxyphase
    have hsx : s * star x = x :=
      sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left
        (sub_ne_zero.mpr (star_injective.ne hxy)))
    have hsz : s * star z = z := by
      linear_combination hsx - hsphase
    have hxzphase : x * star z = z * star x := by
      linear_combination star x * hsz - star z * hsx
    have hreal : (x * star z).im = 0 := by
      have he : star (x * star z) = x * star z := by
        rw [star_mul', star_star, mul_comm (star x) z, ← hxzphase]
      have hi := congrArg Complex.im he
      simp only [Complex.star_def, Complex.conj_im] at hi ⊢
      linarith only [hi]
    have hrep : p * x * y * z = (p * s * y) * (x * star z) := by
      linear_combination -(p * x * y) * hsz
    apply hκ
    rw [hrep, Complex.mul_re, hsy, hreal, zero_mul, mul_zero, sub_zero]
  · have hnorm := congrArg Complex.normSq hst
    simp only [Complex.normSq_mul, normSq_eq_one_of_mul_star s hs,
      normSq_eq_one_of_mul_star t ht, one_mul] at hnorm
    have hxyabs : x * star x = y * star y := by
      simpa only [Complex.star_def, Complex.mul_conj] using congrArg Complex.ofReal hnorm.symm
    have hphase :
        y * (x - z) * (star z - star y) = x * (star x - star z) * (z - y) := by
      linear_combination -(y * (star z - star y)) * hsphase +
        (x * (star x - star z)) * htphase + ((star x - star z) * (star z - star y)) * hst
    have hfactor : (x - y) * (z * star z - x * star x) = 0 := by
      linear_combination hphase - (x - z) * hxyabs
    have hxzabs : z * star z = x * star x :=
      sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hxy))
    have hfactor' : (star x - star z) * (s * (x * star x) + x * z) = 0 := by
      linear_combination (x * star x) * hsphase - x * hxzabs
    have hneg : s * (x * star x) = -(x * z) :=
      eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hfactor').resolve_left
        (sub_ne_zero.mpr (star_injective.ne hxz)))
    have hrep : p * x * y * z = -(p * s * y) * (x * star x) := by
      linear_combination (p * y) * hneg
    apply hκ
    rw [hrep, Complex.star_def, Complex.mul_conj, Complex.mul_re, Complex.neg_re, hsy,
      Complex.ofReal_im, neg_zero, zero_mul, mul_zero, sub_zero]

private theorem unit_gap_phase (x z u v : ℂ) (hxz : x ≠ z)
    (hrel : star v * (x - z) = star (x - z) * u) :
    ∃ s : ℂ, s * star s = 1 ∧ s * (star x - star z) = x - z ∧ v = s * star u := by
  have hdiff := sub_ne_zero.mpr hxz
  have hden : star (x - z) ≠ 0 := fun h => hdiff (star_eq_zero.mp h)
  refine ⟨(x - z) / star (x - z), ?_, ?_, ?_⟩
  · rw [star_div₀, star_star, div_mul_div_comm, mul_comm (star (x - z)) (x - z),
      div_self (mul_ne_zero hdiff hden)]
  · rw [← star_sub, div_mul_cancel₀ _ hden]
  · rw [div_mul_eq_mul_div]
    apply (eq_div_iff hden).mpr
    simpa only [star_mul', star_star] using congrArg star hrel

private theorem re_pair_coefficient_eq_zero (κ x z s u : ℂ) (hu : u ≠ 0)
    (h : (κ * u * (s * star u) / (x * z)).re = 0) : (κ * s / (x * z)).re = 0 := by
  have he : κ * u * (s * star u) / (x * z) = (Complex.normSq u : ℂ) * (κ * s / (x * z)) := by
    rw [Complex.normSq_eq_conj_mul_self, ← Complex.star_def]
    simp only [div_eq_mul_inv]
    ring
  rw [he, Complex.re_ofReal_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (Complex.normSq_pos.mpr hu).ne'

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The mixed commutator for the phase about coordinate `k` constrains the
endpoint values of a path through that coordinate. -/
theorem endpoints_eq_of_hermitian_mixed_commutator (h : ι → ℂ) (B : Matrix ι ι ℂ) (κ : ℂ)
    (hB : B * Bᴴ = Bᴴ * B)
    (hA : (diagonal h - B) * (diagonal h - B)ᴴ = (diagonal h - B)ᴴ * (diagonal h - B))
    (hnz : ∀ l, h l ≠ 0) (hκ : κ.re ≠ 0)
    (hcritical :
      let J := diagonal (fun l => (h l)⁻¹)
      (κ • (B * J - J * B))ᴴ = κ • (B * J - J * B))
    {i j k : ι} (hik : i ≠ k) (hjk : j ≠ k) (hxz : h i ≠ h k) (hzy : h k ≠ h j)
    (hu : B i k ≠ 0) (hv : B k j ≠ 0)
    (hmixed :
      let J := diagonal (fun l => (h l)⁻¹)
      let X := diagonal (fun l => if l = k then Complex.I else 0)
      let Y := J * (X * B - B * X) * J
      let E := κ • (B * Y - Y * B)
      Eᴴ = E) :
    h i = h j := by
  let J := diagonal (fun l => (h l)⁻¹)
  let phase (l : ι) := if l = k then Complex.I else 0
  let X := diagonal phase
  let Y := J * (X * B - B * X) * J
  let E := κ • (B * Y - Y * B)
  let p := κ / (h i * h j * h k)
  change Eᴴ = E at hmixed
  have hY (m n : ι) :
      Y m n = (h m)⁻¹ * ((phase m - phase n) * B m n) * (h n)⁻¹ := by
    simp only [Y, J, X, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.sub_apply]
    ring
  have hentry (m n : ι) (hm : m ≠ k) (hn : n ≠ k) :
      (B * Y - Y * B) m n =
        Complex.I * B m k * B k n * ((h m + h n) / (h m * h k * h n)) := by
    have hl : (B * Y) m n = B m k * Y k n := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_single k
      · intro l _ hl
        simp [hY, phase, hn, hl]
      · simp
    have hr : (Y * B) m n = Y m k * B k n := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_single k
      · intro l _ hl
        simp [hY, phase, hm, hl]
      · simp
    rw [Matrix.sub_apply, hl, hr]
    simp only [hY, phase, if_pos rfl, if_neg hm, if_neg hn, sub_zero, zero_sub]
    field_simp [hnz m, hnz k, hnz n] <;> ring
  obtain ⟨s, hs, hsphase, hsrel⟩ := unit_gap_phase _ _ _ _ hxz
    (cross_entries_of_normal_diagonal_sum h B hB hA i k)
  obtain ⟨t, ht, htphase, htrel⟩ := unit_gap_phase _ _ _ _ hzy
    (cross_entries_of_normal_diagonal_sum h B hB hA k j)
  have hscoeff := stationary_normal_diagonal_pair_zero h B hB hA κ hcritical i k
    (hnz i) (hnz k) hxz
  have htcoeff := stationary_normal_diagonal_pair_zero h B hB hA κ hcritical k j
    (hnz k) (hnz j) hzy
  rw [hsrel] at hscoeff
  rw [htrel] at htcoeff
  have hsy : (p * s * h j).re = 0 := by
    have he : p * s * h j = κ * s / (h i * h k) := by
      dsimp [p]
      field_simp [hnz i, hnz j, hnz k] <;> ring
    rw [he]
    exact re_pair_coefficient_eq_zero _ _ _ _ _ hu hscoeff
  have htx : (p * t * h i).re = 0 := by
    have he : p * t * h i = κ * t / (h k * h j) := by
      dsimp [p]
      field_simp [hnz i, hnz j, hnz k] <;> ring
    rw [he]
    exact re_pair_coefficient_eq_zero _ _ _ _ _ hv htcoeff
  have hmatI : E i j = Complex.I * B i k * B k j * (p * (h i + h j)) := by
    simp only [E, Matrix.smul_apply, smul_eq_mul, hentry i j hik hjk, p]
    field_simp [hnz i, hnz j, hnz k] <;> ring
  have hmatJ : E j i = Complex.I * (t * star (B k j)) * (s * star (B i k)) *
      (p * (h i + h j)) := by
    simp only [E, Matrix.smul_apply, smul_eq_mul, hentry j i hjk hik, htrel, hsrel, p]
    field_simp [hnz i, hnz j, hnz k] <;> ring
  have hraw := congrArg (fun M : Matrix ι ι ℂ => M i j) hmixed
  change star (E j i) = E i j at hraw
  rw [hmatI, hmatJ] at hraw
  have hiStar : star Complex.I = -Complex.I := Complex.conj_I
  have he : (Complex.I * (B i k * B k j)) *
      (p * (h i + h j) + star (p * (h i + h j)) * star (s * t)) = 0 := by
    simp only [star_mul', star_star, hiStar] at hraw ⊢
    linear_combination -hraw
  have hm : p * (h i + h j) = -(star (p * (h i + h j)) * star (s * t)) :=
    eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp he).resolve_left
      (mul_ne_zero Complex.I_ne_zero (mul_ne_zero hu hv)))
  have hrep : p * h i * h j * h k = κ := by
    dsimp [p]
    field_simp [hnz i, hnz j, hnz k] <;> ring
  exact endpoints_eq_of_mixed_phase _ _ _ _ _ _ hxz (by rwa [hrep])
    hs ht hsphase htphase hsy htx hm

end MOC
