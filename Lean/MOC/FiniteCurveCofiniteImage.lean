import MOC.FiniteCurvePrimitiveCoordinate
import Mathlib.Topology.Separation.Connected

/-! A varying polynomial coordinate on a finite affine curve omits at most finitely many values. -/

open Set MvPolynomial
open scoped BigOperators

namespace MOC

/-- The finite projection itself, unlike a general varying coordinate,
takes every complex value on the affine curve. -/
theorem surjective_finite_affine_projection
    {σ : Type*} [Fintype σ]
    (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime]
    (f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ Q)) (hf : f.Finite)
    (hfi : Function.Injective f)
    (t : MvPolynomial σ ℂ) (ht : Ideal.Quotient.mk Q t = f Polynomial.X) :
    Function.Surjective (fun x : zeroLocus Q => eval x.val t) := by
  obtain ⟨P, hP, hirr, hplane⟩ :=
    exists_monic_irreducible_plane_image_of_finite_projection Q f hf hfi t t ht
  have hPd : P.natDegree ≠ 0 := fun h =>
    hirr.not_isUnit ((hP.natDegree_eq_zero_iff_eq_one.mp h).symm ▸ isUnit_one)
  intro a
  let R := P.map (Polynomial.evalRingHom a)
  have hRm : R.Monic := hP.map _
  have hRn : R.natDegree ≠ 0 := by
    change (P.map (Polynomial.evalRingHom a)).natDegree ≠ 0
    rw [hP.natDegree_map]
    exact hPd
  have hRd : R.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hRm.ne_zero]
    exact_mod_cast hRn
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_root R hRd
  obtain ⟨z, hz, hza, _⟩ := (hplane a b).mp hb
  exact ⟨⟨z, hz⟩, hza⟩

/-- Every nonconstant polynomial coordinate on a prime finite complex
affine curve has cofinite image. This applies to the actual affine points,
not merely a dense regular locus. -/
theorem finite_compl_range_varying_affine_coordinate
    {σ : Type*} [Fintype σ]
    (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime]
    (f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ Q)) (hf : f.Finite)
    (hfi : Function.Injective f)
    (t v : MvPolynomial σ ℂ) (ht : Ideal.Quotient.mk Q t = f Polynomial.X)
    (hvar : ∃ x y : zeroLocus Q, eval x.val v ≠ eval y.val v) :
    (Set.range (fun x : zeroLocus Q => eval x.val v))ᶜ.Finite := by
  classical
  letI : ConnectedSpace (zeroLocus Q) := connectedSpace_prime_finite_affine_curve Q f hf hfi t ht
  obtain ⟨P, hP, _, hplane⟩ :=
    exists_monic_irreducible_plane_image_of_finite_projection Q f hf hfi t v ht
  let I := Finset.range (P.natDegree + 1)
  let V (x : zeroLocus Q) := eval x.val v
  have hInf : (Set.range V).Infinite := by
    have hC : IsPreconnected (Set.range V) :=
      (isConnected_range (v.continuous_eval.comp continuous_subtype_val)).isPreconnected
    obtain ⟨x, y, hxy⟩ := hvar
    exact hC.infinite_of_nontrivial ⟨V x, ⟨x, rfl⟩, V y, ⟨y, rfl⟩, hxy⟩
  have hvarP : ∃ i ∈ I, ∃ k : ℕ, 0 < k ∧ (P.coeff i).coeff k ≠ 0 := by
    by_contra! h
    have hcoeff (i : ℕ) : P.coeff i = Polynomial.C ((P.coeff i).coeff 0) := by
      by_cases hi : i ∈ I
      · apply Polynomial.ext
        intro k
        cases k with
        | zero => simp
        | succ k => simpa [Polynomial.coeff_C] using h i hi (k + 1) (Nat.succ_pos _)
      · have hgt : P.natDegree < i := by
          have he := Finset.mem_range.not.mp hi
          omega
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt hgt]
        simp
    have hmap (a : ℂ) :
        P.map (Polynomial.evalRingHom a) = P.map (Polynomial.evalRingHom 0) := by
      apply Polynomial.ext
      intro i
      rw [Polynomial.coeff_map, Polynomial.coeff_map, hcoeff i]
      simp
    apply hInf
    apply (Polynomial.finite_setOf_isRoot (hP.map (Polynomial.evalRingHom 0)).ne_zero).subset
    rintro _ ⟨x, rfl⟩
    have hroot := (hplane (eval x.val t) (eval x.val v)).mpr ⟨x.val, x.property, rfl, rfl⟩
    rwa [hmap] at hroot
  obtain ⟨i, hi, k, hk, hik⟩ := hvarP
  let A : Polynomial ℂ := ∑ j ∈ I, Polynomial.monomial j ((P.coeff j).coeff k)
  have hA : A ≠ 0 := by
    intro h
    have hh := congrArg (fun p : Polynomial ℂ => p.coeff i) h
    exact hik (by simpa [A, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, hi] using hh)
  apply (Polynomial.finite_setOf_isRoot hA).subset
  intro w hw
  change w ∉ Set.range V at hw
  change A.eval w = 0
  apply Classical.byContradiction
  intro hw0
  let J : Polynomial ℂ := ∑ j ∈ I, P.coeff j * Polynomial.C (w ^ j)
  have hJ : J.coeff k = A.eval w := by
    simp only [J, A, Polynomial.finset_sum_coeff, Polynomial.coeff_mul_C,
      Polynomial.eval_finset_sum, Polynomial.eval_monomial]
  have hJk : J.coeff k ≠ 0 := hJ.trans_ne hw0
  have hJdeg : J.degree ≠ 0 := by
    have hn : 0 < J.natDegree := hk.trans_le (Polynomial.le_natDegree_of_ne_zero hJk)
    rw [Polynomial.degree_eq_natDegree (fun h => hJk (by simp [h]))]
    exact ne_of_gt (by exact_mod_cast hn)
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root J hJdeg
  have hval : J.eval a = (P.map (Polynomial.evalRingHom a)).eval w := by
    rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
    simp only [J, I, Polynomial.eval_finset_sum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.coe_evalRingHom]
  have hp : (P.map (Polynomial.evalRingHom a)).IsRoot w := hval.symm.trans ha
  obtain ⟨x, hx, _, hv⟩ := (hplane a w).mp hp
  exact hw ⟨⟨x,hx⟩, hv⟩

/-- In particular, a varying polynomial coordinate on the actual finite
affine curve has a negative projected real part somewhere. -/
theorem exists_affine_point_with_negative_real_of_varying_coordinate
    {σ : Type*} [Fintype σ]
    (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime]
    (f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ Q)) (hf : f.Finite)
    (hfi : Function.Injective f)
    (t v : MvPolynomial σ ℂ) (ht : Ideal.Quotient.mk Q t = f Polynomial.X)
    (hvar : ∃ x y : zeroLocus Q, eval x.val v ≠ eval y.val v) :
    ∃ x : zeroLocus Q, (eval x.val v).re < 0 := by
  let R := Set.range (fun x : zeroLocus Q => eval x.val v)
  have hfinite : Rᶜ.Finite := finite_compl_range_varying_affine_coordinate Q f hf hfi t v ht hvar
  obtain ⟨w, hw, hwr⟩ : ∃ w ∈ R, w.re < 0 := by
    let g (n : ℕ) : ℂ := -((n + 1 : ℕ) : ℂ)
    have hg : Function.Injective g := by
      intro m n h
      have hd : ((m + 1 : ℕ) : ℂ) = ((n + 1 : ℕ) : ℂ) := neg_injective h
      exact Nat.add_right_cancel (by exact_mod_cast hd)
    have hi : (Set.range g).Infinite := Set.infinite_range_of_injective hg
    have H := (hi.diff hfinite).nonempty
    obtain ⟨w, ⟨n, rfl⟩, hw⟩ := H
    have hn : 0 < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    exact ⟨g n, not_not.mp hw, by simpa only [g, Complex.neg_re, Complex.natCast_re,
      neg_lt_zero] using hn⟩
  obtain ⟨x, rfl⟩ := hw
  exact ⟨x, hwr⟩

end MOC
