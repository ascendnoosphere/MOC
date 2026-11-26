import MOC.PinnedPrimeHeight
import MOC.FiniteCurvePrimitiveCoordinate
import MOC.FiniteCurveCofiniteImage
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-! A polynomial level set on an irreducible complex affine variety has a
feasible point with many coordinates on the boundary of the right half-plane. -/

open Set MvPolynomial
open scoped BigOperators

namespace MOC

noncomputable section

variable {σ : Type} [Fintype σ]

/-- The indices on the imaginary axis at a point in complex coordinate space. -/
def affineBoundaryCoordinates (x : σ → ℂ) : Finset σ :=
  Finset.univ.filter fun i => (x i).re = 0

private theorem mem_affineBoundaryCoordinates (x : σ → ℂ) (i : σ) :
    i ∈ affineBoundaryCoordinates x ↔ (x i).re = 0 := by
  simp only [affineBoundaryCoordinates, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem exists_larger_affine_boundary
    (I : Ideal (MvPolynomial σ ℂ)) [I.IsPrime] {d : ℕ}
    (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ I))
    (hf : f.Finite) (hfi : Function.Injective f) (g : MvPolynomial σ ℂ)
    (x : zeroLocus I) (hx : ∀ i, 0 ≤ (x.val i).re)
    (hd : (affineBoundaryCoordinates x.val).card + 1 < d) :
    ∃ y : zeroLocus I, eval y.val g = eval x.val g ∧
      (∀ i, 0 ≤ (y.val i).re) ∧
      affineBoundaryCoordinates x.val ⊂ affineBoundaryCoordinates y.val := by
  classical
  let active := affineBoundaryCoordinates x.val
  let pin (p : MvPolynomial σ ℂ) := p - C (eval x.val p)
  let cuts := insert (pin g) (active.image fun i => pin (X i))
  have hcuts (p : MvPolynomial σ ℂ) (hp : p ∈ cuts) : eval x.val p = 0 := by
    rcases Finset.mem_insert.mp hp with rfl | hp
    · simp only [pin, map_sub, eval_C, sub_self]
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      simp only [pin, map_sub, eval_C, sub_self]
  have hcard : cuts.card < d :=
    (Finset.card_insert_le _ _).trans_lt
      ((Nat.add_le_add_right Finset.card_image_le 1).trans_lt hd)
  obtain ⟨Q, hIQ, hQx, hprime, hmem, F, hF, hFi, t, ht⟩ :=
    exists_finite_curve_at_prime_affine_after_equations I f hf hfi x cuts hcuts hcard
  letI : Q.IsPrime := hprime
  letI := connectedSpace_prime_finite_affine_curve Q F hF hFi t ht
  let x₀ : zeroLocus Q := ⟨x.val, fun p hp => hQx hp⟩
  have hpin (z : zeroLocus Q) (p : MvPolynomial σ ℂ) (hp : pin p ∈ cuts) :
      eval z.val p = eval x.val p := by
    have hz := z.property _ (hmem _ hp)
    simpa only [pin, map_sub, eval_C, sub_eq_zero] using hz
  have hfix (z : zeroLocus Q) (i : σ) (hi : i ∈ active) : z.val i = x.val i := by
    simpa only [eval_X] using hpin z (X i)
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem (fun i => pin (X i)) hi))
  obtain ⟨z, hz⟩ := surjective_finite_affine_projection Q F hF hFi t ht (eval x.val t + 1)
  have hne : z.val ≠ x.val := by
    intro he
    change eval z.val t = eval x.val t + 1 at hz
    rw [he] at hz
    have himpossible : (1 : ℂ) = 0 := by linear_combination -hz
    exact one_ne_zero himpossible
  obtain ⟨j, hj⟩ := not_forall.mp (fun h : ∀ i, z.val i = x.val i => hne (funext h))
  obtain ⟨b, hb⟩ := exists_affine_point_with_negative_real_of_varying_coordinate
    Q F hF hFi t (X j) ht ⟨z, x₀, by simpa only [x₀, eval_X] using hj⟩
  rw [eval_X] at hb
  have hinactive : j ∉ active := fun h => hj (hfix z j h)
  let J := activeᶜ
  have hJ : J.Nonempty := ⟨j, Finset.mem_compl.mpr hinactive⟩
  let m (z : zeroLocus Q) := J.inf' hJ (fun i => (z.val i).re)
  have hc : ContinuousOn m univ :=
    ContinuousOn.finset_inf'_apply hJ fun i _ =>
      (Complex.continuous_re.comp ((continuous_apply i).comp continuous_subtype_val)).continuousOn
  have hpos : 0 < m x₀ := by
    apply (Finset.lt_inf'_iff hJ).mpr
    intro i hi
    exact lt_of_le_of_ne (hx i) (fun he =>
      (Finset.mem_compl.mp hi) ((mem_affineBoundaryCoordinates x.val i).mpr he.symm))
  have hneg : m b < 0 := (Finset.inf'_lt_iff hJ).mpr ⟨j, Finset.mem_compl.mpr hinactive, hb⟩
  obtain ⟨y, _, hy⟩ := (isPreconnected_univ.image m hc).Icc_subset
    ⟨b, Set.mem_univ _, rfl⟩ ⟨x₀, Set.mem_univ _, rfl⟩ ⟨hneg.le, hpos.le⟩
  obtain ⟨i, hi, him⟩ := Finset.exists_mem_eq_inf' hJ (fun k => (y.val k).re)
  have hold (k : σ) (hk : k ∈ active) : (y.val k).re = 0 := by
    rw [hfix y k hk]
    exact (mem_affineBoundaryCoordinates x.val k).mp hk
  refine ⟨⟨y.val, fun p hp => y.property p (hIQ hp)⟩,
    hpin y g (Finset.mem_insert_self ..), ?_, ?_⟩
  · intro k
    by_cases hk : k ∈ active
    · exact (hold k hk).ge
    · exact (Finset.le_inf'_iff hJ _).mp hy.ge k (Finset.mem_compl.mpr hk)
  · apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨fun k hk => (mem_affineBoundaryCoordinates y.val k).mpr (hold k hk), ?_⟩
    intro he
    have hiy := (mem_affineBoundaryCoordinates y.val i).mpr (him.symm.trans hy)
    exact (Finset.mem_compl.mp hi) (he.symm ▸ hiy)

/-- On an irreducible complex affine variety of dimension `d`, each
nonempty polynomial level in the closed right half-planes contains a point
with at least `d - 1` coordinates on the imaginary axis. Dimension is the
transcendence degree of the coordinate ring. -/
theorem exists_affine_support_saturation
    (I : Ideal (MvPolynomial σ ℂ)) [I.IsPrime] {d : ℕ}
    (hd : Algebra.trdeg ℂ (MvPolynomial σ ℂ ⧸ I) = (d : Cardinal))
    (g : MvPolynomial σ ℂ) (x : zeroLocus I) (hx : ∀ i, 0 ≤ (x.val i).re) :
    ∃ y : zeroLocus I, eval y.val g = eval x.val g ∧
      (∀ i, 0 ≤ (y.val i).re) ∧ d - 1 ≤ (affineBoundaryCoordinates y.val).card := by
  classical
  let R := MvPolynomial σ ℂ ⧸ I
  letI : Algebra.FiniteType ℂ R := Algebra.FiniteType.of_surjective
    (Algebra.FiniteType.mvPolynomial ℂ σ) (Ideal.Quotient.mkₐ ℂ I) (Ideal.Quotient.mkₐ_surjective _ _)
  obtain ⟨n, f, hfi, hf⟩ := exists_finite_inj_algHom_of_fg ℂ R
  let A := MvPolynomial (Fin n) ℂ
  letI : Algebra A R := f.toRingHom.toAlgebra
  letI : IsScalarTower ℂ A R := IsScalarTower.of_algebraMap_eq fun c => (f.commutes c).symm
  letI : Module.Finite A R := hf
  letI : FaithfulSMul A R := (faithfulSMul_iff_algebraMap_injective A R).mpr hfi
  have hn : (n : Cardinal) = (d : Cardinal) := by
    calc
      (n : Cardinal) = Algebra.trdeg ℂ A := by
        simp only [A, MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype, Fintype.card_fin,
          Cardinal.lift_natCast]
      _ = Algebra.trdeg ℂ R := by
        simpa only [trdeg_eq_zero (R := A) (A := R), add_zero] using
          (trdeg_add_eq ℂ A (A := R))
      _ = (d : Cardinal) := hd
  have hnd : n = d := by exact_mod_cast hn
  let attainable (J : Finset σ) := ∃ y : zeroLocus I,
    eval y.val g = eval x.val g ∧ (∀ i, 0 ≤ (y.val i).re) ∧ affineBoundaryCoordinates y.val = J
  let S := Finset.univ.filter attainable
  have hstart : affineBoundaryCoordinates x.val ∈ S :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, rfl, hx, rfl⟩
  obtain ⟨J, hJ, hmax⟩ := Finset.exists_max_image S Finset.card ⟨_, hstart⟩
  obtain ⟨y, hy, hyfeas, hyJ⟩ := (Finset.mem_filter.mp hJ).2
  refine ⟨y, hy, hyfeas, ?_⟩
  by_contra! hsmall
  have hbudget : (affineBoundaryCoordinates y.val).card + 1 < n := by omega
  obtain ⟨z, hz, hzfeas, hstrict⟩ := exists_larger_affine_boundary I f hf hfi g y hyfeas hbudget
  have hzS : affineBoundaryCoordinates z.val ∈ S :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, z, hz.trans hy, hzfeas, rfl⟩
  have hle := hmax _ hzS
  rw [← hyJ] at hle
  exact (not_lt_of_ge hle) (Finset.card_lt_card hstrict)

/-- A linear functional on complex coordinate space keeps its full complex
value when at least `d - 1` feasible coordinates reach the boundary. -/
theorem exists_affine_linear_support_saturation
    (I : Ideal (MvPolynomial σ ℂ)) [I.IsPrime] {d : ℕ}
    (hd : Algebra.trdeg ℂ (MvPolynomial σ ℂ ⧸ I) = (d : Cardinal))
    (c : σ → ℂ) (x : zeroLocus I) (hx : ∀ i, 0 ≤ (x.val i).re) :
    ∃ y : zeroLocus I, (∑ i, c i * y.val i) = ∑ i, c i * x.val i ∧
      (∀ i, 0 ≤ (y.val i).re) ∧ d - 1 ≤ (affineBoundaryCoordinates y.val).card := by
  obtain ⟨y, hy, hyfeas, hycard⟩ := exists_affine_support_saturation I hd
    (∑ i, C (c i) * X i) x hx
  exact ⟨y, by simpa only [map_sum, map_mul, eval_C, eval_X] using hy, hyfeas, hycard⟩

end

end MOC
