import MOC.FiniteCurvePrimitiveCoordinate
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.Algebra.MvPolynomial.Funext

/-! A line in the base of a finite normalization cuts a curve through a
pinned point if the normalization satisfies going down. A contracted
principal ideal controls variation of a selected coordinate on the curve. -/

namespace MOC

/-- Select a prime under a pinned prime by going down to a base line.
The additional element `g` survives in the prime quotient by choosing
the line to avoid a nonzero element of its contracted principal ideal. -/
theorem exists_finite_curve_quotient_avoiding
    {k A B : Type*} [Field k] [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Algebra k A] [Algebra A B] [Algebra k B]
    [IsScalarTower k A B] [Module.Finite A B] [Algebra.HasGoingDown A B]
    (m : Ideal B) [m.IsPrime] (g : B) (hg : g ≠ 0)
    (chooseLine : ∀ f : A, f ≠ 0 →
      ∃ line : A →ₐ[k] Polynomial k, Function.Surjective line ∧
        RingHom.ker line ≤ m.under A ∧ line f ≠ 0) :
    ∃ q : Ideal B, q ≤ m ∧ q.IsPrime ∧
      ∃ F : Polynomial k →ₐ[k] B ⧸ q,
        F.Finite ∧ Function.Injective F ∧ Ideal.Quotient.mk q g ≠ 0 := by
  classical
  let I : Ideal B := Ideal.span {g}
  have hI : I.comap (algebraMap A B) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hg (Ideal.subset_span (Set.mem_singleton g))
      (Algebra.IsIntegral.isIntegral g)
  obtain ⟨f, hf, hf₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨line, hsurj, hline, havoid⟩ := chooseLine f hf₀
  let p := RingHom.ker line
  letI : p.IsPrime := RingHom.ker_isPrime line
  letI : (m.under A).IsPrime := Ideal.comap_isPrime (algebraMap A B) m
  letI : m.LiesOver (m.under A) := ⟨rfl⟩
  obtain ⟨q, hqm, hq, hqp⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := p) (q := m.under A) m hline
  letI : q.IsPrime := hq
  letI : q.LiesOver p := hqp
  have hcon : p = q.under A := hqp.over
  let b : A →ₐ[k] B := IsScalarTower.toAlgHom k A B
  have hh : p ≤ Ideal.comap b q := hcon.le
  let f₀ : A ⧸ p →ₐ[k] B ⧸ q := Ideal.quotientMapₐ q b hh
  let e : (A ⧸ p) ≃ₐ[k] Polynomial k := Ideal.quotientKerAlgEquivOfSurjective hsurj
  let F := f₀.comp e.symm.toAlgHom
  have hF (x : A) : F (line x) = Ideal.Quotient.mk q (algebraMap A B x) := by
    change f₀ (e.symm (line x)) = _
    have hx : e (Ideal.Quotient.mk p x) = line x := rfl
    rw [← hx, e.symm_apply_apply]
    rfl
  have hfinite : F.Finite := by
    apply AlgHom.Finite.of_comp_finite (f := line)
    have hcomp : F.comp line = (Ideal.Quotient.mkₐ k q).comp b :=
      AlgHom.ext hF
    rw [hcomp]
    have hb : b.Finite := by
      change (algebraMap A B).Finite
      rw [RingHom.Finite]
      convert (inferInstance : Module.Finite A B)
      ext
      simp_rw [Algebra.smul_def]
      rfl
    exact (AlgHom.Finite.of_surjective _ (Ideal.Quotient.mkₐ_surjective k q)).comp hb
  have hinj : Function.Injective F := by
    apply (RingHom.injective_iff_ker_eq_bot F).mpr
    apply eq_bot_iff.mpr
    intro x hx
    obtain ⟨y, rfl⟩ := hsurj x
    have hzero : F (line y) = 0 := hx
    rw [hF, Ideal.Quotient.eq_zero_iff_mem] at hzero
    have hm : y ∈ q.under A := hzero
    have hker : y ∈ p := hcon ▸ hm
    exact Ideal.mem_bot.mpr hker
  refine ⟨q, hqm, hq, F, hfinite, hinj, ?_⟩
  intro hgz
  have hgm : g ∈ q := Ideal.Quotient.eq_zero_iff_mem.mp hgz
  have hIq : I ≤ q := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hgm)
  have hfm : f ∈ q.under A := hIq hf
  have hfk : f ∈ p := hcon ▸ hfm
  exact havoid hfk


/-- An affine line through `x` that does not lie in a prescribed polynomial
zero set. The restriction map is onto because some coordinate has nonzero
slope. This supplies the line-choice input for a polynomial normalization
of positive rank. -/
theorem exists_affine_line_avoiding
    {k σ : Type*} [Field k] [Infinite k] [Nonempty σ]
    (x : σ → k) (f : MvPolynomial σ k) (hf : f ≠ 0) :
    ∃ line : MvPolynomial σ k →ₐ[k] Polynomial k,
      Function.Surjective line ∧ RingHom.ker line ≤ RingHom.ker (MvPolynomial.eval x) ∧
      line f ≠ 0 := by
  classical
  have hy₀ : ∃ y : σ → k, MvPolynomial.eval y f ≠ 0 := by
    by_contra! h
    exact hf (MvPolynomial.funext (q := 0) (by simpa using h))
  obtain ⟨y, hy, ht⟩ :
      ∃ y : σ → k, y ≠ x ∧ (MvPolynomial.eval x f ≠ 0 ∨ MvPolynomial.eval y f ≠ 0) := by
    by_cases hx : MvPolynomial.eval x f = 0
    · obtain ⟨y, hy⟩ := hy₀
      exact ⟨y, fun e => hy (e.symm ▸ hx), Or.inr hy⟩
    · let y (i : σ) := x i + 1
      refine ⟨y, ?_, Or.inl hx⟩
      intro e
      have he := congrFun e (Classical.choice ‹Nonempty σ›)
      simp [y] at he
  obtain ⟨i, hi⟩ : ∃ i : σ, y i ≠ x i := by
    by_contra! h
    exact hy (funext h)
  let d := y i - x i
  have hd : d ≠ 0 := sub_ne_zero.mpr hi
  let line : MvPolynomial σ k →ₐ[k] Polynomial k :=
    MvPolynomial.aeval (fun j => Polynomial.C (x j) +
      Polynomial.C (y j - x j) * Polynomial.X)
  have he (t : k) : (Polynomial.aeval t).comp line =
      MvPolynomial.aeval (fun j => x j + (y j - x j) * t) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [line]
  have h0 (u : MvPolynomial σ k) : (line u).eval 0 = MvPolynomial.eval x u := by
    have ht₀ := congrArg (fun h : MvPolynomial σ k →ₐ[k] k => h u) (he 0)
    simpa only [AlgHom.comp_apply, Polynomial.coe_aeval_eq_eval, mul_zero, add_zero] using ht₀
  have h1 (u : MvPolynomial σ k) : (line u).eval 1 = MvPolynomial.eval y u := by
    have ht₁ := congrArg (fun h : MvPolynomial σ k →ₐ[k] k => h u) (he 1)
    have hxy (j : σ) : x j + (y j - x j) = y j := by ring
    simpa only [AlgHom.comp_apply, Polynomial.coe_aeval_eq_eval, mul_one, hxy] using ht₁
  let Xlift : MvPolynomial σ k := MvPolynomial.C d⁻¹ * (MvPolynomial.X i - MvPolynomial.C (x i))
  have hX : line Xlift = Polynomial.X := by
    simp only [Xlift, map_mul, map_sub]
    unfold line
    simp only [MvPolynomial.aeval_C, MvPolynomial.aeval_X, Polynomial.algebraMap_eq,
      add_sub_cancel_left]
    change Polynomial.C d⁻¹ * (Polynomial.C d * _) = _
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hd, Polynomial.C_1, one_mul]
  have hright : line.comp (Polynomial.aeval Xlift) = AlgHom.id k (Polynomial k) := by
    apply Polynomial.algHom_ext
    simp [hX]
  refine ⟨line, ?_, ?_, ?_⟩
  · intro u
    exact ⟨Polynomial.aeval Xlift u, congrArg (fun h : Polynomial k →ₐ[k] Polynomial k => h u) hright⟩
  · intro u hu
    change line u = 0 at hu
    change MvPolynomial.eval x u = 0
    rw [← h0, hu, Polynomial.eval_zero]
  · intro hfline
    rcases ht with hx | hy
    · exact hx (by rw [← h0, hfline, Polynomial.eval_zero])
    · exact hy (by rw [← h1, hfline, Polynomial.eval_zero])

/-- A positive-rank finite polynomial normalization gives a curve through
a chosen prime, provided going down holds. Its quotient retains the
chosen nonzero function. -/
theorem exists_polynomial_normalization_curve_avoiding
    {k σ B : Type*} [Field k] [Infinite k] [Nonempty σ]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra (MvPolynomial σ k) B]
    [IsScalarTower k (MvPolynomial σ k) B] [Module.Finite (MvPolynomial σ k) B]
    [Algebra.HasGoingDown (MvPolynomial σ k) B]
    (m : Ideal B) [m.IsPrime] (x : σ → k)
    (hm : m.under (MvPolynomial σ k) = RingHom.ker (MvPolynomial.eval x))
    (g : B) (hg : g ≠ 0) :
    ∃ q : Ideal B, q ≤ m ∧ q.IsPrime ∧
      ∃ F : Polynomial k →ₐ[k] B ⧸ q,
        F.Finite ∧ Function.Injective F ∧ Ideal.Quotient.mk q g ≠ 0 := by
  apply exists_finite_curve_quotient_avoiding (A := MvPolynomial σ k) m g hg
  simpa only [hm] using exists_affine_line_avoiding x

end MOC
