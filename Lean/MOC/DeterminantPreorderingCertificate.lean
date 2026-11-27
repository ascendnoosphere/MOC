import MOC.DeterminantPolynomialInfeasibility
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Order.Ring.Cone
import Mathlib.Algebra.Ring.Semireal.Defs
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Defs

/-! Exact certificate implications for polynomial determinant separation. -/

open BigOperators

namespace MOC

noncomputable section

universe u

private theorem map_sumSq {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {a : R} (ha : IsSumSq a) : IsSumSq (f a) := by
  induction ha with
  | zero =>
      rw [map_zero]
      exact IsSumSq.zero
  | sq_add b _ ih =>
      rw [map_add, map_mul]
      exact IsSumSq.sq_add (f b) ih

private theorem eval_nonneg_of_sumSq_mod_equations {V K : Type*} [Fintype K]
    (f : K → MvPolynomial V ℝ) (x : V → ℝ) (hx : ∀ k, MvPolynomial.eval x (f k) = 0)
    {p s : MvPolynomial V ℝ} (hs : IsSumSq s) (h : K → MvPolynomial V ℝ)
    (he : p = s + ∑ k, h k * f k) : 0 ≤ MvPolynomial.eval x p := by
  have hEval := congrArg (MvPolynomial.eval x) he
  simp only [map_add, map_sum, map_mul, hx, mul_zero, Finset.sum_const_zero, add_zero] at hEval
  rw [hEval]
  exact (map_sumSq (MvPolynomial.eval x) hs).nonneg

private theorem lift_quotient_sumSq {R : Type*} [CommRing R] (I : Ideal R)
    {a : R ⧸ I} (ha : IsSumSq a) : ∃ b : R, IsSumSq b ∧ Ideal.Quotient.mk I b = a := by
  induction ha with
  | zero => exact ⟨0, IsSumSq.zero, map_zero _⟩
  | sq_add c _ ih =>
      obtain ⟨b, hb, hmap⟩ := ih
      obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective (I := I) c
      exact ⟨d * d + b, IsSumSq.sq_add d hb, by rw [map_add, map_mul, hd, hmap]⟩

private def oneAddSquares (R : Type*) [CommRing R] : Submonoid R where
  carrier := {x | ∃ s : R, IsSumSq s ∧ x = 1 + s}
  one_mem' := ⟨0, IsSumSq.zero, (add_zero 1).symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b + a * b, (ha.add hb).add (ha.mul hb), by ring⟩

private theorem clear_localization_sumSq {R L : Type*} [CommRing R] [CommRing L]
    [Algebra R L] (S : Submonoid R) [IsLocalization S L] {z : L} (hz : IsSumSq z) :
    ∃ (d : S) (p : R), IsSumSq p ∧ algebraMap R L p = (algebraMap R L d) ^ 2 * z := by
  induction hz with
  | zero => exact ⟨1, 0, IsSumSq.zero, by rw [map_zero, mul_zero]⟩
  | sq_add z _ ih =>
      obtain ⟨d, p, hp, hscale⟩ := ih
      obtain ⟨⟨a, b⟩, hnum⟩ := IsLocalization.surj S z
      refine ⟨b * d, (a * d) * (a * d) + ((b : R) * b) * p,
        IsSumSq.sq_add (a * d) ((IsSumSq.mul_self (b : R)).mul hp), ?_⟩
      simp only [Submonoid.coe_mul, map_add, map_mul, ← hnum, hscale]
      ring

private theorem one_add_sumSq_isUnit_in_localization {R : Type*} [CommRing R]
    {z : Localization (oneAddSquares R)} (hz : IsSumSq z) : IsUnit (1 + z) := by
  let S := oneAddSquares R
  let L := Localization S
  let q := algebraMap R L
  obtain ⟨d, p, hp, hscale⟩ := clear_localization_sumSq S hz
  have hd : ∃ t : R, IsSumSq t ∧ (d : R) = 1 + t := d.property
  obtain ⟨t, ht, hd⟩ := hd
  have hmem : (d : R) ^ 2 + p ∈ S := by
    refine ⟨t + t + t * t + p, ((ht.add ht).add (ht.mul ht)).add hp, ?_⟩
    rw [hd]
    ring
  have hnum : IsUnit (q ((d : R) ^ 2 + p)) := IsLocalization.map_units L ⟨_, hmem⟩
  have he : q ((d : R) ^ 2 + p) = (1 + z) * (q d) ^ 2 := by
    rw [map_add, map_pow, hscale]
    ring
  rw [he] at hnum
  exact isUnit_of_mul_isUnit_left hnum

/-- A semireal ring has a homomorphism to a semireal field. Localize
at one plus the sums of squares, then pass to a maximal residue field. -/
theorem exists_semireal_field_target {R : Type u} [CommRing R] [IsSemireal R] :
    ∃ (K : Type u) (_ : Field K), IsSemireal K ∧ Nonempty (R →+* K) := by
  let S := oneAddSquares R
  let L := Localization S
  have hzero : (0 : R) ∉ S := by
    rintro ⟨s, hs, hz⟩
    exact IsSemireal.one_add_ne_zero hs hz.symm
  letI : Nontrivial L := by
    refine nontrivial_of_ne (0 : L) 1 fun hz => ?_
    have hmap : algebraMap R L (1 : R) = 0 := by
      rw [map_one]
      exact hz.symm
    obtain ⟨d, hd⟩ := (IsLocalization.map_eq_zero_iff S L (1 : R)).mp hmap
    have hvalue : (d : R) = 0 := by simpa only [mul_one] using hd
    exact hzero (hvalue ▸ d.property)
  obtain ⟨I, hI⟩ := Ideal.exists_maximal (α := L)
  letI : I.IsMaximal := hI
  let K := L ⧸ I
  letI : Field K := Ideal.Quotient.field I
  have hK : IsSemireal K := by
    constructor
    intro s hs hz
    obtain ⟨p, hp, he⟩ := lift_quotient_sumSq I hs
    have hu : IsUnit (Ideal.Quotient.mk I (1 + p)) :=
      (one_add_sumSq_isUnit_in_localization hp).map (Ideal.Quotient.mk I)
    apply hu.ne_zero
    rw [map_add, map_one, he, hz]
  exact ⟨K, inferInstance, hK, ⟨(Ideal.Quotient.mk I).comp (algebraMap R L)⟩⟩

private def adjoinConeElement {K : Type*} [Field K] (P : Subsemiring K)
    (a : K) (ha : a * a ∈ P) : Subsemiring K where
  carrier := {x | ∃ p ∈ P, ∃ q ∈ P, x = p + a * q}
  zero_mem' := ⟨0, P.zero_mem, 0, P.zero_mem, by simp⟩
  one_mem' := ⟨1, P.one_mem, 0, P.zero_mem, by simp⟩
  add_mem' := by
    rintro _ _ ⟨p, hp, q, hq, rfl⟩ ⟨r, hr, s, hs, rfl⟩
    exact ⟨p + r, P.add_mem hp hr, q + s, P.add_mem hq hs, by ring⟩
  mul_mem' := by
    rintro _ _ ⟨p, hp, q, hq, rfl⟩ ⟨r, hr, s, hs, rfl⟩
    exact ⟨p * r + (a * a) * (q * s), P.add_mem (P.mul_mem hp hr) (P.mul_mem ha (P.mul_mem hq hs)),
      p * s + q * r, P.add_mem (P.mul_mem hp hs) (P.mul_mem hq hr), by ring⟩

/-- A semireal field admits an order compatible with its field operations. -/
theorem exists_order_of_semireal_field (K : Type*) [Field K] [IsSemireal K] :
    ∃ _ : LinearOrder K, IsStrictOrderedRing K := by
  classical
  let C₀ := Subsemiring.sumSq K
  let G : Set (Subsemiring K) := {P | C₀ ≤ P ∧ (-1 : K) ∉ P}
  have hbase : C₀ ∈ G :=
    ⟨le_rfl, fun hn => IsSemireal.not_isSumSq_neg_one (Subsemiring.mem_sumSq.mp hn)⟩
  have hchain (c : Set (Subsemiring K)) (hc : c ⊆ G) (hdir : IsChain (· ≤ ·) c)
      (P₀ : Subsemiring K) (hP₀ : P₀ ∈ c) : ∃ B ∈ G, ∀ P ∈ c, P ≤ B := by
    letI : Nonempty c := ⟨⟨P₀, hP₀⟩⟩
    refine ⟨sSup c, ⟨(hc hP₀).1.trans (le_sSup hP₀), ?_⟩, fun _ => le_sSup⟩
    intro hneg
    have ⟨Q, hQ⟩ := (Subsemiring.mem_iSup_of_directed hdir.directed).mp (sSup_eq_iSup' c ▸ hneg)
    exact (hc Q.property).2 hQ
  obtain ⟨P, _, hP⟩ := zorn_le_nonempty₀ G hchain C₀ hbase
  have hsquare (a : K) : a * a ∈ P := hP.1.1 (Subsemiring.mem_sumSq.mpr (IsSumSq.mul_self a))
  have hinv {a : K} (ha : a ∈ P) (hn : a ≠ 0) : a⁻¹ ∈ P := by
    have hm := P.mul_mem ha (hsquare a⁻¹)
    rwa [← mul_assoc, mul_inv_cancel₀ hn, one_mul] at hm
  have htotal (a : K) : a ∈ P ∨ -a ∈ P := by
    by_cases ha : a ∈ P
    · exact Or.inl ha
    right
    let Q := adjoinConeElement P a (hsquare a)
    have hPQ : P ≤ Q := fun p hp => ⟨p, hp, 0, P.zero_mem, by simp⟩
    have haQ : a ∈ Q := ⟨0, P.zero_mem, 1, P.one_mem, by simp⟩
    have hlt : P < Q := lt_of_le_of_ne hPQ (fun he => ha (he.symm ▸ haQ))
    have hnQ : (-1 : K) ∈ Q := by
      by_contra hn
      exact hP.not_prop_of_gt hlt ⟨hP.1.1.trans hPQ, hn⟩
    obtain ⟨p, hp, q, hq, he⟩ := hnQ
    have hqn : q ≠ 0 := by
      intro hz
      have hneg : (-1 : K) = p := by simpa only [hz, mul_zero, add_zero] using he
      exact hP.1.2 (hneg.symm ▸ hp)
    have hsign : -(a * q) = 1 + p := by linear_combination he
    rw [show -a = (1 + p) * q⁻¹ by rw [← hsign, neg_mul, mul_assoc, mul_inv_cancel₀ hqn, mul_one]]
    exact P.mul_mem (P.add_mem P.one_mem hp) (hinv hq hqn)
  let C : RingCone K :=
    { __ := P
      eq_zero_of_mem_of_neg_mem' := by
        intro a ha hna
        by_contra hn
        have hprod := P.mul_mem hna (hinv ha hn)
        rw [neg_mul, mul_inv_cancel₀ hn] at hprod
        exact hP.1.2 hprod }
  letI : IsMaxCone C := ⟨htotal⟩
  let L : LinearOrder K := LinearOrder.mkOfAddGroupCone C (fun a => Classical.propDecidable (a ∈ C))
  letI : LinearOrder K := L
  letI : IsOrderedAddMonoid K := IsOrderedAddMonoid.mkOfCone C
  letI : IsOrderedRing K := IsOrderedRing.mkOfCone C
  letI : ZeroLEOneClass K := ⟨by
    change (1 - 0 : K) ∈ C
    rw [sub_zero]
    exact P.one_mem⟩
  exact ⟨L, IsStrictOrderedRing.of_mul_pos fun a b ha hb =>
    lt_of_le_of_ne (mul_nonneg ha.le hb.le) (mul_ne_zero ha.ne' hb.ne').symm⟩

/-- The coordinate ring is semireal exactly when the polynomial system
has a solution in some semireal field extension of the real coefficients. -/
theorem semireal_polynomial_quotient_iff_extension_point {V : Type u} {E : Type*}
    (f : E → MvPolynomial V ℝ) :
    IsSemireal (MvPolynomial V ℝ ⧸ Ideal.span (Set.range f)) ↔
      ∃ (K : Type u) (_ : Field K) (_ : IsSemireal K)
        (e : ℝ →+* K) (x : V → K), ∀ j, MvPolynomial.eval₂ e x (f j) = 0 := by
  let I := Ideal.span (Set.range f)
  let A := MvPolynomial V ℝ ⧸ I
  constructor
  · intro hA
    letI : IsSemireal A := hA
    obtain ⟨K, hK, hS, ⟨φ⟩⟩ := exists_semireal_field_target (R := A)
    letI := hK
    let ψ := φ.comp (Ideal.Quotient.mk I)
    let e := ψ.comp MvPolynomial.C
    let x : V → K := ψ ∘ MvPolynomial.X
    have he : MvPolynomial.eval₂Hom e x = ψ := by
      apply MvPolynomial.ringHom_ext
      · exact fun r => MvPolynomial.eval₂Hom_C e x r
      · exact fun i => MvPolynomial.eval₂Hom_X' e x i
    refine ⟨K, hK, hS, e, x, fun j => ?_⟩
    change MvPolynomial.eval₂Hom e x (f j) = 0
    rw [he]
    change φ (Ideal.Quotient.mk I (f j)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self j)), map_zero]
  · rintro ⟨K, hK, hS, e, x, hx⟩
    letI := hK
    letI := hS
    let ψ := MvPolynomial.eval₂Hom e x
    have hker : I ≤ RingHom.ker ψ := by
      apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact RingHom.mem_ker.mpr (hx j)
    let φ : A →+* K := Ideal.Quotient.lift I ψ fun p hp => RingHom.mem_ker.mp (hker hp)
    constructor
    intro s hs hz
    have he : 1 + φ s = 0 := by
      simpa only [map_add, map_one, map_zero] using congrArg φ hz
    exact IsSemireal.one_add_ne_zero (map_sumSq φ hs) he

/-- A semireal coordinate ring has a point in a linearly ordered field
extension of the real coefficients. Conversely such a point makes the
coordinate ring semireal. -/
theorem semireal_polynomial_quotient_iff_ordered_extension_point {V : Type u} {E : Type*}
    (f : E → MvPolynomial V ℝ) :
    IsSemireal (MvPolynomial V ℝ ⧸ Ideal.span (Set.range f)) ↔
      ∃ (K : Type u) (_ : Field K) (_ : LinearOrder K) (_ : IsStrictOrderedRing K)
        (e : ℝ →+* K) (x : V → K), ∀ j, MvPolynomial.eval₂ e x (f j) = 0 := by
  rw [semireal_polynomial_quotient_iff_extension_point]
  constructor
  · rintro ⟨K, hK, hS, e, x, hx⟩
    letI := hK
    letI := hS
    obtain ⟨L, hL⟩ := exists_order_of_semireal_field K
    exact ⟨K, hK, L, hL, e, x, hx⟩
  · rintro ⟨K, hK, hL, hO, e, x, hx⟩
    letI := hK
    letI := hL
    letI := hO
    exact ⟨K, hK, inferInstance, e, x, hx⟩

private theorem not_isSemireal_iff_neg_one_sumSq (R : Type*) [CommRing R] :
    ¬ IsSemireal R ↔ IsSumSq (-1 : R) := by
  classical
  constructor
  · intro h
    by_contra hs
    apply h
    constructor
    intro a ha hz
    apply hs
    have he : a = -1 := by
      calc
        a = -1 + (1 + a) := by rw [← add_assoc, neg_add_cancel, zero_add]
        _ = -1 := by rw [hz, add_zero]
    exact he ▸ ha
  · intro hs h
    letI := h
    exact IsSemireal.not_isSumSq_neg_one hs

/-- A sum-of-squares identity modulo finitely many equations is equivalent
to a sum-of-squares representation of minus one in the coordinate ring. -/
theorem polynomial_certificate_iff_quotient_sumSq {R K : Type*} [CommRing R] [Fintype K]
    (f : K → R) :
    (∃ s : R, IsSumSq s ∧ ∃ h : K → R, (-1 : R) = s + ∑ k, h k * f k) ↔
      IsSumSq (-1 : R ⧸ Ideal.span (Set.range f)) := by
  let I := Ideal.span (Set.range f)
  let q := Ideal.Quotient.mk I
  change _ ↔ IsSumSq (-1 : R ⧸ I)
  have hzero (k : K) : q (f k) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self k))
  constructor
  · rintro ⟨s, hs, h, he⟩
    have hq := congrArg q he
    simp only [map_neg, map_one, map_add, map_sum, map_mul, hzero, mul_zero,
      Finset.sum_const_zero, add_zero] at hq
    exact hq.symm ▸ map_sumSq q hs
  · intro hs
    obtain ⟨s, hsq, hmap⟩ := lift_quotient_sumSq I hs
    have hzero' : q (-1 - s) = 0 := by
      change Ideal.Quotient.mk I (-1 - s) = 0
      rw [map_sub, map_neg, map_one, hmap, sub_self]
    obtain ⟨h, he⟩ := Ideal.mem_span_range_iff_exists_fun.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp hzero')
    refine ⟨s, hsq, h, ?_⟩
    calc
      (-1 : R) = (-1 - s) + s := (sub_add_cancel _ _).symm
      _ = s + ∑ k, h k * f k := by rw [he, add_comm]

/-- The absence of a finite sum-of-squares equation certificate is
equivalent to semireality of the coordinate ring. -/
theorem semireal_quotient_iff_no_polynomial_certificate {R K : Type*}
    [CommRing R] [Fintype K] (f : K → R) :
    IsSemireal (R ⧸ Ideal.span (Set.range f)) ↔
      ¬ ∃ s : R, IsSumSq s ∧ ∃ h : K → R, (-1 : R) = s + ∑ k, h k * f k := by
  classical
  rw [polynomial_certificate_iff_quotient_sumSq]
  exact not_not.symm.trans (not_congr (not_isSemireal_iff_neg_one_sumSq _))

/-- A finite equation certificate exists exactly when the equations have
no solution over any ordered field extending the real coefficients. -/
theorem polynomial_certificate_iff_no_ordered_extension_point {V : Type u} {E : Type*}
    [Fintype E] (f : E → MvPolynomial V ℝ) :
    (∃ s : MvPolynomial V ℝ, IsSumSq s ∧ ∃ h : E → MvPolynomial V ℝ,
        (-1 : MvPolynomial V ℝ) = s + ∑ j, h j * f j) ↔
      ¬ ∃ (K : Type u) (_ : Field K) (_ : LinearOrder K) (_ : IsStrictOrderedRing K)
        (e : ℝ →+* K) (x : V → K), ∀ j, MvPolynomial.eval₂ e x (f j) = 0 := by
  rw [polynomial_certificate_iff_quotient_sumSq, ← not_isSemireal_iff_neg_one_sumSq]
  exact not_congr (semireal_polynomial_quotient_iff_ordered_extension_point f)

/-- Real solutions of a polynomial system are the real-valued algebra
homomorphisms of its coordinate ring. -/
theorem real_zeros_iff_real_algebra_point {V K : Type*} (f : K → MvPolynomial V ℝ) :
    (∃ x : V → ℝ, ∀ k, MvPolynomial.eval x (f k) = 0) ↔
      Nonempty ((MvPolynomial V ℝ ⧸ Ideal.span (Set.range f)) →ₐ[ℝ] ℝ) := by
  let I := Ideal.span (Set.range f)
  constructor
  · rintro ⟨x, hx⟩
    have hker : I ≤ RingHom.ker (MvPolynomial.eval x) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨k, rfl⟩
      exact RingHom.mem_ker.mpr (hx k)
    refine ⟨Ideal.Quotient.liftₐ I (MvPolynomial.aeval x) (fun p hp => ?_)⟩
    change MvPolynomial.eval x p = 0
    exact RingHom.mem_ker.mp (hker hp)
  · rintro ⟨φ⟩
    let ψ : MvPolynomial V ℝ →ₐ[ℝ] ℝ := φ.comp (Ideal.Quotient.mkₐ ℝ I)
    let x : V → ℝ := ψ ∘ MvPolynomial.X
    have he : MvPolynomial.aeval x = ψ := (MvPolynomial.aeval_unique ψ).symm
    refine ⟨x, fun k => ?_⟩
    change MvPolynomial.aeval x (f k) = 0
    rw [he]
    change φ (Ideal.Quotient.mk I (f k)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self k)), map_zero]

/-- An exact finite equation certificate follows from a sum-of-squares
representation of minus one in the equation quotient. -/
theorem no_real_zeros_of_quotient_sumSq {V K : Type*} [Fintype K]
    (f : K → MvPolynomial V ℝ)
    (h : IsSumSq (-1 : MvPolynomial V ℝ ⧸ Ideal.span (Set.range f))) :
    ¬ ∃ x : V → ℝ, ∀ k, MvPolynomial.eval x (f k) = 0 := by
  rintro ⟨x, hx⟩
  obtain ⟨s, hs, a, he⟩ := (polynomial_certificate_iff_quotient_sumSq f).mpr h
  have hn := eval_nonneg_of_sumSq_mod_equations f x hx hs a he
  rw [map_neg, map_one] at hn
  exact (not_le_of_gt (neg_neg_of_pos zero_lt_one)) hn

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

local notation "P" => MvPolynomial (DeterminantWitnessVariable ι) ℝ

/-- Additive nonnegative margin polynomials for the closed separation test. -/
def determinantUnitMargin (σ : Equiv.Perm ι) : P := determinantGapPolynomial σ - 1

private theorem exists_unit_margin_scale {K : Type*} [Fintype K] [Nonempty K]
    (g : K → ℝ) (hg : ∀ k, 0 < g k) {n : ℕ} (hn : n ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ k, 1 ≤ r ^ n * g k := by
  obtain ⟨k₀, _, hmin⟩ := Finset.exists_min_image Finset.univ g Finset.univ_nonempty
  let r := max 1 (g k₀)⁻¹
  have hr : 1 ≤ r := le_max_left _ _
  refine ⟨r, zero_lt_one.trans_le hr, fun k => ?_⟩
  calc
    1 = (g k₀)⁻¹ * g k₀ := (inv_mul_cancel₀ (hg k₀).ne').symm
    _ ≤ r * g k₀ := mul_le_mul_of_nonneg_right (le_max_right _ _) (hg k₀).le
    _ ≤ r ^ n * g k₀ := mul_le_mul_of_nonneg_right (le_self_pow₀ hr hn) (hg k₀).le
    _ ≤ r ^ n * g k := mul_le_mul_of_nonneg_left (hmin k (Finset.mem_univ k))
      (pow_nonneg (zero_le_one.trans hr) n)

/-- A strict separator in positive order can be scaled until every
determinant gap is at least one. -/
theorem conjecture_iff_no_unit_margin_witness [Nonempty ι] :
    Conjecture ι ↔ ¬ ∃ x : DeterminantWitnessVariable ι → ℝ,
      (∀ i j c, MvPolynomial.eval x (determinantGramPolynomial i j c) = 0) ∧
      (∀ σ, 0 ≤ MvPolynomial.eval x (determinantUnitMargin σ)) := by
  rw [conjecture_iff_no_polynomial_witness]
  constructor
  · rintro h ⟨x, hU, hgap⟩
    refine h ⟨x, hU, fun σ => zero_lt_one.trans_le (sub_nonneg.mp ?_)⟩
    simpa only [determinantUnitMargin, map_sub, map_one] using hgap σ
  · rintro h ⟨x, hGram, hgap⟩
    obtain ⟨r, _, hnorm⟩ := exists_unit_margin_scale
      (fun σ => MvPolynomial.eval x (determinantGapPolynomial σ)) hgap
      (Fintype.card_ne_zero (α := ι))
    let a := witnessFirstSpectrum x
    let b := witnessSecondSpectrum x
    let U := witnessMixer x
    let y := witnessValuation (fun i => (r : ℂ) * a i) (fun i => (r : ℂ) * b i) U (fun _ => 0)
    obtain ⟨ha, hb, hU⟩ := witnessValuation_values
      (fun i => (r : ℂ) * a i) (fun i => (r : ℂ) * b i) U (fun _ => 0)
    have hUnitary : IsUnitary (witnessMixer y) := by
      rw [hU]
      exact (gramPolynomials_zero_iff x).mp hGram
    refine h ⟨y, (gramPolynomials_zero_iff y).mpr hUnitary, fun σ => ?_⟩
    have he : MvPolynomial.eval y (determinantGapPolynomial σ) =
        r ^ Fintype.card ι * MvPolynomial.eval x (determinantGapPolynomial σ) := by
      rw [eval_determinantGapPolynomial, eval_determinantGapPolynomial, ha, hb, hU,
        determinantValue_scale, matchingProduct_scale, ← mul_sub,
        ← Complex.ofReal_pow, Complex.re_ofReal_mul]
    rw [determinantUnitMargin, map_sub, map_one, he]
    exact sub_nonneg.mpr (hnorm σ)

/-- The nonnegative margins can also be represented by real slack squares. -/
def determinantUnitMarginEquation : DeterminantWitnessEquation ι → P
  | .inl (i, j, c) => determinantGramPolynomial i j c
  | .inr σ => determinantUnitMargin σ - MvPolynomial.X (.inr σ) ^ 2

/-- The closed separation system is equivalent to the slack-square
equation system. -/
theorem conjecture_iff_no_unit_margin_equation_witness [Nonempty ι] :
    Conjecture ι ↔ ¬ ∃ x : DeterminantWitnessVariable ι → ℝ,
      ∀ k, MvPolynomial.eval x (determinantUnitMarginEquation k) = 0 := by
  rw [conjecture_iff_no_unit_margin_witness]
  constructor
  · rintro h ⟨x, hx⟩
    refine h ⟨x, fun i j c => hx (.inl (i, j, c)), fun σ => ?_⟩
    have he : MvPolynomial.eval x (determinantUnitMargin σ) = x (.inr σ) ^ 2 := by
      apply sub_eq_zero.mp
      simpa only [determinantUnitMarginEquation, map_sub, map_pow, MvPolynomial.eval_X]
        using hx (.inr σ)
    rw [he]
    exact sq_nonneg _
  · rintro h ⟨x, hGram, hgap⟩
    let a := witnessFirstSpectrum x
    let b := witnessSecondSpectrum x
    let U := witnessMixer x
    let t (σ : Equiv.Perm ι) := Real.sqrt (MvPolynomial.eval x (determinantUnitMargin σ))
    let y := witnessValuation a b U t
    obtain ⟨ha, hb, hU⟩ := witnessValuation_values a b U t
    have hUnitary : IsUnitary (witnessMixer y) := by
      rw [hU]
      exact (gramPolynomials_zero_iff x).mp hGram
    refine h ⟨y, ?_⟩
    rintro (⟨i, j, c⟩ | σ)
    · exact (gramPolynomials_zero_iff y).mpr hUnitary i j c
    · simp only [determinantUnitMarginEquation, map_sub, map_pow, MvPolynomial.eval_X]
      have he : MvPolynomial.eval y (determinantUnitMargin σ) =
          MvPolynomial.eval x (determinantUnitMargin σ) := by
        simp only [determinantUnitMargin, map_sub, map_one, eval_determinantGapPolynomial]
        rw [ha, hb, hU]
      change MvPolynomial.eval y (determinantUnitMargin σ) - t σ ^ 2 = 0
      dsimp only [t]
      rw [he, Real.sq_sqrt (hgap σ), sub_self]

/-- The extra variables are a common strict margin and its reciprocal square-root witness. -/
abbrev DeterminantCommonMarginVariable (ι : Type*) := DeterminantWitnessVariable ι ⊕ Bool

/-- The common-margin system has one extra equation to force the margin to be positive. -/
abbrev DeterminantCommonMarginEquation (ι : Type*) := DeterminantWitnessEquation ι ⊕ Unit

/-- Express strict separation by a positive common margin and nonnegative
square slacks for the excess over that margin. -/
def determinantCommonMarginPolynomial : DeterminantCommonMarginEquation ι →
    MvPolynomial (DeterminantCommonMarginVariable ι) ℝ
  | .inl (.inl (i, j, c)) => MvPolynomial.rename Sum.inl (determinantGramPolynomial i j c)
  | .inl (.inr σ) => MvPolynomial.rename Sum.inl (determinantGapPolynomial σ) -
      MvPolynomial.X (.inr false) - MvPolynomial.X (.inl (.inr σ)) ^ 2
  | .inr _ => MvPolynomial.X (.inr false) * MvPolynomial.X (.inr true) ^ 2 - 1

/-- The common-margin polynomial equations characterize strict counterexamples. -/
theorem conjecture_iff_no_common_margin_witness [Nonempty ι] :
    Conjecture ι ↔ ¬ ∃ x : DeterminantCommonMarginVariable ι → ℝ,
      ∀ k, MvPolynomial.eval x (determinantCommonMarginPolynomial k) = 0 := by
  rw [conjecture_iff_no_polynomial_witness]
  constructor
  · rintro h ⟨x, hx⟩
    let z : DeterminantWitnessVariable ι → ℝ := x ∘ Sum.inl
    have hδmul : x (.inr false) * x (.inr true) ^ 2 = 1 := by
      apply sub_eq_zero.mp
      simpa only [determinantCommonMarginPolynomial, map_sub, map_mul, map_pow,
        MvPolynomial.eval_X, map_one] using hx (.inr ())
    have hδprod : 0 < x (.inr false) * x (.inr true) ^ 2 := by
      rw [hδmul]
      exact zero_lt_one
    have hδ : 0 < x (.inr false) := pos_of_mul_pos_left hδprod (sq_nonneg _)
    refine h ⟨z, fun i j c => ?_, fun σ => ?_⟩
    · simpa only [determinantCommonMarginPolynomial, MvPolynomial.eval_rename]
        using hx (.inl (.inl (i, j, c)))
    · have he : MvPolynomial.eval z (determinantGapPolynomial σ) - x (.inr false) =
          x (.inl (.inr σ)) ^ 2 := by
        apply sub_eq_zero.mp
        simpa only [determinantCommonMarginPolynomial, MvPolynomial.eval_rename,
          map_sub, map_pow, MvPolynomial.eval_X] using hx (.inl (.inr σ))
      have hn : 0 ≤ MvPolynomial.eval z (determinantGapPolynomial σ) - x (.inr false) := by
        rw [he]
        exact sq_nonneg _
      exact hδ.trans_le (sub_nonneg.mp hn)
  · rintro h ⟨x, hGram, hgap⟩
    let g (σ : Equiv.Perm ι) := MvPolynomial.eval x (determinantGapPolynomial σ)
    obtain ⟨σ₀, _, hmin⟩ := Finset.exists_min_image Finset.univ g Finset.univ_nonempty
    let δ := g σ₀
    have hδ : 0 < δ := hgap σ₀
    have hδle (σ : Equiv.Perm ι) : δ ≤ g σ := hmin σ (Finset.mem_univ σ)
    let a := witnessFirstSpectrum x
    let b := witnessSecondSpectrum x
    let U := witnessMixer x
    let t (σ : Equiv.Perm ι) := Real.sqrt (g σ - δ)
    let z := witnessValuation a b U t
    let y : DeterminantCommonMarginVariable ι → ℝ :=
      Sum.elim z fun c => if c then (Real.sqrt δ)⁻¹ else δ
    obtain ⟨ha, hb, hU⟩ := witnessValuation_values a b U t
    have hUnitary : IsUnitary (witnessMixer z) := by
      rw [hU]
      exact (gramPolynomials_zero_iff x).mp hGram
    refine h ⟨y, ?_⟩
    rintro ((⟨i, j, c⟩ | σ) | ⟨⟩)
    · rw [determinantCommonMarginPolynomial, MvPolynomial.eval_rename]
      exact (gramPolynomials_zero_iff z).mpr hUnitary i j c
    · simp only [determinantCommonMarginPolynomial, map_sub, map_pow, MvPolynomial.eval_X,
        MvPolynomial.eval_rename]
      change MvPolynomial.eval z (determinantGapPolynomial σ) - δ - t σ ^ 2 = 0
      have he : MvPolynomial.eval z (determinantGapPolynomial σ) = g σ := by
        dsimp only [g]
        rw [eval_determinantGapPolynomial, eval_determinantGapPolynomial, ha, hb, hU]
      dsimp only [t]
      rw [he, Real.sq_sqrt (sub_nonneg.mpr (hδle σ)), sub_self]
    · simp only [determinantCommonMarginPolynomial, map_sub, map_mul, map_pow,
        MvPolynomial.eval_X, map_one]
      change δ * (Real.sqrt δ)⁻¹ ^ 2 - 1 = 0
      rw [inv_pow, Real.sq_sqrt hδ.le, mul_inv_cancel₀ hδ.ne', sub_self]

/-- The finite preordering identity uses one product of margins for each
subset of matching permutations. Each product has a sum-of-squares multiplier. -/
def HasDeterminantPreorderingCertificate : Prop :=
  ∃ s : Finset (Equiv.Perm ι) → P, (∀ J, IsSumSq (s J)) ∧
    ∃ h : ι × ι × Bool → P,
      (-1 : P) = (∑ J, s J * ∏ σ ∈ J, determinantUnitMargin σ) +
        ∑ k, h k * determinantGramPolynomial k.1 k.2.1 k.2.2

/-- Evaluating a preordering identity rules out the closed separation system. -/
theorem no_unit_margin_witness_of_preordering_certificate
    (h : HasDeterminantPreorderingCertificate (ι := ι)) :
    ¬ ∃ x : DeterminantWitnessVariable ι → ℝ,
      (∀ i j c, MvPolynomial.eval x (determinantGramPolynomial i j c) = 0) ∧
      (∀ σ, 0 ≤ MvPolynomial.eval x (determinantUnitMargin σ)) := by
  obtain ⟨s, hs, a, he⟩ := h
  rintro ⟨x, hGram, hmargin⟩
  have hEval := congrArg (MvPolynomial.eval x) he
  simp only [map_neg, map_one, map_add, map_sum, map_mul, map_prod, hGram,
    mul_zero, Finset.sum_const_zero, add_zero] at hEval
  have hnonneg : 0 ≤ ∑ J : Finset (Equiv.Perm ι), MvPolynomial.eval x (s J) *
      ∏ σ ∈ J, MvPolynomial.eval x (determinantUnitMargin σ) := by
    apply Finset.sum_nonneg
    intro J _
    exact mul_nonneg (map_sumSq (MvPolynomial.eval x) (hs J)).nonneg
      (Finset.prod_nonneg fun σ _ => hmargin σ)
  linarith only [hEval, hnonneg]

/-- A preordering certificate gives the determinant inclusion in positive order. -/
theorem conjecture_of_preordering_certificate [Nonempty ι]
    (h : HasDeterminantPreorderingCertificate (ι := ι)) : Conjecture ι :=
  conjecture_iff_no_unit_margin_witness.mpr (no_unit_margin_witness_of_preordering_certificate h)

/-- At fixed spectra, an exact sum of squares modulo unitarity suffices
for the polynomial that represents the support cost. This includes the
case where the representative and the identity have degree at most four. -/
theorem conjecture_of_fixed_spectral_cost_certificates [Nonempty ι]
    (h : ∀ a b : ι → ℂ, ∃ σ : Equiv.Perm ι,
      ∃ p s : P, IsSumSq s ∧
        (∀ U : Matrix ι ι ℂ, IsUnitary U →
          MvPolynomial.eval (witnessValuation a b U (fun _ => 0)) p =
            (matchingProduct a b σ).re - (determinantValue a b U).re) ∧
        ∃ q : ι × ι × Bool → P,
          p = s + ∑ k, q k * determinantGramPolynomial k.1 k.2.1 k.2.2) :
    Conjecture ι := by
  rw [conjecture_iff_real_bound]
  intro a b U hU
  obtain ⟨σ, p, s, hs, hvalue, q, hcert⟩ := h a b
  let x := witnessValuation a b U (fun _ => 0)
  obtain ⟨_, _, hxU⟩ := witnessValuation_values a b U (fun _ => 0)
  have hUnitary : IsUnitary (witnessMixer x) := by rwa [hxU]
  have hx := (gramPolynomials_zero_iff x).mpr hUnitary
  have hn := eval_nonneg_of_sumSq_mod_equations
    (fun k : ι × ι × Bool => determinantGramPolynomial k.1 k.2.1 k.2.2)
    x (fun k => hx k.1 k.2.1 k.2.2) hs q hcert
  rw [hvalue U hU] at hn
  exact ⟨σ, sub_nonneg.mp hn⟩

/-- Passing to the slack-square quotient converts a preordering certificate
to a sum-of-squares certificate for equations alone. -/
theorem quotient_sumSq_of_determinant_preordering_certificate
    (h : HasDeterminantPreorderingCertificate (ι := ι)) :
    IsSumSq (-1 : P ⧸ Ideal.span (Set.range determinantUnitMarginEquation)) := by
  let I := Ideal.span (Set.range (determinantUnitMarginEquation (ι := ι)))
  let q := Ideal.Quotient.mk I
  have hzero (k : DeterminantWitnessEquation ι) : q (determinantUnitMarginEquation k) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self k))
  have hGram (i j : ι) (c : Bool) : q (determinantGramPolynomial i j c) = 0 :=
    hzero (.inl (i, j, c))
  have hSq (σ : Equiv.Perm ι) : IsSumSq (q (determinantUnitMargin σ)) := by
    have he : q (determinantUnitMargin σ) = q (MvPolynomial.X (.inr σ) : P) ^ 2 := by
      apply sub_eq_zero.mp
      simpa only [determinantUnitMarginEquation, map_sub, map_pow] using hzero (.inr σ)
    rw [he, pow_two]
    exact IsSumSq.mul_self _
  obtain ⟨s, hs, a, he⟩ := h
  have hq := congrArg q he
  simp only [map_neg, map_one, map_add, map_sum, map_mul, map_prod, hGram, mul_zero,
    Finset.sum_const_zero, add_zero] at hq
  change IsSumSq (-1 : P ⧸ I)
  rw [hq]
  exact IsSumSq.sum fun J _ => (map_sumSq q (hs J)).mul (IsSumSq.prod fun σ _ => hSq σ)

/-- A certificate in the strict separation coordinate ring suffices. -/
theorem conjecture_of_polynomial_quotient_sumSq [Nonempty ι]
    (h : IsSumSq (-1 : P ⧸ Ideal.span (Set.range determinantWitnessPolynomial))) :
    Conjecture ι :=
  conjecture_iff_no_polynomial_equation_witness.mpr
    (no_real_zeros_of_quotient_sumSq determinantWitnessPolynomial h)

/-- In positive order, the conjecture holds exactly when the strict
separation coordinate ring has no real point. -/
theorem conjecture_iff_no_polynomial_quotient_real_point [Nonempty ι] :
    Conjecture ι ↔
      ¬ Nonempty ((P ⧸ Ideal.span (Set.range determinantWitnessPolynomial)) →ₐ[ℝ] ℝ) :=
  conjecture_iff_no_polynomial_equation_witness.trans
    (not_congr (real_zeros_iff_real_algebra_point determinantWitnessPolynomial))

/-- The missing direction of certificate completeness is the real-point
theorem for the semireal strict separation coordinate ring. -/
theorem determinant_certificate_completeness_iff_semireal_real_point [Nonempty ι] :
    let A := P ⧸ Ideal.span (Set.range determinantWitnessPolynomial)
    (Conjecture ι → IsSumSq (-1 : A)) ↔ (IsSemireal A → Nonempty (A →ₐ[ℝ] ℝ)) := by
  classical
  dsimp only
  rw [conjecture_iff_no_polynomial_quotient_real_point,
    ← not_isSemireal_iff_neg_one_sumSq]
  constructor
  · intro h hsemi
    by_contra hpoint
    exact h hpoint hsemi
  · intro h hpoint hsemi
    exact hpoint (h hsemi)

/-- Certificate completeness for strict separation is equivalent to
descent of its polynomial solutions from ordered extensions to the reals. -/
theorem determinant_certificate_completeness_iff_ordered_field_descent [Nonempty ι] :
    let f := determinantWitnessPolynomial (ι := ι)
    let A := P ⧸ Ideal.span (Set.range f)
    (Conjecture ι → IsSumSq (-1 : A)) ↔
      ((∃ (K : Type u) (_ : Field K) (_ : LinearOrder K) (_ : IsStrictOrderedRing K)
          (e : ℝ →+* K) (x : DeterminantWitnessVariable ι → K),
          ∀ j, MvPolynomial.eval₂ e x (f j) = 0) →
        ∃ x : DeterminantWitnessVariable ι → ℝ, ∀ j, MvPolynomial.eval x (f j) = 0) := by
  have h := determinant_certificate_completeness_iff_semireal_real_point (ι := ι)
  dsimp only at h ⊢
  rw [h, semireal_polynomial_quotient_iff_ordered_extension_point,
    ← real_zeros_iff_real_algebra_point]

end
end MOC
