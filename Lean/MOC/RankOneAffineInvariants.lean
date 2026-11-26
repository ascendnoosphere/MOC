import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Classification of polynomial invariants that are affine in the product of
two varying roots at fixed trace. The leading homogeneous component tests all
possible coefficients of the complementary monic polynomial. -/

open BigOperators Finset MvPolynomial
open scoped Polynomial

namespace MOC.RankOneAffineInvariants

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def lineSubstitution (b v : ι → ℂ) : MvPolynomial ι ℂ →+* ℂ[X] :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i => Polynomial.C (v i) * Polynomial.X + Polynomial.C (b i))

private theorem lineSubstitution_eval (p : MvPolynomial ι ℂ) (b v : ι → ℂ) (q : ℂ) :
    (lineSubstitution b v p).eval q = MvPolynomial.eval (fun i => v i * q + b i) p := by
  change Polynomial.evalRingHom q (MvPolynomial.eval₂Hom Polynomial.C _ p) = _
  rw [MvPolynomial.map_eval₂Hom]
  have hc : (Polynomial.evalRingHom q).comp Polynomial.C = RingHom.id ℂ := by apply RingHom.ext; intro a; simp
  simp [hc, MvPolynomial.eval]

private theorem lineSubstitution_top (p : MvPolynomial ι ℂ) (b v : ι → ℂ)
    (hv : ∀ i, v i ≠ 0) (d : ℕ) (hd : ∀ m ∈ p.support, m.degree ≤ d) :
    (lineSubstitution b v p).coeff d =
      MvPolynomial.eval v (MvPolynomial.homogeneousComponent d p) := by
  classical
  let L (i : ι) := Polynomial.C (v i) * Polynomial.X + Polynomial.C (b i)
  have hL (i : ι) : (L i).natDegree = 1 := Polynomial.natDegree_linear (hv i)
  have hN (i : ι) : L i ≠ 0 := by
    intro h
    simpa [h] using hL i
  conv_lhs => rw [p.as_sum]
  rw [map_sum, Polynomial.finset_sum_coeff, MvPolynomial.homogeneousComponent_apply, map_sum,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  let Q := ∏ i ∈ m.support, (L i)^(m i)
  have hQ : Q.natDegree = m.degree := by
    dsimp only [Q, Finsupp.degree]
    rw [Polynomial.natDegree_prod _ _ (fun i _ => pow_ne_zero _ (hN i))]
    simp only [Polynomial.natDegree_pow, hL, mul_one]
  have hlc : Q.leadingCoeff = m.prod (fun i k => (v i)^k) := by
    simp only [Q, Polynomial.leadingCoeff_prod, Polynomial.leadingCoeff_pow, L,
      Polynomial.leadingCoeff_linear (hv _), Finsupp.prod]
  change (MvPolynomial.eval₂Hom Polynomial.C L (MvPolynomial.monomial m (p.coeff m))).coeff d = _
  rw [MvPolynomial.eval₂Hom_monomial, Polynomial.coeff_C_mul, MvPolynomial.eval_monomial]
  change p.coeff m * Q.coeff d = _
  by_cases he : m.degree = d
  · rw [if_pos he, ← he, ← hQ, Polynomial.coeff_natDegree, hlc]
  · rw [if_neg he, Polynomial.coeff_eq_zero_of_natDegree_lt (hQ.trans_lt (lt_of_le_of_ne (hd m hm) he)), mul_zero]

/-- If an affine restriction exists on a line of every direction with nonzero
coordinates, every monomial of the polynomial has degree at most one. The
base point may depend on the direction. -/
theorem degree_le_one_of_affine_lines (p : MvPolynomial ι ℂ)
    (h : ∀ v : ι → ℂ, (∀ i, v i ≠ 0) → ∃ (b : ι → ℂ) (α β : ℂ),
      ∀ q : ℂ, MvPolynomial.eval (fun i => v i * q + b i) p = β*q + α) :
    ∀ m ∈ p.support, m.degree ≤ 1 := by
  classical
  intro m hm
  by_contra! hbig
  obtain ⟨k, hk, hmax⟩ := p.support.exists_max_image (fun u => u.degree) ⟨m, hm⟩
  have hd : 1 < k.degree := hbig.trans_le (hmax m hm)
  let T := MvPolynomial.homogeneousComponent k.degree p
  have hT : T ≠ 0 := by
    intro hzero
    have hh := congrArg (MvPolynomial.coeff k) hzero
    simp only [T, MvPolynomial.coeff_homogeneousComponent, if_pos rfl, MvPolynomial.coeff_zero] at hh
    exact MvPolynomial.mem_support_iff.mp hk hh
  have hn : T * (∏ i : ι, (MvPolynomial.X i : MvPolynomial ι ℂ)) ≠ 0 :=
    mul_ne_zero hT (Finset.prod_ne_zero_iff.mpr fun _ _ => MvPolynomial.X_ne_zero _)
  obtain ⟨v, hv⟩ : ∃ v : ι → ℂ,
      MvPolynomial.eval v (T * (∏ i : ι, (MvPolynomial.X i : MvPolynomial ι ℂ))) ≠ 0 := by
    by_contra! he
    exact hn (MvPolynomial.funext fun v => by simp [he])
  simp only [map_mul, map_prod, MvPolynomial.eval_X] at hv
  have hv' : ∀ i, v i ≠ 0 := fun i => Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hv) i (Finset.mem_univ _)
  obtain ⟨b, α, β, hab⟩ := h v hv'
  have hline : lineSubstitution b v p = Polynomial.C β * Polynomial.X + Polynomial.C α := by
    apply Polynomial.funext
    intro q
    rw [lineSubstitution_eval, hab]
    simp
  have hlow : (lineSubstitution b v p).natDegree ≤ 1 := hline ▸ Polynomial.natDegree_linear_le
  have ht := lineSubstitution_top p b v hv' k.degree hmax
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hlow.trans_lt hd)] at ht
  exact left_ne_zero_of_mul hv ht.symm

/-- The coefficients of the complementary monic polynomial are c₀=1,
c₁,…,cₘ. Use zero above degree m. -/
def complementaryCoefficient {m : ℕ} (c : Fin (m+1) → ℂ) (k : ℕ) : ℂ :=
  if hk : k < m+1 then c ⟨k,hk⟩ else 0

/-- The coefficient e_(i+2) independent of the product of the selected roots.
The sum of all roots equals t. -/
def pairBase {m : ℕ} (t : ℂ) (c : Fin (m+1) → ℂ) (i : Fin (m+1)) : ℂ :=
  complementaryCoefficient c (i.val+2) +
    (t - complementaryCoefficient c 1) * complementaryCoefficient c (i.val+1)

/-- In order m+2, write a symmetric polynomial in its elementary
coefficients. The coefficient ring ℂ[X] records the trace. The other
indeterminates record e₂ through e_(m+2), in that order. -/
def PairProductAffine {m : ℕ} (p : MvPolynomial (Fin (m+1)) ℂ[X]) : Prop :=
  ∀ (t : ℂ) (c : Fin (m+1) → ℂ), c 0 = 1 → ∃ α β : ℂ, ∀ q : ℂ,
    MvPolynomial.eval (fun i => c i * q + pairBase t c i)
      (MvPolynomial.map (Polynomial.evalRingHom t) p) = β*q + α

private theorem coefficient_vanishes {m : ℕ} {p : MvPolynomial (Fin (m+1)) ℂ[X]}
    (h : PairProductAffine p) (k : Fin (m+1) →₀ ℕ) (hk : 1 < k.degree) : p.coeff k = 0 := by
  apply Polynomial.funext
  intro t
  let P := MvPolynomial.map (Polynomial.evalRingHom t) p
  have hdegree : ∀ u ∈ P.support, u.degree ≤ 1 := by
    apply degree_le_one_of_affine_lines
    intro v hv
    let c (i : Fin (m+1)) := v i / v 0
    have hc : c 0 = 1 := div_self (hv 0)
    obtain ⟨α, β, hab⟩ := h t c hc
    refine ⟨pairBase t c, α, β * v 0, fun q => ?_⟩
    have harg : (fun i => v i * q + pairBase t c i) =
        (fun i => c i * (v 0 * q) + pairBase t c i) := by
      funext i
      dsimp [c]
      field_simp [hv 0] <;> ring
    rw [harg, hab (v 0 * q)]
    ring
  have hzero : P.coeff k = 0 := by
    by_contra hn
    exact (not_le_of_gt hk) (hdegree k (MvPolynomial.mem_support_iff.mpr hn))
  simpa only [P, MvPolynomial.coeff_map, Polynomial.coe_evalRingHom, Polynomial.eval_zero] using hzero

private theorem degree_one_single {σ : Type*} [DecidableEq σ] (d : σ →₀ ℕ)
    (hd : d.degree = 1) : ∃ i, d = Finsupp.single i 1 := by
  have hc : d.toMultiset.card = 1 := (Finsupp.card_toMultiset d).trans hd
  obtain ⟨i, hi⟩ := Multiset.card_eq_one.mp hc
  refine ⟨i, ?_⟩
  have he := (Multiset.toFinsupp_eq_iff (s := ({i} : Multiset σ)) (f := d)).mpr hi.symm
  simpa using he.symm

/-- Classification of pair-product-affine symmetric invariants in elementary
coordinates, with polynomials in the trace as coefficients. -/
theorem pairProductAffine_iff {m : ℕ} (p : MvPolynomial (Fin (m+1)) ℂ[X]) :
    PairProductAffine p ↔ ∃ (f₀ : ℂ[X]) (f : Fin (m+1) → ℂ[X]),
      p = MvPolynomial.C f₀ + ∑ i, MvPolynomial.C (f i) * MvPolynomial.X i := by
  classical
  constructor
  · intro h
    refine ⟨p.coeff 0, fun i => p.coeff (Finsupp.single i 1), ?_⟩
    ext k
    simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_sum, MvPolynomial.C_mul_X_eq_monomial,
      MvPolynomial.coeff_monomial, MvPolynomial.coeff_C]
    by_cases hk : k = 0
    · subst k
      simp
    · have h0 : k.degree ≠ 0 := fun he => hk ((Finsupp.degree_eq_zero_iff k).mp he)
      by_cases h1 : k.degree = 1
      · obtain ⟨i, rfl⟩ := degree_one_single k h1
        simp
      · have hn (i : Fin (m+1)) : Finsupp.single i 1 ≠ k := by
          intro he
          exact h1 (he ▸ Finsupp.degree_single i 1)
        simp [hk, Ne.symm hk, hn, coefficient_vanishes h k (by omega)]
  · rintro ⟨f₀, f, rfl⟩ t c hc
    refine ⟨f₀.eval t + ∑ i, (f i).eval t * pairBase t c i,
      ∑ i, (f i).eval t * c i, fun q => ?_⟩
    simp only [map_add, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
      MvPolynomial.eval_C, MvPolynomial.eval_X, Polynomial.coe_evalRingHom,
      mul_add, ← mul_assoc, Finset.sum_add_distrib, Finset.sum_mul]
    ring

/-- Elementary coefficients of a multiset of remaining roots, in descending
order of the powers of the characteristic variable. -/
def rootCoefficients (m : ℕ) (r : Multiset ℂ) (i : Fin (m+1)) : ℂ :=
  ((r.map fun x => Polynomial.X + Polynomial.C x).prod).coeff (m-i.val)

theorem exists_roots_of_complementary_coefficients {m : ℕ} (c : Fin (m+1) → ℂ)
    (hc : c 0 = 1) : ∃ r : Multiset ℂ, r.card = m ∧ rootCoefficients m r = c := by
  classical
  let Q : ℂ[X] := ∑ i : Fin (m+1), Polynomial.monomial (m-i.val) (c i)
  have hcoeff (i : Fin (m+1)) : Q.coeff (m-i.val) = c i := by
    dsimp only [Q]
    rw [Polynomial.finset_sum_coeff, Finset.sum_eq_single i]
    · exact Polynomial.coeff_monomial_same _ _
    · intro j _ hji
      apply Polynomial.coeff_monomial_of_ne
      intro he
      apply hji
      apply Fin.ext
      omega
    · simp
  have hdeg : Q.natDegree = m := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      intro j hj
      dsimp only [Q]
      rw [Polynomial.finset_sum_coeff]
      exact Finset.sum_eq_zero fun i _ => Polynomial.coeff_monomial_of_ne _ (by omega)
    · have he : Q.coeff m = 1 := by simpa using (hcoeff 0).trans hc
      rw [he]; exact one_ne_zero
  have htop : Q.coeff m = 1 := by simpa using (hcoeff 0).trans hc
  have hmon : Q.Monic := by change Q.coeff Q.natDegree = 1; rwa [hdeg]
  have hsplit := IsAlgClosed.splits Q
  have hprod := Polynomial.eq_prod_roots_of_monic_of_splits_id hmon hsplit
  have hcard := Polynomial.natDegree_eq_card_roots hsplit
  refine ⟨Q.roots.map Neg.neg, ?_, ?_⟩
  · simpa [hdeg] using hcard.symm
  · funext i
    simpa [rootCoefficients, Multiset.map_map, Function.comp_def, sub_eq_add_neg] using
      (congrArg (fun P : ℂ[X] => P.coeff (m-i.val)) hprod.symm).trans (hcoeff i)

theorem rootCoefficients_zero {m : ℕ} (r : Multiset ℂ) (hr : r.card = m) :
    rootCoefficients m r 0 = 1 := by
  let Q : ℂ[X] := (r.map fun x => Polynomial.X + Polynomial.C x).prod
  have hmon : Q.Monic := Polynomial.monic_multiset_prod_of_monic r _ (fun x _ => Polynomial.monic_X_add_C x)
  have hd : Q.natDegree = m := by
    dsimp only [Q]
    rw [Polynomial.natDegree_multiset_prod]
    · simpa [Multiset.map_map, Function.comp_def, Multiset.map_const', Multiset.sum_replicate] using hr
    · intro he
      obtain ⟨x, _, he⟩ := Multiset.mem_map.mp he
      exact (Polynomial.monic_X_add_C x).ne_zero he
  change Q.coeff (m-0) = 1
  simpa [hd] using hmon.coeff_natDegree

/-- The classification can be tested on actual pairs of complex roots. -/
theorem pairProductAffine_iff_root_pairs {m : ℕ} (p : MvPolynomial (Fin (m+1)) ℂ[X]) :
    PairProductAffine p ↔ ∀ (t : ℂ) (r : Multiset ℂ), r.card = m →
      ∃ α β : ℂ, ∀ x y : ℂ, x+y = t - complementaryCoefficient (rootCoefficients m r) 1 →
        MvPolynomial.eval (fun i => rootCoefficients m r i * (x*y) + pairBase t (rootCoefficients m r) i)
          (MvPolynomial.map (Polynomial.evalRingHom t) p) = β*(x*y) + α := by
  constructor
  · intro h t r hr
    obtain ⟨α, β, hab⟩ := h t _ (rootCoefficients_zero r hr)
    exact ⟨α, β, fun x y _ => hab (x*y)⟩
  · intro h t c hc
    obtain ⟨r, hr, he⟩ := exists_roots_of_complementary_coefficients c hc
    obtain ⟨α, β, hab⟩ := h t r hr
    rw [he] at hab
    refine ⟨α, β, fun q => ?_⟩
    let s := t - complementaryCoefficient c 1
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (s^2-4*q) (show 0 < 2 by decide)
    have hsum : (s+z)/2 + (s-z)/2 = s := by ring
    have hprod : ((s+z)/2) * ((s-z)/2) = q := by linear_combination -hz/4
    simpa only [hprod] using hab ((s+z)/2) ((s-z)/2) hsum

end

end MOC.RankOneAffineInvariants
