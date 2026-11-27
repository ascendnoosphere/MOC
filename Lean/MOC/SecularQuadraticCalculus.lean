import MOC.QuadraticSecularHarmonic
import MOC.SecularResidueCalculus

/-! The quadratic secular moment and its normalized first- and
second-derivative data. -/

open BigOperators Finset Filter
open scoped Topology

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private structure SecondDerivativeAt (f : ℝ → ℝ) (v w x : ℝ) : Prop where
  first : HasDerivAt f v x
  second : HasDerivAt (deriv f) w x
  near : ∀ᶠ t in 𝓝 x, DifferentiableAt ℝ f t

private theorem SecondDerivativeAt.add {f g : ℝ → ℝ} {v w y z x : ℝ}
    (hf : SecondDerivativeAt f v w x) (hg : SecondDerivativeAt g y z x) :
    SecondDerivativeAt (fun t => f t + g t) (v+y) (w+z) x := by
  refine ⟨hf.first.add hg.first, ?_, ?_⟩
  · apply (hf.second.add hg.second).congr_of_eventuallyEq
    filter_upwards [hf.near, hg.near] with t hft hgt using deriv_add hft hgt
  · filter_upwards [hf.near, hg.near] with t hft hgt using hft.add hgt

private theorem SecondDerivativeAt.sub {f g : ℝ → ℝ} {v w y z x : ℝ}
    (hf : SecondDerivativeAt f v w x) (hg : SecondDerivativeAt g y z x) :
    SecondDerivativeAt (fun t => f t - g t) (v-y) (w-z) x := by
  refine ⟨hf.first.sub hg.first, ?_, ?_⟩
  · apply (hf.second.sub hg.second).congr_of_eventuallyEq
    filter_upwards [hf.near, hg.near] with t hft hgt using deriv_sub hft hgt
  · filter_upwards [hf.near, hg.near] with t hft hgt using hft.sub hgt

private theorem SecondDerivativeAt.mul {f g : ℝ → ℝ} {v w y z x : ℝ}
    (hf : SecondDerivativeAt f v w x) (hg : SecondDerivativeAt g y z x) :
    SecondDerivativeAt (fun t => f t * g t)
      (v * g x + f x * y)
      (w * g x + 2 * v * y + f x * z) x := by
  refine ⟨hf.first.mul hg.first, ?_, ?_⟩
  · have h := (hf.second.mul hg.first).add (hf.first.mul hg.second)
    rw [hf.first.deriv, hg.first.deriv] at h
    have h' : HasDerivAt (fun t => deriv f t * g t + f t * deriv g t)
        (w * g x + 2 * v * y + f x * z) x := by
      convert h using 1
      ring
    apply h'.congr_of_eventuallyEq
    filter_upwards [hf.near, hg.near] with t hft hgt using deriv_mul hft hgt
  · filter_upwards [hf.near, hg.near] with t hft hgt using hft.mul hgt

private theorem SecondDerivativeAt.sum {κ : Type*} {s : Finset κ}
    {f : κ → ℝ → ℝ} {v w : κ → ℝ} {x : ℝ}
    (h : ∀ j ∈ s, SecondDerivativeAt (f j) (v j) (w j) x) :
    SecondDerivativeAt (fun t => ∑ j ∈ s, f j t) (∑ j ∈ s, v j) (∑ j ∈ s, w j) x := by
  have hnear : ∀ᶠ t in 𝓝 x, ∀ j ∈ s, DifferentiableAt ℝ (f j) t := by
    exact (Filter.eventually_all_finite (I := (s : Set κ)) s.finite_toSet).mpr
      (fun j hj => (h j hj).near)
  refine ⟨HasDerivAt.sum (fun j hj => (h j hj).first), ?_, ?_⟩
  · apply (HasDerivAt.sum (fun j hj => (h j hj).second)).congr_of_eventuallyEq
    filter_upwards [hnear] with t ht using deriv_sum ht
  · filter_upwards [hnear] with t ht using DifferentiableAt.sum ht

private theorem secondDerivativeAt_const (c x : ℝ) :
    SecondDerivativeAt (fun _ => c) 0 0 x := by
  refine ⟨hasDerivAt_const _ _, ?_, Eventually.of_forall fun _ => differentiableAt_const _⟩
  simpa only [deriv_const'] using (hasDerivAt_const x (0 : ℝ))

private theorem secondDerivativeAt_id (x : ℝ) :
    SecondDerivativeAt (fun t => t) 1 0 x := by
  refine ⟨hasDerivAt_id' _, ?_, Eventually.of_forall fun _ => differentiableAt_id⟩
  simpa only [deriv_id''] using (hasDerivAt_const x (1 : ℝ))

private theorem SecondDerivativeAt.const_mul {f : ℝ → ℝ} {v w x : ℝ}
    (hf : SecondDerivativeAt f v w x) (c : ℝ) :
    SecondDerivativeAt (fun t => c * f t) (c*v) (c*w) x := by
  simpa only [zero_mul, mul_zero, zero_add, add_zero] using (secondDerivativeAt_const c x).mul hf

/-- The determinant of the retained diagonal matrix shifted by a scalar. -/
def secularNodalMinor (d : ι → ℝ) (S : Finset ι) (z : ℝ) : ℝ :=
  ∏ j ∈ S, (d j-z)

omit [Fintype ι] in
private theorem secondDerivativeAt_secularNodalMinor (d : ι → ℝ)
    (S : Finset ι) (z : ℝ) (i : ι) :
    SecondDerivativeAt (fun t => secularNodalMinor (Function.update d i t) S z)
      (if i ∈ S then secularNodalMinor d (S.erase i) z else 0) 0 (d i) := by
  by_cases hi : i ∈ S
  · have he (t : ℝ) : secularNodalMinor (Function.update d i t) S z =
        secularNodalMinor d (S.erase i) z * (t-z) := by
      unfold secularNodalMinor
      rw [← prod_erase_mul S (fun j => Function.update d i t j-z) hi, Function.update_self]
      congr 1
      apply prod_congr rfl
      intro j hj
      rw [Function.update_of_ne (ne_of_mem_erase hj)]
    simp only [he, if_pos hi]
    simpa only [sub_zero, mul_one, mul_zero] using
      ((secondDerivativeAt_id (d i)).sub (secondDerivativeAt_const z (d i))).const_mul
        (secularNodalMinor d (S.erase i) z)
  · have he (t : ℝ) : secularNodalMinor (Function.update d i t) S z =
        secularNodalMinor d S z := by
      unfold secularNodalMinor
      apply prod_congr rfl
      intro j hj
      have hji : j ≠ i := fun he => hi (he ▸ hj)
      rw [Function.update_of_ne hji]
    simp only [he, if_neg hi]
    exact secondDerivativeAt_const _ _

private theorem secularLinearMinor_near_differentiable (h d : ι → ℝ)
    (hd : Function.Injective d) (S : Finset ι) (z : ℝ) (i : ι) :
    ∀ᶠ t in 𝓝 (d i), DifferentiableAt ℝ
      (fun s => secularLinearMinor h (Function.update d i s) S z) t := by
  filter_upwards [eventually_injective_single_coordinate_update d hd i] with t ht
  simpa only [Function.update_self, Function.update_idem] using
    (hasDerivAt_secularLinearMinor_update h (Function.update d i t) ht S z i).differentiableAt

private theorem secondDerivativeAt_secularLinearMinor
    (h d : ι → ℝ) (hd : Function.Injective d) (S : Finset ι) (z : ℝ) (i : ι) :
    SecondDerivativeAt (fun t => secularLinearMinor h (Function.update d i t) S z)
      (deriv (fun t => secularLinearMinor h (Function.update d i t) S z) (d i))
      (deriv (deriv (fun t => secularLinearMinor h (Function.update d i t) S z)) (d i)) (d i) := by
  refine ⟨(hasDerivAt_secularLinearMinor_update h d hd S z i).differentiableAt.hasDerivAt,
    (hasSecondDerivAt_secularLinearMinor_update h d hd S z i).differentiableAt.hasDerivAt,
    secularLinearMinor_near_differentiable h d hd S z i⟩

private theorem secondDerivativeAt_residue
    (h d : ι → ℝ) (hd : Function.Injective d) (i j : ι) :
    SecondDerivativeAt (fun t => secularResidue h (Function.update d i t) j)
      (deriv (fun t => secularResidue h (Function.update d i t) j) (d i))
      (deriv (deriv (fun t => secularResidue h (Function.update d i t) j)) (d i)) (d i) := by
  let r (t : ℝ) := secularResidue h (Function.update d i t) j
  let p (t : ℝ) := secularNodalMinor (Function.update d i t) {j} 0
  have he : (fun t => secularLinearMinor h (Function.update d i t) {j} 0 - p t) = r := by
    funext t
    simp [secularLinearMinor, p, secularNodalMinor, r]
  have hD := (secondDerivativeAt_secularLinearMinor h d hd {j} 0 i).sub
    (secondDerivativeAt_secularNodalMinor d {j} 0 i)
  rw [he] at hD
  change SecondDerivativeAt r (deriv r (d i)) (deriv (deriv r) (d i)) (d i)
  simpa only [hD.first.deriv, hD.second.deriv] using hD

private abbrev coordDeriv (f : (ι → ℝ) → ℝ) (d : ι → ℝ) (i : ι) : ℝ :=
  deriv (fun t => f (Function.update d i t)) (d i)

private abbrev coordSecond (f : (ι → ℝ) → ℝ) (d : ι → ℝ) (i : ι) : ℝ :=
  deriv (deriv (fun t => f (Function.update d i t))) (d i)

private theorem deletedResidueSum_deriv (h d : ι → ℝ)
    (hd : Function.Injective d) (S : Finset ι) (i : ι) :
    coordDeriv (fun p => ∑ j ∈ Sᶜ, secularResidue h p j) d i =
      if i ∈ S then -(∑ j ∈ Sᶜ, secularResidue h d j / (d i-d j))
      else -(1 + ∑ j ∈ S, secularResidue h d j / (d j-d i)) := by
  let r := secularResidue h d
  let R (j : ι) (t : ℝ) := secularResidue h (Function.update d i t) j
  let s (j : ι) := r j / (d j - d i)
  have H (j : ι) (hji : j ≠ i) : HasDerivAt (R j) (s j) (d i) :=
    hasDerivAt_secularResidue_update_of_ne h d (Ne.symm hji) (hd.ne (Ne.symm hji))
  change deriv (fun t => ∑ j ∈ Sᶜ, R j t) (d i) = _
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    have hp : HasDerivAt (fun t => ∑ j ∈ Sᶜ, R j t) (∑ j ∈ Sᶜ, s j) (d i) :=
      HasDerivAt.sum fun j hj => H j (fun he => (mem_compl.mp hj) (he ▸ hi))
    rw [hp.deriv, ← sum_neg_distrib]
    apply sum_congr rfl
    intro j _
    change r j / (d j-d i) = -(r j / (d i-d j))
    rw [← neg_sub (d j) (d i), div_neg, neg_neg]
  · rw [if_neg hi]
    have hi' : i ∈ Sᶜ := mem_compl.mpr hi
    have hsum : ∀ t : ℝ, (∑ j ∈ Sᶜ, R j t) =
        R i t + ∑ j ∈ (Sᶜ.erase i), R j t := by
      intro t
      rw [add_comm]
      exact (sum_erase_add _ _ hi').symm
    have hD := (hasDerivAt_secularResidue_update_self h d hd i).add
      (HasDerivAt.sum (u := Sᶜ.erase i) fun j hj => H j (ne_of_mem_erase hj))
    rw [show (fun t => ∑ j ∈ Sᶜ, R j t) =
      (fun t => R i t + ∑ j ∈ Sᶜ.erase i, R j t) from funext hsum, hD.deriv]
    have he : (∑ j ∈ univ.erase i, s j) =
        (∑ j ∈ S, s j) + ∑ j ∈ Sᶜ.erase i, s j := by
      have hu : S ∪ Sᶜ.erase i = univ.erase i := by
        ext j
        by_cases hj : j = i
        · subst j; simp [hi]
        · simp [hj, em (j ∈ S)]
      have hdis : Disjoint S (Sᶜ.erase i) := by
        rw [disjoint_left]
        exact fun j hj h' => (mem_compl.mp (mem_of_mem_erase h')) hj
      rw [← hu, sum_union hdis]
    change -1 - (∑ j ∈ univ.erase i, s j) + (∑ j ∈ Sᶜ.erase i, s j) =
      -(1 + ∑ j ∈ S, s j)
    rw [he]
    ring

private theorem residue_sum_weighted_second (h d : ι → ℝ)
    (hd : Function.Injective d) (S : Finset ι) :
    ∑ i, secularResidue h d i *
      coordSecond (fun p => ∑ j ∈ S, secularResidue h p j) d i = 0 := by
  have hR (i j : ι) : coordSecond (fun p => secularResidue h p j) d i =
      coordSecond (fun p => secularLinearMinor h p {j} 0) d i := by
    let r (t : ℝ) := secularResidue h (Function.update d i t) j
    let p (t : ℝ) := secularNodalMinor (Function.update d i t) {j} 0
    have he : (fun t => secularLinearMinor h (Function.update d i t) {j} 0 - p t) = r := by
      funext t
      simp [secularLinearMinor, p, secularNodalMinor, r]
    have hD := (secondDerivativeAt_secularLinearMinor h d hd {j} 0 i).sub
      (secondDerivativeAt_secularNodalMinor d {j} 0 i)
    rw [he] at hD
    exact hD.second.deriv.trans (sub_zero _)
  have hS (i : ι) : coordSecond (fun p => ∑ j ∈ S, secularResidue h p j) d i =
      ∑ j ∈ S, coordSecond (fun p => secularResidue h p j) d i := by
    exact (SecondDerivativeAt.sum (s := S) fun j _ => secondDerivativeAt_residue h d hd i j).second.deriv
  simp_rw [hS, hR, mul_sum]
  rw [sum_comm]
  exact sum_eq_zero fun j _ => secularLinearMinor_weighted_second_sum h d hd {j} 0

private theorem secularLinearMinor_factor (h d : ι → ℝ) (S : Finset ι) (z : ℝ)
    (hz : ∀ i, d i ≠ z) :
    secularLinearMinor h d S z = secularNodalMinor d S z *
      (1 + ∑ j ∈ S, secularResidue h d j * (d j-z)⁻¹) := by
  unfold secularLinearMinor
  rw [mul_add, mul_one, mul_sum]
  congr 1
  apply sum_congr rfl
  intro j hj
  unfold secularNodalMinor
  rw [← prod_erase_mul S _ hj]
  field_simp [sub_ne_zero.mpr (hz j)]
  ring

omit [Fintype ι] in
private theorem nodalMinor_update_gradient (d : ι → ℝ) (S : Finset ι) (z : ℝ)
    (hz : ∀ i, d i ≠ z) (i : ι) :
    coordDeriv (fun p => secularNodalMinor p S z) d i =
      if i ∈ S then secularNodalMinor d S z * (d i-z)⁻¹ else 0 := by
  rw [coordDeriv, (secondDerivativeAt_secularNodalMinor d S z i).first.deriv]
  by_cases hi : i ∈ S
  · rw [if_pos hi, if_pos hi]
    unfold secularNodalMinor
    rw [← prod_erase_mul S _ hi, mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr (hz i)), mul_one]
  · rw [if_neg hi, if_neg hi]

private theorem linearMinor_update_gradient (h d : ι → ℝ) (hd : Function.Injective d)
    (S : Finset ι) (z : ℝ) (hz : ∀ i, d i ≠ z) (i : ι) :
    coordDeriv (fun p => secularLinearMinor h p S z) d i = secularNodalMinor d S z *
      (if i ∈ S then
        (∑ j ∈ Sᶜ, secularResidue h d j / (d i-d j)) * (d i-z)⁻¹
       else ∑ j ∈ S, secularResidue h d j * (d j-z)⁻¹ / (d j-d i)) := by
  have hfactor (j : ι) (hj : j ∈ S) :
      secularNodalMinor d (S.erase j) z = secularNodalMinor d S z * (d j-z)⁻¹ := by
    unfold secularNodalMinor
    rw [← prod_erase_mul S _ hj, mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr (hz j)), mul_one]
  rw [coordDeriv, (hasDerivAt_secularLinearMinor_update h d hd S z i).deriv]
  by_cases hi : i ∈ S
  · rw [if_pos hi, if_pos hi]
    change secularNodalMinor d (S.erase i) z * _ = _
    rw [hfactor i hi]
    ring
  · rw [if_neg hi, if_neg hi, mul_sum]
    apply sum_congr rfl
    intro j hj
    change _ * secularNodalMinor d (S.erase j) z = _
    rw [hfactor j hj]
    ring

/-- The reduced quadratic moment, for the two scalar roots `t` and `u`
of the quadratic polynomial. -/
def secularQuadraticMinor (h d : ι → ℝ) (S : Finset ι) (t u : ℝ) : ℝ :=
  secularLinearMinor h d S t * secularLinearMinor h d S u +
    (∑ j ∈ Sᶜ, secularResidue h d j) *
      (secularNodalMinor d S u * secularLinearMinor h d S t -
        secularNodalMinor d S t * secularLinearMinor h d S u) / (t-u)

private theorem normalized_secular_gradient_sum_cancel (d r : ι → ℝ) (S : Finset ι)
    (hd : Function.Injective d) (t u : ℝ)
    (ht : ∀ i, d i ≠ t) (hu : ∀ i, d i ≠ u) :
    let X (v : ℝ) (i : ι) := (d i-v)⁻¹
    let A (i : ι) := ∑ j ∈ Sᶜ, r j / (d i-d j)
    let L (v : ℝ) := 1 + ∑ i ∈ S, r i * X v i
    let Y (v : ℝ) (j : ι) := ∑ i ∈ S, r i * X v i / (d i-d j)
    let C (j : ι) := 1 + ∑ i ∈ S, r i / (d i-d j)
    (∑ i, r i * (if i ∈ S then
      (t-u) * (A i)^2 * (X t i * X u i) -
        A i * (X u i * L t - X t i * L u + A i * (X t i - X u i))
      else (t-u) * (Y t i * Y u i) - C i * (Y t i - Y u i))) = 0 := by
  intro X A L Y C
  have hde (i : S) (j : (Sᶜ : Finset ι)) : d i ≠ d j := by
    apply hd.ne
    intro hij
    exact (mem_compl.mp j.property) (hij ▸ i.property)
  have hc := secular_quadratic_product_rule_cancel
    (fun i : S => d i) (fun i : S => r i)
    (fun j : (Sᶜ : Finset ι) => d j) (fun j : (Sᶜ : Finset ι) => r j) t u hde
    (fun i => ht i) (fun i => hu i) (fun j => ht j) (fun j => hu j)
  let A' (i : ι) := ∑ j : (Sᶜ : Finset ι), r j / (d i-d j)
  let L' (v : ℝ) := 1 + ∑ i : S, r i * X v i
  let Y' (v : ℝ) (j : ι) := ∑ i : S, r i * X v i / (d i-d j)
  let C' (j : ι) := 1 + ∑ i : S, r i / (d i-d j)
  have hA' (i : ι) : A' i = A i :=
    Finset.sum_coe_sort (Sᶜ : Finset ι) (fun j => r j / (d i-d j))
  have hL' (v : ℝ) : L' v = L v :=
    congrArg (fun x : ℝ => 1+x) (Finset.sum_coe_sort S (fun i => r i * X v i))
  have hY' (v : ℝ) (j : ι) : Y' v j = Y v j :=
    Finset.sum_coe_sort S (fun i => r i * X v i / (d i-d j))
  have hC' (j : ι) : C' j = C j :=
    congrArg (fun x : ℝ => 1+x) (Finset.sum_coe_sort S (fun i => r i / (d i-d j)))
  let leftTerm (i : ι) := r i * ((t-u) * A i ^ 2 * (X t i * X u i) -
    A i * (X u i * L t - X t i * L u + A i * (X t i - X u i)))
  let rightTerm (i : ι) := r i * ((t-u) * (Y t i * Y u i) - C i * (Y t i - Y u i))
  change (∑ i : S, r i * ((t-u) * A' i ^ 2 * (X t i * X u i) -
    A' i * (X u i * L' t - X t i * L' u + A' i * (X t i - X u i)))) +
    (∑ i : (Sᶜ : Finset ι), r i * ((t-u) * (Y' t i * Y' u i) -
      C' i * (Y' t i - Y' u i))) = 0 at hc
  simp only [hA', hL', hY', hC'] at hc
  change (∑ i : S, leftTerm i) + (∑ i : (Sᶜ : Finset ι), rightTerm i) = 0 at hc
  rw [Finset.sum_coe_sort S leftTerm, Finset.sum_coe_sort (Sᶜ : Finset ι) rightTerm] at hc
  rw [← sum_add_sum_compl S]
  have hs : (∑ i ∈ S, r i * (if i ∈ S then
      (t-u) * A i ^ 2 * (X t i * X u i) -
        A i * (X u i * L t - X t i * L u + A i * (X t i - X u i))
      else (t-u) * (Y t i * Y u i) - C i * (Y t i - Y u i))) =
      ∑ i ∈ S, r i * ((t-u) * A i ^ 2 * (X t i * X u i) -
        A i * (X u i * L t - X t i * L u + A i * (X t i - X u i))) :=
    sum_congr rfl fun i hi => by rw [if_pos hi]
  have hS : (∑ i ∈ Sᶜ, r i * (if i ∈ S then
      (t-u) * A i ^ 2 * (X t i * X u i) -
        A i * (X u i * L t - X t i * L u + A i * (X t i - X u i))
      else (t-u) * (Y t i * Y u i) - C i * (Y t i - Y u i))) =
      ∑ i ∈ Sᶜ, r i * ((t-u) * (Y t i * Y u i) - C i * (Y t i - Y u i)) :=
    sum_congr rfl fun i hi => by rw [if_neg (mem_compl.mp hi)]
  rw [hs, hS]
  exact hc

/-- The secular moment of the quadratic image has zero weighted sum of
pure second derivatives. -/
theorem secularQuadraticMinor_weighted_second_sum (h d : ι → ℝ)
    (hd : Function.Injective d) (S : Finset ι) (t u : ℝ) (htu : t ≠ u)
    (ht : ∀ i, d i ≠ t) (hu : ∀ i, d i ≠ u) :
    (∑ i, secularResidue h d i *
      coordSecond (fun p => secularQuadraticMinor h p S t u) d i) = 0 := by
  let f (z : ℝ) (p : ι → ℝ) := secularLinearMinor h p S z
  let p (z : ℝ) (x : ι → ℝ) := secularNodalMinor x S z
  let q (x : ι → ℝ) := ∑ j ∈ Sᶜ, secularResidue h x j
  let r := secularResidue h d
  let δ := t-u
  let g (x : ι → ℝ) := p u x * f t x - p t x * f u x
  let G (i : ι) :=
    coordDeriv (p u) d i * f t d + p u d * coordDeriv (f t) d i -
      (coordDeriv (p t) d i * f u d + p t d * coordDeriv (f u) d i)
  let W : (ι → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun v => ∑ i, r i * v i
      map_add' := fun a b => by
        simp only [Pi.add_apply, mul_add, sum_add_distrib]
      map_smul' := fun c a => by
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, mul_left_comm (r _), ← mul_sum] }
  have hF (z : ℝ) (i : ι) :
      SecondDerivativeAt (fun s => f z (Function.update d i s))
        (coordDeriv (f z) d i) (coordSecond (f z) d i) (d i) :=
    secondDerivativeAt_secularLinearMinor h d hd S z i
  have hP (z : ℝ) (i : ι) :
      SecondDerivativeAt (fun s => p z (Function.update d i s)) (coordDeriv (p z) d i) 0 (d i) := by
    have h' := secondDerivativeAt_secularNodalMinor d S z i
    simpa only [p, h'.first.deriv] using h'
  have hQ (i : ι) : SecondDerivativeAt (fun s => q (Function.update d i s))
      (coordDeriv q d i) (coordSecond q d i) (d i) := by
    have h' := SecondDerivativeAt.sum (s := Sᶜ) fun j _ => secondDerivativeAt_residue h d hd i j
    simpa only [q, h'.first.deriv, h'.second.deriv] using h'
  have hcross (i : ι) :
      coordDeriv (p u) d i * coordDeriv (f t) d i =
        coordDeriv (p t) d i * coordDeriv (f u) d i := by
    simp only [p, f, nodalMinor_update_gradient d S u hu i, nodalMinor_update_gradient d S t ht i,
      linearMinor_update_gradient h d hd S t ht i, linearMinor_update_gradient h d hd S u hu i]
    by_cases hi : i ∈ S
    · simp only [if_pos hi]
      ring
    · simp only [if_neg hi, zero_mul]
  have hG (i : ι) : SecondDerivativeAt (fun s => g (Function.update d i s)) (G i)
      (p u d * coordSecond (f t) d i - p t d * coordSecond (f u) d i) (d i) := by
    have h' := ((hP u i).mul (hF t i)).sub ((hP t i).mul (hF u i))
    simp only [Function.update_eq_self, zero_mul, zero_add] at h'
    have he :
        (2 * coordDeriv (p u) d i * coordDeriv (f t) d i + p u d * coordSecond (f t) d i) -
          (2 * coordDeriv (p t) d i * coordDeriv (f u) d i + p t d * coordSecond (f u) d i) =
        p u d * coordSecond (f t) d i - p t d * coordSecond (f u) d i := by
      linear_combination 2 * hcross i
    rw [he] at h'
    exact h'
  have hpure (i : ι) :
      coordSecond (fun x => secularQuadraticMinor h x S t u) d i =
        f u d * coordSecond (f t) d i +
        f t d * coordSecond (f u) d i +
        (g d * coordSecond q d i +
          (q d * p u d) * coordSecond (f t) d i -
          (q d * p t d) * coordSecond (f u) d i) * δ⁻¹ +
        2 * (coordDeriv (f t) d i * coordDeriv (f u) d i +
          δ⁻¹ * (coordDeriv q d i * G i)) := by
    have h' := ((hF t i).mul (hF u i)).add (((hQ i).mul (hG i)).const_mul δ⁻¹)
    simp only [Function.update_eq_self] at h'
    have he : (fun x => secularQuadraticMinor h (Function.update d i x) S t u) =
        (fun x => f t (Function.update d i x) * f u (Function.update d i x) +
          δ⁻¹ * (q (Function.update d i x) * g (Function.update d i x))) := by
      funext x
      simp only [secularQuadraticMinor, p, f, q, g, δ, div_eq_mul_inv]
      ring
    rw [coordSecond, he, h'.second.deriv]
    ring
  have hFt : W (fun i => coordSecond (f t) d i) = 0 :=
    secularLinearMinor_weighted_second_sum h d hd S t
  have hFu : W (fun i => coordSecond (f u) d i) = 0 :=
    secularLinearMinor_weighted_second_sum h d hd S u
  have hq : W (fun i => coordSecond q d i) = 0 := residue_sum_weighted_second h d hd Sᶜ
  let E (i : ι) := coordDeriv (f t) d i * coordDeriv (f u) d i +
    δ⁻¹ * (coordDeriv q d i * G i)
  have hWeighted : W (fun i => coordSecond (fun x => secularQuadraticMinor h x S t u) d i) =
      2 * W E := by
    have hEq : (fun i => coordSecond (fun x => secularQuadraticMinor h x S t u) d i) =
        (f u d) • (fun i => coordSecond (f t) d i) +
        (f t d) • (fun i => coordSecond (f u) d i) +
        δ⁻¹ • ((g d) • (fun i => coordSecond q d i) +
          (q d * p u d) • (fun i => coordSecond (f t) d i) -
          (q d * p t d) • (fun i => coordSecond (f u) d i)) + (2 : ℝ) • E := by
      funext i
      simp only [hpure i, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, E]
      ring
    simp only [hEq, map_add, map_sub, map_smul, hFt, hFu, hq,
      smul_eq_mul, mul_zero, zero_add, sub_zero]
  let X (v : ℝ) (i : ι) := (d i-v)⁻¹
  let A (i : ι) := ∑ j ∈ Sᶜ, r j / (d i-d j)
  let L (v : ℝ) := 1 + ∑ i ∈ S, r i * X v i
  let Y (v : ℝ) (j : ι) := ∑ i ∈ S, r i * X v i / (d i-d j)
  let C (j : ι) := 1 + ∑ i ∈ S, r i / (d i-d j)
  let Z (i : ι) := if i ∈ S then
      δ * A i ^ 2 * (X t i * X u i) -
        A i * (X u i * L t - X t i * L u + A i * (X t i - X u i))
    else δ * (Y t i * Y u i) - C i * (Y t i - Y u i)
  have hZ : W Z = 0 := normalized_secular_gradient_sum_cancel d r S hd t u ht hu
  have hPt : ∀ i, coordDeriv (p t) d i = if i ∈ S then p t d * X t i else 0 :=
    nodalMinor_update_gradient d S t ht
  have hPu : ∀ i, coordDeriv (p u) d i = if i ∈ S then p u d * X u i else 0 :=
    nodalMinor_update_gradient d S u hu
  have hDt : ∀ i, coordDeriv (f t) d i = p t d *
      (if i ∈ S then A i * X t i else Y t i) :=
    linearMinor_update_gradient h d hd S t ht
  have hDu : ∀ i, coordDeriv (f u) d i = p u d *
      (if i ∈ S then A i * X u i else Y u i) :=
    linearMinor_update_gradient h d hd S u hu
  have hDq : ∀ i, coordDeriv q d i = if i ∈ S then -A i else -C i :=
    deletedResidueSum_deriv h d hd S
  have hft : f t d = p t d * L t := secularLinearMinor_factor h d S t ht
  have hfu : f u d = p u d * L u := secularLinearMinor_factor h d S u hu
  have hnz : δ ≠ 0 := sub_ne_zero.mpr htu
  have hE : E = (p t d * p u d * δ⁻¹) • Z := by
    funext i
    simp only [E, G, Z, hPt, hPu, hDt, hDu, hDq, hft, hfu, Pi.smul_apply, smul_eq_mul]
    by_cases hi : i ∈ S
    · simp only [if_pos hi]
      field_simp [hnz]
      ring
    · simp only [if_neg hi, zero_mul, zero_add]
      field_simp [hnz]
      ring
  change W (fun i => coordSecond (fun p => secularQuadraticMinor h p S t u) d i) = 0
  rw [hWeighted, hE, map_smul, hZ]
  simp

private theorem secondDerivativeAt_secularQuadraticMinor
    (h d : ι → ℝ) (hd : Function.Injective d) (S : Finset ι) (t u : ℝ) (i : ι) :
    let f (x : ℝ) := secularQuadraticMinor h (Function.update d i x) S t u
    SecondDerivativeAt f (deriv f (d i)) (deriv (deriv f) (d i)) (d i) := by
  intro f
  have hF (z : ℝ) := secondDerivativeAt_secularLinearMinor h d hd S z i
  have hP (z : ℝ) := secondDerivativeAt_secularNodalMinor d S z i
  have hQ := SecondDerivativeAt.sum (s := Sᶜ) fun j _ => secondDerivativeAt_residue h d hd i j
  have hG := ((hP u).mul (hF t)).sub ((hP t).mul (hF u))
  have hD := ((hF t).mul (hF u)).add ((hQ.mul hG).const_mul (t-u)⁻¹)
  have hf : (fun x => secularLinearMinor h (Function.update d i x) S t *
      secularLinearMinor h (Function.update d i x) S u +
      (t-u)⁻¹ * ((∑ j ∈ Sᶜ, secularResidue h (Function.update d i x) j) *
        (secularNodalMinor (Function.update d i x) S u * secularLinearMinor h (Function.update d i x) S t -
         secularNodalMinor (Function.update d i x) S t * secularLinearMinor h (Function.update d i x) S u))) =
      f := by
    funext x
    simp only [f, secularQuadraticMinor, div_eq_mul_inv]
    ring
  rw [hf] at hD
  simpa only [hD.first.deriv, hD.second.deriv] using hD

/-- A real linear combination of quadratic principal moments has
the derivative regularity and weighted harmonicity of each moment. -/
theorem secularQuadraticMinor_weighted_linear_combination
    (h d : ι → ℝ) (hd : Function.Injective d) (t u : ℝ) (htu : t ≠ u)
    (ht : ∀ i, d i ≠ t) (hu : ∀ i, d i ≠ u) (w : Finset ι → ℝ) :
    let F (p : ι → ℝ) := ∑ S : Finset ι, w S * secularQuadraticMinor h p S t u
    (∀ i, ∀ᶠ x in 𝓝 (d i), DifferentiableAt ℝ (fun y => F (Function.update d i y)) x) ∧
    (∀ i, DifferentiableAt ℝ (deriv (fun y => F (Function.update d i y))) (d i)) ∧
    (∑ i, secularResidue h d i * deriv (deriv (fun y => F (Function.update d i y))) (d i)) = 0 := by
  intro F
  have hF (i : ι) :
      SecondDerivativeAt (fun y => F (Function.update d i y))
        (∑ S : Finset ι, w S * coordDeriv (fun p => secularQuadraticMinor h p S t u) d i)
        (∑ S : Finset ι, w S * coordSecond (fun p => secularQuadraticMinor h p S t u) d i) (d i) :=
    SecondDerivativeAt.sum fun S _ => (secondDerivativeAt_secularQuadraticMinor h d hd S t u i).const_mul (w S)
  refine ⟨fun i => (hF i).near, fun i => (hF i).second.differentiableAt, ?_⟩
  simp_rw [(hF _).second.deriv, mul_sum, mul_left_comm (secularResidue h d _) (w _)]
  rw [sum_comm]
  simp only [← mul_sum, secularQuadraticMinor_weighted_second_sum h d hd _ t u htu ht hu,
    mul_zero, sum_const_zero]

end

end MOC
