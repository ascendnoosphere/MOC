import MOC.AffineCurveLocalOpen
import MOC.GapFreeContactFibre

/-! Infinitesimal contact-offset control at the sharp count.
The finite-curve strategy starts from Zheng, DOI: 10.13140/RG.2.2.36790.25923. -/

open Matrix MvPolynomial Set Filter
open scoped Topology

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- At the minimal terminal count, all sufficiently small real steps
along a prescribed imaginary contact direction are realized by strict
witnesses with exactly the same contacts, mixer, direction, and pivot. -/
theorem StrictMatchingSupport.realize_small_imaginary_contact_shifts_of_sharp_count
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (hmax : ∀ v : StrictMatchingSupport U, v.contacts.card ≤ w.contacts.card)
    (hcard : w.contacts.card ≤ 2 * Fintype.card ι - 1)
    (u : Equiv.Perm ι → ℝ) (hur : u w.pivot = 0)
    (q₀ : Equiv.Perm ι) (hq₀ : q₀ ∈ w.contacts) (hu₀ : u q₀ ≠ 0)
    {N : Set (Equiv.Perm ι → ℂ)} (hN : N ∈ 𝓝 (matchingProduct w.a w.b)) :
    ∀ᶠ τ : ℝ in 𝓝 0, ∃ v : StrictMatchingSupport U,
      v.η = w.η ∧ v.pivot = w.pivot ∧ v.contacts = w.contacts ∧
      matchingProduct v.a v.b ∈ N ∧
      ∀ q ∈ w.contacts, w.η * (matchingProduct v.a v.b w.pivot - matchingProduct v.a v.b q) =
        w.η * (matchingProduct w.a w.b w.pivot - matchingProduct w.a w.b q) +
        (u q : ℂ) * Complex.I * (τ : ℂ) := by
  classical
  let p := matchingProduct w.a w.b
  let R (q : Equiv.Perm ι) : ProfileRing ι := C w.η * (X w.pivot - X q)
  let d (q : Equiv.Perm ι) : ℂ := (u q : ℂ) * Complex.I
  let D (q : Equiv.Perm ι) : ProfileRing ι := R q - C (eval p (R q))
  let g : ProfileRing ι := C ((d q₀)⁻¹) * D q₀
  let pin (q : Equiv.Perm ι) : ProfileRing ι := D q - C (d q) * g
  let J := (w.contacts.erase w.pivot).erase q₀
  let E := J.image pin
  have hd₀ : d q₀ ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hu₀) Complex.I_ne_zero
  have hqr : q₀ ≠ w.pivot := fun h => hu₀ (h ▸ hur)
  have hpiv : w.pivot ∈ w.contacts := by simp [StrictMatchingSupport.contacts]
  have hqerase : q₀ ∈ w.contacts.erase w.pivot := Finset.mem_erase.mpr ⟨hqr,hq₀⟩
  have hE : E.card < 2 * Fintype.card ι - 2 := by
    have h := Finset.card_image_le (f := pin) (s := J)
    change E.card ≤ (J.card) at h
    dsimp only [J] at h
    rw [Finset.card_erase_of_mem hqerase, Finset.card_erase_of_mem hpiv] at h
    have hpos := Finset.card_pos.mpr ⟨q₀,hqerase⟩
    rw [Finset.card_erase_of_mem hpiv] at hpos
    omega
  have hp : p ∈ zeroLocus (profileIdeal ι) := (profileIdeal_exact (ι := ι)) ▸ ⟨w.a,w.b,rfl⟩
  obtain ⟨Q,hIQ,hQz,hQ,hpin,F,hF,hFi,t,ht⟩ :=
    exists_prime_profile_curve_fixing_observables p hp E hE
  letI : Q.IsPrime := hQ
  let x₀ : zeroLocus Q := ⟨p,hQz⟩
  have heval (y : Equiv.Perm ι → ℂ) (q : Equiv.Perm ι) :
      eval y (R q) = w.η * (y w.pivot - y q) := by
    simp only [R, map_mul, eval_C, map_sub, eval_X]
  have hg₀ : eval p g = 0 := by simp [g,D]
  have hpin₀ (q : Equiv.Perm ι) : eval p (pin q) = 0 := by simp [pin, D, hg₀]
  have hline (y : zeroLocus Q) (q : Equiv.Perm ι) (hq : q ∈ w.contacts) :
      eval y.val (R q) = eval p (R q) + d q * eval y.val g := by
    by_cases hpq : q = w.pivot
    · subst q
      simp [heval, d, hur]
    by_cases hqq₀ : q = q₀
    · subst q
      have hval : eval y.val g = (d q₀)⁻¹ * (eval y.val (R q₀) - eval p (R q₀)) := by
        simp only [g,D,map_mul,eval_C,map_sub]
      rw [hval, ← mul_assoc, mul_inv_cancel₀ hd₀, one_mul]
      ring
    have hJ : q ∈ J := by simp [J, hq, hpq, hqq₀]
    have hqpin := hpin y (pin q) (Finset.mem_image_of_mem pin hJ)
    rw [hpin₀] at hqpin
    simp only [pin,D,map_sub,map_mul,eval_C] at hqpin
    linear_combination hqpin
  have hexact (y : zeroLocus Q) : ∃ a b : ι → ℂ, matchingProduct a b = y.val := by
    have hy : y.val ∈ zeroLocus (profileIdeal ι) := fun q hq => y.property q (hIQ hq)
    rwa [← profileIdeal_exact] at hy
  have hη : w.η ≠ 0 := fun h => by simpa [h] using w.strict
  have hvar : ∃ x y : zeroLocus Q, eval x.val g ≠ eval y.val g := by
    by_contra! h
    have hconst (y : zeroLocus Q) : eval y.val g = 0 := (h y x₀).trans hg₀
    have hold (y : zeroLocus Q) (q : Equiv.Perm ι) (hq : q ∈ w.contacts) :
        y.val w.pivot - y.val q = x₀.val w.pivot - x₀.val q := by
      have hEq := hline y q hq
      rw [hconst y, mul_zero, add_zero, heval, heval] at hEq
      exact mul_left_cancel₀ hη hEq
    obtain ⟨v,_,_,hv,_⟩ :=
      w.exists_more_contacts_on_affine_difference_curve hU Q F hF hFi t ht x₀ rfl hexact hold
    exact (not_lt_of_ge (hmax v)) (Finset.card_lt_card hv)
  let G (y : zeroLocus Q) := (matchingProfileDetGap U w.η w.pivot y.val).re
  let P (q : Equiv.Perm ι) (y : zeroLocus Q) := (eval y.val (R q)).re
  let A : Set (zeroLocus Q) :=
    {y | y.val ∈ N ∧ 0 < G y ∧ ∀ q ∉ w.contacts, 0 < P q y}
  have hGcont : Continuous G := by
    unfold G matchingProfileDetGap
    apply Complex.continuous_re.comp
    apply continuous_finset_sum _
    intro q _
    exact continuous_const.mul (continuous_const.mul
      (((continuous_apply q).comp continuous_subtype_val).sub
        ((continuous_apply w.pivot).comp continuous_subtype_val)))
  have hGpos : 0 < G x₀ := by
    dsimp only [G,x₀,p]
    rw [matchingProfileDetGap_matchingProduct _ _ _ hU, mul_sub, Complex.sub_re]
    exact sub_pos.mpr w.strict
  have hPcont (q : Equiv.Perm ι) : Continuous (P q) :=
    Complex.continuous_re.comp ((R q).continuous_eval.comp continuous_subtype_val)
  have hPpos (q : Equiv.Perm ι) (hq : q ∉ w.contacts) : 0 < P q x₀ := by
    unfold P
    rw [heval, mul_sub, Complex.sub_re]
    apply sub_pos.mpr
    apply lt_of_le_of_ne (w.maximal q)
    intro he
    exact hq (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
  have hA : A ∈ 𝓝 x₀ := by
    have hN' := continuous_subtype_val.continuousAt.eventually_mem (x := x₀) hN
    have hG' : ∀ᶠ y in 𝓝 x₀, 0 < G y := hGcont.continuousAt.eventually_mem (Ioi_mem_nhds hGpos)
    have hP' : ∀ᶠ y in 𝓝 x₀, ∀ q ∉ w.contacts, 0 < P q y := by
      rw [Filter.eventually_all]
      intro q
      by_cases hq : q ∈ w.contacts
      · exact Filter.Eventually.of_forall fun _ h => False.elim (h hq)
      · exact ((hPcont q).continuousAt.eventually_mem (Ioi_mem_nhds (hPpos q hq))).mono
          fun y hy _ => hy
    exact hN'.and (hG'.and hP')
  have himg := affine_curve_varying_coordinate_mem_nhds_image Q F hF hFi t g ht hvar x₀ hA
  rw [show eval x₀.val g = 0 from hg₀] at himg
  have hreal : ∀ᶠ τ : ℝ in 𝓝 0, (τ : ℂ) ∈
      (fun y : zeroLocus Q => eval y.val g) '' A :=
    Complex.continuous_ofReal.continuousAt.eventually_mem (by simpa using himg)
  filter_upwards [hreal] with τ hτ
  obtain ⟨y,⟨hyN,hyG,hyP⟩,hyτ⟩ := hτ
  obtain ⟨a,b,hab⟩ := hexact y
  change eval y.val g = (τ : ℂ) at hyτ
  have hRe (q : Equiv.Perm ι) (hq : q ∈ w.contacts) : P q y = 0 := by
    unfold P
    rw [hline y q hq,hyτ, Complex.add_re, heval, mul_sub, Complex.sub_re]
    dsimp only [p]
    rw [(Finset.mem_filter.mp hq).2]
    simp [d, Complex.mul_re, Complex.mul_im]
  have hproj (q : Equiv.Perm ι) : P q y =
      (w.η * matchingProduct a b w.pivot).re -
        (w.η * matchingProduct a b q).re := by
    unfold P
    rw [heval, ← hab, mul_sub, Complex.sub_re]
  have hmax' (q : Equiv.Perm ι) :
      (w.η * matchingProduct a b q).re ≤ (w.η * matchingProduct a b w.pivot).re := by
    apply sub_nonneg.mp
    rw [← hproj]
    by_cases hq : q ∈ w.contacts
    · exact (hRe q hq).ge
    · exact (hyP q hq).le
  have hstrict : (w.η * matchingProduct a b w.pivot).re < (w.η * determinantValue a b U).re := by
    dsimp only [G] at hyG
    rwa [← hab, matchingProfileDetGap_matchingProduct _ _ _ hU, mul_sub,
      Complex.sub_re, sub_pos] at hyG
  let v : StrictMatchingSupport U := ⟨a,b,w.η,w.pivot,hmax',hstrict⟩
  refine ⟨v,rfl,rfl,?_,hab.symm ▸ hyN,?_⟩
  · ext q
    constructor
    · intro hvq
      by_cases hwq : q ∈ w.contacts
      · exact hwq
      · have hh := hyP q hwq
        have hx : (w.η * matchingProduct a b q).re =
            (w.η * matchingProduct a b w.pivot).re := (Finset.mem_filter.mp hvq).2
        rw [hproj, hx, sub_self] at hh
        exact (lt_irrefl _ hh).elim
    · intro hq
      have hh := hRe q hq
      rw [hproj, sub_eq_zero] at hh
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh.symm⟩
  · intro q hq
    have he := hline y q hq
    rw [hyτ,heval,heval,← hab] at he
    exact he

/-- Collision-freeness of active complex products may be imposed at the
sharp count, without claiming it at the starting witness. -/
theorem StrictMatchingSupport.exists_distinct_active_products_of_sharp_count
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (hmax : ∀ v : StrictMatchingSupport U, v.contacts.card ≤ w.contacts.card)
    (hcard : w.contacts.card ≤ 2 * Fintype.card ι - 1)
    (hpos : 1 < w.contacts.card)
    {N : Set (Equiv.Perm ι → ℂ)} (hN : N ∈ 𝓝 (matchingProduct w.a w.b)) :
    ∃ v : StrictMatchingSupport U, v.η = w.η ∧ v.pivot = w.pivot ∧
      v.contacts = w.contacts ∧ matchingProduct v.a v.b ∈ N ∧
      Set.InjOn (matchingProduct v.a v.b) (w.contacts : Set (Equiv.Perm ι)) := by
  classical
  have hp : w.pivot ∈ w.contacts := by simp [StrictMatchingSupport.contacts]
  have hother : 0 < (w.contacts.erase w.pivot).card := by
    rw [Finset.card_erase_of_mem hp]
    omega
  obtain ⟨q₀,hq⟩ := Finset.card_pos.mp hother
  obtain ⟨hqr,hq₀⟩ := Finset.mem_erase.mp hq
  let e := Fintype.equivFin (Equiv.Perm ι)
  let u (q : Equiv.Perm ι) : ℝ := ((e q).val : ℝ) - ((e w.pivot).val : ℝ)
  have hur : u w.pivot = 0 := sub_self _
  have hu : Function.Injective u := by
    intro i j h
    apply e.injective
    apply Fin.val_injective
    exact Nat.cast_inj.mp (sub_left_inj.mp h)
  obtain hshift := w.realize_small_imaginary_contact_shifts_of_sharp_count
    hU hmax hcard u hur q₀ hq₀ (fun h => hqr (hu (h.trans hur.symm))) hN
  let f (q : Equiv.Perm ι) (τ : ℝ) : ℂ :=
    w.η * (matchingProduct w.a w.b w.pivot - matchingProduct w.a w.b q) +
      (u q : ℂ) * Complex.I * (τ : ℂ)
  have hδ : ∀ᶠ τ : ℝ in 𝓝 0, ∀ i j, f i 0 ≠ f j 0 → f i τ ≠ f j τ := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    by_cases hij : f i 0 = f j 0
    · exact Eventually.of_forall fun _ h => (h hij).elim
    · have hc : Continuous (fun τ => f i τ - f j τ) := by dsimp [f]; fun_prop
      exact (hc.continuousAt.eventually_ne (sub_ne_zero.mpr hij)).mono
        (fun τ h _ => sub_ne_zero.mp h)
  have hτ : ∃ τ : ℝ, ((∃ v : StrictMatchingSupport U, v.η = w.η ∧
      v.pivot = w.pivot ∧ v.contacts = w.contacts ∧ matchingProduct v.a v.b ∈ N ∧
      ∀ q ∈ w.contacts, w.η * (matchingProduct v.a v.b w.pivot -
        matchingProduct v.a v.b q) = f q τ) ∧
      (∀ i j, f i 0 ≠ f j 0 → f i τ ≠ f j τ)) ∧ τ ≠ 0 := by
    exact (mem_closure_iff_nhds.mp ((dense_compl_singleton (0 : ℝ)) 0) _
      (hshift.and hδ))
  obtain ⟨τ,⟨⟨v,hη,hp',hS,hNv,hmove⟩,hne⟩,hτne⟩ := hτ
  refine ⟨v,hη,hp',hS,hNv,?_⟩
  intro i hi j hj hij
  have h : f i τ = f j τ := (hmove i hi).symm.trans (by simpa only [← hij] using hmove j hj)
  by_cases hbase : f i 0 = f j 0
  · have hbase' : w.η * (matchingProduct w.a w.b w.pivot - matchingProduct w.a w.b i) =
        w.η * (matchingProduct w.a w.b w.pivot - matchingProduct w.a w.b j) := by
      simpa only [f,Complex.ofReal_zero,mul_zero,add_zero] using hbase
    dsimp only [f] at h
    rw [hbase'] at h
    exact hu (Complex.ofReal_injective (mul_right_cancel₀ Complex.I_ne_zero
      (mul_right_cancel₀ (Complex.ofReal_ne_zero.mpr hτne) (add_left_cancel h))))
  · exact (hne i j hbase h).elim

end MOC
