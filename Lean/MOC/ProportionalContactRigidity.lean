import MOC.GapFreeContactFibre

/-! Spectral affine incidence rigidity at a contact-maximal strict profile.
The argument uses exact normalized matching profiles and the gap-free
isolation derived from the contact transfer of Zheng (preprint DOI
10.13140/RG.2.2.36790.25923), without arithmetic certificates. -/

open Matrix Set Filter
open scoped BigOperators Topology
open Polynomial (C X)

namespace MOC

noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The affine polynomial attached to one spectral edge. -/
private def edgeLine (a b x y : ι → ℂ) (i j : ι) : Polynomial ℂ :=
  C (a i + b j) + C (x i + y j) * X

/-- A rationally normalized affine variation which is constant on all
contacts must preserve every matching product as a polynomial identity.
The denominator need not have no roots; isolation only uses its value
one at the starting point. -/
private theorem affineProducts_eq_of_proportional_contacts
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (hmax : ∀ v : StrictMatchingSupport U, v.contacts.card ≤ w.contacts.card)
    (x y ℓ : ι → ℂ)
    (hlock : ∀ q ∈ w.contacts,
      (∀ j, x (q j) + y j = ℓ (q j) * (w.a (q j) + w.b j)) ∨
        ∃ j, w.a (q j) + w.b j = 0 ∧ x (q j) + y j = 0) :
    ∀ q : Equiv.Perm ι,
      (∏ j, edgeLine w.a w.b x y (q j) j) =
        C (matchingProduct w.a w.b q) * ∏ i, (1 + C (ℓ i) * X) := by
  let P (q : Equiv.Perm ι) := ∏ j, edgeLine w.a w.b x y (q j) j
  let D : Polynomial ℂ := ∏ i, (1 + C (ℓ i) * X)
  let p := matchingProduct w.a w.b
  have hP (t : ℂ) : (fun q => (P q).eval t) =
      matchingProduct (fun i => w.a i + t * x i) (fun i => w.b i + t * y i) := by
    funext q
    simp only [P, edgeLine, matchingProduct, Polynomial.eval_prod, Polynomial.eval_add,
      Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
    exact Finset.prod_congr rfl fun _ _ => by ring
  have hD₀ : D.eval 0 = 1 := by simp [D,Polynomial.eval_prod]
  have hlock' (q : Equiv.Perm ι) (hq : q ∈ w.contacts) : P q = C (p q) * D := by
    rcases hlock q hq with h | ⟨j,hj,hxy⟩
    · have he (j : ι) : edgeLine w.a w.b x y (q j) j =
          C (w.a (q j) + w.b j) * (1 + C (ℓ (q j)) * X) := by
        rw [edgeLine,h j,map_mul,mul_add,mul_one]
        ring
      simp_rw [P,he,Finset.prod_mul_distrib, ← map_prod,
        Equiv.prod_comp q (fun i => (1 : Polynomial ℂ) + C (ℓ i) * X)]
      rfl
    · have he : edgeLine w.a w.b x y (q j) j = 0 := by simp [edgeLine,hj,hxy]
      have hP0 : P q = 0 := Finset.prod_eq_zero (Finset.mem_univ j) he
      have hp0 : p q = 0 := Finset.prod_eq_zero (Finset.mem_univ j) hj
      simp [hP0,hp0]
  let f (t : ℂ) (q : Equiv.Perm ι) := (P q).eval t / D.eval t
  have hf₀ : f 0 = p := by
    funext q
    change (P q).eval 0 / D.eval 0 = p q
    rw [hD₀,div_one]
    have he := congrFun (hP 0) q
    simpa only [zero_mul,add_zero] using he
  have hDne : ∀ᶠ t in 𝓝 (0 : ℂ), D.eval t ≠ 0 :=
    (isOpen_ne_fun D.continuous continuous_const).preimage continuous_id |>.mem_nhds (by simp [hD₀])
  have hfc : ContinuousAt f 0 := by
    apply continuousAt_pi.mpr
    intro q
    exact (P q).continuous.continuousAt.div D.continuous.continuousAt (by simp [hD₀])
  obtain ⟨O, hO, hpO, hIso⟩ := w.exists_isolating_open_of_max_contact_differences hU hmax
  have hnear : ∀ᶠ t in 𝓝 (0 : ℂ), f t = p ∧ D.eval t ≠ 0 := by
    have hfO : ∀ᶠ t in 𝓝 (0 : ℂ), f t ∈ O :=
      hfc.eventually (hO.mem_nhds (hf₀.symm ▸ hpO))
    filter_upwards [hfO,hDne] with t ht hne
    have hExact : f t ∈ MvPolynomial.zeroLocus (profileIdeal ι) := by
      obtain ⟨c,hc⟩ := IsAlgClosed.exists_pow_nat_eq (D.eval t)⁻¹ (Fintype.card_pos (α := ι))
      rw [← profileIdeal_exact]
      refine ⟨fun i => c * (w.a i + t * x i),fun i => c * (w.b i + t * y i),?_⟩
      funext q
      rw [matchingProduct_scale,hc,← congrFun (hP t) q,inv_mul_eq_div]
    have hfibre : f t ∈ MvPolynomial.zeroLocus w.differenceFibreIdeal := by
      apply (w.mem_differenceFibre_iff _).mpr
      refine ⟨hExact,?_⟩
      have hfix (q : Equiv.Perm ι) (hq : q ∈ w.contacts) : f t q = p q := by
        change (P q).eval t / D.eval t = p q
        rw [hlock' q hq,Polynomial.eval_mul,Polynomial.eval_C,mul_div_cancel_right₀ _ hne]
      intro q hq
      rw [hfix q hq, hfix w.pivot (by simp [StrictMatchingSupport.contacts])]
    have he : f t ∈ O ∩ MvPolynomial.zeroLocus w.differenceFibreIdeal := ⟨ht,hfibre⟩
    rw [hIso] at he
    exact ⟨he,hne⟩
  intro q
  apply Polynomial.eq_of_infinite_eval_eq
  apply infinite_of_mem_nhds (0 : ℂ)
  filter_upwards [hnear] with t ht
  change (P q).eval t = (C (p q) * D).eval t
  simp only [Polynomial.eval_mul,Polynomial.eval_C]
  exact (div_eq_iff ht.2).mp (congrFun ht.1 q)


omit [Fintype ι] [Nonempty ι] in
private theorem exists_perm_two (i k j l : ι) (hik : i ≠ k) (hjl : j ≠ l) :
    ∃ q : Equiv.Perm ι, q j = i ∧ q l = k := by
  let s : Equiv.Perm ι := Equiv.swap j i
  let t : Equiv.Perm ι := Equiv.swap (s l) k
  have hs : s j = i := Equiv.swap_apply_left _ _
  have hsi : s l ≠ i := by rw [← hs]; exact s.injective.ne hjl.symm
  refine ⟨t*s,?_ ,?_⟩
  · simp only [Equiv.Perm.mul_apply,hs,t,Equiv.swap_apply_of_ne_of_ne hsi.symm hik]
  · exact Equiv.swap_apply_left _ _

/-- The first two coefficients of the switched matching identity force
the exact row/column dichotomy on the matrix of normalized slopes. -/
private theorem profileLine_row_or_column
    (m : ι → ι → ℂ)
    (h : ∀ q : Equiv.Perm ι, (∏ j, (1 + C (m (q j) j) * X)) =
      ∏ j, (1 + C (m j j) * X)) :
    (∃ r : ι → ℂ, ∀ i j, m i j = r i) ∨ (∃ s : ι → ℂ, ∀ i j, m i j = s j) := by
  classical
  let Q (i j : ι) : Polynomial ℂ := 1 + C (m i j) * X
  have hQ (i j : ι) : Q i j ≠ 0 := by
    intro he
    have hz := congrArg (Polynomial.eval 0) he
    simp [Q] at hz
  have hp (i k j l : ι) : Q i j * Q k l = Q k j * Q i l := by
    by_cases hik : i = k
    · subst k; rfl
    by_cases hjl : j = l
    · subst l; exact mul_comm _ _
    obtain ⟨q,hqj,hql⟩ := exists_perm_two i k j l hik hjl
    let p := q * Equiv.swap j l
    let T := Finset.univ.erase j |>.erase l
    have hj : j ∈ (Finset.univ : Finset ι) := Finset.mem_univ _
    have hl : l ∈ (Finset.univ : Finset ι).erase j :=
      Finset.mem_erase.mpr ⟨Ne.symm hjl,Finset.mem_univ _⟩
    have he (u : Equiv.Perm ι) : (∏ x, Q (u x) x) =
        Q (u j) j * (Q (u l) l * ∏ x ∈ T, Q (u x) x) := by
      rw [← Finset.mul_prod_erase Finset.univ (fun x => Q (u x) x) hj,
        ← Finset.mul_prod_erase _ (fun x => Q (u x) x) hl]
    have e : (∏ x, Q (q x) x) = ∏ x, Q (p x) x := (h q).trans (h p).symm
    have hpj : p j = k := by simp only [p,Equiv.Perm.mul_apply,Equiv.swap_apply_left,hql]
    have hpl : p l = i := by simp only [p,Equiv.Perm.mul_apply,Equiv.swap_apply_right,hqj]
    have hT : (∏ x ∈ T, Q (p x) x) = ∏ x ∈ T, Q (q x) x := by
      apply Finset.prod_congr rfl
      intro x hx
      have hx' := Finset.mem_erase.mp hx
      rw [show p x = q x by
        simp only [p,Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne (Finset.mem_erase.mp hx'.2).1 hx'.1]]
    rw [he q,he p,hqj,hql,hpj,hpl,hT,← mul_assoc,← mul_assoc] at e
    exact mul_right_cancel₀ (Finset.prod_ne_zero_iff.mpr fun x _ => hQ (q x) x) e
  have expand (u v : ℂ) :
      (1 + C u * X) * (1 + C v * X) =
        1 + C (u+v) * X + C (u*v) * X^2 := by
    rw [map_add,map_mul]
    ring
  have hs (i k j l : ι) : m i j + m k l = m k j + m i l := by
    have he := hp i k j l
    dsimp only [Q] at he
    rw [expand,expand] at he
    have h1 := congrArg (fun p : Polynomial ℂ => p.coeff 1) he
    simpa only [Polynomial.coeff_add,Polynomial.coeff_one,Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow,if_pos rfl,if_neg one_ne_zero,
      if_neg (show (1:ℕ) ≠ 2 by omega),zero_add,add_zero] using h1
  have hm (i k j l : ι) : m i j * m k l = m k j * m i l := by
    have he := hp i k j l
    dsimp only [Q] at he
    rw [expand,expand] at he
    have h2 := congrArg (fun p : Polynomial ℂ => p.coeff 2) he
    simpa only [Polynomial.coeff_add,Polynomial.coeff_one,Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow,if_pos rfl,if_neg (show (2:ℕ) ≠ 0 by omega),
      if_neg (show (2:ℕ) ≠ 1 by omega),zero_add,add_zero] using h2
  let z := Classical.choice (inferInstance : Nonempty ι)
  let r (i : ι) := m i z
  let s (j : ι) := m z j - m z z
  have hrs (i j : ι) : m i j = r i + s j := by
    have h' := hs i z j z
    dsimp only [r,s]
    linear_combination h'
  have hc (i k j l : ι) : (r i-r k) * (s j-s l) = 0 := by
    have he := hm i k j l
    simp only [hrs] at he
    linear_combination -he
  by_cases hr : ∀ i, r i = r z
  · exact Or.inr ⟨fun j => r z + s j,fun i j => (hrs i j).trans (by rw [hr i])⟩
  · obtain ⟨i,hi⟩ := not_forall.mp hr
    have hsz : s z = 0 := sub_self _
    have hsj (j : ι) : s j = 0 := by
      have he := hc i z j z
      rw [hsz,sub_zero] at he
      exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hi)
    exact Or.inl ⟨r,fun i j => by rw [hrs,hsj,add_zero]⟩


/-- At maximal contact count, the edge equations of zero-free profiles
admit no affine variation except common scaling and translation.
The hypotheses only require nonconstant spectra, not pairwise
distinct entries within either spectrum. -/
theorem StrictMatchingSupport.proportional_incidence_rigidity
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (hmax : ∀ v : StrictMatchingSupport U, v.contacts.card ≤ w.contacts.card)
    (ha : ∃ i j, w.a i ≠ w.a j) (hb : ∃ i j, w.b i ≠ w.b j)
    (hn : ∀ i j, w.a i + w.b j ≠ 0)
    (x y ℓ : ι → ℂ)
    (he : ∀ q ∈ w.contacts, ∀ j, x (q j) + y j = ℓ (q j) * (w.a (q j) + w.b j)) :
    ∃ d c : ℂ, (∀ i, x i = d * w.a i + c) ∧
      (∀ j, y j = d * w.b j - c) ∧ (∀ i, ℓ i = d) := by
  classical
  let m (i j : ι) := (x i + y j) / (w.a i + w.b j)
  let Q (i j : ι) : Polynomial ℂ := 1 + C (m i j) * X
  let D : Polynomial ℂ := ∏ i, (1 + C (ℓ i) * X)
  have hmul (i j : ι) : m i j * (w.a i + w.b j) = x i + y j :=
    div_mul_cancel₀ _ (hn i j)
  have hpoly (q : Equiv.Perm ι) : (∏ j, Q (q j) j) = D := by
    have h' := affineProducts_eq_of_proportional_contacts hU w hmax x y ℓ
      (fun v hv => Or.inl (he v hv)) q
    have hf (i j : ι) : edgeLine w.a w.b x y i j = C (w.a i + w.b j) * Q i j := by
      simp only [edgeLine, ← hmul i j, map_mul, Q]
      ring
    simp_rw [hf,Finset.prod_mul_distrib, ← map_prod] at h'
    have hz : matchingProduct w.a w.b q ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ => hn (q j) j
    exact mul_left_cancel₀ (Polynomial.C_ne_zero.mpr hz) h'
  have hall (q : Equiv.Perm ι) : (∏ j, Q (q j) j) = ∏ j, Q j j :=
    (hpoly q).trans (hpoly 1).symm
  let z := Classical.choice (inferInstance : Nonempty ι)
  obtain ⟨d,hd⟩ : ∃ d, ∀ i j, m i j = d := by
    rcases profileLine_row_or_column m hall with ⟨r,hr⟩ | ⟨s,hs⟩
    · obtain ⟨j,l,hjl⟩ := hb
      have hrow (i : ι) : r i * (w.b j - w.b l) = y j - y l := by
        have p := hmul i j
        have q := hmul i l
        rw [hr] at p q
        linear_combination p - q
      refine ⟨r z,fun i j' => (hr i j').trans ?_⟩
      exact mul_right_cancel₀ (sub_ne_zero.mpr hjl) ((hrow i).trans (hrow z).symm)
    · obtain ⟨i,k,hik⟩ := ha
      have hcol (j : ι) : s j * (w.a i - w.a k) = x i - x k := by
        have p := hmul i j
        have q := hmul k j
        rw [hs] at p q
        linear_combination p - q
      refine ⟨s z,fun i' j => (hs i' j).trans ?_⟩
      exact mul_right_cancel₀ (sub_ne_zero.mpr hik) ((hcol j).trans (hcol z).symm)
  let c := d * w.b z - y z
  have hxy (i j : ι) : d * (w.a i+w.b j) = x i+y j := by
    rw [← hd i j,hmul]
  have hxp (i : ι) : x i = d * w.a i + c := by
    dsimp only [c]
    linear_combination -(hxy i z)
  have hyp (j : ι) : y j = d * w.b j - c := by
    have h := hxy z j
    rw [hxp z] at h
    linear_combination -h
  refine ⟨d,c,hxp,hyp,fun i => ?_⟩
  let j := w.pivot.symm i
  have e := he w.pivot (by simp [StrictMatchingSupport.contacts]) j
  change x (w.pivot j) + y j = ℓ (w.pivot j) * (w.a (w.pivot j) + w.b j) at e
  rw [← hxy] at e
  have h' := mul_right_cancel₀ (hn (w.pivot j) j) e
  simpa [j] using h'.symm


/-- The union of the terminal contact assignments has at least (3n-2)
distinct edges. The same lower bound holds for every covering edge set.
This is an incidence-rank bound, not just a count of permutations. -/
theorem StrictMatchingSupport.contact_edge_card_lower_bound
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (hmax : ∀ v : StrictMatchingSupport U, v.contacts.card ≤ w.contacts.card)
    (ha : ∃ i j, w.a i ≠ w.a j) (hb : ∃ i j, w.b i ≠ w.b j)
    (hn : ∀ i j, w.a i + w.b j ≠ 0)
    (E : Finset (ι × ι)) (hE : ∀ q ∈ w.contacts, ∀ j, (q j,j) ∈ E) :
    3 * Fintype.card ι - 2 ≤ E.card := by
  classical
  let V := (ι → ℂ) × (ι → ℂ) × (ι → ℂ)
  let L : V →ₗ[ℂ] (E → ℂ) :=
    { toFun := fun v e => v.1 e.val.1 + v.2.1 e.val.2 -
        v.2.2 e.val.1 * (w.a e.val.1 + w.b e.val.2)
      map_add' := fun u v => by
        funext e
        change (u.1 e.val.1 + v.1 e.val.1) + (u.2.1 e.val.2 + v.2.1 e.val.2) -
          (u.2.2 e.val.1 + v.2.2 e.val.1) * (w.a e.val.1 + w.b e.val.2) = _
        change _ = (u.1 e.val.1 + u.2.1 e.val.2 - _ * _) +
          (v.1 e.val.1 + v.2.1 e.val.2 - _ * _)
        ring
      map_smul' := fun d u => by
        funext e
        change d * u.1 e.val.1 + d * u.2.1 e.val.2 -
          (d * u.2.2 e.val.1) * (w.a e.val.1 + w.b e.val.2) =
            d * (u.1 e.val.1 + u.2.1 e.val.2 - u.2.2 e.val.1 * _)
        ring }
  let z := Classical.choice (inferInstance : Nonempty ι)
  let W : ↥(LinearMap.ker L) →ₗ[ℂ] (ℂ × ℂ) :=
    { toFun := fun v => (v.val.2.2 z, v.val.1 z - v.val.2.2 z * w.a z)
      map_add' := by
        intro u v
        change (u.val.2.2 z + v.val.2.2 z,
          u.val.1 z + v.val.1 z - (u.val.2.2 z + v.val.2.2 z) * w.a z) = _
        exact Prod.ext rfl (by change _ = (_ - _ * _) + (_ - _ * _); ring)
      map_smul' := by
        intro d u
        change (d * u.val.2.2 z,
          d * u.val.1 z - (d * u.val.2.2 z) * w.a z) =
            (d * u.val.2.2 z, d * (u.val.1 z - u.val.2.2 z * w.a z))
        exact Prod.ext rfl (by ring) }
  have hnormal (v : ↥(LinearMap.ker L)) : ∃ d c : ℂ,
      (∀ i, v.val.1 i = d * w.a i + c) ∧
      (∀ j, v.val.2.1 j = d * w.b j - c) ∧ (∀ i, v.val.2.2 i = d) := by
    apply w.proportional_incidence_rigidity hU hmax ha hb hn
    intro q hq j
    have h := congrFun (LinearMap.mem_ker.mp v.property) ⟨(q j,j),hE q hq j⟩
    exact sub_eq_zero.mp h
  have hWinj : Function.Injective W := by
    intro u v e
    obtain ⟨d,c,h1,h2,h3⟩ := hnormal u
    obtain ⟨d',c',k1,k2,k3⟩ := hnormal v
    have hd : d = d' := by
      have hh := congrArg Prod.fst e
      exact (h3 z).symm.trans (hh.trans (k3 z))
    subst d'
    have hc : c = c' := by
      have hh := congrArg Prod.snd e
      change u.val.1 z - u.val.2.2 z * w.a z =
        v.val.1 z - v.val.2.2 z * w.a z at hh
      rw [h1,k1,h3,k3] at hh
      linear_combination hh
    subst c'
    exact Subtype.ext (Prod.ext (funext fun i => (h1 i).trans (k1 i).symm)
      (Prod.ext (funext fun i => (h2 i).trans (k2 i).symm)
        (funext fun i => (h3 i).trans (k3 i).symm)))
  have hker := LinearMap.finrank_le_finrank_of_injective hWinj
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  have hdim := (LinearMap.range L).finrank_le
  change Module.finrank ℂ (LinearMap.ker L) ≤ Module.finrank ℂ (ℂ × ℂ) at hker
  simp only [Module.finrank_prod, Module.finrank_self] at hker
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hdim
  simp only [V, Module.finrank_prod, Module.finrank_fintype_fun_eq_card] at hrank
  have hadd := Nat.add_le_add hdim hker
  rw [hrank] at hadd
  omega

end
end MOC
