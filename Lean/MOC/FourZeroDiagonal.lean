import MOC.ContactWeightPositivity
import MOC.Realification

/-! A zero-diagonal orthogonal mixer in order four admits nonnegative
Leibniz weights. The proof uses alternating halves of a derangement and
orthogonality in the off-diagonal two-by-two blocks. -/

open Finset Matrix

namespace MOC

private theorem fin4_choice_complement (i j k : Fin 4) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ l : Fin 4, l ≠ i ∧ l ≠ j ∧ l ≠ k := by
  let S : Finset (Fin 4) := ((Finset.univ.erase i).erase j).erase k
  have hki : k ∈ (Finset.univ.erase i).erase j := by simp [hik.symm, hjk.symm]
  have hji : j ∈ Finset.univ.erase i := by simp [hij.symm]
  have hS : S.card = 1 := by
    simp [S, Finset.card_erase_of_mem, hki, hji, Fintype.card_fin]
  obtain ⟨l, hl⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  have he : l ≠ k ∧ l ≠ j ∧ l ≠ i := by simpa [S] using hl
  exact ⟨l, he.2.2, he.2.1, he.1⟩

private theorem fin4_cover (i j k l : Fin 4) (hij : i ≠ j)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ∀ x : Fin 4, x = i ∨ x = j ∨ x = k ∨ x = l := by
  let S : Finset (Fin 4) := {i,j,k,l}
  have hS : S.card = 4 := by
    simp [S, hij, hik, hil, hjk, hjl, hkl, Finset.card_insert_of_not_mem]
  have hu : S = univ := Finset.eq_univ_of_card S (by simp [hS])
  intro x
  have hx : x ∈ S := hu ▸ mem_univ x
  simpa [S] using hx

/-- Each derangement of four labels sends one two-element half onto its
complement. Construct the half along cycles, without a permutation table. -/
theorem fin4_derangement_alternating (σ : Equiv.Perm (Fin 4)) (hs : ∀ i, σ i ≠ i) :
    ∃ i k, i ≠ k ∧ σ i ≠ k ∧ σ k ≠ i := by
  let i : Fin 4 := 0
  let j := σ i
  have hij : i ≠ j := (hs i).symm
  by_cases h : σ j = i
  · obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 4, k ≠ i ∧ k ≠ j := by
      have hc : ((Finset.univ.erase i).erase j : Finset (Fin 4)).card = 2 := by
        simp [Finset.card_erase_of_mem, hij.symm, Fintype.card_fin]
      obtain ⟨k, hk⟩ := Finset.card_pos.mp (show 0 < ((Finset.univ.erase i).erase j).card by omega)
      have he : k ≠ j ∧ k ≠ i := by simpa using hk
      exact ⟨k, he.2, he.1⟩
    exact ⟨i, k, hki.symm, hkj.symm, fun he => hkj (σ.injective (he.trans h.symm))⟩
  · let k := σ j
    have hik : i ≠ k := Ne.symm h
    have hjk : j ≠ k := (hs j).symm
    obtain ⟨l, hli, hlj, hlk⟩ := fin4_choice_complement i j k hij hik hjk
    refine ⟨i, k, hik, hjk, ?_⟩
    intro hki
    have hlσ := fin4_cover i j k l hij hik hli.symm hjk hlj.symm hlk.symm (σ l)
    rcases hlσ with he | he | he | he
    · exact hlk (σ.injective (he.trans hki.symm))
    · exact hli (σ.injective he)
    · exact hlj (σ.injective he)
    · exact hs l he

noncomputable section

private def fibreMask (O : Matrix (Fin 4) (Fin 4) ℝ)
    (I J : Finset (Fin 4)) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => if (i ∈ I ↔ j ∈ J) then O i j else 0

private theorem mask_det_div_nonneg (O : Matrix.orthogonalGroup (Fin 4) ℝ)
    (I J : Finset (Fin 4)) : 0 ≤ (fibreMask O.val I J).det / O.val.det := by
  classical
  let U := Complex.ofRealHom.mapMatrix O.val
  let M := Complex.ofRealHom.mapMatrix (fibreMask O.val I J)
  have hU := isUnitary_ofReal_orthogonal O
  have hM (σ : Equiv.Perm (Fin 4)) :
      leibnizTerm M σ = if J.map σ.toEmbedding = I then leibnizTerm U σ else 0 := by
    unfold leibnizTerm
    by_cases h : J.map σ.toEmbedding = I
    · simp only [h, if_true]
      congr 1
      apply Finset.prod_congr rfl
      intro j _
      have hmem : σ j ∈ I ↔ j ∈ J := by
        rw [← h, Finset.mem_map_equiv, Equiv.symm_apply_apply]
      simp [M, U, fibreMask, hmem]
    · simp only [h, if_false]
      have hnot : ¬ ∀ j, σ j ∈ I ↔ j ∈ J := by
        intro hh
        apply h
        ext x
        rw [Finset.mem_map_equiv, ← hh (σ.symm x), Equiv.apply_symm_apply]
      push_neg at hnot
      obtain ⟨j, hj⟩ := hnot
      have hb : ¬ (σ j ∈ I ↔ j ∈ J) := by tauto
      have hz : M (σ j) j = 0 := by simp [M, fibreMask, hb]
      rw [prod_eq_zero (f := fun i => M (σ i) i) (mem_univ j) hz, mul_zero]
  have hd : M.det / U.det =
      ∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin 4) => J.map σ.toEmbedding = I), signedWeight U σ := by
    rw [Matrix.det_apply', Finset.sum_div, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro σ _
    rw [show ((Equiv.Perm.sign σ : ℤ) : ℂ) * (∏ j, M (σ j) j) = leibnizTerm M σ from rfl, hM]
    by_cases h : J.map σ.toEmbedding = I <;> simp [h, signedWeight]
  rw [sum_signedWeight_image_eq_subsetMinorSq U hU I J] at hd
  have hn : (M.det / U.det).re = (fibreMask O.val I J).det / O.val.det := by
    change ((Complex.ofRealHom.mapMatrix (fibreMask O.val I J)).det /
      (Complex.ofRealHom.mapMatrix O.val).det).re = _
    rw [← RingHom.map_det, ← RingHom.map_det]
    exact congrArg Complex.re (Complex.ofReal_div _ _).symm
  rw [← hn, hd, Complex.ofReal_re]
  exact subsetMinorSq_nonneg U I J

private def pairLookup (u v : Fin 4) (t : Fin 2) : Fin 4 :=
  Fin.cases u (fun _ => v) t

private theorem pairLookup_cases (u v : Fin 4) (t : Fin 2) :
    pairLookup u v t = u ∨ pairLookup u v t = v :=
  Fin.cases (Or.inl rfl) (fun _ => Or.inr rfl) t

private theorem pairLookup_injective {u v : Fin 4} (huv : u ≠ v) :
    Function.Injective (pairLookup u v) := by
  intro x
  refine Fin.cases ?_ (fun i => ?_) x
  · intro y; refine Fin.cases ?_ (fun j => ?_) y
    · intro _; rfl
    · intro h; exact (huv h).elim
  · intro y; refine Fin.cases ?_ (fun j => ?_) y
    · intro h; exact (huv h.symm).elim
    · intro _; rw [Fin.eq_zero i, Fin.eq_zero j]

private def splitPair (u v w z : Fin 4)
    (huv : u ≠ v) (huw : u ≠ w) (huz : u ≠ z) (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z) :
    Fin 2 ⊕ Fin 2 ≃ Fin 4 := by
  let f := Sum.elim (pairLookup u v) (pairLookup w z)
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · exact congrArg Sum.inl (pairLookup_injective huv hab)
    · exfalso
      rcases pairLookup_cases u v a with ha | ha <;>
      rcases pairLookup_cases w z b with hb | hb
      · exact huw (ha.symm.trans (hab.trans hb))
      · exact huz (ha.symm.trans (hab.trans hb))
      · exact hvw (ha.symm.trans (hab.trans hb))
      · exact hvz (ha.symm.trans (hab.trans hb))
    · exfalso
      rcases pairLookup_cases w z a with ha | ha <;>
      rcases pairLookup_cases u v b with hb | hb
      · exact huw (hb.symm.trans (hab.symm.trans ha))
      · exact hvw (hb.symm.trans (hab.symm.trans ha))
      · exact huz (hb.symm.trans (hab.symm.trans ha))
      · exact hvz (hb.symm.trans (hab.symm.trans ha))
    · exact congrArg Sum.inr (pairLookup_injective hwz hab)
  · intro x
    rcases fin4_cover u v w z huv huw huz hvw hvz hwz x with hx | hx | hx | hx
    · exact ⟨Sum.inl 0, hx.symm⟩
    · exact ⟨Sum.inl 1, hx.symm⟩
    · exact ⟨Sum.inr 0, hx.symm⟩
    · exact ⟨Sum.inr 1, hx.symm⟩

/-- For two orthogonal rows of a two-column block, its diagonal term has
the same weak sign as the determinant. -/
private theorem pair_det_product_nonneg {a b c d : ℝ} (h : a * c + b * d = 0) :
    0 ≤ (a * d) * (a * d - b * c) := by
  have he : (a * d) * (a * d - b * c) = (a*d)^2 + (a*c)^2 := by
    linear_combination -(a*c) * h
  rw [he]
  positivity

private theorem cast_weight_of_real (O : Matrix.orthogonalGroup (Fin 4) ℝ)
    (σ : Equiv.Perm (Fin 4)) :
    realSignedWeight (Complex.ofRealHom.mapMatrix O.val) σ =
      (∏ j, O.val (σ j) j) / (O.val.submatrix σ id).det := by
  let q : ℝ := (Equiv.Perm.sign σ : ℤ)
  have hq : q * q = 1 := by
    have h : (Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign σ : ℤ) = 1 :=
      congrArg (fun u : ℤˣ => (u : ℤ)) (Int.units_mul_self (Equiv.Perm.sign σ))
    change ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign σ : ℤ) : ℝ) = 1
    rw [← Int.cast_mul, h, Int.cast_one]
  unfold realSignedWeight signedWeight leibnizTerm
  have hd : (O.val.det : ℂ) = (Complex.ofRealHom.mapMatrix O.val).det :=
    RingHom.map_det Complex.ofRealHom O.val
  change (((Equiv.Perm.sign σ : ℤ) : ℂ) *
      (∏ j, (O.val (σ j) j : ℂ)) / (Complex.ofRealHom.mapMatrix O.val).det).re = _
  rw [← hd, ← Complex.ofReal_prod, ← Complex.ofReal_intCast, ← Complex.ofReal_mul,
    ← Complex.ofReal_div, Complex.ofReal_re, Matrix.det_permute]
  change q * (∏ j, O.val (σ j) j) / O.val.det = (∏ j, O.val (σ j) j) / (q * O.val.det)
  rw [div_mul_eq_div_div]
  congr 1
  have hqi : q⁻¹ = q := by
    symm
    exact eq_inv_of_mul_eq_one_left hq
  rw [div_eq_mul_inv, hqi, mul_comm]

/-- Every real signed Leibniz weight of a zero-diagonal orthogonal order-four
mixer is nonnegative. This uses only the structure of an alternating pair
split and the squared-minor identity, not a list of permutations. -/
theorem four_realSignedWeight_nonneg_of_zero_diagonal
    (O : Matrix.orthogonalGroup (Fin 4) ℝ) (hz : ∀ j, O.val j j = 0)
    (σ : Equiv.Perm (Fin 4)) :
    0 ≤ realSignedWeight (Complex.ofRealHom.mapMatrix O.val) σ := by
  classical
  rw [cast_weight_of_real]
  by_cases hp : ∏ j, O.val (σ j) j = 0
  · rw [hp, zero_div]
  have hs (j : Fin 4) : σ j ≠ j := by
    intro h
    exact hp (prod_eq_zero (mem_univ j) (h.symm ▸ hz j))
  obtain ⟨i,k,hik,hik',hki'⟩ := fin4_derangement_alternating σ hs
  let j := σ i
  let l := σ k
  have hij : i ≠ j := (hs i).symm
  have hil : i ≠ l := hki'.symm
  have hkj : k ≠ j := hik'.symm
  have hkl : k ≠ l := (hs k).symm
  have hjl : j ≠ l := fun h => hik (σ.injective h)
  let e := splitPair i k j l hik hij hil hkj hkl hjl
  have he₀ : e (Sum.inl 0) = i := rfl
  have he₁ : e (Sum.inl 1) = k := rfl
  have he₂ : e (Sum.inr 0) = j := rfl
  have he₃ : e (Sum.inr 1) = l := rfl
  let I : Finset (Fin 4) := {j,l}
  let J : Finset (Fin 4) := {i,k}
  have hsJ (x : Fin 4) : σ x ∈ I ↔ x ∈ J := by
    simp only [I, J, mem_insert, mem_singleton]
    exact or_congr σ.injective.eq_iff σ.injective.eq_iff
  let M := fibreMask O.val I J
  let N := M.submatrix σ id
  let U := O.val.submatrix σ id
  let A : Matrix (Fin 2) (Fin 2) ℝ := O.val.submatrix
    (fun t => σ (e (Sum.inl t))) (fun t => e (Sum.inl t))
  let D : Matrix (Fin 2) (Fin 2) ℝ := O.val.submatrix
    (fun t => σ (e (Sum.inr t))) (fun t => e (Sum.inr t))
  have heJ (a : Fin 2) : e (Sum.inl a) ∈ J := by
    rcases pairLookup_cases i k a with he | he
    · change e (Sum.inl a) = i at he
      simp [J, he]
    · change e (Sum.inl a) = k at he
      simp [J, he]
  have heI (a : Fin 2) : e (Sum.inr a) ∉ J := by
    rcases pairLookup_cases j l a with he | he
    · change e (Sum.inr a) = j at he
      simp [J, he, hij.symm, hkj.symm]
    · change e (Sum.inr a) = l at he
      simp [J, he, hil.symm, hkl.symm]
  have hN : N.submatrix e e = Matrix.fromBlocks A 0 0 D := by
    ext (p | p) (q | q) : 1
    · change (fibreMask O.val I J) (σ (e (Sum.inl p))) (e (Sum.inl q)) =
        O.val (σ (e (Sum.inl p))) (e (Sum.inl q))
      simp [fibreMask, hsJ, heJ]
    · change (fibreMask O.val I J) (σ (e (Sum.inl p))) (e (Sum.inr q)) = 0
      simp [fibreMask, hsJ, heJ, heI]
    · change (fibreMask O.val I J) (σ (e (Sum.inr p))) (e (Sum.inl q)) = 0
      simp [fibreMask, hsJ, heJ, heI]
    · change (fibreMask O.val I J) (σ (e (Sum.inr p))) (e (Sum.inr q)) =
        O.val (σ (e (Sum.inr p))) (e (Sum.inr q))
      simp [fibreMask, hsJ, heI]
  have hNdet : N.det = A.det * D.det := by
    rw [← Matrix.det_submatrix_equiv_self e N, hN, Matrix.det_fromBlocks_zero₁₂]
  have hratio : 0 ≤ N.det / U.det := by
    change 0 ≤ (M.submatrix σ id).det / (O.val.submatrix σ id).det
    rw [Matrix.det_permute, Matrix.det_permute, mul_div_mul_left]
    · exact mask_det_div_nonneg O I J
    · exact_mod_cast Units.ne_zero (Equiv.Perm.sign σ)
  let p := ∏ t, O.val (σ t) t
  let a := A 0 0 * A 1 1
  let d := D 0 0 * D 1 1
  have hp' : p = a * d := by
    dsimp only [p]
    rw [← Equiv.prod_comp e (fun t => O.val (σ t) t), Fintype.prod_sum_type,
      Fin.prod_univ_two, Fin.prod_univ_two]
    rfl
  have horth (u v : Fin 4) (huv : u ≠ v) : ∑ t, O.val u t * O.val v t = 0 := by
    have hO : O.val * O.valᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin 4) ℝ).mp O.property
    have ho := congrArg (fun Z : Matrix (Fin 4) (Fin 4) ℝ => Z u v) hO
    simpa [Matrix.mul_apply, Matrix.one_apply, huv] using ho
  have hsum (u v : Fin 4) :
      ∑ t, O.val u t * O.val v t =
        (O.val u i * O.val v i + O.val u k * O.val v k) +
        (O.val u j * O.val v j + O.val u l * O.val v l) := by
    rw [← Equiv.sum_comp e (fun t => O.val u t * O.val v t), Fintype.sum_sum_type,
      Fin.sum_univ_two, Fin.sum_univ_two, he₀, he₁, he₂, he₃]
  have hAorth : A 0 0 * A 1 0 + A 0 1 * A 1 1 = 0 := by
    change O.val j i * O.val l i + O.val j k * O.val l k = 0
    have h := horth j l hjl
    rw [hsum j l] at h
    simpa [hz] using h
  have hJI (x : Fin 4) (hx : x ∉ I) : x = i ∨ x = k := by
    rcases fin4_cover i k j l hik hij hil hkj hkl hjl x with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hx (by simp [I, h])).elim
    · exact (hx (by simp [I, h])).elim
  have hDj : σ j = i ∨ σ j = k := hJI _ ((hsJ j).not.mpr (by simp [J, hij.symm, hkj.symm]))
  have hDl : σ l = i ∨ σ l = k := hJI _ ((hsJ l).not.mpr (by simp [J, hil.symm, hkl.symm]))
  have hDorth : D 0 0 * D 1 0 + D 0 1 * D 1 1 = 0 := by
    change O.val (σ j) j * O.val (σ l) j + O.val (σ j) l * O.val (σ l) l = 0
    have h := horth (σ j) (σ l) (σ.injective.ne hjl)
    rw [hsum (σ j) (σ l)] at h
    rcases hDj with h₁ | h₁ <;> rcases hDl with h₂ | h₂
    · exact (hjl (σ.injective (h₁.trans h₂.symm))).elim
    · simpa [h₁,h₂,hz] using h
    · simpa [h₁,h₂,hz] using h
    · exact (hjl (σ.injective (h₁.trans h₂.symm))).elim
  have hAd : 0 ≤ a * A.det := by
    rw [Matrix.det_fin_two]
    exact pair_det_product_nonneg hAorth
  have hDd : 0 ≤ d * D.det := by
    rw [Matrix.det_fin_two]
    exact pair_det_product_nonneg hDorth
  have hprod : a * d ≠ 0 := by
    have hp₀ : p ≠ 0 := hp
    rwa [hp'] at hp₀
  have hpos : 0 < p * N.det := by
    rw [hp', hNdet, mul_mul_mul_comm]
    apply mul_pos
    · rw [Matrix.det_fin_two]
      change 0 < (A 0 0 * A 1 1) * (A 0 0 * A 1 1 - A 0 1 * A 1 0)
      have ha : a ≠ 0 := left_ne_zero_of_mul hprod
      have he : (A 0 0 * A 1 1) * (A 0 0 * A 1 1 - A 0 1 * A 1 0) =
          (A 0 0 * A 1 1)^2 + (A 0 0 * A 1 0)^2 := by
        linear_combination -(A 0 0 * A 1 0) * hAorth
      rw [he]
      exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero ha) (sq_nonneg _)
    · rw [Matrix.det_fin_two]
      change 0 < (D 0 0 * D 1 1) * (D 0 0 * D 1 1 - D 0 1 * D 1 0)
      have hd : d ≠ 0 := right_ne_zero_of_mul hprod
      have he : (D 0 0 * D 1 1) * (D 0 0 * D 1 1 - D 0 1 * D 1 0) =
          (D 0 0 * D 1 1)^2 + (D 0 0 * D 1 0)^2 := by
        linear_combination -(D 0 0 * D 1 0) * hDorth
      rw [he]
      exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hd) (sq_nonneg _)
  have hnd : N.det ≠ 0 := right_ne_zero_of_mul hpos.ne'
  have hnn : 0 ≤ (p / U.det) * N.det^2 := by
    calc
      0 ≤ (p * N.det) * (N.det / U.det) := mul_nonneg hpos.le hratio
      _ = (p / U.det) * N.det ^ 2 := by ring
  exact nonneg_of_mul_nonneg_left hnn (sq_pos_of_ne_zero hnd)

/-- The zero-diagonal real orthogonal family satisfies MOC for arbitrary
complex spectra. -/
theorem four_holds_zero_diagonal_orthogonal
    (a b : Fin 4 → ℂ) (O : Matrix.orthogonalGroup (Fin 4) ℝ)
    (hz : ∀ j, O.val j j = 0) :
    Holds a b (Complex.ofRealHom.mapMatrix O.val) :=
  holds_of_nonneg_realSignedWeight a b (isUnitary_ofReal_orthogonal O)
    (four_realSignedWeight_nonneg_of_zero_diagonal O hz)

end

end MOC
