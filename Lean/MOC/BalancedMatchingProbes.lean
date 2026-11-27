import MOC.SpectralProfileDeterminant
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

open BigOperators Matrix

namespace MOC.SpectralProfile

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

private def starMatrix (o : κ) (t : κ → ℂ) : Matrix κ κ ℂ :=
  Matrix.of fun i j =>
    if i = o then
      if j = o then ∑ k ∈ Finset.univ.erase o, t k else -t j
    else if j = o then -t i else if i = j then t j else 0

private theorem starMatrix_symmetric (o : κ) (t : κ → ℂ) (i j : κ) :
    starMatrix o t i j = starMatrix o t j i := by
  by_cases hij : i = j
  · subst j
    rfl
  · by_cases hi : i = o
    · subst i
      simp only [starMatrix, Matrix.of_apply, if_pos rfl, if_neg (Ne.symm hij), if_neg hij]
    · by_cases hj : j = o
      · subst j
        simp only [starMatrix, Matrix.of_apply, if_pos rfl, if_neg hi, if_neg (Ne.symm hi)]
      · simp only [starMatrix, Matrix.of_apply, if_neg hi, if_neg hj, if_neg hij,
          if_neg (Ne.symm hij)]

private theorem starMatrix_row_sum (o : κ) (t : κ → ℂ) (i : κ) :
    ∑ j, starMatrix o t i j = 0 := by
  classical
  rw [← Finset.add_sum_erase Finset.univ (fun j => starMatrix o t i j) (Finset.mem_univ o)]
  by_cases hi : i = o
  · subst i
    have he : ∑ j ∈ Finset.univ.erase o, starMatrix o t o j =
        ∑ j ∈ Finset.univ.erase o, -t j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [starMatrix, Matrix.of_apply, if_pos rfl,
        if_neg (Finset.mem_erase.mp hj).1, if_true]
    rw [he, Finset.sum_neg_distrib]
    simp [starMatrix]
  · rw [Finset.sum_eq_single i]
    · simp [starMatrix, hi]
    · intro j hj hji
      simp [starMatrix, hi, (Finset.mem_erase.mp hj).1, hji.symm]
    · simp [hi]

private theorem starMatrix_supported (o : κ) (t : κ → ℂ) (σ : Equiv.Perm κ)
    (hs : ∀ j, starMatrix o t (σ j) j ≠ 0) :
    σ = 1 ∨ ∃ i, i ≠ o ∧ σ = Equiv.swap o i := by
  have ha (j : κ) (hj : j ≠ o) : σ j = o ∨ σ j = j := by
    by_contra! h
    exact hs j (by simp [starMatrix, h.1, hj, h.2])
  by_cases h : σ o = o
  · left
    ext j
    by_cases hj : j = o
    · simpa only [hj, Equiv.Perm.one_apply] using h
    · exact (ha j hj).resolve_left (fun he => hj (σ.injective (he.trans h.symm)))
  · let i := σ o
    have hi : i ≠ o := h
    have he : σ i = o := (ha i hi).resolve_right (fun h' => hi (σ.injective h'))
    refine Or.inr ⟨i, hi, ?_⟩
    ext j
    by_cases hj : j = o
    · subst j
      exact (Equiv.swap_apply_left o i).symm
    · by_cases hji : j = i
      · subst j
        rw [Equiv.swap_apply_right, he]
      · rw [Equiv.swap_apply_of_ne_of_ne hj hji]
        exact (ha j hj).resolve_left (fun hh => hji (σ.injective (hh.trans he.symm)))

private theorem star_product_one (o : κ) (t : κ → ℂ) :
    (∏ j, starMatrix o t j j) =
      (∑ i ∈ Finset.univ.erase o, t i) * ∏ i ∈ Finset.univ.erase o, t i := by
  rw [← Finset.mul_prod_erase Finset.univ (fun j => starMatrix o t j j) (Finset.mem_univ o)]
  simp only [starMatrix, Matrix.of_apply, if_pos rfl]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp only [if_neg (Finset.mem_erase.mp hj).1, if_true]

private theorem star_product_swap (o : κ) (t : κ → ℂ) (i : κ) (hi : i ≠ o) :
    (∏ j, starMatrix o t (Equiv.swap o i j) j) =
      t i * ∏ j ∈ Finset.univ.erase o, t j := by
  let T : Finset κ := Finset.univ.erase o
  have hmem : i ∈ T := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩
  rw [← Finset.mul_prod_erase Finset.univ (fun j => starMatrix o t (Equiv.swap o i j) j)
    (Finset.mem_univ o)]
  change _ * (∏ j ∈ T, _) = t i * ∏ j ∈ T, t j
  rw [← Finset.mul_prod_erase T (fun j => starMatrix o t (Equiv.swap o i j) j) hmem,
    ← Finset.mul_prod_erase T t hmem, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have ht : ∏ j ∈ T.erase i, starMatrix o t (Equiv.swap o i j) j =
      ∏ j ∈ T.erase i, t j := by
    apply Finset.prod_congr rfl
    intro j hj
    obtain ⟨hji, hj⟩ := Finset.mem_erase.mp hj
    have hjo := (Finset.mem_erase.mp hj).1
    rw [Equiv.swap_apply_of_ne_of_ne hjo hji]
    simp [starMatrix, hjo]
  rw [ht]
  simp only [starMatrix, Matrix.of_apply, if_pos rfl, if_neg hi, if_neg (Ne.symm hi), if_true]
  ring

private theorem signedEvaluation_starMatrix (g : Equiv.Perm κ → ℂ) (o : κ) (t : κ → ℂ) :
    signedEvaluation g (starMatrix o t) =
      (∏ i ∈ Finset.univ.erase o, t i) *
        ∑ i ∈ Finset.univ.erase o, t i * (g 1 - g (Equiv.swap o i)) := by
  classical
  let T : Finset κ := Finset.univ.erase o
  let v (i : κ) : Equiv.Perm κ := Equiv.swap o i
  let f (σ : Equiv.Perm κ) : ℂ :=
    ((Equiv.Perm.sign σ : ℤ) : ℂ) * g σ * ∏ j, starMatrix o t (σ j) j
  have hv : Function.Injective v := by
    intro i j he
    simpa only [v, Equiv.swap_apply_left] using congrArg (fun σ : Equiv.Perm κ => σ o) he
  have h1 : (1 : Equiv.Perm κ) ∉ T.image v := by
    rintro h
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
    apply (Finset.mem_erase.mp hi).1
    simpa only [v, Equiv.swap_apply_left, Equiv.Perm.one_apply] using
      congrArg (fun σ : Equiv.Perm κ => σ o) he
  have hsum : ∑ σ, f σ = f 1 + ∑ i ∈ T, f (v i) := by
    calc
      _ = ∑ σ ∈ insert 1 (T.image v), f σ := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro σ _ hn
        by_contra hf
        have hs (j : κ) : starMatrix o t (σ j) j ≠ 0 := by
          intro hj
          apply hf
          have hp : (∏ k, starMatrix o t (σ k) k) = 0 :=
            Finset.prod_eq_zero (Finset.mem_univ j) hj
          simp only [f, hp, mul_zero]
        rcases starMatrix_supported o t σ hs with he | ⟨i, hi, he⟩
        · subst σ
          exact hn (Finset.mem_insert_self _ _)
        · exact hn (Finset.mem_insert_of_mem (Finset.mem_image.mpr
            ⟨i, Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩, he.symm⟩))
      _ = _ := by rw [Finset.sum_insert h1, Finset.sum_image (fun _ _ _ _ hij => hv hij)]
  have hterm (i : κ) (hi : i ∈ T) : f (v i) =
      - (t i * g (v i)) * ∏ j ∈ T, t j := by
    have hio := (Finset.mem_erase.mp hi).1
    dsimp only [f, v]
    rw [Equiv.Perm.sign_swap hio.symm, star_product_swap _ _ _ hio]
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
    ring
  have hbase : f 1 = (∑ i ∈ T, t i) * g 1 * ∏ j ∈ T, t j := by
    dsimp only [f]
    simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Equiv.Perm.one_apply,
      star_product_one]
    ring
  change ∑ σ, f σ = _
  rw [hsum, hbase]
  rw [Finset.sum_congr rfl hterm]
  rw [← Finset.sum_mul]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul]
  ring

private theorem signedEvaluation_starMatrix_relabel (g : Equiv.Perm κ → ℂ)
    (p : Equiv.Perm κ) (o : κ) (t : κ → ℂ) :
    signedEvaluation g ((starMatrix o t).submatrix p.symm id) =
      ((Equiv.Perm.sign p : ℤ) : ℂ) *
        signedEvaluation (fun σ => g (p * σ)) (starMatrix o t) := by
  unfold signedEvaluation
  rw [← Equiv.sum_comp (Equiv.mulLeft p) (fun σ =>
    ((Equiv.Perm.sign σ : ℤ) : ℂ) * g σ *
      ∏ j, ((starMatrix o t).submatrix p.symm id) (σ j) j), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  change ((Equiv.Perm.sign (p * σ) : ℤ) : ℂ) * g (p * σ) *
      (∏ j, starMatrix o t (p.symm ((p * σ) j)) (id j)) = _
  simp only [Equiv.Perm.mul_apply, Equiv.symm_apply_apply, id_eq, Equiv.Perm.sign_mul,
    Units.val_mul, Int.cast_mul]
  ring

private theorem signedEvaluation_eq_zero_on_row_balanced_const [Nonempty κ]
    (c : ℂ) (S : Matrix κ κ ℂ) (hS : ∀ i, ∑ j, S i j = 0) :
    signedEvaluation (fun _ => c) S = 0 := by
  have hdet : S.det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp (by
    refine ⟨fun _ => 1, ?_, ?_⟩
    · obtain ⟨i⟩ := ‹Nonempty κ›
      intro he
      exact one_ne_zero (congrFun he i)
    · funext i
      simpa only [Matrix.mulVec, dotProduct, mul_one, Pi.zero_apply] using hS i)
  have he : signedEvaluation (fun _ => c) S = c * S.det := by
    rw [signedEvaluation, Matrix.det_apply', Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  rw [he, hdet, mul_zero]

/-- Balanced matrices determine a complex function on permutations up to an
additive constant. All functions are permitted, including spectral profiles. -/
theorem signedEvaluation_zero_on_balanced_iff_constant [Nonempty κ]
    (g : Equiv.Perm κ → ℂ) :
    (∀ S : Matrix κ κ ℂ, (∀ i, ∑ j, S i j = 0) → (∀ j, ∑ i, S i j = 0) →
      signedEvaluation g S = 0) ↔ ∃ c, ∀ p, g p = c := by
  classical
  constructor
  · intro h
    have hlin (p : Equiv.Perm κ) (o : κ) (t : κ → ℂ) (ht : ∀ i, t i ≠ 0) :
        ∑ i ∈ Finset.univ.erase o, t i * (g p - g (p * Equiv.swap o i)) = 0 := by
      let S := (starMatrix o t).submatrix p.symm id
      have hr (i : κ) : ∑ j, S i j = 0 := starMatrix_row_sum o t (p.symm i)
      have hc (j : κ) : ∑ i, S i j = 0 := by
        change ∑ i, starMatrix o t (p.symm i) j = 0
        rw [Equiv.sum_comp p.symm (fun i => starMatrix o t i j)]
        simp_rw [starMatrix_symmetric o t _ j]
        exact starMatrix_row_sum o t j
      have he := h S hr hc
      change signedEvaluation g ((starMatrix o t).submatrix p.symm id) = 0 at he
      simp only [signedEvaluation_starMatrix_relabel, signedEvaluation_starMatrix, mul_one] at he
      have hn : (((Equiv.Perm.sign p : ℤ) : ℂ)) ≠ 0 := by
        exact_mod_cast (Units.ne_zero (Equiv.Perm.sign p))
      exact (mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hn)).resolve_left
        (Finset.prod_ne_zero_iff.mpr fun i _ => ht i)
    have hs (p : Equiv.Perm κ) (o i : κ) (hi : i ≠ o) : g (p * Equiv.swap o i) = g p := by
      let d (j : κ) : ℂ := g p - g (p * Equiv.swap o j)
      let t (j : κ) : ℂ := if j = i then 2 else 1
      have hb := hlin p o (fun _ => 1) (fun _ => one_ne_zero)
      have ht := hlin p o t (fun j => by by_cases hj : j = i <;> simp [t, hj])
      have he (j : κ) : t j * d j = d j + if j = i then d i else 0 := by
        by_cases hj : j = i
        · subst j
          simp [t, two_mul]
        · simp [t, hj]
      change (∑ j ∈ Finset.univ.erase o, 1 * d j) = 0 at hb
      simp only [one_mul] at hb
      change (∑ j ∈ Finset.univ.erase o, t j * d j) = 0 at ht
      simp_rw [he, Finset.sum_add_distrib] at ht
      rw [hb, zero_add, Finset.sum_eq_single i] at ht
      · rw [if_pos rfl] at ht
        exact (sub_eq_zero.mp ht).symm
      · intro j _ hj
        rw [if_neg hj]
      · simp [hi]
    refine ⟨g 1, fun p => ?_⟩
    refine Equiv.Perm.swap_induction_on' p rfl (fun q i j hij ih => ?_)
    exact (hs q i j hij.symm).trans ih
  · rintro ⟨c, hc⟩ S hS _
    have he : g = fun _ => c := funext hc
    rw [he]
    exact signedEvaluation_eq_zero_on_row_balanced_const c S hS

end
end MOC.SpectralProfile
