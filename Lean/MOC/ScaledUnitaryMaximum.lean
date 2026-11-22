import MOC.ConcentricScalarMaximum
import MOC.CommonCommutant
import MOC.Normal
import MOC.Support

/-! Removing the eigenbasis assumption in the concentric-circle maximum theorem. -/

open Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem adjoint_unitary (U : Matrix ι ι ℂ) (hU : IsUnitary U) : IsUnitary Uᴴ := by
  simpa only [IsUnitary, Matrix.conjTranspose_conjTranspose] using And.intro hU.2 hU.1

private noncomputable def similarity (Q : Matrix ι ι ℂ) (hQ : IsUnitary Q) : Matrix ι ι ℂ →+* Matrix ι ι ℂ where
  toFun X := Q * X * Qᴴ
  map_one' := by rw [Matrix.mul_one, hQ.1]
  map_zero' := by rw [Matrix.mul_zero, Matrix.zero_mul]
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_mul' X Y := by
    change Q * (X * Y) * Qᴴ = Q * X * Qᴴ * (Q * Y * Qᴴ)
    rw [show Q * (X * Y) * Qᴴ = Q * X * (1 : Matrix ι ι ℂ) * Y * Qᴴ by
      simp only [Matrix.mul_one, Matrix.mul_assoc]]
    rw [← hQ.2]
    simp only [Matrix.mul_assoc]

private theorem similarity_apply (Q : Matrix ι ι ℂ) (hQ : IsUnitary Q) (X : Matrix ι ι ℂ) :
    similarity Q hQ X = Q * X * Qᴴ := rfl

private theorem similarity_unconj (Q : Matrix ι ι ℂ) (hQ : IsUnitary Q) (X : Matrix ι ι ℂ) :
    similarity Qᴴ (adjoint_unitary Q hQ) (similarity Q hQ X) = X := by
  simp only [similarity_apply, Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc, hQ.2,
    Matrix.one_mul]
  rw [Matrix.mul_assoc X Qᴴ Q, hQ.2, Matrix.mul_one]

private theorem similarity_star (Q : Matrix ι ι ℂ) (hQ : IsUnitary Q) (X : Matrix ι ι ℂ) :
    (similarity Q hQ X)ᴴ = similarity Q hQ Xᴴ := by
  simp only [similarity_apply, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

private theorem similarity_smul (Q : Matrix ι ι ℂ) (hQ : IsUnitary Q) (z : ℂ) (X : Matrix ι ι ℂ) :
    similarity Q hQ (z • X) = z • similarity Q hQ X := by
  simp only [similarity_apply, Matrix.mul_smul, Matrix.smul_mul]

private theorem similarity_unitary (Q : Matrix ι ι ℂ) (hQ : IsUnitary Q)
    (X : Matrix ι ι ℂ) (hX : IsUnitary X) : IsUnitary (similarity Q hQ X) := by
  constructor <;> rw [similarity_star, ← map_mul]
  · rw [hX.1, map_one]
  · rw [hX.2, map_one]

/-- Two scaled unitaries at a support maximum commute in order greater than
two if their common commutant is scalar and their positive radii differ. -/
theorem commute_of_scaled_unitary_maximum
    (A B : Matrix ι ι ℂ) (hA : IsUnitary A) (hB : IsUnitary B)
    (t : ℝ) (ht : 0 < t) (hlt : t < 1) (η : ℂ) (hη : η ≠ 0) (hcard : 2 < Fintype.card ι)
    (hcomm : ∀ Y : Matrix ι ι ℂ, Commute A Y → Commute B Y →
      ∃ c : ℂ, Y = c • (1 : Matrix ι ι ℂ))
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * (A + V * ((t : ℂ) • B) * Vᴴ).det).re ≤ (η * (A + (t : ℂ) • B).det).re) :
    Commute A B := by
  let W := Aᴴ * B
  have hW := relative_unitary A B hA hB
  have hWnormal : IsStarNormal W := by
    constructor
    change Wᴴ * W = W * Wᴴ
    exact hW.2.trans hW.1.symm
  obtain ⟨w, Q, hQ, hWdiag⟩ := exists_unitary_diagonalization W hWnormal
  let f := similarity Qᴴ (adjoint_unitary Q hQ)
  let g := similarity Q hQ
  have hf (X : Matrix ι ι ℂ) : f (g X) = X := similarity_unconj Q hQ X
  have hg (X : Matrix ι ι ℂ) : g (f X) = X := by
    simpa only [f, g, Matrix.conjTranspose_conjTranspose] using
      similarity_unconj Qᴴ (adjoint_unitary Q hQ) X
  have hfW : f W = diagonal w := by rw [hWdiag]; exact hf (diagonal w)
  have hdu : IsUnitary (diagonal w) := by
    rw [← hfW]
    exact similarity_unitary _ _ W hW
  have hw (i : ι) : Complex.normSq (w i) = 1 := by
    have he := congrArg (fun M : Matrix ι ι ℂ => M i i) hdu.1
    apply Complex.ofReal_injective
    simpa only [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq,
      Matrix.one_apply_eq, Pi.mul_apply, Pi.star_apply, Complex.star_def, Complex.mul_conj,
      Complex.ofReal_one] using he
  have hAW : A * W = B := by simp only [W, ← Matrix.mul_assoc, hA.1, Matrix.one_mul]
  have hfB : f B = f A * diagonal w := by rw [← hAW, map_mul, hfW]
  have hAB (Y : Matrix ι ι ℂ) (ha : Commute (f A) Y) (hb : Commute (diagonal w) Y) :
      ∃ c : ℂ, Y = c • (1 : Matrix ι ι ℂ) := by
    have hb' : Commute (f B) Y := by rw [hfB]; exact ha.mul_left hb
    obtain ⟨c, hc⟩ := hcomm (g Y)
      (by simpa only [hg] using ha.map g) (by simpa only [hg] using hb'.map g)
    refine ⟨c, ?_⟩
    calc
      Y = f (g Y) := (hf Y).symm
      _ = _ := by rw [hc, similarity_smul, map_one]
  have hfdet (X : Matrix ι ι ℂ) : (f X).det = X.det := by
    exact det_unitary_conjugation Qᴴ X (adjoint_unitary Q hQ)
  have hmax' (R : Matrix ι ι ℂ) (hR : IsUnitary R) :
      (η * (f A + R * ((t : ℂ) • (f A * diagonal w)) * Rᴴ).det).re ≤
        (η * (f A + (t : ℂ) • (f A * diagonal w)).det).re := by
    have hleft : f (A + g R * ((t : ℂ) • B) * (g R)ᴴ) =
        f A + R * ((t : ℂ) • f B) * Rᴴ := by
      have hstar : f ((g R)ᴴ) = Rᴴ := by rw [← similarity_star, hf]
      rw [map_add, map_mul, map_mul, similarity_smul, hf, hstar]
    have hright : f (A + (t : ℂ) • B) = f A + (t : ℂ) • f B := by
      rw [map_add, similarity_smul]
    rw [← hfB, ← hleft, ← hright, hfdet, hfdet]
    exact hmax (g R) (similarity_unitary _ _ R hR)
  have hsame := relative_unitary_scalar_of_support_maximum (f A) (similarity_unitary _ _ A hA)
    w hw t ht hlt η hη hcard hAB hmax'
  have hne : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  let i₀ := Classical.choice hne
  have hws : diagonal w = w i₀ • (1 : Matrix ι ι ℂ) := by
    rw [Matrix.smul_one_eq_diagonal]
    exact congrArg diagonal (funext fun i => hsame i i₀)
  have hcomm' : Commute (f A) (f B) := by
    rw [hfB, hws, Matrix.mul_smul, Matrix.mul_one]
    exact (Commute.refl (f A)).smul_right _
  simpa only [hg] using hcomm'.map g

private theorem unitary_diagonal_of_normSq_one (a : ι → ℂ)
    (ha : ∀ i, Complex.normSq (a i) = 1) : IsUnitary (diagonal a) := by
  have he (i : ι) : a i * star (a i) = 1 := by
    simp only [Complex.star_def, Complex.mul_conj, ha, Complex.ofReal_one]
  have he' (i : ι) : star (a i) * a i = 1 := by rw [mul_comm, he]
  constructor
  · rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    simp only [Pi.mul_apply, Pi.star_apply, he, Matrix.diagonal_one]
  · rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    simp only [Pi.mul_apply, Pi.star_apply, he', Matrix.diagonal_one]

private theorem holds_of_simple_concentric_aux {n : ℕ}
    (t : ℝ) (ht : 0 < t) (hlt : t < 1)
    (hbelow : ∀ m < n, ∀ (a b : Fin m → ℂ),
      (∀ i, Complex.normSq (a i) = 1) → (∀ i, Complex.normSq (b i) = 1) →
      Function.Injective a → Function.Injective b →
      ∀ U : Matrix (Fin m) (Fin m) ℂ, IsUnitary U → Holds a (fun i => (t : ℂ) * b i) U)
    (a b : Fin n → ℂ)
    (ha : ∀ i, Complex.normSq (a i) = 1) (hb : ∀ i, Complex.normSq (b i) = 1)
    (haInj : Function.Injective a) (hbInj : Function.Injective b)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) :
    Holds a (fun i => (t : ℂ) * b i) U := by
  by_cases hn : n ≤ 3
  · exact conjecture_le_three hn a _ U hU
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let d (i : Fin n) := (t : ℂ) * b i
  change Holds a d U
  by_contra hbad
  rw [holds_iff_directional] at hbad
  push_neg at hbad
  obtain ⟨η, hsep⟩ := hbad
  have hη : η ≠ 0 := by
    intro h
    subst η
    simpa using hsep (Equiv.refl _)
  obtain ⟨V, hV, hvmax⟩ := exists_support_maximizer a d η
  have hfail : ¬ Holds a d V := by
    intro h
    obtain ⟨σ, hσ⟩ := (holds_iff_directional a d V).mp h η
    exact (not_le_of_gt (hsep σ)) ((hvmax U hU).trans hσ)
  have hcut : ¬ HasProperPairedBlocks V := by
    rintro ⟨m, k, er, ec, P, Q, hm, hk, hsplit⟩
    have hcard := Fintype.card_congr er
    simp only [Fintype.card_sum, Fintype.card_fin] at hcard
    have hBlocksUnitary : IsUnitary (fromBlocks P 0 0 Q) := hsplit ▸ unitary_reindex er ec hV
    obtain ⟨hP, hQ⟩ := unitary_directSum_iff.mp hBlocksUnitary
    have hleft := hbelow m (by omega) (fun i => a (er (.inl i))) (fun i => b (ec (.inl i)))
      (fun i => ha (er (.inl i))) (fun i => hb (ec (.inl i)))
      (haInj.comp (er.injective.comp Sum.inl_injective))
      (hbInj.comp (ec.injective.comp Sum.inl_injective)) P hP
    have hright := hbelow k (by omega) (fun i => a (er (.inr i))) (fun i => b (ec (.inr i)))
      (fun i => ha (er (.inr i))) (fun i => hb (ec (.inr i)))
      (haInj.comp (er.injective.comp Sum.inr_injective))
      (hbInj.comp (ec.injective.comp Sum.inr_injective)) Q hQ
    have hsum (f : Fin n → ℂ) (e : Fin m ⊕ Fin k ≃ Fin n) :
        Sum.elim (fun i => f (e (.inl i))) (fun i => f (e (.inr i))) = f ∘ e := by
      funext i
      cases i <;> rfl
    apply hfail
    apply (holds_reindex_iff er ec a d V).mp
    rw [hsplit, ← hsum a er, ← hsum d ec]
    exact holds_directSum _ _ _ _ P Q hleft hright
  let A := diagonal a
  let B := V * diagonal b * Vᴴ
  have hA : IsUnitary A := unitary_diagonal_of_normSq_one a ha
  have hB : IsUnitary B := similarity_unitary V hV (diagonal b) (unitary_diagonal_of_normSq_one b hb)
  have hc (Y : Matrix (Fin n) (Fin n) ℂ) (hAY : Commute A Y) (hBY : Commute B Y) :=
    scalar_of_commute_simple_summands hV hcut haInj hbInj Y hAY hBY
  have hmax (W : Matrix (Fin n) (Fin n) ℂ) (hW : IsUnitary W) :
      (η * (A + W * ((t : ℂ) • B) * Wᴴ).det).re ≤ (η * (A + (t : ℂ) • B).det).re := by
    have huw : IsUnitary (W * V) := by
      simpa only [Matrix.conjTranspose_conjTranspose] using
        relative_unitary Wᴴ V (adjoint_unitary W hW) hV
    have he : diagonal d = (t : ℂ) • diagonal b := Matrix.diagonal_smul (t : ℂ) b
    simpa only [determinantValue, he, A, B, Matrix.conjTranspose_mul,
      Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul] using hvmax (W * V) huw
  have hAB := commute_of_scaled_unitary_maximum A B hA hB t ht hlt η hη
    (by rw [Fintype.card_fin]; omega) hc hmax
  have hdiag : B = diagonal B.diag := by
    ext i j : 1
    by_cases hij : i = j
    · subst j
      simp
    · have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) hAB.eq
      change (diagonal a * B) i j = (B * diagonal a) i j at he
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm (B i j)] at he
      have hz : (a i - a j) * B i j = 0 := by rw [sub_mul, he, sub_self]
      rw [Matrix.diagonal_apply_ne _ hij]
      exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr fun h => hij (haInj h))
  have hBd : V * diagonal d * Vᴴ = diagonal (fun i => (t : ℂ) * B i i) := by
    change V * diagonal ((t : ℂ) • b) * Vᴴ = diagonal ((t : ℂ) • B.diag)
    rw [Matrix.diagonal_smul, Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]
    change (t : ℂ) • B = (t : ℂ) • diagonal B.diag
    rw [← hdiag]
  have hOne : IsUnitary (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [IsUnitary]
  apply hfail
  exact holds_of_joint_unitary_diagonalization a d a (fun i => (t : ℂ) * B i i)
    hV hOne (by simp) (by simpa only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one] using hBd)

/-- The determinant inclusion for simple concentric spectra of normalized
radii one and `t`, in every finite order. -/
theorem holds_of_simple_concentric {n : ℕ} (t : ℝ) (ht : 0 < t) (hlt : t < 1)
    (a b : Fin n → ℂ) (ha : ∀ i, Complex.normSq (a i) = 1) (hb : ∀ i, Complex.normSq (b i) = 1)
    (haInj : Function.Injective a) (hbInj : Function.Injective b)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) : Holds a (fun i => (t : ℂ) * b i) U := by
  revert a b ha hb haInj hbInj U hU
  induction n using Nat.strong_induction_on with
  | h n ih => exact holds_of_simple_concentric_aux t ht hlt ih

end MOC
