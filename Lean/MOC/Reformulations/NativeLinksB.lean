import MOC.Reformulations.FirstGeometric

/-! Exact native matrix links for the normalized projective lifts and the
commuting quantum integrals. Both comparisons use the spectra of the
selected matrices. -/

open Matrix BigOperators

namespace MOC.Reformulations.NativeLinksB
noncomputable section

/-- Projective transformations with specified invertible, normal linear lifts.
Both determinants refer to these fixed representatives, not projective ratios. -/
def ProjectiveLiftForm : Prop :=
  ∀ (n : ℕ) (A B U : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ),
    IsStarNormal A → IsStarNormal B → IsUnit A.det → IsUnit B.det → IsUnitary U →
    A.charpoly.roots = (Finset.univ : Finset (Fin n)).val.map a →
    B.charpoly.roots = (Finset.univ : Finset (Fin n)).val.map b →
    (A + U * B * Uᴴ).det ∈ convexHull ℝ (Set.range (matchingProduct a b))

private theorem diagonal_normal {n : ℕ} (a : Fin n → ℂ) :
    IsStarNormal (diagonal a) := by
  constructor
  change Commute (diagonal a)ᴴ (diagonal a)
  rw [Matrix.diagonal_conjTranspose, Commute, SemiconjBy,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  exact congrArg Matrix.diagonal (funext fun _ => mul_comm _ _)

theorem projectiveLiftForm_iff : ProjectiveLiftForm ↔ MOCIsTrue := by
  constructor
  · intro h
    apply moc_iff_projectiveDiagonalLifts.mpr
    intro n a b U ha hb hU
    have hroots (s : Fin n → ℂ) :
        (diagonal s).charpoly.roots = (Finset.univ : Finset (Fin n)).val.map s := by
      simpa using roots_unitary_diagonalization s
        (isUnitary_one (ι := Fin n))
    exact h n _ _ U a b (diagonal_normal a) (diagonal_normal b) ha hb hU (hroots a) (hroots b)
  · intro h n A B U a b hA hB _ _ hU ha hb
    exact moc_iff_complexMatrices.mp h n A B U a b hA hB hU ha hb

/-- An enumeration of the joint eigenvalue vectors of a self-adjoint tuple.
One unitary works for all entries of the tuple; repetitions are permitted.
Such a witness encodes internal commutation and self-adjointness. -/
def HasRealJointSpectrum {n r : ℕ} (A : Fin r → Matrix (Fin n) (Fin n) ℂ)
    (a : Fin n → Fin r → ℝ) : Prop :=
  ∃ V : Matrix (Fin n) (Fin n) ℂ, IsUnitary V ∧
    ∀ k, A k = V * diagonal (fun j => (a j k : ℂ)) * Vᴴ

/-- The actual linear evaluation used in the integrable-systems comparison. -/
def evaluateSpectrum {n r : ℕ} (c : Fin r → ℂ) (a : Fin n → Fin r → ℝ)
    (j : Fin n) : ℂ :=
  ∑ k, c k * a j k

private theorem evaluateTuple_joint {n r : ℕ} (c : Fin r → ℂ)
    (A : Fin r → Matrix (Fin n) (Fin n) ℂ) (a : Fin n → Fin r → ℝ)
    (V : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ k, A k = V * diagonal (fun j => (a j k : ℂ)) * Vᴴ) :
    (∑ k, c k • A k) = V * diagonal (evaluateSpectrum c a) * Vᴴ := by
  have hs : (∑ k, c k • A k) =
      ∑ k, V * (c k • diagonal (fun j => (a j k : ℂ))) * Vᴴ := by
    apply Finset.sum_congr rfl
    intro k _
    rw [h k, Matrix.mul_smul, Matrix.smul_mul]
  rw [hs, ← Matrix.sum_mul, ← Matrix.mul_sum]
  congr 2
  ext i j
  by_cases hij : i = j
  · subst j
    simp [evaluateSpectrum, Matrix.sum_apply, smul_eq_mul]
  · simp [Matrix.sum_apply, Matrix.diagonal_apply_ne _ hij, hij]

/-- For actual commuting Hermitian tuples on the two sides, in any complex
linear direction, the determinant is in the corresponding matching hull.
The weights may depend on the direction. -/
def QuantumIntegralsForm : Prop :=
  ∀ (n r : ℕ) (A B : Fin r → Matrix (Fin n) (Fin n) ℂ)
    (a b : Fin n → Fin r → ℝ) (c : Fin r → ℂ) (U : Matrix (Fin n) (Fin n) ℂ),
    HasRealJointSpectrum A a → HasRealJointSpectrum B b → IsUnitary U →
    ((∑ k, c k • A k) + U * (∑ k, c k • B k) * Uᴴ).det ∈
      convexHull ℝ (Set.range (matchingProduct (evaluateSpectrum c a) (evaluateSpectrum c b)))

theorem quantumIntegralsForm_iff : QuantumIntegralsForm ↔ MOCIsTrue := by
  classical
  constructor
  · intro h n a b U hU
    let a' (j : Fin n) : Fin 2 → ℝ := ![(a j).re, (a j).im]
    let b' (j : Fin n) : Fin 2 → ℝ := ![(b j).re, (b j).im]
    let c : Fin 2 → ℂ := ![1, Complex.I]
    let A (k : Fin 2) := diagonal (fun j => (a' j k : ℂ))
    let B (k : Fin 2) := diagonal (fun j => (b' j k : ℂ))
    have h1 : IsUnitary (1 : Matrix (Fin n) (Fin n) ℂ) := isUnitary_one
    have hA : ∀ k, A k = 1 * diagonal (fun j => (a' j k : ℂ)) *
        (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ := by intro k; simp [A]
    have hB : ∀ k, B k = 1 * diagonal (fun j => (b' j k : ℂ)) *
        (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ := by intro k; simp [B]
    have ha : evaluateSpectrum c a' = a := by
      funext j
      simp [a', c, evaluateSpectrum, Fin.sum_univ_two, mul_comm Complex.I, Complex.re_add_im]
    have hb : evaluateSpectrum c b' = b := by
      funext j
      simp [b', c, evaluateSpectrum, Fin.sum_univ_two, mul_comm Complex.I, Complex.re_add_im]
    have hr := h n 2 A B a' b' c U ⟨1, h1, hA⟩ ⟨1, h1, hB⟩ hU
    rw [evaluateTuple_joint c A a' 1 hA, evaluateTuple_joint c B b' 1 hB, ha, hb] at hr
    simpa [Holds, determinantValue] using hr
  · intro h n r A B a b c U ⟨V, hV, hv⟩ ⟨W, hW, hw⟩ hU
    rw [evaluateTuple_joint c A a V hv, evaluateTuple_joint c B b W hw]
    exact moc_iff_normalFrames.mp h n (evaluateSpectrum c a) (evaluateSpectrum c b) V W U hV hW hU

end

end MOC.Reformulations.NativeLinksB
