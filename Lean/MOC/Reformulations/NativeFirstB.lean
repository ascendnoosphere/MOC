import MOC.Reformulations.FirstUnitary
import MOC.Reformulations.SecondNative
import MOC.Reformulations.SecondReal
import MOC.Normal

/-! Finite operator lemmas for native forms 068–133. No spectral relabelling
by arbitrary complex functions is used: the displayed lists are the actual
characteristic roots of the specified operators, counted with multiplicity. -/

open BigOperators Matrix

namespace MOC.Reformulations.NativeFirstB

noncomputable section

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- Actual characteristic roots with multiplicity. -/
def HasRoots {n : ℕ} (A : Mat n) (a : Fin n → ℂ) : Prop :=
  A.charpoly.roots = (Finset.univ : Finset (Fin n)).val.map a

/-- The determinant hull for actual finite operators in a fixed frame. -/
def OperatorHull {n : ℕ} (A B U : Mat n) (a b : Fin n → ℂ) : Prop :=
  (A + U * B * Uᴴ).det ∈ convexHull ℝ (Set.range (matchingProduct a b))

theorem unitaryMul {n : ℕ} {U V : Mat n} (hU : IsUnitary U) (hV : IsUnitary V) :
    IsUnitary (U * V) := by
  have h : IsUnitary Uᴴ := ⟨by simpa using hU.2, by simpa using hU.1⟩
  simpa using relative_unitary Uᴴ V h hV

theorem operatorHull_of_spectral {n : ℕ} (A B U : Mat n) (a b : Fin n → ℂ)
    (hA : IsStarNormal A) (hB : IsStarNormal B) (hU : IsUnitary U)
    (ha : HasRoots A a) (hb : HasRoots B b)
    (h : ∀ (e f : Equiv.Perm (Fin n)) (V : Mat n), IsUnitary V → Holds (a ∘ e) (b ∘ f) V) : OperatorHull A B U a b := by
  obtain ⟨a', V, hV, rfl⟩ := exists_unitary_diagonalization A hA
  obtain ⟨b', W, hW, rfl⟩ := exists_unitary_diagonalization B hB
  unfold HasRoots at ha hb
  rw [roots_unitary_diagonalization a' hV] at ha
  rw [roots_unitary_diagonalization b' hW] at hb
  obtain ⟨e, rfl⟩ := exists_perm_of_equal_multisets a a' ha.symm
  obtain ⟨f, rfl⟩ := exists_perm_of_equal_multisets b b' hb.symm
  let T := U * W
  have ht : IsUnitary T := unitaryMul hU hW
  have hB' : U * (W * diagonal b' * Wᴴ) * Uᴴ = T * diagonal b' * Tᴴ := by
    simp only [T, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  unfold OperatorHull
  rw [hB', determinantValue_relative a' b' V T hV]
  have hz := h e.symm f.symm (Vᴴ * T) (relative_unitary V T hV ht)
  have hae : (a' ∘ e) ∘ e.symm = a' := by funext j; simp
  have hbf : (b' ∘ f) ∘ f.symm = b' := by funext j; simp
  rw [hae, hbf] at hz
  unfold Holds at hz
  rw [matchingRange_relabel]
  exact hz

theorem operatorHull_of_moc (h : MOCIsTrue) {n : ℕ} (A B U : Mat n) (a b : Fin n → ℂ)
    (hA : IsStarNormal A) (hB : IsStarNormal B) (hU : IsUnitary U)
    (ha : HasRoots A a) (hb : HasRoots B b) : OperatorHull A B U a b :=
  operatorHull_of_spectral A B U a b hA hB hU ha hb (fun e f V hV => h n (a ∘ e) (b ∘ f) V hV)

theorem realOperatorHull {n : ℕ} (A B U : Mat n) (a b : Fin n → ℝ)
    (hA : IsStarNormal A) (hB : IsStarNormal B) (hU : IsUnitary U)
    (ha : HasRoots A (fun j => a j)) (hb : HasRoots B (fun j => b j)) :
    OperatorHull A B U (fun j => a j) (fun j => b j) :=
  operatorHull_of_spectral A B U _ _ hA hB hU ha hb
    (fun e f V hV => holds_of_real_spectra (a ∘ e) (b ∘ f) V hV)

/-- 068: signed Dirac eigenvalues, on the chosen self-adjoint finite blocks. -/
theorem diracBlockHull {n : ℕ} (A B U : Mat n) (a b : Fin n → ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hU : IsUnitary U)
    (ha : HasRoots A (fun j => a j)) (hb : HasRoots B (fun j => b j)) :
    OperatorHull A B U (fun j => a j) (fun j => b j) :=
  by
  have hNA : IsStarNormal A := ⟨by change Commute Aᴴ A; rw [hA.eq]⟩
  have hNB : IsStarNormal B := ⟨by change Commute Bᴴ B; rw [hB.eq]⟩
  exact realOperatorHull A B U a b hNA hNB hU ha hb

/-- 069: the finite shifted determinant of the actual singular-value lists.
No limit or Dixmier trace is asserted. -/
theorem shiftedSingularValueHull {n : ℕ} (a b : Fin n → ℝ) (U : Mat n)
    (hU : IsUnitary U) :
    (1 + diagonal (fun j => (a j : ℂ)) + U * diagonal (fun j => (b j : ℂ)) * Uᴴ).det ∈
      convexHull ℝ (Set.range (fun σ : Equiv.Perm (Fin n) =>
        ∏ j, (1 + (a (σ j) : ℂ) + b j))) := by
  have hd : diagonal (fun j => ((1 + a j : ℝ) : ℂ)) =
      (1 : Mat n) + diagonal (fun j => (a j : ℂ)) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
  have hh := holds_of_real_spectra (fun j => 1 + a j) b U hU
  unfold Holds determinantValue at hh
  rw [hd] at hh
  simpa only [matchingProduct, Complex.ofReal_add, Complex.ofReal_one] using hh

/-! 070: `InvertibleRepresentativeForm` in `SecondReal` proves the exact
endpoint determinant statement (with its singular extension). It does not
prove the Jacobi/integral identity for piecewise smooth invertible paths,
or identify the period group of a Banach-algebra trace.

071: the finite relative operator is an Euler determinant. The trace-class
Fredholm determinant and closure over finite permutations of an infinite
spectral sequence are not replaced here by a finite hull. -/

/-- 071: the actual finite relative determinant with nonzero scalar reference. -/
def FinitePerturbationForm : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℂ) (U : Mat n) (z : ℂ), z ≠ 0 → IsUnitary U →
    ((1 : Mat n) - z⁻¹ • (diagonal a + U * diagonal b * Uᴴ)).det ∈
      convexHull ℝ (Set.range (fun σ : Equiv.Perm (Fin n) =>
        ∏ j, (1 - z⁻¹ * (a (σ j) + b j))))

theorem finitePerturbationForm_iff : FinitePerturbationForm ↔ MOCIsTrue := by
  constructor
  · intro h
    apply (fixedEulerParameterForm_iff (one_ne_zero : (1 : ℂ) ≠ 0)).mp
    intro n a b U hU _ _
    simpa only [inv_one] using h n a b U 1 one_ne_zero hU
  · intro h n a b U z _ hU
    exact finiteEulerForm_iff.mpr h n a b U z⁻¹ hU

/-- 072 and 122: actual channel and Maslov phase spectra. The eigenvalues
are not replaced by functions of the phases. -/
theorem unitaryPhaseOperatorHull {n : ℕ} (A B U : Mat n) (a b : Fin n → ℂ)
    (hA : IsStarNormal A) (hB : IsStarNormal B) (hU : IsUnitary U)
    (ha : HasRoots A a) (hb : HasRoots B b)
    (ha₁ : ∀ j, Complex.normSq (a j) = 1)
    (hb₁ : ∀ j, Complex.normSq (b j) = 1) : OperatorHull A B U a b :=
  operatorHull_of_spectral A B U a b hA hB hU ha hb
    (fun e f V hV => unitarySpectralHull (a ∘ e) (b ∘ f) (fun j => ha₁ (e j)) (fun j => hb₁ (f j)) V hV)

end

end MOC.Reformulations.NativeFirstB
