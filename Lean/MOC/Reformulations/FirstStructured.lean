import MOC.Reformulations.FirstMatrix
import Mathlib.Data.Sym.Basic

/-! Compound spectral constructions in their genuine index spaces, and several
restricted determinant statements. The degree-one witnesses prove equivalence
of the families, not equivalence at every fixed higher degree. -/

open BigOperators Matrix

namespace MOC.Reformulations
noncomputable section

private theorem conjecture_fintype (h : MOCIsTrue) (ι : Type)
    [Fintype ι] [DecidableEq ι] : Conjecture ι :=
  (conjecture_reindex_iff (Fintype.equivFin ι)).mpr (h (Fintype.card ι))

private theorem holds_of_equiv {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : κ ≃ ι)
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (_hU : IsUnitary U)
    (h : Holds (a ∘ e) (b ∘ e) (U.submatrix e e)) :
    Holds a b U :=
  (holds_reindex_iff e e a b U).mp h

/-- In the exterior eigenbasis the entries are products over
subsets, counted once for each exterior basis vector. -/
def exteriorSpectrum : Prop :=
  ∀ (n k m : ℕ) (_ : 1 ≤ k) (_ : k ≤ n)
    (e : Fin m ≃ {s : Finset (Fin n) // s.card = k})
    (a b : Fin n → ℂ) (U : Matrix (Fin m) (Fin m) ℂ),
    IsUnitary U →
    Holds (fun i => ∏ j ∈ (e i).val, a j) (fun i => ∏ j ∈ (e i).val, b j) U

private def oneSubset (n : ℕ) : Fin n ≃ {s : Finset (Fin n) // s.card = 1} :=
  Equiv.ofBijective (fun i => ⟨{i}, Finset.card_singleton i⟩) (by
    constructor
    · intro i j h
      have hs : ({i} : Finset (Fin n)) = {j} := congrArg Subtype.val h
      have hi : i ∈ ({j} : Finset (Fin n)) := hs ▸ Finset.mem_singleton_self i
      exact Finset.mem_singleton.mp hi
    · rintro ⟨s, hs⟩
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hs
      exact ⟨i, rfl⟩)

theorem moc_iff_exteriorSpectrum : MOCIsTrue ↔ exteriorSpectrum := by
  constructor
  · intro h n k m _ _ e a b U hU
    exact h m _ _ U hU
  · intro h n a b U hU
    by_cases hn : 1 ≤ n
    · have hh := h n 1 n le_rfl hn (oneSubset n) a b U hU
      change Holds (fun i => ∏ j ∈ ({i} : Finset (Fin n)), a j)
        (fun i => ∏ j ∈ ({i} : Finset (Fin n)), b j) U at hh
      simpa only [Finset.prod_singleton] using hh
    · exact conjecture_le_three (by omega) a b U hU

/-- Multiset-indexed eigenvalue monomials of the symmetric
power. A multiset records the exponents of exactly one basis monomial. -/
def symmetricSpectrum : Prop :=
  ∀ (n k m : ℕ) (_ : 1 ≤ k) (e : Fin m ≃ Sym (Fin n) k)
    (a b : Fin n → ℂ) (U : Matrix (Fin m) (Fin m) ℂ),
    IsUnitary U →
    Holds (fun i => ((e i).toMultiset.map a).prod)
      (fun i => ((e i).toMultiset.map b).prod) U

private def oneSym (n : ℕ) : Fin n ≃ Sym (Fin n) 1 :=
  Equiv.ofBijective (fun i => ⟨{i}, Multiset.card_singleton i⟩) (by
    constructor
    · intro i j h
      have hs : ({i} : Multiset (Fin n)) = {j} := congrArg Subtype.val h
      have hi : i ∈ ({j} : Multiset (Fin n)) := hs ▸ Multiset.mem_singleton_self i
      exact Multiset.mem_singleton.mp hi
    · rintro ⟨s, hs⟩
      obtain ⟨i, rfl⟩ := Multiset.card_eq_one.mp hs
      exact ⟨i, rfl⟩)

theorem moc_iff_symmetricSpectrum : MOCIsTrue ↔ symmetricSpectrum := by
  constructor
  · intro h n k m _ e a b U hU
    exact h m _ _ U hU
  · intro h n a b U hU
    have hh := h n 1 n le_rfl (oneSym n) a b U hU
    change Holds (fun i => (({i} : Multiset (Fin n)).map a).prod)
      (fun i => (({i} : Multiset (Fin n)).map b).prod) U at hh
    simpa only [Multiset.map_singleton, Multiset.prod_singleton] using hh

/-- The full tensor-product spectrum, with multiplicity indexed by
pairs of eigenvectors. -/
def tensorSpectrum : Prop :=
  ∀ (m n : ℕ) (a c : Fin m → ℂ) (b d : Fin n → ℂ)
    (U : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ),
    IsUnitary U →
    Holds (fun i => a i.1 * b i.2) (fun i => c i.1 * d i.2) U

private def prodFinOne (n : ℕ) : Fin n × Fin 1 ≃ Fin n where
  toFun i := i.1
  invFun i := (i, 0)
  left_inv _ := Prod.ext rfl (Subsingleton.elim _ _)
  right_inv _ := rfl

theorem moc_iff_tensorSpectrum : MOCIsTrue ↔ tensorSpectrum := by
  constructor
  · intro h m n a c b d U hU
    exact conjecture_fintype h (Fin m × Fin n) _ _ U hU
  · intro h n a b U hU
    let e := prodFinOne n
    have hh := h n 1 a b (fun _ => 1) (fun _ => 1) (U.submatrix e e)
      (unitary_reindex e e hU)
    exact holds_of_equiv e a b U hU (by simpa [e, prodFinOne, Function.comp_def] using hh)

/-- Direct sums of two nonempty spectral lists. The relative
unitary is allowed to mix between the two blocks. -/
def directSumSpectrum : Prop :=
  ∀ (m n : ℕ) (_ : 0 < m) (_ : 0 < n) (a c : Fin m → ℂ) (b d : Fin n → ℂ)
    (U : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ), IsUnitary U →
    Holds (Sum.elim a b) (Sum.elim c d) U

theorem moc_iff_directSumSpectrum : MOCIsTrue ↔ directSumSpectrum := by
  constructor
  · intro h m n _ _ a c b d U hU
    exact conjecture_fintype h (Fin m ⊕ Fin n) _ _ U hU
  · intro h n a b U hU
    cases n with
    | zero => exact conjecture_le_three (by decide) a b U hU
    | succ n =>
      by_cases hn : 0 < n
      · let e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv
        have hh := h n 1 hn (by decide)
          (a ∘ e ∘ Sum.inl) (b ∘ e ∘ Sum.inl) (a ∘ e ∘ Sum.inr) (b ∘ e ∘ Sum.inr)
          (U.submatrix e e) (unitary_reindex e e hU)
        apply holds_of_equiv e a b U hU
        have hsplit (f : Fin (n + 1) → ℂ) :
            Sum.elim (f ∘ e ∘ Sum.inl) (f ∘ e ∘ Sum.inr) = f ∘ e := by
          funext x
          cases x <;> rfl
        simpa only [hsplit] using hh
      · exact conjecture_le_three (by omega) a b U hU

/-- The Kronecker sum spectrum consists of every sum of one eigenvalue
from each factor, counted by the pair of labels. -/
def kroneckerSumSpectrum : Prop :=
  ∀ (m n : ℕ) (a c : Fin m → ℂ) (b d : Fin n → ℂ)
    (U : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ),
    IsUnitary U → Holds (fun i => a i.1 + b i.2) (fun i => c i.1 + d i.2) U

theorem moc_iff_kroneckerSumSpectrum : MOCIsTrue ↔ kroneckerSumSpectrum := by
  constructor
  · intro h m n a c b d U hU
    exact conjecture_fintype h (Fin m × Fin n) _ _ U hU
  · intro h n a b U hU
    let e := prodFinOne n
    have hh := h n 1 a b (fun _ => 0) (fun _ => 0) (U.submatrix e e)
      (unitary_reindex e e hU)
    exact holds_of_equiv e a b U hU (by simpa [e, prodFinOne, Function.comp_def] using hh)

/-- On the full matrix-unit basis the adjoint eigenvalues are
differences, using spectra of the same order on both sides. -/
def adjointSpectrum : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℂ) (U : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ),
    IsUnitary U → Holds (fun i => a i.1 - a i.2) (fun i => b i.1 - b i.2) U

theorem adjointSpectrum_of_moc (h : MOCIsTrue) : adjointSpectrum := by
  intro n a b U hU
  exact conjecture_fintype h (Fin n × Fin n) _ _ U hU

theorem not_moc_of_not_adjointSpectrum (h : ¬ adjointSpectrum) : ¬ MOCIsTrue :=
  fun hm => h (adjointSpectrum_of_moc hm)

/-- Selecting matrix units with one reference column changes the assertion.
This selection does recover all complex lists in order n. -/
def selectedAdjointSpectrum : Prop :=
  ∀ (n : ℕ) (a b : Fin n ⊕ Fin 1 → ℂ) (U : Matrix (Fin n) (Fin n) ℂ),
    IsUnitary U →
    Holds (fun i => a (.inl i) - a (.inr 0)) (fun i => b (.inl i) - b (.inr 0)) U

theorem moc_iff_selectedAdjointSpectrum : MOCIsTrue ↔ selectedAdjointSpectrum := by
  constructor
  · intro h n a b U hU
    exact h n _ _ U hU
  · intro h n a b U hU
    simpa using h n (Sum.elim a (fun _ => 0)) (Sum.elim b (fun _ => 0)) U hU

/-- The eigenvalues of conjugation by an invertible normal matrix
are ratios in the full matrix-unit basis. -/
def conjugationSpectrum : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℂ), (∀ i, a i ≠ 0) → (∀ i, b i ≠ 0) →
    ∀ (U : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ),
    IsUnitary U → Holds (fun i => a i.1 / a i.2) (fun i => b i.1 / b i.2) U

theorem conjugationSpectrum_of_moc (h : MOCIsTrue) : conjugationSpectrum := by
  intro n a b _ _ U hU
  exact conjecture_fintype h (Fin n × Fin n) _ _ U hU

theorem not_moc_of_not_conjugationSpectrum (h : ¬ conjugationSpectrum) : ¬ MOCIsTrue :=
  fun hm => h (conjugationSpectrum_of_moc hm)

/-- The hull for each evaluation of the homogeneous determinant polynomial.
The convex weights can depend on the evaluation point. -/
def pointwiseMixedDiscriminant : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℂ) (s t : ℂ) (U : Matrix (Fin n) (Fin n) ℂ),
    IsUnitary U → Holds (fun i => s * a i) (fun i => t * b i) U

theorem moc_iff_pointwiseMixedDiscriminant : MOCIsTrue ↔ pointwiseMixedDiscriminant := by
  constructor
  · intro h n a b s t U hU
    exact h n _ _ U hU
  · intro h n a b U hU
    simpa using h n a b 1 1 U hU

end
end MOC.Reformulations
