import MOC.CrossedMinorBridge
import MOC.FourMinorTransport
import MOC.OrderFiveCommonLawObstruction
import MOC.UniformCrossingObstruction

/-! Independently marked crossed transports are genuinely weaker than a
positive common pair law. The transports use Lyons's finite shadow
argument, DOI: 10.1007/s10240-003-0016-0. The strictness witness reuses
the existing five-dimensional Householder obstruction (Drury,
DOI: 10.1016/S0024-3795(99)00173-1); no new spectral
or arithmetic testing is used. -/

open Matrix Finset BigOperators

namespace MOC

/-- A minor table passes the crossed inequality tests at every independent
choice of marked row and column. The permutations only choose coordinates
for the two spectator sets; the transport measures are allowed to differ. -/
def IndependentCrossedTests {n : ℕ}
    (m : Finset (Fin (n+1)) → Finset (Fin (n+1)) → ℝ) : Prop :=
  ∀ (r c : Equiv.Perm (Fin (n+1))),
    let rv := (Fin.succEmb n).trans r.toEmbedding
    let cv := (Fin.succEmb n).trans c.toEmbedding
    ∃ μ : (Finset (Fin n) × Finset (Fin n)) → (Finset (Fin n) × Finset (Fin n)) → ℝ,
      (∀ A B, 0 ≤ μ A B) ∧
      (∀ A B, μ A B ≠ 0 → A.1 ⊆ B.1 ∧ B.2 ⊆ A.2 ∧ A.1.card = B.2.card) ∧
      (∀ A, ∑ B, μ A B = m (insert (r 0) (A.1.map rv)) (A.2.map cv)) ∧
      (∀ B, ∑ A, μ A B = m (B.1.map rv) (insert (c 0) (B.2.map cv)))

/-- Every unitary minor table satisfies the crossed tests at all marks,
not only at the diagonal pairs of labels. -/
theorem independentCrossedTests_of_unitary {n : ℕ}
    (U : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hU : IsUnitary U) :
    IndependentCrossedTests (subsetMinorSq U) := by
  intro r c
  obtain ⟨μ, hp, hS, hr, hc⟩ :=
    exists_crossed_subsetMinorSq_transport (U.submatrix r c) (unitary_reindex r c hU)
  refine ⟨μ, hp, hS, ?_, ?_⟩
  · intro A
    simpa only [squared_minor_reindex r c U hU, Finset.map_insert, Finset.map_map,
      Equiv.toEmbedding_apply] using hr A
  · intro B
    simpa only [squared_minor_reindex r c U hU, Finset.map_insert, Finset.map_map,
      Equiv.toEmbedding_apply] using hc B

/-- Passing every crossed test still does not ensure a simultaneous positive
permutation law on doubletons. The witness is an actual orthogonal mixer.
This rules out one certificate strengthening, not the MOC inequality. -/
theorem exists_unitary_crossedTests_without_positive_pair_law :
    ∃ U : Matrix (Fin 5) (Fin 5) ℂ, IsUnitary U ∧ IndependentCrossedTests (subsetMinorSq U) ∧
      ¬ ∃ w : Equiv.Perm (Fin 5) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ) = 1 ∧
        ∀ I J : Finset (Fin 5), I.card = 2 → J.card = 2 →
          (∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin 5) => J.map σ.toEmbedding = I), w σ) =
            subsetMinorSq U I J := by
  exact ⟨orderFiveFlatReflection, unitary_orderFiveFlatReflection,
    independentCrossedTests_of_unitary orderFiveFlatReflection unitary_orderFiveFlatReflection,
    orderFiveFlatReflection_no_positive_pair_law⟩


/-- The independently marked crossed relaxation is strictly weaker than
a common positive pair law in every order above four. -/
theorem exists_unitary_crossedTests_without_positive_pair_law_of_four_lt
    (n : ℕ) (hn : 4 < n + 1) :
    ∃ U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, IsUnitary U ∧ IndependentCrossedTests (subsetMinorSq U) ∧
      ¬ ∃ w : Equiv.Perm (Fin (n + 1)) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ) = 1 ∧
        ∀ I J : Finset (Fin (n + 1)), I.card = 2 → J.card = 2 →
          (∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) => J.map σ.toEmbedding = I), w σ) =
            subsetMinorSq U I J := by
  have hN : 4 < Fintype.card (Fin (n + 1)) := by simpa using hn
  have hU := unitary_flatReflectionUniform (ι := Fin (n + 1)) (by omega)
  exact ⟨_, hU, independentCrossedTests_of_unitary _ hU,
    flatReflectionUniform_no_positive_pair_law hN⟩

end MOC
