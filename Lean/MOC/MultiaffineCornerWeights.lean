import MOC.TwoFreeEntries
import MOC.SpectralMinorDecomposition
import Mathlib.Data.Finset.Powerset

/-! A single law for a multiaffine pencil can be tested on its Boolean corners. -/

open Finset BigOperators

namespace MOC.MultiaffineCornerWeights

noncomputable section

variable {κ P : Type*} [Fintype κ] [DecidableEq κ] [Fintype P]

def evaluate (c : Finset κ → ℂ) (z : κ → ℂ) : ℂ :=
  ∑ I, c I * ∏ i ∈ I, z i

private theorem evaluate_corner (c : Finset κ → ℂ) (J : Finset κ) :
    evaluate c (fun i => if i ∈ J then 1 else 0) = ∑ I ∈ J.powerset, c I := by
  classical
  have hprod (I : Finset κ) : (∏ i ∈ I, (if i ∈ J then (1 : ℂ) else 0)) =
      if I ⊆ J then 1 else 0 := by
    by_cases h : I ⊆ J
    · exact (Finset.prod_eq_one fun i hi => if_pos (h hi)).trans (if_pos h).symm
    · obtain ⟨i, hi, hij⟩ := Finset.not_subset.mp h
      rw [if_neg h, Finset.prod_eq_zero hi (if_neg hij)]
  have hf : Finset.univ.filter (fun I : Finset κ => I ⊆ J) = J.powerset := by
    ext I
    simp
  rw [← hf, Finset.sum_filter]
  simp only [evaluate, hprod, mul_ite, mul_one, mul_zero]

private theorem eq_of_powerset_sums {c d : Finset κ → ℂ}
    (h : ∀ J, (∑ I ∈ J.powerset, c I) = ∑ I ∈ J.powerset, d I) : c = d := by
  classical
  funext J
  induction J using Finset.strongInduction with
  | H J ih =>
    have hs : (∑ I ∈ J.powerset, (c I - d I)) = 0 := by
      rw [Finset.sum_sub_distrib, h, sub_self]
    have honly : (∑ I ∈ J.powerset, (c I - d I)) = c J - d J := by
      apply Finset.sum_eq_single J
      · intro I hI hne
        exact sub_eq_zero.mpr (ih I (Finset.ssubset_iff_subset_ne.mpr
          ⟨Finset.mem_powerset.mp hI, hne⟩))
      · simp
    exact sub_eq_zero.mp (honly.symm.trans hs)

/-- For any fixed weights, their coefficient identities hold if and only if
the same weights agree at all Boolean corners. -/
theorem coefficient_law_iff_corner_law (d : Finset κ → ℂ) (c : P → Finset κ → ℂ)
    (w : P → ℝ) :
    (∀ I, d I = ∑ p, (w p : ℂ) * c p I) ↔
      ∀ J : Finset κ, evaluate d (fun i => if i ∈ J then 1 else 0) =
        ∑ p, (w p : ℂ) * evaluate (c p) (fun i => if i ∈ J then 1 else 0) := by
  classical
  let e (I : Finset κ) := ∑ p, (w p : ℂ) * c p I
  have hs (J : Finset κ) :
      (∑ I ∈ J.powerset, e I) = ∑ p, (w p : ℂ) * ∑ I ∈ J.powerset, c p I := by
    simp only [e, Finset.mul_sum]
    rw [Finset.sum_comm]
  simp_rw [evaluate_corner, ← hs]
  exact ⟨fun h J => by simp only [h, e],
    fun h I => congrFun (eq_of_powerset_sums h) I⟩

/-- Carathéodory's bound is one plus the real dimension of the coefficient
space. For two free entries this gives nine matching products. -/
theorem coefficient_hull_small_law (d : Finset κ → ℂ) (c : P → Finset κ → ℂ)
    (h : d ∈ convexHull ℝ (Set.range c)) :
    ∃ m : ℕ, m ≤ 2^(Fintype.card κ + 1) + 1 ∧
      ∃ (p : Fin m → P) (w : Fin m → ℝ), (∀ i, 0 ≤ w i) ∧
        (∑ i, w i) = 1 ∧ (∑ i, w i • c (p i)) = d := by
  classical
  obtain ⟨J,hJ,g,v,hg,hi,hv,hm,he⟩ := eq_pos_convex_span_of_mem_convexHull h
  letI : Fintype J := hJ
  choose p hp using fun i : J => hg (Set.mem_range_self i)
  have hcard : Fintype.card J ≤ 2^(Fintype.card κ + 1) + 1 := by
    have hb := hi.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
    simpa [Module.finrank_pi_fintype, Complex.finrank_real_complex, Fintype.card_finset,
      pow_succ] using hb
  let e := (Fintype.equivFin J).symm
  refine ⟨_, hcard, p ∘ e, v ∘ e, fun i => (hv (e i)).le, (Equiv.sum_comp e v).trans hm, ?_⟩
  calc
    _ = ∑ i : J, v i • c (p i) := Equiv.sum_comp e (fun i => v i • c (p i))
    _ = d := by simpa only [hp] using he

/-- Specializing any subset of the free inputs preserves a common law.
Here the image of an arbitrary map selects the allowed inputs after specialization. -/
theorem common_law_specializes {X Y : Type*} (D : X → ℂ) (C : P → X → ℂ)
    (w : P → ℝ) (h : ∀ x, D x = ∑ p, (w p : ℂ) * C p x) (specializeAt : Y → X) :
    ∀ y, D (specializeAt y) = ∑ p, (w p : ℂ) * C p (specializeAt y) :=
  fun y => h (specializeAt y)

/-- Coordinates of an evaluation direction lie on the rank-one quadric.
The direction (1,0,0,1) lies outside it. -/
theorem bilinear_evaluation_direction (α z u : ℂ) :
    α * (α*z*u) = (α*z)*(α*u) := by ring

theorem diagonal_direction_not_evaluation :
    ¬ ∃ α z u : ℂ, α = 1 ∧ α*z = 0 ∧ α*u = 0 ∧ α*z*u = 1 := by
  rintro ⟨α,z,u,rfl,hz,hu,hone⟩
  simp at hz hu
  simp [hz] at hone

end

end MOC.MultiaffineCornerWeights
