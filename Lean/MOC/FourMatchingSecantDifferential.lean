import MOC.FourMatchingSegreTangent
import MOC.FourMatchingHessianMatrix
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Differentiating the Segre identity bounds the Hessian on the
full-rank secant parameter chart. -/

open Matrix TrivSqZeroExt

namespace MOC

variable {R : Type*} [CommRing R]

/-- Noncrossing coordinates commute with polynomial evaluation. -/
theorem fourNoncrossingCoordinates_map {S : Type*} [CommRing S] (f : R →+* S) (p : Fin 8 → R)
    (i : Fin 14) : f (fourNoncrossingCoordinates p i) =
      fourNoncrossingCoordinates (fun j => f (p j)) i := by
  fin_cases i <;> simp [fourNoncrossingCoordinates, fourBracketCoordinates]

private theorem noncrossing_snd_map {M : Type*} [AddCommGroup M] [Module R M]
    [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (f : M →ₗ[R] R)
    (p : Fin 8 → R) (u : Fin 8 → M) (i : Fin 14) :
    f ((fourNoncrossingCoordinates (fun j => (⟨p j, u j⟩ : TrivSqZeroExt R M)) i).snd) =
      (fourNoncrossingCoordinates (fun j => (⟨p j, f (u j)⟩ : DualNumber R)) i).snd := by
  let P (j : Fin 8) : TrivSqZeroExt R M := ⟨p j, u j⟩
  let F := (TrivSqZeroExt.map f).toRingHom
  have h (j : Fin 8) : F (P j) = (⟨p j, f (u j)⟩ : DualNumber R) :=
    TrivSqZeroExt.ext (fst_map f _) (snd_map f _)
  calc
    _ = (F (fourNoncrossingCoordinates P i)).snd := (snd_map f _).symm
    _ = (fourNoncrossingCoordinates (fun j => F (P j)) i).snd :=
      congrArg TrivSqZeroExt.snd (fourNoncrossingCoordinates_map F P i)
    _ = _ := by simp only [h]

private def noncrossingDifferential (p : Fin 8 → R) : (Fin 8 → R) →ₗ[R] (Fin 14 → R) where
  toFun u i := (fourNoncrossingCoordinates (fun j => (⟨p j, u j⟩ : DualNumber R)) i).snd
  map_add' u v := by
    funext i
    let d (j : Fin 8) : R × R := (u j, v j)
    let F := LinearMap.fst R R R
    let G := LinearMap.snd R R R
    exact (noncrossing_snd_map (F + G) p d i).symm.trans
      (congrArg₂ (· + ·) (noncrossing_snd_map F p d i) (noncrossing_snd_map G p d i))
  map_smul' t u := by
    funext i
    exact (noncrossing_snd_map (t • LinearMap.id) p u i).symm

/-- The linear part of the addition map on two matching profiles. -/
def fourMatchingSecantDifferential (p q : Fin 8 → R) :
    ((Fin 8 → R) × (Fin 8 → R)) →ₗ[R] (Fin 14 → R) :=
  (noncrossingDifferential p).coprod (noncrossingDifferential q)

private def dualBaseMap {S : Type*} [CommRing S] (f : R →+* S) :
    DualNumber R →+* DualNumber S where
  toFun z := ⟨f z.fst, f z.snd⟩
  map_zero' := TrivSqZeroExt.ext (map_zero f) (map_zero f)
  map_one' := TrivSqZeroExt.ext (map_one f) (map_zero f)
  map_add' := by
    intro a b
    apply TrivSqZeroExt.ext <;> simp [map_add]
  map_mul' := by
    intro a b
    apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.fst_mul, DualNumber.snd_mul, map_mul]

private theorem noncrossingDifferential_map {S : Type*} [CommRing S] (f : R →+* S)
    (p u : Fin 8 → R) (i : Fin 14) :
    f (noncrossingDifferential p u i) =
      noncrossingDifferential (fun j => f (p j)) (fun j => f (u j)) i :=
  congrArg TrivSqZeroExt.snd
    (fourNoncrossingCoordinates_map (dualBaseMap f) (fun j => ⟨p j, u j⟩) i)

/-- The secant derivative is polynomial over the integers in the two
marked configurations and the two varying directions. -/
theorem fourMatchingSecantDifferential_map {S : Type*} [CommRing S] (f : R →+* S)
    (p q u v : Fin 8 → R) (i : Fin 14) :
    f (fourMatchingSecantDifferential p q (u, v) i) =
      fourMatchingSecantDifferential (fun j => f (p j)) (fun j => f (q j))
        (fun j => f (u j), fun j => f (v j)) i := by
  simp only [fourMatchingSecantDifferential, LinearMap.coprod_apply, Pi.add_apply,
    map_add, noncrossingDifferential_map]

private theorem noncrossing_dual (p u : Fin 8 → R) :
    fourNoncrossingCoordinates (fun j => (⟨p j, u j⟩ : DualNumber R)) =
      fun i => (⟨fourNoncrossingCoordinates p i, noncrossingDifferential p u i⟩ : DualNumber R) := by
  funext i
  apply TrivSqZeroExt.ext
  · exact fourNoncrossingCoordinates_map (TrivSqZeroExt.fstHom R R R).toRingHom _ i
  · rfl

private theorem matchingGradient_dual_snd (f g : Fin 14 → R) (i : Fin 14) :
    (fourMatchingGradient (fun j => (⟨f j, g j⟩ : DualNumber R)) i).snd =
      (fourMatchingHessian f).mulVec g i := by
  rw [fourMatchingHessian_mulVec_apply]
  fin_cases i <;> simp [fourMatchingGradient, DualNumber.snd_mul] <;> ring

private theorem matchingHessian_secant_differential (p q u v : Fin 8 → R) :
    let f := fun j => fourNoncrossingCoordinates p j + fourNoncrossingCoordinates q j
    let X := fourMatchingSegreMatrix p q
    let V : Matrix (Fin 4) (Fin 8) R := fun i j => ![0, u j, v j, p j * v j + u j * q j] i
    (fourMatchingHessian f).mulVec (fourMatchingSecantDifferential p q (u, v)) =
      fourSegreResponseDifferential X V := by
  let P (j : Fin 8) : DualNumber R := ⟨p j, u j⟩
  let Q (j : Fin 8) : DualNumber R := ⟨q j, v j⟩
  dsimp only
  have hX : fourMatchingSegreMatrix P Q =
      (fun i j => (⟨fourMatchingSegreMatrix p q i j,
        ![0, u j, v j, p j * v j + u j * q j] i⟩ : DualNumber R)) := by
    ext i j : 1
    fin_cases i <;> apply TrivSqZeroExt.ext <;>
      simp [P, Q, fourMatchingSegreMatrix, TrivSqZeroExt.fst_mul, DualNumber.snd_mul]
  funext i
  have he := fourMatchingGradient_segre P Q i
  rw [hX, show fourNoncrossingCoordinates P = _ from noncrossing_dual p u,
    show fourNoncrossingCoordinates Q = _ from noncrossing_dual q v] at he
  calc
    _ = (fourMatchingGradient (fun j =>
        (⟨fourNoncrossingCoordinates p j + fourNoncrossingCoordinates q j,
          fourMatchingSecantDifferential p q (u, v) j⟩ : DualNumber R)) i).snd :=
      (matchingGradient_dual_snd _ _ i).symm
    _ = _ := congrArg TrivSqZeroExt.snd he

/-- Where the secant parameter derivative has rank at least twelve and its
Segre matrix has a five-column frame, the matching Hessian has rank at most
twelve. -/
theorem fourMatchingHessian_finrank_le_twelve_of_secant_frame (p q : Fin 8 → ℂ)
    (e : Fin 4 → Fin 8) (j₀ : Fin 8) (v : Fin 4 → ℂ)
    (hP : IsUnit ((fourMatchingSegreMatrix p q).submatrix id e))
    (hv : ∀ j, v j ≠ 0)
    (hframe : ((fourMatchingSegreMatrix p q).submatrix id e).mulVec v =
      fun i => fourMatchingSegreMatrix p q i j₀)
    (hJ : 12 ≤ Module.finrank ℂ (LinearMap.range (fourMatchingSecantDifferential p q))) :
    Module.finrank ℂ (LinearMap.range (fourMatchingHessian
      (fun j => fourNoncrossingCoordinates p j + fourNoncrossingCoordinates q j)).mulVecLin) ≤ 12 := by
  let X := fourMatchingSegreMatrix p q
  let H := (fourMatchingHessian
    (fun j => fourNoncrossingCoordinates p j + fourNoncrossingCoordinates q j)).mulVecLin
  let J := fourMatchingSecantDifferential p q
  let D := fourSegreResponseDifferential X
  have hD : Module.finrank ℂ (LinearMap.range D) ≤ 10 :=
    fourSegreResponseDifferential_finrank_le_ten X e j₀ v hP hv hframe (fun j => ⟨0, one_ne_zero⟩)
  let W := LinearMap.range J
  let H' := H.comp W.subtype
  have hH' : LinearMap.range H' ≤ LinearMap.range D := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨⟨u, w⟩, h⟩ := a.property
    refine ⟨fun i j => ![0, u j, w j, p j * w j + u j * q j] i, ?_⟩
    change D _ = H a.val
    rw [← h]
    exact (matchingHessian_secant_differential p q u w).symm
  have hR := (Submodule.finrank_mono hH').trans hD
  let k : LinearMap.ker H' →ₗ[ℂ] LinearMap.ker H :=
    (W.subtype.comp (LinearMap.ker H').subtype).codRestrict _ (fun a => a.property)
  have hk : Function.Injective k := by
    intro a b he
    exact Subtype.ext (Subtype.ext (congrArg Subtype.val he))
  have hK := LinearMap.finrank_le_finrank_of_injective hk
  have h₁ := H'.finrank_range_add_finrank_ker
  have h₂ := H.finrank_range_add_finrank_ker
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h₂
  change 12 ≤ Module.finrank ℂ W at hJ
  change Module.finrank ℂ (LinearMap.range H) ≤ 12
  omega

end MOC
