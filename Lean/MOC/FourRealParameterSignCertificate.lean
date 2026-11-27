import MOC.FourRealParameterSignCertificateFrom0
import MOC.FourRealParameterSignCertificateFrom44
import MOC.FourRealParameterSignCertificateFrom87
import MOC.FourRealParameterSignCertificateFrom130

set_option Elab.async false

open BigOperators Matrix Polynomial
open scoped Polynomial MOC.RealParameterCertificate.Univariate
open MOC.RealParameterCertificate (Univariate)

namespace MOC.FourRealParameterCellCertificate

theorem compactBandSignValid_true (i : Fin 173) (negative : Bool) :
    compactBandSignValid i negative = true := by
  have hi := i.isLt
  by_cases h0 : i.val < 44
  · let j : Fin 44 := ⟨i.val - 0, by omega⟩
    have he : j.val + 0 = i.val := by dsimp only [j]; omega
    have hIndex : (⟨j.val + 0, by simpa only [he] using hi⟩ : Fin 173) = i := Fin.ext he
    have h := compactBandSignFrom0 j negative
    rw [hIndex] at h
    exact h
  by_cases h44 : i.val < 87
  · let j : Fin 43 := ⟨i.val - 44, by omega⟩
    have he : j.val + 44 = i.val := by dsimp only [j]; omega
    have hIndex : (⟨j.val + 44, by simpa only [he] using hi⟩ : Fin 173) = i := Fin.ext he
    have h := compactBandSignFrom44 j negative
    rw [hIndex] at h
    exact h
  by_cases h87 : i.val < 130
  · let j : Fin 43 := ⟨i.val - 87, by omega⟩
    have he : j.val + 87 = i.val := by dsimp only [j]; omega
    have hIndex : (⟨j.val + 87, by simpa only [he] using hi⟩ : Fin 173) = i := Fin.ext he
    have h := compactBandSignFrom87 j negative
    rw [hIndex] at h
    exact h
  let j : Fin 43 := ⟨i.val - 130, by omega⟩
  have he : j.val + 130 = i.val := by dsimp only [j]; omega
  have hIndex : (⟨j.val + 130, by simpa only [he] using hi⟩ : Fin 173) = i := Fin.ext he
  have h := compactBandSignFrom130 j negative
  rw [hIndex] at h
  exact h

theorem compactBand_signs (i : Fin 173) (negative : Bool) :
    let b := compactBandData i
    let p := compactPolygon (b.chart negative)
    ∀ k : Fin p.size, compactWeightValid b negative (p.turns k) = true ∧
      ∀ j : Fin 12, compactWeightValid b negative ((compactFacet (p.facets k)).terms j).weight = true := by
  let b := compactBandData i
  let p := compactPolygon (b.chart negative)
  change ∀ k : Fin p.size, compactWeightValid b negative (p.turns k) = true ∧
    ∀ j : Fin 12, compactWeightValid b negative ((compactFacet (p.facets k)).terms j).weight = true
  intro k
  have h : checkAll (fun k : Fin p.size =>
    compactWeightValid b negative (p.turns k) &&
      checkAll fun j : Fin 12 => compactWeightValid b negative ((compactFacet (p.facets k)).terms j).weight) = true :=
    compactBandSignValid_true i negative
  have hk := Bool.and_eq_true_iff.mp (checkAll_at h k)
  exact ⟨hk.1, fun j => checkAll_at hk.2 j⟩

end MOC.FourRealParameterCellCertificate
