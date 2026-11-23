import MOC.WeightedDiamondLowerRows
import MOC.WeightedDiamondPackedCut

/-! Add the inequality at permutation 10 to the order-four ray census. -/

namespace MOC.RayCoefficients

namespace LowerCut4

set_option maxRecDepth 32000
set_option maxHeartbeats 60000000

private def positiveIndex : Array ℕ :=
  #[0, 1, 2, 0, 0, 0, 0, 0, 0, 3, 0, 4, 0, 0, 0, 5, 6, 0, 0, 0, 0, 0, 0, 7, 8, 0, 9, 0, 0, 0, 10, 11, 12, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 3, 0, 4, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0]

private def edges : Array (Crossing 34 71) :=
  #[.keep 28 [1], .keep 29 [1, 1], .keep 30 [1, 1], .skip 6, .skip 7, .keep 31 [1], .keep 32 [1], .keep 33 [1], .skip 9, .keep 34 [1], .skip 21, .keep 35 [1], .keep 36 [1], .keep 37 [1], .keep 38 [1], .skip 13, .keep 39 [0, 1], .keep 40 [1], .keep 41 [1], .keep 42 [1, 2], .skip 8, .skip 3, .keep 43 [1, 2], .keep 44 [1, 3, 2], .keep 45 [1, 3, 2], .skip 4, .keep 46 [1], .skip 19, .keep 47 [0, 1], .keep 48 [1], .keep 49 [1], .keep 50 [1, 2], .skip 10, .skip 5, .keep 51 [1], .keep 52 [1], .keep 53 [1], .keep 54 [1], .keep 55 [1], .keep 56 [1, 1], .keep 57 [1, 1], .skip 11, .keep 58 [1], .keep 59 [1], .skip 18, .keep 60 [1, 1], .keep 61 [1], .keep 62 [1], .keep 63 [1], .keep 64 [1], .keep 65 [1, 1], .keep 66 [1], .keep 67 [1], .keep 68 [1], .skip 16, .keep 69 [1], .keep 70 [1]]

private def edgeIndex : Array (Array ℕ) :=
  #[
    #[0, 1, 2, 3, 4, 4],
    #[5, 6, 7, 8, 9, 10],
    #[11, 12, 13, 3, 14, 15],
    #[16, 17, 18, 19, 20, 21],
    #[22, 23, 24, 25, 26, 27],
    #[28, 29, 30, 31, 32, 33],
    #[34, 35, 36, 4, 37, 10],
    #[38, 39, 40, 21, 41, 42],
    #[43, 44, 45, 21, 4, 4],
    #[46, 47, 48, 21, 32, 32],
    #[49, 50, 15, 33, 4, 4],
    #[51, 52, 53, 33, 20, 20],
    #[54, 55, 56, 8, 20, 20]]

private def maskTable : Array ℕ :=
  #[16417, 48, 16640, 33280, 565248, 786432, 49155, 5, 10, 32786, 4160, 8320, 61440, 282624, 524385, 524608, 276, 557123, 195, 12300, 45076, 266260, 552, 262784, 737, 780, 960, 266764, 532520, 532748, 278659, 262290, 466, 28712]

private def separators : Array ℕ :=
  #[21108210690902565953175340105187207592567489631680, 194615442441749425093018021504960957177775294419972, 395256911590691830892961832138578148338854667944392, 724150488690408671721703510430740765065146425949679, 917257101693369762979484401845503062656737700597363, 917257239679230678887715283642769583460165706436211, 724150488690408671728041956860003827217173242658287, 96553309201876338834180735218658045549536149047362, 51293900871132644522287502408077075351611959774307, 724150488690408671711562112200778026588317090463215, 298712076323456719041826985762340995419078870315404, 346988499859098990045989240851464982737430280320429, 724150488690408671728041956860002674295682594455023, 868789335063443069271830521817533719760227378219602, 917256687735787015254792027208224612336125438709363, 917256690523380165071120035777618153072524949835379, 377444405732656293447229075526087848755989343113480, 917257101693369762979483898932362102971001029119603, 327659284078840302657716351124814441938257081244903, 113148467862589382975102913734237364150690692642221, 724150488690408671710294809771185846657429212151279, 868697990775548374535984352823028200152960877546066, 434490293034397818915727695434047475094290649228585, 868556693384638415309984906004450745532397891701330, 434490293121591238380125192663487884999839622341929, 434490293162138093538372217641494579187196603147561, 434490293158352452206376777235464536679518181795113, 868697990601323803037547232395694936219683171945042, 917256634771517168744562375863482682114319461240435, 917256422914437782703642531274159091954885157572211, 868772208091130597753257822386158580235622718982738, 868138509810675735137204662915205687761236371524178, 374521536262593284682155915574581216975909135064328, 21119628672444213632223806393237951458846494373325]

private def kept : Array (Fin 71) :=
  #[0, 1, 2, 3, 4, 5, 6, 0, 0, 7, 0, 8, 9, 10, 11, 12, 13, 0, 14, 0, 15, 16, 17, 18, 19, 20, 21, 0, 22, 23, 24, 25, 26, 27]

private def origin : Array (RayOrigin 34) :=
  #[.kept 0, .kept 1, .kept 2, .kept 3, .kept 4, .kept 5, .kept 6, .kept 9, .kept 11, .kept 12, .kept 13, .kept 14, .kept 15, .kept 16, .kept 18, .kept 20, .kept 21, .kept 22, .kept 23, .kept 24, .kept 25, .kept 26, .kept 28, .kept 29, .kept 30, .kept 31, .kept 32, .kept 33, .crossing 0 7, .crossing 0 8, .crossing 0 10, .crossing 1 7, .crossing 1 8, .crossing 1 10, .crossing 1 19, .crossing 2 7, .crossing 2 8, .crossing 2 10, .crossing 2 19, .crossing 9 7, .crossing 9 8, .crossing 9 10, .crossing 9 17, .crossing 11 7, .crossing 11 8, .crossing 11 10, .crossing 11 19, .crossing 15 7, .crossing 15 8, .crossing 15 10, .crossing 15 17, .crossing 16 7, .crossing 16 8, .crossing 16 10, .crossing 16 19, .crossing 23 7, .crossing 23 8, .crossing 23 10, .crossing 23 27, .crossing 24 7, .crossing 24 10, .crossing 26 7, .crossing 26 8, .crossing 26 10, .crossing 30 7, .crossing 30 8, .crossing 31 7, .crossing 31 8, .crossing 31 10, .crossing 32 8, .crossing 32 10]

private def mask (p : Fin 34) : ℕ := maskTable.getD p.val 0

private def separator (p k : Fin 34) : Fin 24 :=
  Fin.ofNat' 24 (((separators.getD p.val 0) >>> (5 * k.val)) % 32)

local instance : NeZero lowerStage4.size := ⟨by decide +kernel⟩
local instance : NeZero lowerStage5.size := ⟨by decide +kernel⟩

def plan : RayCutPlan 34 71 where
  kept p := kept.getD p.val 0
  crossing p k := edges.getD ((edgeIndex.getD (positiveIndex.getD p.val 0) #[]).getD
    (negativeIndex.getD k.val 0) 0) (.skip p)
  origin l := origin.getD l.val (.kept 0)

private abbrev old : Fin 34 → Row := lowerStage4.rays
private abbrev nextRows : Fin 71 → Row := lowerStage5.rays
private abbrev imposed := lowerStage4.imposed

private theorem oldSigns : ∀ p i, i ∈ imposed → zero (old p i) = true ∨ positive (old p i) = true := by
  apply checkRayBlocks (n := 34)
  intro k
  fin_cases k <;> decide +kernel

private theorem mask_eq : ∀ p i, (mask p).testBit i.val =
    (decide (i ∈ imposed) && positive (old p i)) := by
  apply checkRayBlocks (n := 34)
  intro k
  fin_cases k <;> decide +kernel

private theorem separate : ∀ p k, p ≠ k → let i := separator p k
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply checkRayBlocks (n := 34)
  intro k
  fin_cases k <;> decide +kernel

private theorem crossing : ∀ p k, positive (old p 10) = true → negative (old k 10) = true →
    maskCrossing old nextRows imposed 10 mask p k (plan.crossing p k) := by
  apply checkRayBlocks (n := 34)
  intro k
  fin_cases k <;> decide +kernel

theorem valid : plan.Valid old nextRows imposed 10 := by
  obtain ⟨sep, cross⟩ := validateRayMasks plan mask separator oldSigns mask_eq separate crossing
  refine ⟨oldSigns, ?_, ?_, ?_, sep, ?_, cross, ?_⟩ <;> apply checkRayBlocks <;>
    intro k <;> fin_cases k <;> decide +kernel

end LowerCut4

end MOC.RayCoefficients
