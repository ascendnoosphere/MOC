import MOC.DuplicateAnchorObstruction
import Mathlib.Tactic.Positivity

/-! A four-dimensional spectral pair for which every scalar padding
with nonzero sum enlarges the real support. -/

namespace MOC.ScalarAnchor

open scoped BigOperators

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

private def slack3 (hr _hi fr fi kr ki : ℝ) : ℝ :=
  25 + 10 * hr - 40 * fr - 20 * fi - 40 * kr - 40 * ki

private def slack4 (hr hi fr fi kr ki : ℝ) : ℝ :=
  15 - 2 * hr + 14 * hi - 12 * fr - 16 * fi + 10 * kr + 30 * ki

private def slack13 (hr hi fr fi kr ki : ℝ) : ℝ :=
  69 - 4 * hr + 28 * hi - 124 * fr + 68 * fi + 160 * kr + 80 * ki

private def slack14 (hr hi fr fi kr ki : ℝ) : ℝ :=
  -3 - 8 * hr - 4 * hi + 20 * fr + 20 * fi + 32 * kr + 16 * ki

private def slack20 (hr hi fr fi _kr ki : ℝ) : ℝ :=
  5 + 20 * hr - 40 * hi + 20 * fr + 60 * fi - 100 * ki

private def slack21 (hr hi fr fi kr ki : ℝ) : ℝ :=
  5 - 20 * hr - 20 * hi + 20 * fr + 20 * fi + 160 * kr - 80 * ki

private def slack22 (hr hi fr fi kr ki : ℝ) : ℝ :=
  77 + 8 * hr + 44 * hi - 124 * fr + 68 * fi + 32 * kr + 176 * ki

private def slack23 (hr hi fr fi kr ki : ℝ) : ℝ :=
  85 + 30 * hr + 40 * hi - 140 * fr - 20 * fi - 160 * kr + 120 * ki

private def slack27 (hr hi fr _fi kr ki : ℝ) : ℝ :=
  65 + 20 * hr - 10 * hi - 100 * fr - 120 * kr - 40 * ki

private def slack33 (hr hi fr fi kr ki : ℝ) : ℝ :=
  9 - 4 * hr - 2 * hi - 4 * fr - 22 * fi - 20 * kr + 20 * ki

private def slack44 (hr hi fr fi kr ki : ℝ) : ℝ :=
  -5 + 15 * hr - 5 * hi + 25 * fr + 25 * fi - 10 * kr - 30 * ki

private def slack47 (hr hi fr fi kr ki : ℝ) : ℝ :=
  80 + 35 * hr + 5 * hi - 145 * fr + 15 * fi - 150 * kr + 50 * ki

private def slack50 (hr hi fr fi kr ki : ℝ) : ℝ :=
  9 - 14 * hr + 2 * hi + 8 * fr - 44 * fi - 32 * kr - 24 * ki

private def slack56 (_hr hi fr fi kr ki : ℝ) : ℝ :=
  1 - 2 * hi + 4 * fr - 6 * fi - 4 * kr + 4 * ki

private def slack57 (hr hi fr fi kr ki : ℝ) : ℝ :=
  9 - 4 * hr + 2 * hi - 12 * fr - 14 * fi - 12 * kr + 16 * ki

private def slack58 (hr hi fr fi kr ki : ℝ) : ℝ :=
  -1 - 4 * hr + 2 * hi + 8 * fr - 14 * fi - 2 * kr - 14 * ki

private def slack59 (hr hi _fr fi kr ki : ℝ) : ℝ :=
  3 + 1 * hr + 2 * hi - 10 * fi + 4 * kr - 12 * ki

private def slack68 (hr hi fr fi kr ki : ℝ) : ℝ :=
  -7 + 7 * hr + 1 * hi + 19 * fr + 17 * fi - 12 * kr - 16 * ki

private def slack69 (hr hi fr fi kr ki : ℝ) : ℝ :=
  1 - 3 * hr - 1 * hi + 3 * fr + 1 * fi + 12 * kr - 16 * ki

private def slack70 (hr hi fr fi kr ki : ℝ) : ℝ :=
  15 + 10 * hr + 5 * hi - 25 * fr + 25 * fi + 10 * kr + 30 * ki

private def slack71 (hr hi fr fi kr ki : ℝ) : ℝ :=
  30 + 15 * hr - 5 * hi - 55 * fr + 35 * fi - 50 * kr + 50 * ki

private def slack80 (hr hi _fr fi kr ki : ℝ) : ℝ :=
  9 + 4 * hr + 2 * hi - 10 * fi + 4 * kr + 12 * ki

private def slack88 (hr hi fr fi _kr ki : ℝ) : ℝ :=
  5 - 2 * hr - 2 * hi - 2 * fr + 6 * fi - 8 * ki

private def slack89 (hr hi fr fi kr ki : ℝ) : ℝ :=
  21 + 2 * hr + 10 * hi - 34 * fr + 38 * fi + 64 * kr + 8 * ki

private def slack90 (hr hi fr fi kr ki : ℝ) : ℝ :=
  -9 - 2 * hr - 10 * hi + 26 * fr + 26 * fi + 32 * kr + 4 * ki

private def slack92 (hr hi fr fi kr _ki : ℝ) : ℝ :=
  1 - 1 * hr + 1 * hi + 3 * fr + 1 * fi - 4 * kr

private def slack93 (hr hi fr fi kr ki : ℝ) : ℝ :=
  -7 + 5 * hr - 1 * hi + 19 * fr + 17 * fi + 4 * kr - 32 * ki

private def slack94 (hr hi fr fi kr ki : ℝ) : ℝ :=
  -1 + 2 * hr - 3 * hi + 7 * fr + 9 * fi + 10 * kr - 2 * ki

private def slack95 (hr hi fr fi kr ki : ℝ) : ℝ :=
  -2 - 1 * hr - 5 * hi + 9 * fr + 19 * fi + 14 * kr + 18 * ki

-- This identity is a certificate of infeasibility for the linear
-- support bounds together with the real and imaginary rank equations.
private theorem infeasible (hr hi fr fi kr ki : ℝ)
    (hs3 : 0 ≤ slack3 hr hi fr fi kr ki)
    (hs4 : 0 ≤ slack4 hr hi fr fi kr ki)
    (hs13 : 0 ≤ slack13 hr hi fr fi kr ki)
    (hs14 : 0 ≤ slack14 hr hi fr fi kr ki)
    (hs20 : 0 ≤ slack20 hr hi fr fi kr ki)
    (hs21 : 0 ≤ slack21 hr hi fr fi kr ki)
    (hs22 : 0 ≤ slack22 hr hi fr fi kr ki)
    (hs23 : 0 ≤ slack23 hr hi fr fi kr ki)
    (hs27 : 0 ≤ slack27 hr hi fr fi kr ki)
    (hs33 : 0 ≤ slack33 hr hi fr fi kr ki)
    (hs44 : 0 ≤ slack44 hr hi fr fi kr ki)
    (hs47 : 0 ≤ slack47 hr hi fr fi kr ki)
    (hs50 : 0 ≤ slack50 hr hi fr fi kr ki)
    (hs56 : 0 ≤ slack56 hr hi fr fi kr ki)
    (hs57 : 0 ≤ slack57 hr hi fr fi kr ki)
    (hs58 : 0 ≤ slack58 hr hi fr fi kr ki)
    (hs59 : 0 ≤ slack59 hr hi fr fi kr ki)
    (hs68 : 0 ≤ slack68 hr hi fr fi kr ki)
    (hs69 : 0 ≤ slack69 hr hi fr fi kr ki)
    (hs70 : 0 ≤ slack70 hr hi fr fi kr ki)
    (hs71 : 0 ≤ slack71 hr hi fr fi kr ki)
    (hs80 : 0 ≤ slack80 hr hi fr fi kr ki)
    (hs88 : 0 ≤ slack88 hr hi fr fi kr ki)
    (hs89 : 0 ≤ slack89 hr hi fr fi kr ki)
    (hs90 : 0 ≤ slack90 hr hi fr fi kr ki)
    (hs92 : 0 ≤ slack92 hr hi fr fi kr ki)
    (hs93 : 0 ≤ slack93 hr hi fr fi kr ki)
    (hs94 : 0 ≤ slack94 hr hi fr fi kr ki)
    (hs95 : 0 ≤ slack95 hr hi fr fi kr ki)
    (hreal : hr * kr - hi * ki + fr * fr - fi * fi - fr = 0)
    (himag : hr * ki + hi * kr + 2 * fr * fi - fi = 0) : False := by
  let s3 := slack3 hr hi fr fi kr ki
  let s4 := slack4 hr hi fr fi kr ki
  let s13 := slack13 hr hi fr fi kr ki
  let s14 := slack14 hr hi fr fi kr ki
  let s20 := slack20 hr hi fr fi kr ki
  let s21 := slack21 hr hi fr fi kr ki
  let s22 := slack22 hr hi fr fi kr ki
  let s23 := slack23 hr hi fr fi kr ki
  let s27 := slack27 hr hi fr fi kr ki
  let s33 := slack33 hr hi fr fi kr ki
  let s44 := slack44 hr hi fr fi kr ki
  let s47 := slack47 hr hi fr fi kr ki
  let s50 := slack50 hr hi fr fi kr ki
  let s56 := slack56 hr hi fr fi kr ki
  let s57 := slack57 hr hi fr fi kr ki
  let s58 := slack58 hr hi fr fi kr ki
  let s59 := slack59 hr hi fr fi kr ki
  let s68 := slack68 hr hi fr fi kr ki
  let s69 := slack69 hr hi fr fi kr ki
  let s70 := slack70 hr hi fr fi kr ki
  let s71 := slack71 hr hi fr fi kr ki
  let s80 := slack80 hr hi fr fi kr ki
  let s88 := slack88 hr hi fr fi kr ki
  let s89 := slack89 hr hi fr fi kr ki
  let s90 := slack90 hr hi fr fi kr ki
  let s92 := slack92 hr hi fr fi kr ki
  let s93 := slack93 hr hi fr fi kr ki
  let s94 := slack94 hr hi fr fi kr ki
  let s95 := slack95 hr hi fr fi kr ki
  have hn3 : 0 ≤ s3 := hs3
  have hn4 : 0 ≤ s4 := hs4
  have hn13 : 0 ≤ s13 := hs13
  have hn14 : 0 ≤ s14 := hs14
  have hn20 : 0 ≤ s20 := hs20
  have hn21 : 0 ≤ s21 := hs21
  have hn22 : 0 ≤ s22 := hs22
  have hn23 : 0 ≤ s23 := hs23
  have hn27 : 0 ≤ s27 := hs27
  have hn33 : 0 ≤ s33 := hs33
  have hn44 : 0 ≤ s44 := hs44
  have hn47 : 0 ≤ s47 := hs47
  have hn50 : 0 ≤ s50 := hs50
  have hn56 : 0 ≤ s56 := hs56
  have hn57 : 0 ≤ s57 := hs57
  have hn58 : 0 ≤ s58 := hs58
  have hn59 : 0 ≤ s59 := hs59
  have hn68 : 0 ≤ s68 := hs68
  have hn69 : 0 ≤ s69 := hs69
  have hn70 : 0 ≤ s70 := hs70
  have hn71 : 0 ≤ s71 := hs71
  have hn80 : 0 ≤ s80 := hs80
  have hn88 : 0 ≤ s88 := hs88
  have hn89 : 0 ≤ s89 := hs89
  have hn90 : 0 ≤ s90 := hs90
  have hn92 : 0 ≤ s92 := hs92
  have hn93 : 0 ≤ s93 := hs93
  have hn94 : 0 ≤ s94 := hs94
  have hn95 : 0 ≤ s95 := hs95
  let nonnegative : ℝ :=
      1099818200609807790771998245486009808535161545532106865102641665648785194613252589349163748601829978531564730785088248773412038123378225 * s88 +
      113338798187558081228949043309230804275146322060041877829841015862868047486044677059313126062281908949500515275292071523007955853664 * s3 * s20 * s20 +
      3175192244202151352790167745229367148412467692923586736341172694540873223746129395877470590962289008570495014889225472276530962014196 * s3 * s20 * s88 +
      7586052878348189012364186036303128262942922061958146429354602841056636012481504039464325166906493416448566417157740019173695820283656 * s3 * s20 * s92 +
      720309142421906447976221866599157868650572321830686179858500893863234669212702662962265757084440808394558681231169904897099280376500 * s3 * s27 * s56 +
      10286858653039729294984424205585502999882594736549001044782560760345166833401469309890156429019296211414848091041852442573953059580900 * s3 * s50 * s80 +
      3072753547259699703433279599573410266642175467126131200801301662373289268621595340667534510224056488818381359183570999843145574385600 * s4 * s4 * s57 +
      308690472236693975874686131074996003559006306717786441094290648898758328312750316824446512030210657364674795764327171480731153391588400 * s4 * s57 +
      136241204059405424187753911516714962899565080346158916061590091552938326941407290650354950781462008003852950119903368433011841988448200 * s4 * s80 * s92 +
      3236870705493971196357540742267235161376373711492998424944638259720037575128344069052182270493466634840923743114596303955202657493165 * s13 * s14 * s88 +
      20920608715501954314779085307367336907077496374451197802587719962500057848411206240559964382527232760848078168242044471071453822866940 * s13 * s14 * s92 +
      1067379411340940582526592578301983661533578935181505230080832622561709965018402620341148667108882410226102411123432359730461825674380 * s13 * s50 * s80 +
      3310051989815192428264091893506709216307723970570952315736699409764292577939120013972018887632920220119973422315356905524504331108000 * s13 * s56 * s57 +
      71808388740104419467239496265001136866468847088680402974936203755741940747829364674567418115064453984570907380593217045630065133478900 * s13 * s57 +
      209798512354795140268481715934470146411952773503845176155356621086218225459653764519943246758721655065938619822774155190687347955581680 * s13 * s92 +
      47726611062886103193514461742969066806202956430052787541630555882401670764224980032558910841111005641211165288228621247928890539094820 * s14 * s80 * s92 +
      3932048017072275919545612699822330866003774505715559529303966512089595810987010046122849940657127440940913917181929910517979287574088 * s20 * s50 * s88 +
      2087185576142200182455026070808902019594038630048029142612143587991272211506877399824319967049578218632004339650615633142697187218400 * s20 * s59 * s68 +
      19733425726364765395345495682699532641647167191309338096802939515655759905397742494522009864737200482327218994279131616066376835909680 * s21 * s92 * s92 +
      1093965700316027437961817034650561298282276918221757981240842555691304272460167332064593590253228173661198477030435774445986737853000 * s22 * s56 * s68 +
      108569464274574231660927867989041820807895475298908254389024737232891265390112909367783964396765555915397418961228055222722820490700 * s23 * s23 * s56 +
      3050414281477153435281836840128410983924024673629055171818590677884008698251174909395287426311055327705697150662525127031874159308832 * s23 * s70 * s92 +
      8653556758776123388967093075587217471328725115687910574533195952405082402187011520716799010745841521595318202645774536109304758597400 * s23 * s80 * s95 +
      5783190451793130959259769947267904742625733019432400671935206826690507393045272912405144568720838760637481809981028312881127298877200 * s23 * s88 * s95 +
      8902957708628605159792053470469767096947188339850932330726087689641569370846260204042228423112958715508130959935779040557438046408000 * s27 * s56 * s56 +
      68970280800402903404000846913556543366408196509928562333770014215496379590127628885516112926019536826285972571760789109947029185100720 * s33 * s92 +
      105934245625744819391092441142946217744325187077164902545346956379421835440683070138851656342420875506818299069194784514937791273520 * s44 * s44 * s50 +
      1332361771412851357045408107242353705241253497976960823076948564449814750049296569084910900866693357165711907000245299287988499605360 * s44 * s47 * s50 +
      13150324627268729494502842437156573741243711721840611930600231770329120288621706238452351292105167640277237257220652425640963991360000 * s44 * s50 * s69 +
      8428745923747608295861332697102991167898172277813190421084691355168521946525381319425379539119099551438517721347252467860542597210224 * s44 * s50 * s80 +
      8943076869440538677640102769061245155469739735667998245655027712691043110826251574358809630463778727135158676498372750046120685968000 * s44 * s58 * s95 +
      462196165261692993681157398654213719913468264576373767691189806751544423889919258948707341103557993852298421120844515325488014110508300 * s47 * s56 +
      6260392686483460987258171545336430690068286387074685929608819936646857994558520375083733001087727924470901284961325956824278932498000 * s47 * s56 * s59 +
      319487472745323826756405872416871834915991470176767510842905887423889139507892197309958272384562739180700830745686011612898025325306320 * s47 * s68 +
      3929294941491760230356794851303796777176530598728678013668151238726832751246317862197148220660134714512684510499628005250216323151200 * s47 * s92 * s95 +
      57714634535157557438443211700182369170580377161356841695622892249509135395450896443478103409943507622930487648619800199548720323550000 * s50 * s56 * s59 +
      6261618587029557553734643693978203363425990945148653884162645780888407085610398060289014829036284245973078359045496479502396116453000 * s50 * s56 * s68 +
      247309332841876132546725502484564109805834418266542872136728402515446592121354897576925362069756232796499973076801925545801344730992600 * s50 * s59 * s88 +
      80743485320334066100024505882512439937918149945872234810340271517134978138670380687082941138789292501788624627286958243384327688035400 * s50 * s80 +
      211150203496290362767829255122893354896014469601990250109078645729002792564628593681652575381434769610673814043742784610620218395645400 * s56 * s58 * s80 +
      401790158364630254004126815949051627574215830248913168915804892940464703847826510698144877948912762611291434484305073821245117063596100 * s56 * s58 * s88 +
      1004305310645265291203817217437659812012941850116095925845685713124493120531668115948364033724906721008938545326443078838828506351721600 * s56 * s59 * s92 +
      163320786777629235581128024228115384043716022993800165259923454311785736312979681353187240133482175819564723797807712744078350856707900 * s56 * s68 * s92 +
      145677939622767125011483812637321739609474616987731537189480746191476757140406807119908347498436305104035946996751420869759251400301000 * s56 * s69 * s88 +
      865822462706439416387474918191476307649145358905698270450481628528814935984935148305968133811224114381447980176577344452795088164600 * s56 * s71 * s89 +
      80231497607127106270544346931489679133054469018548675098135292281859981486136184745843685777683562960932949590238689542787485677421100 * s56 * s88 * s92 +
      269642904650543893322622791586692646958462110043935139911488434268152991836181588669193941382875188042398701780008325865388093239486900 * s56 * s92 * s92 +
      138200841778789401001748767788591640046268301361920888059513823423982279436514640985397668709833816535753054701038064381329971300171200 * s57 * s59 * s80 +
      17440228455073413018470894461587250775245903968142825616488858372686953359362707229195083615113342566862803777031446214007463637538160 * s57 * s68 * s92 +
      152625079311415129444476405505151942393304256509841118777642517143887017036366711454211577911344286811630620083521710734439886602907480 * s57 * s80 * s92 +
      121471310663454006950550283806675870843438948714372132380547016212309938995241285072835220599794529626603842774799354871653175553597200 * s57 * s92 * s94 +
      7385904339874084389390425264336882812752958849060384313305488299872224739706668976462518390371202597026561511938946596621125163427200 * s58 * s58 * s80 +
      69454772814237889127197563270805966658736663675247454253093706195541063876275057586065583380152166221675551374314150625423632889912032 * s58 * s70 * s88 +
      54968665143501640503284789006059242964671456980880781144488703447240122711340671317047450752795605134881862967860307670849401497721040 * s58 * s80 * s90 +
      5003090106041774567709118659180594140709333217771583914602986859914258177207700874871328487933459740581216910435608818048302713044200 * s59 * s68 * s88 +
      3125981702938078120151519045613409826465227623226893019587621719722525244007016525684310547123812047007185189055859823486633246042155 * s59 * s71 * s88 +
      48612576566035062500204742727616643515749295813374157275622688993259029899538663154119844385644144305899862560441428146123615435505500 * s59 * s88 * s88 +
      270912330567194810203555393957204606425887370057025894828325210776676950269918692359460170096086787892236130369731951518477044266011525 * s59 * s88 * s95 +
      203042076175879949417466931300913902585204063994076658776415088018965235800431613476448771983284501269439268426602521606979186991444000 * s59 * s92 * s95 +
      6212037874804269559216260773695946485894705231352394602974095390940958903491010759776483192699687752386110780685348851142649011475000 * s68 * s68 * s95 +
      29044134260037519660539938271301785753588939496079609912515205274799819297548327109998342970461137614123530491427288061208993382841000 * s68 * s71 * s92 +
      47140478646790640303028954075246927902873457904040308977414835934820192667650616064754238468129920016537747386339058215648770129129340 * s68 * s80 * s88 +
      707129717793295490339079040464665716283087028758639616637128385640109595610843541217383266117104989716475805590088971342772244291455680 * s70 * s92 * s92 +
      25636367908633149207446130152221498550492246501980426270289814274567089443204256645630466951040196603302807770007423284534258274791200 * s71 * s92 * s94 +
      4164626200598205458307110971976022285445478835968163504497592527319281871144533745219321162061125008574181538447516270540588741397660 * s80 * s88 * s88 +
      73610804411681391044825455468046821241512951808757125782874165795349199152355710284396320079192089018982061284801496727210063496705400 * s80 * s88 * s95 +
      18877007630779481819090441699515396814110528882671995612053878334731101894869855702466377878089246577294612249484850998778748146325000 * s80 * s89 * s95 +
      157030972614793189524942093639530816538961625147940129574406675681871254344495410476613578190375754249034100183432816773992681379501880 * s88 * s88 * s90 +
      506349071748460316351066426005425208974667750478305799840962340591598563251908029205217832398910916406173730945992693365960329626396240 * s88 * s90 * s92 +
      395625742514145217314986694926715551005403028627924170929997658740287129170764239796867568554589215972669827297188700340883425485060080 * s90 * s92 * s92 +
      962490162750601854017553415759038215874834096864759788787144995745542119866696490945099980919894575698537681459358149446407897786990000 * s93 * s95
  have hnonnegative : 0 ≤ nonnegative := by
    dsimp only [nonnegative]
    positivity
  have identity : nonnegative +
      (1233910231353147420609370431200429032418710502945815158800427143225635666250936499416889621474060021636085802714791958462915113650259478400 * 1 +
      (-187231080293401045637047524202257031818616282186909348403498434668670550421885319172660990531947144449690206541145268600692941251840620800) * hr +
      101160752317262305669790706007153209388319796866922600299860337382965048244585491050047746595133784238629458369118763003956279788287801600 * hi +
      343601502831902620566860358275891676650558049361691517932706526295115069625660568665718724440230973465633076060868961474039215748520672000 * fr +
      (-619692747705588529276510562379719500006608973734570101805756186646027146040637599271790016587568278137382215831507790243776873067274156800) * kr +
      (-198560446323745077823656553960164800480902542135290031973648813700192524950861465589019492358617727894616375405424369495221948638715718400) * ki) *
        (hr * kr - hi * ki + fr * fr - fi * fi - fr) +
      ((-193626362568220598890082522314411567480436661663968973589593268887144498501562804874766403638882829263037577176653098848866130472489654400) * 1 +
      (-26693436759447570175717421529225678568672613934548162587446608904107892984551363876561802917704321319356199231397649740617830846043520000) * hr +
      (-19593323485912513877399707026968641855881517620379744634504004858516453100887617875494985244477877749642781839346184398954735337187136000) * hi) *
        (hr * ki + hi * kr + 2 * fr * fi - fi) = -631424107325270974131459525182654097074394119919307923549540873718672694551355456144573945827445410546401761697030536480294270958303150 := by
    dsimp only [nonnegative, s3, s4, s13, s14, s20, s21, s22, s23, s27, s33, s44, s47, s50, s56, s57, s58, s59, s68, s69, s70, s71, s80, s88, s89, s90, s92, s93, s94, s95]
    unfold slack3 slack4 slack13 slack14 slack20 slack21 slack22 slack23 slack27 slack33 slack44 slack47 slack50 slack56 slack57 slack58 slack59 slack68 slack69 slack70 slack71 slack80 slack88 slack89 slack90 slack92 slack93 slack94 slack95
    ring
  simp only [hreal, himag, mul_zero, add_zero] at identity
  rw [identity] at hnonnegative
  norm_num at hnonnegative

/-- Append one scalar spectral value. -/
def appendScalar {α : Type*} (f : Fin 4 → α) (x : α) : Fin 5 → α :=
  ![f 0, f 1, f 2, f 3, x]

private noncomputable def witnessPermutation (f : Fin 5 → Fin 5)
    (h : ∀ i j : Fin 5, f i = f j → i = j) : Equiv.Perm (Fin 5) :=
  let hi : Function.Injective f := fun _ _ hf => h _ _ hf
  Equiv.ofBijective f ⟨hi, Finite.injective_iff_surjective.mp hi⟩

-- The scalar replacement matrix has rank one. Its coefficients satisfy
-- the two equations used in the infeasibility certificate.
private theorem scalarRank (c d h f k : ℂ) (hn : c + d ≠ 0)
    (hh : h = c * d / (c + d)) (hf : f = d / (c + d)) (hk : k = 1 / (c + d)) :
    h * k = f * (1 - f) := by
  rw [hh, hf, hk]
  field_simp
  ring

private theorem exchangeFactor (c d h f k : ℂ) (hn : c + d ≠ 0)
    (hh : h = c * d / (c + d)) (hf : f = d / (c + d)) (hk : k = 1 / (c + d))
    (a b : ℂ) : (a + d) * (c + b) / (c + d) = a + h + f * (b - a) + k * a * b := by
  rw [hh, hf, hk]
  field_simp
  ring

private theorem slackOfExchange (c d h f k : ℂ) (hn : c + d ≠ 0)
    (hh : h = c * d / (c + d)) (hf : f = d / (c + d)) (hk : k = 1 / (c + d))
    (upper : ∀ τ : Equiv.Perm (Fin 5),
      (matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
        (appendScalar DuplicateAnchor.rightSpectrum d) τ / (c + d)).re ≤ 5)
    {τ : Equiv.Perm (Fin 5)} {q a b : ℂ} {value : ℝ}
    (product : matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
      (appendScalar DuplicateAnchor.rightSpectrum d) τ = q * (a + d) * (c + b))
    (difference : value = 5 - (q * (a + h + f * (b - a) + k * a * b)).re) :
    0 ≤ value := by
  have bound := upper τ
  rw [product, mul_assoc, mul_div_assoc, exchangeFactor c d h f k hn hh hf hk] at bound
  rw [difference]
  exact sub_nonneg.mpr bound

private noncomputable def exchange3 : Equiv.Perm (Fin 5) :=
  witnessPermutation ![0, 1, 2, 4, 3] (by decide +kernel)

private theorem exchangeProduct3 (c d : ℂ) :
    matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
      (appendScalar DuplicateAnchor.rightSpectrum d) exchange3 =
    (⟨((-10) : ℝ), 0⟩ : ℂ) * ((⟨(2 : ℝ), (-2)⟩ : ℂ) + d) * (c + (⟨((-2) : ℝ), 0⟩ : ℂ)) := by
  rw [matchingProduct, Fin.prod_univ_succ, Fin.prod_univ_four]
  change ((⟨((2 : ℤ) : ℝ), ((1 : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * (((⟨((0 : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨(((-2) : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-1) : ℤ) : ℝ), (((-1) : ℤ) : ℝ)⟩ : ℂ)) * (c + (⟨(((-2) : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ) + d)) = _
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

private theorem exchangeDifference3 (h f k : ℂ) :
    slack3 h.re h.im f.re f.im k.re k.im =
      5 - ((⟨((-10) : ℝ), 0⟩ : ℂ) * ((⟨(2 : ℝ), (-2)⟩ : ℂ) + h + f * ((⟨((-2) : ℝ), 0⟩ : ℂ) - (⟨(2 : ℝ), (-2)⟩ : ℂ)) + k * (⟨(2 : ℝ), (-2)⟩ : ℂ) * (⟨((-2) : ℝ), 0⟩ : ℂ))).re := by
  norm_num [slack3, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]; ring

private noncomputable def exchange4 : Equiv.Perm (Fin 5) :=
  witnessPermutation ![4, 1, 3, 2, 0] (by decide +kernel)

private theorem exchangeProduct4 (c d : ℂ) :
    matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
      (appendScalar DuplicateAnchor.rightSpectrum d) exchange4 =
    (⟨(2 : ℝ), 14⟩ : ℂ) * ((⟨(2 : ℝ), 1⟩ : ℂ) + d) * (c + (⟨(1 : ℝ), 0⟩ : ℂ)) := by
  rw [matchingProduct, Fin.prod_univ_succ, Fin.prod_univ_four]
  change (c + (⟨((1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * (((⟨((0 : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-1) : ℤ) : ℝ), (((-1) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨(((-2) : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-2) : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), ((1 : ℤ) : ℝ)⟩ : ℂ) + d)) = _
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

private theorem exchangeDifference4 (h f k : ℂ) :
    slack4 h.re h.im f.re f.im k.re k.im =
      5 - ((⟨(2 : ℝ), 14⟩ : ℂ) * ((⟨(2 : ℝ), 1⟩ : ℂ) + h + f * ((⟨(1 : ℝ), 0⟩ : ℂ) - (⟨(2 : ℝ), 1⟩ : ℂ)) + k * (⟨(2 : ℝ), 1⟩ : ℂ) * (⟨(1 : ℝ), 0⟩ : ℂ))).re := by
  norm_num [slack4, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]; ring

private noncomputable def exchange13 : Equiv.Perm (Fin 5) :=
  witnessPermutation ![0, 4, 3, 1, 2] (by decide +kernel)

private theorem exchangeProduct13 (c d : ℂ) :
    matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
      (appendScalar DuplicateAnchor.rightSpectrum d) exchange13 =
    (⟨(4 : ℝ), 28⟩ : ℂ) * ((⟨((-2) : ℝ), 2⟩ : ℂ) + d) * (c + (⟨(1 : ℝ), (-2)⟩ : ℂ)) := by
  rw [matchingProduct, Fin.prod_univ_succ, Fin.prod_univ_four]
  change ((⟨((2 : ℤ) : ℝ), ((1 : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((c + (⟨((1 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-1) : ℤ) : ℝ), (((-1) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((0 : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-2) : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((⟨(((-2) : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + d)) = _
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

private theorem exchangeDifference13 (h f k : ℂ) :
    slack13 h.re h.im f.re f.im k.re k.im =
      5 - ((⟨(4 : ℝ), 28⟩ : ℂ) * ((⟨((-2) : ℝ), 2⟩ : ℂ) + h + f * ((⟨(1 : ℝ), (-2)⟩ : ℂ) - (⟨((-2) : ℝ), 2⟩ : ℂ)) + k * (⟨((-2) : ℝ), 2⟩ : ℂ) * (⟨(1 : ℝ), (-2)⟩ : ℂ))).re := by
  norm_num [slack13, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]; ring

private noncomputable def exchange14 : Equiv.Perm (Fin 5) :=
  witnessPermutation ![0, 2, 4, 1, 3] (by decide +kernel)

private theorem exchangeProduct14 (c d : ℂ) :
    matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
      (appendScalar DuplicateAnchor.rightSpectrum d) exchange14 =
    (⟨(8 : ℝ), (-4)⟩ : ℂ) * ((⟨(2 : ℝ), (-2)⟩ : ℂ) + d) * (c + (⟨((-1) : ℝ), (-1)⟩ : ℂ)) := by
  rw [matchingProduct, Fin.prod_univ_succ, Fin.prod_univ_four]
  change ((⟨((2 : ℤ) : ℝ), ((1 : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * (((⟨(((-2) : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ)) * (c + (⟨(((-1) : ℤ) : ℝ), (((-1) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((0 : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-2) : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ) + d)) = _
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

private theorem exchangeDifference14 (h f k : ℂ) :
    slack14 h.re h.im f.re f.im k.re k.im =
      5 - ((⟨(8 : ℝ), (-4)⟩ : ℂ) * ((⟨(2 : ℝ), (-2)⟩ : ℂ) + h + f * ((⟨((-1) : ℝ), (-1)⟩ : ℂ) - (⟨(2 : ℝ), (-2)⟩ : ℂ)) + k * (⟨(2 : ℝ), (-2)⟩ : ℂ) * (⟨((-1) : ℝ), (-1)⟩ : ℂ))).re := by
  norm_num [slack14, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]; ring

private noncomputable def exchange20 : Equiv.Perm (Fin 5) :=
  witnessPermutation ![4, 3, 2, 1, 0] (by decide +kernel)

private theorem exchangeProduct20 (c d : ℂ) :
    matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
      (appendScalar DuplicateAnchor.rightSpectrum d) exchange20 =
    (⟨((-20) : ℝ), (-40)⟩ : ℂ) * ((⟨(2 : ℝ), 1⟩ : ℂ) + d) * (c + (⟨(1 : ℝ), 0⟩ : ℂ)) := by
  rw [matchingProduct, Fin.prod_univ_succ, Fin.prod_univ_four]
  change (c + (⟨((1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * (((⟨((2 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨(((-2) : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-1) : ℤ) : ℝ), (((-1) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((0 : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-2) : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), ((1 : ℤ) : ℝ)⟩ : ℂ) + d)) = _
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

private theorem exchangeDifference20 (h f k : ℂ) :
    slack20 h.re h.im f.re f.im k.re k.im =
      5 - ((⟨((-20) : ℝ), (-40)⟩ : ℂ) * ((⟨(2 : ℝ), 1⟩ : ℂ) + h + f * ((⟨(1 : ℝ), 0⟩ : ℂ) - (⟨(2 : ℝ), 1⟩ : ℂ)) + k * (⟨(2 : ℝ), 1⟩ : ℂ) * (⟨(1 : ℝ), 0⟩ : ℂ))).re := by
  norm_num [slack20, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]; ring

private noncomputable def exchange21 : Equiv.Perm (Fin 5) :=
  witnessPermutation ![0, 4, 2, 1, 3] (by decide +kernel)

private theorem exchangeProduct21 (c d : ℂ) :
    matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
      (appendScalar DuplicateAnchor.rightSpectrum d) exchange21 =
    (⟨(20 : ℝ), (-20)⟩ : ℂ) * ((⟨(2 : ℝ), (-2)⟩ : ℂ) + d) * (c + (⟨(1 : ℝ), (-2)⟩ : ℂ)) := by
  rw [matchingProduct, Fin.prod_univ_succ, Fin.prod_univ_four]
  change ((⟨((2 : ℤ) : ℝ), ((1 : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((c + (⟨((1 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨(((-2) : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-1) : ℤ) : ℝ), (((-1) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((0 : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-2) : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ) + d)) = _
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

private theorem exchangeDifference21 (h f k : ℂ) :
    slack21 h.re h.im f.re f.im k.re k.im =
      5 - ((⟨(20 : ℝ), (-20)⟩ : ℂ) * ((⟨(2 : ℝ), (-2)⟩ : ℂ) + h + f * ((⟨(1 : ℝ), (-2)⟩ : ℂ) - (⟨(2 : ℝ), (-2)⟩ : ℂ)) + k * (⟨(2 : ℝ), (-2)⟩ : ℂ) * (⟨(1 : ℝ), (-2)⟩ : ℂ))).re := by
  norm_num [slack21, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]; ring

private noncomputable def exchange22 : Equiv.Perm (Fin 5) :=
  witnessPermutation ![0, 3, 4, 1, 2] (by decide +kernel)

private theorem exchangeProduct22 (c d : ℂ) :
    matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
      (appendScalar DuplicateAnchor.rightSpectrum d) exchange22 =
    (⟨((-8) : ℝ), 44⟩ : ℂ) * ((⟨((-2) : ℝ), 2⟩ : ℂ) + d) * (c + (⟨((-1) : ℝ), (-1)⟩ : ℂ)) := by
  rw [matchingProduct, Fin.prod_univ_succ, Fin.prod_univ_four]
  change ((⟨((2 : ℤ) : ℝ), ((1 : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * (((⟨((2 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ)) * (c + (⟨(((-1) : ℤ) : ℝ), (((-1) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((0 : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-2) : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((⟨(((-2) : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + d)) = _
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

private theorem exchangeDifference22 (h f k : ℂ) :
    slack22 h.re h.im f.re f.im k.re k.im =
      5 - ((⟨((-8) : ℝ), 44⟩ : ℂ) * ((⟨((-2) : ℝ), 2⟩ : ℂ) + h + f * ((⟨((-1) : ℝ), (-1)⟩ : ℂ) - (⟨((-2) : ℝ), 2⟩ : ℂ)) + k * (⟨((-2) : ℝ), 2⟩ : ℂ) * (⟨((-1) : ℝ), (-1)⟩ : ℂ))).re := by
  norm_num [slack22, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]; ring

private noncomputable def exchange23 : Equiv.Perm (Fin 5) :=
  witnessPermutation ![0, 3, 2, 4, 1] (by decide +kernel)

private theorem exchangeProduct23 (c d : ℂ) :
    matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
      (appendScalar DuplicateAnchor.rightSpectrum d) exchange23 =
    (⟨((-30) : ℝ), 40⟩ : ℂ) * ((⟨(0 : ℝ), 2⟩ : ℂ) + d) * (c + (⟨((-2) : ℝ), 0⟩ : ℂ)) := by
  rw [matchingProduct, Fin.prod_univ_succ, Fin.prod_univ_four]
  change ((⟨((2 : ℤ) : ℝ), ((1 : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * (((⟨((2 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨(((-2) : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-1) : ℤ) : ℝ), (((-1) : ℤ) : ℝ)⟩ : ℂ)) * (c + (⟨(((-2) : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((0 : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + d)) = _
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

private theorem exchangeDifference23 (h f k : ℂ) :
    slack23 h.re h.im f.re f.im k.re k.im =
      5 - ((⟨((-30) : ℝ), 40⟩ : ℂ) * ((⟨(0 : ℝ), 2⟩ : ℂ) + h + f * ((⟨((-2) : ℝ), 0⟩ : ℂ) - (⟨(0 : ℝ), 2⟩ : ℂ)) + k * (⟨(0 : ℝ), 2⟩ : ℂ) * (⟨((-2) : ℝ), 0⟩ : ℂ))).re := by
  norm_num [slack23, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]; ring

private noncomputable def exchange27 : Equiv.Perm (Fin 5) :=
  witnessPermutation ![1, 0, 2, 4, 3] (by decide +kernel)

private theorem exchangeProduct27 (c d : ℂ) :
    matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
      (appendScalar DuplicateAnchor.rightSpectrum d) exchange27 =
    (⟨((-20) : ℝ), (-10)⟩ : ℂ) * ((⟨(2 : ℝ), (-2)⟩ : ℂ) + d) * (c + (⟨((-2) : ℝ), 0⟩ : ℂ)) := by
  rw [matchingProduct, Fin.prod_univ_succ, Fin.prod_univ_four]
  change ((⟨((0 : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * (((⟨((2 : ℤ) : ℝ), ((1 : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨(((-2) : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-1) : ℤ) : ℝ), (((-1) : ℤ) : ℝ)⟩ : ℂ)) * (c + (⟨(((-2) : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ) + d)) = _
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

private theorem exchangeDifference27 (h f k : ℂ) :
    slack27 h.re h.im f.re f.im k.re k.im =
      5 - ((⟨((-20) : ℝ), (-10)⟩ : ℂ) * ((⟨(2 : ℝ), (-2)⟩ : ℂ) + h + f * ((⟨((-2) : ℝ), 0⟩ : ℂ) - (⟨(2 : ℝ), (-2)⟩ : ℂ)) + k * (⟨(2 : ℝ), (-2)⟩ : ℂ) * (⟨((-2) : ℝ), 0⟩ : ℂ))).re := by
  norm_num [slack27, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]; ring

private noncomputable def exchange33 : Equiv.Perm (Fin 5) :=
  witnessPermutation ![1, 4, 0, 3, 2] (by decide +kernel)

private theorem exchangeProduct33 (c d : ℂ) :
    matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
      (appendScalar DuplicateAnchor.rightSpectrum d) exchange33 =
    (⟨(4 : ℝ), (-2)⟩ : ℂ) * ((⟨((-2) : ℝ), 2⟩ : ℂ) + d) * (c + (⟨(1 : ℝ), (-2)⟩ : ℂ)) := by
  rw [matchingProduct, Fin.prod_univ_succ, Fin.prod_univ_four]
  change ((⟨((0 : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((c + (⟨((1 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), ((1 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-1) : ℤ) : ℝ), (((-1) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-2) : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((⟨(((-2) : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + d)) = _
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

private theorem exchangeDifference33 (h f k : ℂ) :
    slack33 h.re h.im f.re f.im k.re k.im =
      5 - ((⟨(4 : ℝ), (-2)⟩ : ℂ) * ((⟨((-2) : ℝ), 2⟩ : ℂ) + h + f * ((⟨(1 : ℝ), (-2)⟩ : ℂ) - (⟨((-2) : ℝ), 2⟩ : ℂ)) + k * (⟨((-2) : ℝ), 2⟩ : ℂ) * (⟨(1 : ℝ), (-2)⟩ : ℂ))).re := by
  norm_num [slack33, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]; ring

private noncomputable def exchange44 : Equiv.Perm (Fin 5) :=
  witnessPermutation ![4, 3, 2, 0, 1] (by decide +kernel)

private theorem exchangeProduct44 (c d : ℂ) :
    matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
      (appendScalar DuplicateAnchor.rightSpectrum d) exchange44 =
    (⟨((-15) : ℝ), (-5)⟩ : ℂ) * ((⟨(0 : ℝ), 2⟩ : ℂ) + d) * (c + (⟨(1 : ℝ), 0⟩ : ℂ)) := by
  rw [matchingProduct, Fin.prod_univ_succ, Fin.prod_univ_four]
  change (c + (⟨((1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * (((⟨((2 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨(((-2) : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-1) : ℤ) : ℝ), (((-1) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), ((1 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-2) : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((0 : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + d)) = _
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

private theorem exchangeDifference44 (h f k : ℂ) :
    slack44 h.re h.im f.re f.im k.re k.im =
      5 - ((⟨((-15) : ℝ), (-5)⟩ : ℂ) * ((⟨(0 : ℝ), 2⟩ : ℂ) + h + f * ((⟨(1 : ℝ), 0⟩ : ℂ) - (⟨(0 : ℝ), 2⟩ : ℂ)) + k * (⟨(0 : ℝ), 2⟩ : ℂ) * (⟨(1 : ℝ), 0⟩ : ℂ))).re := by
  norm_num [slack44, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]; ring

private noncomputable def exchange47 : Equiv.Perm (Fin 5) :=
  witnessPermutation ![1, 3, 2, 4, 0] (by decide +kernel)

private theorem exchangeProduct47 (c d : ℂ) :
    matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
      (appendScalar DuplicateAnchor.rightSpectrum d) exchange47 =
    (⟨((-35) : ℝ), 5⟩ : ℂ) * ((⟨(2 : ℝ), 1⟩ : ℂ) + d) * (c + (⟨((-2) : ℝ), 0⟩ : ℂ)) := by
  rw [matchingProduct, Fin.prod_univ_succ, Fin.prod_univ_four]
  change ((⟨((0 : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * (((⟨((2 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨(((-2) : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-1) : ℤ) : ℝ), (((-1) : ℤ) : ℝ)⟩ : ℂ)) * (c + (⟨(((-2) : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), ((1 : ℤ) : ℝ)⟩ : ℂ) + d)) = _
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

private theorem exchangeDifference47 (h f k : ℂ) :
    slack47 h.re h.im f.re f.im k.re k.im =
      5 - ((⟨((-35) : ℝ), 5⟩ : ℂ) * ((⟨(2 : ℝ), 1⟩ : ℂ) + h + f * ((⟨((-2) : ℝ), 0⟩ : ℂ) - (⟨(2 : ℝ), 1⟩ : ℂ)) + k * (⟨(2 : ℝ), 1⟩ : ℂ) * (⟨((-2) : ℝ), 0⟩ : ℂ))).re := by
  norm_num [slack47, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]; ring

private noncomputable def exchange50 : Equiv.Perm (Fin 5) :=
  witnessPermutation ![2, 0, 4, 3, 1] (by decide +kernel)

private theorem exchangeProduct50 (c d : ℂ) :
    matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
      (appendScalar DuplicateAnchor.rightSpectrum d) exchange50 =
    (⟨(14 : ℝ), 2⟩ : ℂ) * ((⟨(0 : ℝ), 2⟩ : ℂ) + d) * (c + (⟨((-1) : ℝ), (-1)⟩ : ℂ)) := by
  rw [matchingProduct, Fin.prod_univ_succ, Fin.prod_univ_four]
  change ((⟨(((-2) : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * (((⟨((2 : ℤ) : ℝ), ((1 : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ)) * (c + (⟨(((-1) : ℤ) : ℝ), (((-1) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-2) : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((0 : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + d)) = _
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

private theorem exchangeDifference50 (h f k : ℂ) :
    slack50 h.re h.im f.re f.im k.re k.im =
      5 - ((⟨(14 : ℝ), 2⟩ : ℂ) * ((⟨(0 : ℝ), 2⟩ : ℂ) + h + f * ((⟨((-1) : ℝ), (-1)⟩ : ℂ) - (⟨(0 : ℝ), 2⟩ : ℂ)) + k * (⟨(0 : ℝ), 2⟩ : ℂ) * (⟨((-1) : ℝ), (-1)⟩ : ℂ))).re := by
  norm_num [slack50, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]; ring

private noncomputable def exchange56 : Equiv.Perm (Fin 5) :=
  witnessPermutation ![4, 1, 0, 3, 2] (by decide +kernel)

private theorem exchangeProduct56 (c d : ℂ) :
    matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
      (appendScalar DuplicateAnchor.rightSpectrum d) exchange56 =
    (⟨(0 : ℝ), (-2)⟩ : ℂ) * ((⟨((-2) : ℝ), 2⟩ : ℂ) + d) * (c + (⟨(1 : ℝ), 0⟩ : ℂ)) := by
  rw [matchingProduct, Fin.prod_univ_succ, Fin.prod_univ_four]
  change (c + (⟨((1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * (((⟨((0 : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), ((1 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-1) : ℤ) : ℝ), (((-1) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-2) : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((⟨(((-2) : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + d)) = _
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

private theorem exchangeDifference56 (h f k : ℂ) :
    slack56 h.re h.im f.re f.im k.re k.im =
      5 - ((⟨(0 : ℝ), (-2)⟩ : ℂ) * ((⟨((-2) : ℝ), 2⟩ : ℂ) + h + f * ((⟨(1 : ℝ), 0⟩ : ℂ) - (⟨((-2) : ℝ), 2⟩ : ℂ)) + k * (⟨((-2) : ℝ), 2⟩ : ℂ) * (⟨(1 : ℝ), 0⟩ : ℂ))).re := by
  norm_num [slack56, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]; ring

private noncomputable def exchange57 : Equiv.Perm (Fin 5) :=
  witnessPermutation ![2, 4, 0, 3, 1] (by decide +kernel)

private theorem exchangeProduct57 (c d : ℂ) :
    matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
      (appendScalar DuplicateAnchor.rightSpectrum d) exchange57 =
    (⟨(4 : ℝ), 2⟩ : ℂ) * ((⟨(0 : ℝ), 2⟩ : ℂ) + d) * (c + (⟨(1 : ℝ), (-2)⟩ : ℂ)) := by
  rw [matchingProduct, Fin.prod_univ_succ, Fin.prod_univ_four]
  change ((⟨(((-2) : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((c + (⟨((1 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), ((1 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-1) : ℤ) : ℝ), (((-1) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-2) : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((0 : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + d)) = _
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

private theorem exchangeDifference57 (h f k : ℂ) :
    slack57 h.re h.im f.re f.im k.re k.im =
      5 - ((⟨(4 : ℝ), 2⟩ : ℂ) * ((⟨(0 : ℝ), 2⟩ : ℂ) + h + f * ((⟨(1 : ℝ), (-2)⟩ : ℂ) - (⟨(0 : ℝ), 2⟩ : ℂ)) + k * (⟨(0 : ℝ), 2⟩ : ℂ) * (⟨(1 : ℝ), (-2)⟩ : ℂ))).re := by
  norm_num [slack57, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]; ring

private noncomputable def exchange58 : Equiv.Perm (Fin 5) :=
  witnessPermutation ![2, 1, 4, 3, 0] (by decide +kernel)

private theorem exchangeProduct58 (c d : ℂ) :
    matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
      (appendScalar DuplicateAnchor.rightSpectrum d) exchange58 =
    (⟨(4 : ℝ), 2⟩ : ℂ) * ((⟨(2 : ℝ), 1⟩ : ℂ) + d) * (c + (⟨((-1) : ℝ), (-1)⟩ : ℂ)) := by
  rw [matchingProduct, Fin.prod_univ_succ, Fin.prod_univ_four]
  change ((⟨(((-2) : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * (((⟨((0 : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ)) * (c + (⟨(((-1) : ℤ) : ℝ), (((-1) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-2) : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), ((1 : ℤ) : ℝ)⟩ : ℂ) + d)) = _
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

private theorem exchangeDifference58 (h f k : ℂ) :
    slack58 h.re h.im f.re f.im k.re k.im =
      5 - ((⟨(4 : ℝ), 2⟩ : ℂ) * ((⟨(2 : ℝ), 1⟩ : ℂ) + h + f * ((⟨((-1) : ℝ), (-1)⟩ : ℂ) - (⟨(2 : ℝ), 1⟩ : ℂ)) + k * (⟨(2 : ℝ), 1⟩ : ℂ) * (⟨((-1) : ℝ), (-1)⟩ : ℂ))).re := by
  norm_num [slack58, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]; ring

private noncomputable def exchange59 : Equiv.Perm (Fin 5) :=
  witnessPermutation ![2, 1, 0, 4, 3] (by decide +kernel)

private theorem exchangeProduct59 (c d : ℂ) :
    matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
      (appendScalar DuplicateAnchor.rightSpectrum d) exchange59 =
    (⟨((-1) : ℝ), 2⟩ : ℂ) * ((⟨(2 : ℝ), (-2)⟩ : ℂ) + d) * (c + (⟨((-2) : ℝ), 0⟩ : ℂ)) := by
  rw [matchingProduct, Fin.prod_univ_succ, Fin.prod_univ_four]
  change ((⟨(((-2) : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * (((⟨((0 : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), ((1 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-1) : ℤ) : ℝ), (((-1) : ℤ) : ℝ)⟩ : ℂ)) * (c + (⟨(((-2) : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ) + d)) = _
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

private theorem exchangeDifference59 (h f k : ℂ) :
    slack59 h.re h.im f.re f.im k.re k.im =
      5 - ((⟨((-1) : ℝ), 2⟩ : ℂ) * ((⟨(2 : ℝ), (-2)⟩ : ℂ) + h + f * ((⟨((-2) : ℝ), 0⟩ : ℂ) - (⟨(2 : ℝ), (-2)⟩ : ℂ)) + k * (⟨(2 : ℝ), (-2)⟩ : ℂ) * (⟨((-2) : ℝ), 0⟩ : ℂ))).re := by
  norm_num [slack59, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]; ring

private noncomputable def exchange68 : Equiv.Perm (Fin 5) :=
  witnessPermutation ![4, 3, 1, 0, 2] (by decide +kernel)

private theorem exchangeProduct68 (c d : ℂ) :
    matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
      (appendScalar DuplicateAnchor.rightSpectrum d) exchange68 =
    (⟨((-7) : ℝ), 1⟩ : ℂ) * ((⟨((-2) : ℝ), 2⟩ : ℂ) + d) * (c + (⟨(1 : ℝ), 0⟩ : ℂ)) := by
  rw [matchingProduct, Fin.prod_univ_succ, Fin.prod_univ_four]
  change (c + (⟨((1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * (((⟨((2 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((0 : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-1) : ℤ) : ℝ), (((-1) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), ((1 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-2) : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((⟨(((-2) : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + d)) = _
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

private theorem exchangeDifference68 (h f k : ℂ) :
    slack68 h.re h.im f.re f.im k.re k.im =
      5 - ((⟨((-7) : ℝ), 1⟩ : ℂ) * ((⟨((-2) : ℝ), 2⟩ : ℂ) + h + f * ((⟨(1 : ℝ), 0⟩ : ℂ) - (⟨((-2) : ℝ), 2⟩ : ℂ)) + k * (⟨((-2) : ℝ), 2⟩ : ℂ) * (⟨(1 : ℝ), 0⟩ : ℂ))).re := by
  norm_num [slack68, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]; ring

private noncomputable def exchange69 : Equiv.Perm (Fin 5) :=
  witnessPermutation ![2, 4, 1, 0, 3] (by decide +kernel)

private theorem exchangeProduct69 (c d : ℂ) :
    matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
      (appendScalar DuplicateAnchor.rightSpectrum d) exchange69 =
    (⟨(3 : ℝ), (-1)⟩ : ℂ) * ((⟨(2 : ℝ), (-2)⟩ : ℂ) + d) * (c + (⟨(1 : ℝ), (-2)⟩ : ℂ)) := by
  rw [matchingProduct, Fin.prod_univ_succ, Fin.prod_univ_four]
  change ((⟨(((-2) : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((c + (⟨((1 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((0 : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-1) : ℤ) : ℝ), (((-1) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), ((1 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-2) : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ) + d)) = _
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

private theorem exchangeDifference69 (h f k : ℂ) :
    slack69 h.re h.im f.re f.im k.re k.im =
      5 - ((⟨(3 : ℝ), (-1)⟩ : ℂ) * ((⟨(2 : ℝ), (-2)⟩ : ℂ) + h + f * ((⟨(1 : ℝ), (-2)⟩ : ℂ) - (⟨(2 : ℝ), (-2)⟩ : ℂ)) + k * (⟨(2 : ℝ), (-2)⟩ : ℂ) * (⟨(1 : ℝ), (-2)⟩ : ℂ))).re := by
  norm_num [slack69, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]; ring

private noncomputable def exchange70 : Equiv.Perm (Fin 5) :=
  witnessPermutation ![2, 3, 4, 0, 1] (by decide +kernel)

private theorem exchangeProduct70 (c d : ℂ) :
    matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
      (appendScalar DuplicateAnchor.rightSpectrum d) exchange70 =
    (⟨((-10) : ℝ), 5⟩ : ℂ) * ((⟨(0 : ℝ), 2⟩ : ℂ) + d) * (c + (⟨((-1) : ℝ), (-1)⟩ : ℂ)) := by
  rw [matchingProduct, Fin.prod_univ_succ, Fin.prod_univ_four]
  change ((⟨(((-2) : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * (((⟨((2 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ)) * (c + (⟨(((-1) : ℤ) : ℝ), (((-1) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), ((1 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-2) : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((0 : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + d)) = _
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

private theorem exchangeDifference70 (h f k : ℂ) :
    slack70 h.re h.im f.re f.im k.re k.im =
      5 - ((⟨((-10) : ℝ), 5⟩ : ℂ) * ((⟨(0 : ℝ), 2⟩ : ℂ) + h + f * ((⟨((-1) : ℝ), (-1)⟩ : ℂ) - (⟨(0 : ℝ), 2⟩ : ℂ)) + k * (⟨(0 : ℝ), 2⟩ : ℂ) * (⟨((-1) : ℝ), (-1)⟩ : ℂ))).re := by
  norm_num [slack70, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]; ring

private noncomputable def exchange71 : Equiv.Perm (Fin 5) :=
  witnessPermutation ![2, 3, 1, 4, 0] (by decide +kernel)

private theorem exchangeProduct71 (c d : ℂ) :
    matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
      (appendScalar DuplicateAnchor.rightSpectrum d) exchange71 =
    (⟨((-15) : ℝ), (-5)⟩ : ℂ) * ((⟨(2 : ℝ), 1⟩ : ℂ) + d) * (c + (⟨((-2) : ℝ), 0⟩ : ℂ)) := by
  rw [matchingProduct, Fin.prod_univ_succ, Fin.prod_univ_four]
  change ((⟨(((-2) : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * (((⟨((2 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((0 : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-1) : ℤ) : ℝ), (((-1) : ℤ) : ℝ)⟩ : ℂ)) * (c + (⟨(((-2) : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), ((1 : ℤ) : ℝ)⟩ : ℂ) + d)) = _
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

private theorem exchangeDifference71 (h f k : ℂ) :
    slack71 h.re h.im f.re f.im k.re k.im =
      5 - ((⟨((-15) : ℝ), (-5)⟩ : ℂ) * ((⟨(2 : ℝ), 1⟩ : ℂ) + h + f * ((⟨((-2) : ℝ), 0⟩ : ℂ) - (⟨(2 : ℝ), 1⟩ : ℂ)) + k * (⟨(2 : ℝ), 1⟩ : ℂ) * (⟨((-2) : ℝ), 0⟩ : ℂ))).re := by
  norm_num [slack71, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]; ring

private noncomputable def exchange80 : Equiv.Perm (Fin 5) :=
  witnessPermutation ![4, 1, 0, 2, 3] (by decide +kernel)

private theorem exchangeProduct80 (c d : ℂ) :
    matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
      (appendScalar DuplicateAnchor.rightSpectrum d) exchange80 =
    (⟨((-4) : ℝ), 2⟩ : ℂ) * ((⟨(2 : ℝ), (-2)⟩ : ℂ) + d) * (c + (⟨(1 : ℝ), 0⟩ : ℂ)) := by
  rw [matchingProduct, Fin.prod_univ_succ, Fin.prod_univ_four]
  change (c + (⟨((1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * (((⟨((0 : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), ((1 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-1) : ℤ) : ℝ), (((-1) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨(((-2) : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-2) : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ) + d)) = _
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

private theorem exchangeDifference80 (h f k : ℂ) :
    slack80 h.re h.im f.re f.im k.re k.im =
      5 - ((⟨((-4) : ℝ), 2⟩ : ℂ) * ((⟨(2 : ℝ), (-2)⟩ : ℂ) + h + f * ((⟨(1 : ℝ), 0⟩ : ℂ) - (⟨(2 : ℝ), (-2)⟩ : ℂ)) + k * (⟨(2 : ℝ), (-2)⟩ : ℂ) * (⟨(1 : ℝ), 0⟩ : ℂ))).re := by
  norm_num [slack80, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]; ring

private noncomputable def exchange88 : Equiv.Perm (Fin 5) :=
  witnessPermutation ![4, 2, 0, 1, 3] (by decide +kernel)

private theorem exchangeProduct88 (c d : ℂ) :
    matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
      (appendScalar DuplicateAnchor.rightSpectrum d) exchange88 =
    (⟨(2 : ℝ), (-2)⟩ : ℂ) * ((⟨(2 : ℝ), (-2)⟩ : ℂ) + d) * (c + (⟨(1 : ℝ), 0⟩ : ℂ)) := by
  rw [matchingProduct, Fin.prod_univ_succ, Fin.prod_univ_four]
  change (c + (⟨((1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * (((⟨(((-2) : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), ((1 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-1) : ℤ) : ℝ), (((-1) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((0 : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-2) : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ) + d)) = _
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

private theorem exchangeDifference88 (h f k : ℂ) :
    slack88 h.re h.im f.re f.im k.re k.im =
      5 - ((⟨(2 : ℝ), (-2)⟩ : ℂ) * ((⟨(2 : ℝ), (-2)⟩ : ℂ) + h + f * ((⟨(1 : ℝ), 0⟩ : ℂ) - (⟨(2 : ℝ), (-2)⟩ : ℂ)) + k * (⟨(2 : ℝ), (-2)⟩ : ℂ) * (⟨(1 : ℝ), 0⟩ : ℂ))).re := by
  norm_num [slack88, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]; ring

private noncomputable def exchange89 : Equiv.Perm (Fin 5) :=
  witnessPermutation ![3, 4, 0, 1, 2] (by decide +kernel)

private theorem exchangeProduct89 (c d : ℂ) :
    matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
      (appendScalar DuplicateAnchor.rightSpectrum d) exchange89 =
    (⟨((-2) : ℝ), 10⟩ : ℂ) * ((⟨((-2) : ℝ), 2⟩ : ℂ) + d) * (c + (⟨(1 : ℝ), (-2)⟩ : ℂ)) := by
  rw [matchingProduct, Fin.prod_univ_succ, Fin.prod_univ_four]
  change ((⟨((2 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((c + (⟨((1 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), ((1 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-1) : ℤ) : ℝ), (((-1) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((0 : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-2) : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((⟨(((-2) : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + d)) = _
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

private theorem exchangeDifference89 (h f k : ℂ) :
    slack89 h.re h.im f.re f.im k.re k.im =
      5 - ((⟨((-2) : ℝ), 10⟩ : ℂ) * ((⟨((-2) : ℝ), 2⟩ : ℂ) + h + f * ((⟨(1 : ℝ), (-2)⟩ : ℂ) - (⟨((-2) : ℝ), 2⟩ : ℂ)) + k * (⟨((-2) : ℝ), 2⟩ : ℂ) * (⟨(1 : ℝ), (-2)⟩ : ℂ))).re := by
  norm_num [slack89, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]; ring

private noncomputable def exchange90 : Equiv.Perm (Fin 5) :=
  witnessPermutation ![3, 2, 4, 1, 0] (by decide +kernel)

private theorem exchangeProduct90 (c d : ℂ) :
    matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
      (appendScalar DuplicateAnchor.rightSpectrum d) exchange90 =
    (⟨(2 : ℝ), (-10)⟩ : ℂ) * ((⟨(2 : ℝ), 1⟩ : ℂ) + d) * (c + (⟨((-1) : ℝ), (-1)⟩ : ℂ)) := by
  rw [matchingProduct, Fin.prod_univ_succ, Fin.prod_univ_four]
  change ((⟨((2 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * (((⟨(((-2) : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ)) * (c + (⟨(((-1) : ℤ) : ℝ), (((-1) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((0 : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-2) : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), ((1 : ℤ) : ℝ)⟩ : ℂ) + d)) = _
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

private theorem exchangeDifference90 (h f k : ℂ) :
    slack90 h.re h.im f.re f.im k.re k.im =
      5 - ((⟨(2 : ℝ), (-10)⟩ : ℂ) * ((⟨(2 : ℝ), 1⟩ : ℂ) + h + f * ((⟨((-1) : ℝ), (-1)⟩ : ℂ) - (⟨(2 : ℝ), 1⟩ : ℂ)) + k * (⟨(2 : ℝ), 1⟩ : ℂ) * (⟨((-1) : ℝ), (-1)⟩ : ℂ))).re := by
  norm_num [slack90, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]; ring

private noncomputable def exchange92 : Equiv.Perm (Fin 5) :=
  witnessPermutation ![4, 2, 1, 0, 3] (by decide +kernel)

private theorem exchangeProduct92 (c d : ℂ) :
    matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
      (appendScalar DuplicateAnchor.rightSpectrum d) exchange92 =
    (⟨(1 : ℝ), 1⟩ : ℂ) * ((⟨(2 : ℝ), (-2)⟩ : ℂ) + d) * (c + (⟨(1 : ℝ), 0⟩ : ℂ)) := by
  rw [matchingProduct, Fin.prod_univ_succ, Fin.prod_univ_four]
  change (c + (⟨((1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * (((⟨(((-2) : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((0 : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-1) : ℤ) : ℝ), (((-1) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), ((1 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-2) : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ) + d)) = _
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

private theorem exchangeDifference92 (h f k : ℂ) :
    slack92 h.re h.im f.re f.im k.re k.im =
      5 - ((⟨(1 : ℝ), 1⟩ : ℂ) * ((⟨(2 : ℝ), (-2)⟩ : ℂ) + h + f * ((⟨(1 : ℝ), 0⟩ : ℂ) - (⟨(2 : ℝ), (-2)⟩ : ℂ)) + k * (⟨(2 : ℝ), (-2)⟩ : ℂ) * (⟨(1 : ℝ), 0⟩ : ℂ))).re := by
  norm_num [slack92, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]; ring

private noncomputable def exchange93 : Equiv.Perm (Fin 5) :=
  witnessPermutation ![3, 4, 1, 0, 2] (by decide +kernel)

private theorem exchangeProduct93 (c d : ℂ) :
    matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
      (appendScalar DuplicateAnchor.rightSpectrum d) exchange93 =
    (⟨((-5) : ℝ), (-1)⟩ : ℂ) * ((⟨((-2) : ℝ), 2⟩ : ℂ) + d) * (c + (⟨(1 : ℝ), (-2)⟩ : ℂ)) := by
  rw [matchingProduct, Fin.prod_univ_succ, Fin.prod_univ_four]
  change ((⟨((2 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((c + (⟨((1 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((0 : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-1) : ℤ) : ℝ), (((-1) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), ((1 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-2) : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((⟨(((-2) : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + d)) = _
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

private theorem exchangeDifference93 (h f k : ℂ) :
    slack93 h.re h.im f.re f.im k.re k.im =
      5 - ((⟨((-5) : ℝ), (-1)⟩ : ℂ) * ((⟨((-2) : ℝ), 2⟩ : ℂ) + h + f * ((⟨(1 : ℝ), (-2)⟩ : ℂ) - (⟨((-2) : ℝ), 2⟩ : ℂ)) + k * (⟨((-2) : ℝ), 2⟩ : ℂ) * (⟨(1 : ℝ), (-2)⟩ : ℂ))).re := by
  norm_num [slack93, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]; ring

private noncomputable def exchange94 : Equiv.Perm (Fin 5) :=
  witnessPermutation ![3, 2, 4, 0, 1] (by decide +kernel)

private theorem exchangeProduct94 (c d : ℂ) :
    matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
      (appendScalar DuplicateAnchor.rightSpectrum d) exchange94 =
    (⟨((-2) : ℝ), (-3)⟩ : ℂ) * ((⟨(0 : ℝ), 2⟩ : ℂ) + d) * (c + (⟨((-1) : ℝ), (-1)⟩ : ℂ)) := by
  rw [matchingProduct, Fin.prod_univ_succ, Fin.prod_univ_four]
  change ((⟨((2 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * (((⟨(((-2) : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ)) * (c + (⟨(((-1) : ℤ) : ℝ), (((-1) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), ((1 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-2) : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((0 : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + d)) = _
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

private theorem exchangeDifference94 (h f k : ℂ) :
    slack94 h.re h.im f.re f.im k.re k.im =
      5 - ((⟨((-2) : ℝ), (-3)⟩ : ℂ) * ((⟨(0 : ℝ), 2⟩ : ℂ) + h + f * ((⟨((-1) : ℝ), (-1)⟩ : ℂ) - (⟨(0 : ℝ), 2⟩ : ℂ)) + k * (⟨(0 : ℝ), 2⟩ : ℂ) * (⟨((-1) : ℝ), (-1)⟩ : ℂ))).re := by
  norm_num [slack94, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]; ring

private noncomputable def exchange95 : Equiv.Perm (Fin 5) :=
  witnessPermutation ![3, 2, 1, 4, 0] (by decide +kernel)

private theorem exchangeProduct95 (c d : ℂ) :
    matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
      (appendScalar DuplicateAnchor.rightSpectrum d) exchange95 =
    (⟨(1 : ℝ), (-5)⟩ : ℂ) * ((⟨(2 : ℝ), 1⟩ : ℂ) + d) * (c + (⟨((-2) : ℝ), 0⟩ : ℂ)) := by
  rw [matchingProduct, Fin.prod_univ_succ, Fin.prod_univ_four]
  change ((⟨((2 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * (((⟨(((-2) : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨((1 : ℤ) : ℝ), (((-2) : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((0 : ℤ) : ℝ), ((2 : ℤ) : ℝ)⟩ : ℂ) + (⟨(((-1) : ℤ) : ℝ), (((-1) : ℤ) : ℝ)⟩ : ℂ)) * (c + (⟨(((-2) : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ)) * ((⟨((2 : ℤ) : ℝ), ((1 : ℤ) : ℝ)⟩ : ℂ) + d)) = _
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

private theorem exchangeDifference95 (h f k : ℂ) :
    slack95 h.re h.im f.re f.im k.re k.im =
      5 - ((⟨(1 : ℝ), (-5)⟩ : ℂ) * ((⟨(2 : ℝ), 1⟩ : ℂ) + h + f * ((⟨((-2) : ℝ), 0⟩ : ℂ) - (⟨(2 : ℝ), 1⟩ : ℂ)) + k * (⟨(2 : ℝ), 1⟩ : ℂ) * (⟨((-2) : ℝ), 0⟩ : ℂ))).re := by
  norm_num [slack95, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]; ring

/-- Every scalar padding with nonzero sum creates a normalized matching
product with real part greater than the original support of five. -/
theorem scalar_support_exceeds (c d : ℂ) (hn : c + d ≠ 0) :
    ∃ τ : Equiv.Perm (Fin 5),
      5 < (matchingProduct (appendScalar DuplicateAnchor.leftSpectrum c)
        (appendScalar DuplicateAnchor.rightSpectrum d) τ / (c + d)).re := by
  by_contra! upper
  let h := c * d / (c + d)
  let f := d / (c + d)
  let k := 1 / (c + d)
  have rank := scalarRank c d h f k hn rfl rfl rfl
  have hre : h.re * k.re - h.im * k.im + f.re * f.re - f.im * f.im - f.re = 0 := by
    have he := congrArg Complex.re rank
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im] at he
    apply Eq.trans _ (sub_eq_zero.mpr he)
    ring
  have him : h.re * k.im + h.im * k.re + 2 * f.re * f.im - f.im = 0 := by
    have he := congrArg Complex.im rank
    simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im] at he
    apply Eq.trans _ (sub_eq_zero.mpr he)
    ring
  have justify := @slackOfExchange c d h f k hn rfl rfl rfl upper
  apply infeasible h.re h.im f.re f.im k.re k.im
  · exact @justify _ _ _ _ _ (exchangeProduct3 c d) (exchangeDifference3 h f k)
  · exact @justify _ _ _ _ _ (exchangeProduct4 c d) (exchangeDifference4 h f k)
  · exact @justify _ _ _ _ _ (exchangeProduct13 c d) (exchangeDifference13 h f k)
  · exact @justify _ _ _ _ _ (exchangeProduct14 c d) (exchangeDifference14 h f k)
  · exact @justify _ _ _ _ _ (exchangeProduct20 c d) (exchangeDifference20 h f k)
  · exact @justify _ _ _ _ _ (exchangeProduct21 c d) (exchangeDifference21 h f k)
  · exact @justify _ _ _ _ _ (exchangeProduct22 c d) (exchangeDifference22 h f k)
  · exact @justify _ _ _ _ _ (exchangeProduct23 c d) (exchangeDifference23 h f k)
  · exact @justify _ _ _ _ _ (exchangeProduct27 c d) (exchangeDifference27 h f k)
  · exact @justify _ _ _ _ _ (exchangeProduct33 c d) (exchangeDifference33 h f k)
  · exact @justify _ _ _ _ _ (exchangeProduct44 c d) (exchangeDifference44 h f k)
  · exact @justify _ _ _ _ _ (exchangeProduct47 c d) (exchangeDifference47 h f k)
  · exact @justify _ _ _ _ _ (exchangeProduct50 c d) (exchangeDifference50 h f k)
  · exact @justify _ _ _ _ _ (exchangeProduct56 c d) (exchangeDifference56 h f k)
  · exact @justify _ _ _ _ _ (exchangeProduct57 c d) (exchangeDifference57 h f k)
  · exact @justify _ _ _ _ _ (exchangeProduct58 c d) (exchangeDifference58 h f k)
  · exact @justify _ _ _ _ _ (exchangeProduct59 c d) (exchangeDifference59 h f k)
  · exact @justify _ _ _ _ _ (exchangeProduct68 c d) (exchangeDifference68 h f k)
  · exact @justify _ _ _ _ _ (exchangeProduct69 c d) (exchangeDifference69 h f k)
  · exact @justify _ _ _ _ _ (exchangeProduct70 c d) (exchangeDifference70 h f k)
  · exact @justify _ _ _ _ _ (exchangeProduct71 c d) (exchangeDifference71 h f k)
  · exact @justify _ _ _ _ _ (exchangeProduct80 c d) (exchangeDifference80 h f k)
  · exact @justify _ _ _ _ _ (exchangeProduct88 c d) (exchangeDifference88 h f k)
  · exact @justify _ _ _ _ _ (exchangeProduct89 c d) (exchangeDifference89 h f k)
  · exact @justify _ _ _ _ _ (exchangeProduct90 c d) (exchangeDifference90 h f k)
  · exact @justify _ _ _ _ _ (exchangeProduct92 c d) (exchangeDifference92 h f k)
  · exact @justify _ _ _ _ _ (exchangeProduct93 c d) (exchangeDifference93 h f k)
  · exact @justify _ _ _ _ _ (exchangeProduct94 c d) (exchangeDifference94 h f k)
  · exact @justify _ _ _ _ _ (exchangeProduct95 c d) (exchangeDifference95 h f k)
  · exact hre
  · exact him

end MOC.ScalarAnchor
