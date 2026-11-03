/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import BoxKGen.Templates
public import BoxKGen.N11x16.Base
-- Build order only (at most 2 certificate modules build at once).
import BoxKGen.N11x14.S7

@[expose] public section

set_option Elab.async false
namespace BoxKGen.N11x16
open ZZN ZZN.Cut ZZN.BoxK BoxKGen

noncomputable def d1120 : CData := (![4,4,4,6], [], [(t3792, ⟨false, false, false, true, true, true⟩), (t6965, ⟨false, false, false, true, false, false⟩), (t3742, ⟨false, false, false, false, false, true⟩), (t3787, ⟨false, false, false, false, true, true⟩), (t5600, ⟨false, false, false, false, true, true⟩), (t1975, ⟨false, false, false, false, false, false⟩), (t9237, ⟨false, false, false, true, false, false⟩)], [], [])
theorem sl1120 : sliceCOK 11 16 d1120.1 L1 b1 11 ![4,4,4,6] d1120.2.1 0 d1120.2.2.1 d1120.2.2.2.1 [] d1120.2.2.2.2 = true := by decide +kernel
theorem g1120 : SliceGood 11 16 d1120.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 11 16 ![4,4,4,6] [] [])) sl1120
noncomputable def d1121 : CData := (![4,4,5,5], [], [(t5, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl1121 : sliceCOK 11 16 d1121.1 L2 b2 11 ![4,4,5,5] d1121.2.1 0 d1121.2.2.1 d1121.2.2.2.1 [] d1121.2.2.2.2 = true := by decide +kernel
theorem g1121 : SliceGood 11 16 d1121.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base2 (subM_zero (tgtM 11 16 ![4,4,5,5] [] [])) sl1121
noncomputable def d1122 : CData := (![4,4,5,6], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t4374, ⟨false, false, false, false, true, true⟩), (t4, ⟨false, false, false, false, false, false⟩), (t93, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl1122 : sliceCOK 11 16 d1122.1 L1 b1 11 ![4,4,5,6] d1122.2.1 0 d1122.2.2.1 d1122.2.2.2.1 [] d1122.2.2.2.2 = true := by decide +kernel
theorem g1122 : SliceGood 11 16 d1122.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 11 16 ![4,4,5,6] [] [])) sl1122
noncomputable def d1123 : CData := (![4,4,6,6], [], [(t5, ⟨false, false, false, false, false, false⟩), (t3742, ⟨false, false, false, false, false, true⟩), (t4374, ⟨false, false, false, false, false, true⟩)], [], [])
theorem sl1123 : sliceCOK 11 16 d1123.1 L3 b3 11 ![4,4,6,6] d1123.2.1 0 d1123.2.2.1 d1123.2.2.2.1 [] d1123.2.2.2.2 = true := by decide +kernel
theorem g1123 : SliceGood 11 16 d1123.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base3 (subM_zero (tgtM 11 16 ![4,4,6,6] [] [])) sl1123
noncomputable def d1124 : CData := (![4,5,4,5], [], [(t3763, ⟨false, false, false, false, false, true⟩), (t148, ⟨false, false, false, false, false, false⟩), (t4285, ⟨false, false, false, true, false, true⟩), (t1548, ⟨false, false, false, false, false, false⟩), (t3033, ⟨false, false, false, false, false, false⟩), (t15, ⟨false, false, false, true, false, false⟩), (t2434, ⟨false, false, false, false, false, false⟩), (t9194, ⟨false, false, false, true, true, false⟩), (t806, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl1124 : sliceCOK 11 16 d1124.1 L4 b4 11 ![4,5,4,5] d1124.2.1 0 d1124.2.2.1 d1124.2.2.2.1 [] d1124.2.2.2.2 = true := by decide +kernel
theorem g1124 : SliceGood 11 16 d1124.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base4 (subM_zero (tgtM 11 16 ![4,5,4,5] [] [])) sl1124
noncomputable def d1125 : CData := (![4,5,4,6], [], [(t2048, ⟨false, false, false, false, false, false⟩), (t4873, ⟨false, false, false, true, true, true⟩), (t1867, ⟨false, false, false, false, false, false⟩), (t4835, ⟨false, false, false, true, true, false⟩), (t3770, ⟨false, false, false, true, true, false⟩), (t5592, ⟨false, false, false, true, true, true⟩), (t6769, ⟨false, false, false, true, false, false⟩), (t4, ⟨false, false, false, false, false, false⟩), (t9725, ⟨false, false, false, false, true, true⟩)], [], [])
theorem sl1125 : sliceCOK 11 16 d1125.1 L5 b5 11 ![4,5,4,6] d1125.2.1 0 d1125.2.2.1 d1125.2.2.2.1 [] d1125.2.2.2.2 = true := by decide +kernel
theorem g1125 : SliceGood 11 16 d1125.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 11 16 ![4,5,4,6] [] [])) sl1125
noncomputable def d1126 : CData := (![4,5,5,5], [], [(t7518, ⟨false, false, false, true, false, true⟩), (t9525, ⟨false, false, false, true, false, false⟩), (t7517, ⟨false, false, false, true, false, false⟩), (t6917, ⟨false, false, false, false, true, true⟩)], [], [])
theorem sl1126 : sliceCOK 11 16 d1126.1 L6 b6 11 ![4,5,5,5] d1126.2.1 0 d1126.2.2.1 d1126.2.2.2.1 [] d1126.2.2.2.2 = true := by decide +kernel
theorem g1126 : SliceGood 11 16 d1126.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base6 (subM_zero (tgtM 11 16 ![4,5,5,5] [] [])) sl1126
noncomputable def d1127 : CData := (![4,5,5,6], [], [(t3936, ⟨false, false, false, false, true, true⟩), (t2576, ⟨false, false, false, false, false, false⟩), (t9234, ⟨false, false, false, false, true, true⟩), (t2343, ⟨false, false, false, false, false, false⟩), (t4, ⟨false, false, false, false, false, false⟩), (t3895, ⟨false, false, false, false, false, false⟩), (t88, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl1127 : sliceCOK 11 16 d1127.1 L7 b7 11 ![4,5,5,6] d1127.2.1 0 d1127.2.2.1 d1127.2.2.2.1 [] d1127.2.2.2.2 = true := by decide +kernel
theorem g1127 : SliceGood 11 16 d1127.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base7 (subM_zero (tgtM 11 16 ![4,5,5,6] [] [])) sl1127
noncomputable def d1128 : CData := (![4,6,4,6], [], [(t1976, ⟨false, false, false, false, false, false⟩), (t92, ⟨false, false, false, false, false, false⟩), (t4210, ⟨false, false, false, false, true, false⟩), (t3742, ⟨false, false, false, false, false, true⟩), (t25, ⟨false, false, false, false, false, false⟩), (t2251, ⟨false, false, false, false, false, false⟩), (t4511, ⟨false, false, false, true, true, false⟩), (t6381, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl1128 : sliceCOK 11 16 d1128.1 L8 b8 11 ![4,6,4,6] d1128.2.1 0 d1128.2.2.1 d1128.2.2.2.1 [] d1128.2.2.2.2 = true := by decide +kernel
theorem g1128 : SliceGood 11 16 d1128.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base8 (subM_zero (tgtM 11 16 ![4,6,4,6] [] [])) sl1128
noncomputable def d1129 : CData := (![4,6,5,5], [], [(t3925, ⟨false, false, false, false, true, true⟩), (t1277, ⟨false, false, false, false, false, true⟩)], [], [])
theorem sl1129 : sliceCOK 11 16 d1129.1 L10 b10 11 ![4,6,5,5] d1129.2.1 0 d1129.2.2.1 d1129.2.2.2.1 [] d1129.2.2.2.2 = true := by decide +kernel
theorem g1129 : SliceGood 11 16 d1129.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base10 (subM_zero (tgtM 11 16 ![4,6,5,5] [] [])) sl1129
noncomputable def d1130 : CData := (![5,5,5,5], [], [(t1297, ⟨false, false, false, false, false, false⟩), (t3763, ⟨false, false, false, false, false, true⟩), (t5511, ⟨false, false, false, false, false, false⟩), (t1278, ⟨false, false, false, false, false, false⟩)], [], [(1693, 151, 1485516154921036856198492106163289284633774060021597550894248176806500798102638589271305717563431345658476368269440378650037229481453062550180952454651661866525419503435860190833008285988516012760146524807473009983917912640501953635635350326390707294969629213640478285932381299064527196742526176310381728374732275734300891946232565850130394941768972082924118630480, 25, 585664355415514533789255866110783301832687102647506867739225), (1695, 139, 18749849899063135124583756251733157555166034214530426754137308944531947921870779347276934383008692240884979217662449048349686951085833025682766125862118528839076923339480328736676325094815464586701507554698671355661183675854499223321424622093589781307215381031015382653495138841007521425221024092490019083342914084914411627605388189776, 37, 47399657776895041883509528490124678220345163574459830876883226098603616802895812719434329), (2413, 110, 2813625312842511490150922175934448717299490505638245112057910292915358372853214067223482543900985306086583336052081481493431418028546861932689417911754744634703545958170174335071465126717068518437156137182308127074512776083261719990145838036501144925913797037678672, 66, 320681118014419104314374828397828092838146517471948596254329842005125926422505980645941793747947581564886178401210453373874274556928402666071319747078021142358), (2415, 80, 1593503865695003538159092307632759706091633455012521979674314792078234028031876158664277833021996006247100768555293552949495427845024246083688227108168570588049092961539329887208688400127254608, 96, 578771104582260073707462710354369659921180703989294724879113751028685087686213964235829860952216779249092602674137078306675536398306080740374036926070173472646877171257012772244066671385773465148681276800365020398242040486050612822), (9885, 129, 15520039830416428801672283706573578798683054543736426902907427457690775143332165107955851799933685069180762753815931669843861085230454416057618607879424155218606640984554801934792107723161885676609065383478299377077534404023545457549824757034336167872547290069364204040413179983374711471911681711265047711404370, 47, 56095500819898194370570686909365786676616394812143834912926557099653907689369230800694969526733711989004902615385), (10605, 114, 12084397641420874350201542603735916892046950831146985611104395762678728709641813287415259572901453667309722504840937740208615056096815298237648780750379607925750100312291380357917599160192137294866766102157338609287970819497039033090692568392318313444704123263949058391232850, 62, 74664391114939727129997072763630604817122351883216130226294322131860037078156413165581241623287475343617862488767444185122436459011245473100433155670)])
theorem sl1130 : sliceCOK 11 16 d1130.1 L11 b11 11 ![5,5,5,5] d1130.2.1 0 d1130.2.2.1 d1130.2.2.2.1 [] d1130.2.2.2.2 = true := by decide +kernel
theorem g1130 : SliceGood 11 16 d1130.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base11 (subM_zero (tgtM 11 16 ![5,5,5,5] [] [])) sl1130
end BoxKGen.N11x16
