import WinKU.Shared.D
import WinKU.Shared.T0
import WinKU.Shared.T1
import WinKU.Shared.T2
import WinKU.Shared.G0
import WinKU.Shared.G1
import WinKU.Shared.G2
import WinKU.Shared.G3
import WinKU.Shared.G4
import WinKU.Shared.G5
import WinKU.Shared.G6
import WinKU.Shared.G7
import WinKU.Shared.G8
import WinKU.Shared.G9
import WinKU.Shared.G10
import WinKU.Shared.G11
import WinKU.Shared.G12
import WinKU.Shared.G13
import WinKU.Shared.G14
import WinKU.Shared.G15
set_option Elab.async false
namespace WinKU.Shared
open ZZN.WinK ZZN.Win
def AllP {α : Type} (P : α → Prop) : List α → Prop
  | [] => True
  | a :: l => P a ∧ AllP P l
theorem AllP.mem {α : Type} {P : α → Prop} : ∀ {L : List α}, AllP P L → ∀ p ∈ L, P p
  | _ :: _, ⟨h, _⟩, _, .head _ => h
  | _ :: _, ⟨_, t⟩, p, .tail _ hp => AllP.mem t p hp
theorem hU25 : ∀ p ∈ UL25, stepOK 6 6 [] 25 p.1 p.2 UL26 UF26 UN26 = true := by
  exact AllP.mem (L := UL25) ⟨stU25_0, stU25_1, stU25_2, stU25_3, stU25_4, stU25_5, trivial⟩
theorem hU26 : ∀ p ∈ UL26, stepOK 6 6 [] 26 p.1 p.2 UL27 UF27 UN27 = true := by
  exact AllP.mem (L := UL26) ⟨stU26_0, stU26_1, stU26_2, stU26_3, stU26_4, stU26_5, stU26_6, trivial⟩
theorem hU27 : ∀ p ∈ UL27, stepOK 6 6 [] 27 p.1 p.2 UL28 UF28 UN28 = true := by
  exact AllP.mem (L := UL27) ⟨stU27_0, stU27_1, stU27_2, stU27_3, stU27_4, stU27_5, stU27_6, trivial⟩
theorem hU28 : ∀ p ∈ UL28, stepOK 6 6 [] 28 p.1 p.2 UL29 UF29 UN29 = true := by
  exact AllP.mem (L := UL28) ⟨stU28_0, stU28_1, stU28_2, stU28_3, stU28_4, stU28_5, stU28_6, stU28_7, trivial⟩
theorem hU29 : ∀ p ∈ UL29, stepOK 6 6 [] 29 p.1 p.2 UL30 UF30 UN30 = true := by
  exact AllP.mem (L := UL29) ⟨stU29_0, stU29_1, stU29_2, stU29_3, stU29_4, stU29_5, stU29_6, stU29_7, stU29_8, trivial⟩
theorem hU30 : ∀ p ∈ UL30, stepOK 6 6 [] 30 p.1 p.2 UL31 UF31 UN31 = true := by
  exact AllP.mem (L := UL30) ⟨stU30_0, stU30_1, stU30_2, stU30_3, stU30_4, stU30_5, stU30_6, stU30_7, stU30_8, stU30_9, stU30_10, trivial⟩
theorem hU31 : ∀ p ∈ UL31, stepOK 6 6 [] 31 p.1 p.2 UL32 UF32 UN32 = true := by
  exact AllP.mem (L := UL31) ⟨stU31_0, stU31_1, stU31_2, stU31_3, stU31_4, stU31_5, stU31_6, stU31_7, stU31_8, stU31_9, stU31_10, stU31_11, stU31_12, stU31_13, stU31_14, stU31_15, stU31_16, stU31_17, trivial⟩
theorem hU32 : ∀ p ∈ UL32, stepOK 6 6 [] 32 p.1 p.2 UL33 UF33 UN33 = true := by
  exact AllP.mem (L := UL32) ⟨stU32_0, stU32_1, stU32_2, stU32_3, stU32_4, stU32_5, stU32_6, stU32_7, stU32_8, stU32_9, stU32_10, stU32_11, stU32_12, stU32_13, stU32_14, stU32_15, stU32_16, stU32_17, stU32_18, stU32_19, trivial⟩
theorem hU33 : ∀ p ∈ UL33, stepOK 6 6 [] 33 p.1 p.2 UL34 UF34 UN34 = true := by
  exact AllP.mem (L := UL33) ⟨stU33_0, stU33_1, stU33_2, stU33_3, stU33_4, stU33_5, stU33_6, stU33_7, stU33_8, stU33_9, stU33_10, stU33_11, stU33_12, stU33_13, stU33_14, stU33_15, stU33_16, stU33_17, stU33_18, stU33_19, stU33_20, trivial⟩
theorem hU34 : ∀ p ∈ UL34, stepOK 6 6 [] 34 p.1 p.2 UL35 UF35 UN35 = true := by
  exact AllP.mem (L := UL34) ⟨stU34_0, stU34_1, stU34_2, stU34_3, stU34_4, stU34_5, stU34_6, stU34_7, stU34_8, stU34_9, stU34_10, stU34_11, stU34_12, stU34_13, stU34_14, stU34_15, stU34_16, stU34_17, stU34_18, stU34_19, stU34_20, stU34_21, stU34_22, trivial⟩
theorem hU35 : ∀ p ∈ UL35, stepOK 6 6 [] 35 p.1 p.2 UL36 UF36 UN36 = true := by
  exact AllP.mem (L := UL35) ⟨stU35_0, stU35_1, stU35_2, stU35_3, stU35_4, stU35_5, stU35_6, stU35_7, stU35_8, stU35_9, stU35_10, stU35_11, stU35_12, stU35_13, stU35_14, stU35_15, stU35_16, stU35_17, stU35_18, stU35_19, stU35_20, stU35_21, stU35_22, stU35_23, stU35_24, trivial⟩
theorem sigAll0_0 : ∀ j, j < NS0 → outsideSig 0 (sigDec (getW SA0 j)).1 (sigDec (getW SA0 j)).2.1 (sigDec (getW SA0 j)).2.2.1 (sigDec (getW SA0 j)).2.2.2.1 (sigDec (getW SA0 j)).2.2.2.2 = false := by
  intro j hj
  by_cases h0 : j < 64
  · exact sigsOKR_spec sg0_0_0 j (by omega) h0
  by_cases h1 : j < 128
  · exact sigsOKR_spec sg0_0_1 j (by omega) h1
  by_cases h2 : j < 192
  · exact sigsOKR_spec sg0_0_2 j (by omega) h2
  by_cases h3 : j < 256
  · exact sigsOKR_spec sg0_0_3 j (by omega) h3
  by_cases h4 : j < 320
  · exact sigsOKR_spec sg0_0_4 j (by omega) h4
  by_cases h5 : j < 384
  · exact sigsOKR_spec sg0_0_5 j (by omega) h5
  by_cases h6 : j < 448
  · exact sigsOKR_spec sg0_0_6 j (by omega) h6
  by_cases h7 : j < 512
  · exact sigsOKR_spec sg0_0_7 j (by omega) h7
  by_cases h8 : j < 576
  · exact sigsOKR_spec sg0_0_8 j (by omega) h8
  by_cases h9 : j < 640
  · exact sigsOKR_spec sg0_0_9 j (by omega) h9
  by_cases h10 : j < 704
  · exact sigsOKR_spec sg0_0_10 j (by omega) h10
  by_cases h11 : j < 768
  · exact sigsOKR_spec sg0_0_11 j (by omega) h11
  · exact sigsOKR_spec sg0_0_12 j (by omega) (by simpa [NS0] using hj)
theorem finU0_0 : ∀ p ∈ UL36, finalOK 6 6 0 (none) p.1 p.2 = true := by
  exact AllP.mem (L := UL36) ⟨(final_of_sigs' sigAll0_0 fsig0_0), (final_of_sigs' sigAll0_0 fsig0_1), (final_of_sigs' sigAll0_0 fsig0_2), (final_of_sigs' sigAll0_0 fsig0_3), (final_of_sigs' sigAll0_0 fsig0_4), (final_of_sigs' sigAll0_0 fsig0_5), (final_of_sigs' sigAll0_0 fsig0_6), (final_of_sigs' sigAll0_0 fsig0_7), (final_of_sigs' sigAll0_0 fsig0_8), (final_of_sigs' sigAll0_0 fsig0_9), (final_of_sigs' sigAll0_0 fsig0_10), (final_of_sigs' sigAll0_0 fsig0_11), (final_of_sigs' sigAll0_0 fsig0_12), (final_of_sigs' sigAll0_0 fsig0_13), (final_of_sigs' sigAll0_0 fsig0_14), (final_of_sigs' sigAll0_0 fsig0_15), (final_of_sigs' sigAll0_0 fsig0_16), (final_of_sigs' sigAll0_0 fsig0_17), (final_of_sigs' sigAll0_0 fsig0_18), (final_of_sigs' sigAll0_0 fsig0_19), (final_of_sigs' sigAll0_0 fsig0_20), (final_of_sigs' sigAll0_0 fsig0_21), (final_of_sigs' sigAll0_0 fsig0_22), (final_of_sigs' sigAll0_0 fsig0_23), (final_of_sigs' sigAll0_0 fsig0_24), (final_of_sigs' sigAll0_0 fsig0_25), (final_of_sigs' sigAll0_0 fsig0_26), (final_of_sigs' sigAll0_0 fsig0_27), (final_of_sigs' sigAll0_0 fsig0_28), (final_of_sigs' sigAll0_0 fsig0_29), (final_of_sigs' sigAll0_0 fsig0_30), (final_of_sigs' sigAll0_0 fsig0_31), (final_of_sigs' sigAll0_0 fsig0_32), (final_of_sigs' sigAll0_0 fsig0_33), (final_of_sigs' sigAll0_0 fsig0_34), (final_of_sigs' sigAll0_0 fsig0_35), (final_of_sigs' sigAll0_0 fsig0_36), (final_of_sigs' sigAll0_0 fsig0_37), (final_of_sigs' sigAll0_0 fsig0_38), (final_of_sigs' sigAll0_0 fsig0_39), (final_of_sigs' sigAll0_0 fsig0_40), (final_of_sigs' sigAll0_0 fsig0_41), (final_of_sigs' sigAll0_0 fsig0_42), (final_of_sigs' sigAll0_0 fsig0_43), (final_of_sigs' sigAll0_0 fsig0_44), (final_of_sigs' sigAll0_0 fsig0_45), (final_of_sigs' sigAll0_0 fsig0_46), (final_of_sigs' sigAll0_0 fsig0_47), (final_of_sigs' sigAll0_0 fsig0_48), (final_of_sigs' sigAll0_0 fsig0_49), (final_of_sigs' sigAll0_0 fsig0_50), (final_of_sigs' sigAll0_0 fsig0_51), (final_of_sigs' sigAll0_0 fsig0_52), (final_of_sigs' sigAll0_0 fsig0_53), (final_of_sigs' sigAll0_0 fsig0_54), (final_of_sigs' sigAll0_0 fsig0_55), (final_of_sigs' sigAll0_0 fsig0_56), (final_of_sigs' sigAll0_0 fsig0_57), (final_of_sigs' sigAll0_0 fsig0_58), (final_of_sigs' sigAll0_0 fsig0_59), (final_of_sigs' sigAll0_0 fsig0_60), (final_of_sigs' sigAll0_0 fsig0_61), (final_of_sigs' sigAll0_0 fsig0_62), (final_of_sigs' sigAll0_0 fsig0_63), (final_of_sigs' sigAll0_0 fsig0_64), (final_of_sigs' sigAll0_0 fsig0_65), (final_of_sigs' sigAll0_0 fsig0_66), (final_of_sigs' sigAll0_0 fsig0_67), (final_of_sigs' sigAll0_0 fsig0_68), (final_of_sigs' sigAll0_0 fsig0_69), (final_of_sigs' sigAll0_0 fsig0_70), (final_of_sigs' sigAll0_0 fsig0_71), (final_of_sigs' sigAll0_0 fsig0_72), (final_of_sigs' sigAll0_0 fsig0_73), (final_of_sigs' sigAll0_0 fsig0_74), (final_of_sigs' sigAll0_0 fsig0_75), (final_of_sigs' sigAll0_0 fsig0_76), (final_of_sigs' sigAll0_0 fsig0_77), (final_of_sigs' sigAll0_0 fsig0_78), (final_of_sigs' sigAll0_0 fsig0_79), (final_of_sigs' sigAll0_0 fsig0_80), (final_of_sigs' sigAll0_0 fsig0_81), (final_of_sigs' sigAll0_0 fsig0_82), (final_of_sigs' sigAll0_0 fsig0_83), (final_of_sigs' sigAll0_0 fsig0_84), (final_of_sigs' sigAll0_0 fsig0_85), (final_of_sigs' sigAll0_0 fsig0_86), (final_of_sigs' sigAll0_0 fsig0_87), (final_of_sigs' sigAll0_0 fsig0_88), (final_of_sigs' sigAll0_0 fsig0_89), (final_of_sigs' sigAll0_0 fsig0_90), (final_of_sigs' sigAll0_0 fsig0_91), (final_of_sigs' sigAll0_0 fsig0_92), (final_of_sigs' sigAll0_0 fsig0_93), (final_of_sigs' sigAll0_0 fsig0_94), (final_of_sigs' sigAll0_0 fsig0_95), (final_of_sigs' sigAll0_0 fsig0_96), (final_of_sigs' sigAll0_0 fsig0_97), (final_of_sigs' sigAll0_0 fsig0_98), (final_of_sigs' sigAll0_0 fsig0_99), (final_of_sigs' sigAll0_0 fsig0_100), (final_of_sigs' sigAll0_0 fsig0_101), (final_of_sigs' sigAll0_0 fsig0_102), (final_of_sigs' sigAll0_0 fsig0_103), (final_of_sigs' sigAll0_0 fsig0_104), (final_of_sigs' sigAll0_0 fsig0_105), (final_of_sigs' sigAll0_0 fsig0_106), (final_of_sigs' sigAll0_0 fsig0_107), (final_of_sigs' sigAll0_0 fsig0_108), (final_of_sigs' sigAll0_0 fsig0_109), (final_of_sigs' sigAll0_0 fsig0_110), (final_of_sigs' sigAll0_0 fsig0_111), (final_of_sigs' sigAll0_0 fsig0_112), (final_of_sigs' sigAll0_0 fsig0_113), (final_of_sigs' sigAll0_0 fsig0_114), (final_of_sigs' sigAll0_0 fsig0_115), (final_of_sigs' sigAll0_0 fsig0_116), (final_of_sigs' sigAll0_0 fsig0_117), (final_of_sigs' sigAll0_0 fsig0_118), (final_of_sigs' sigAll0_0 fsig0_119), trivial⟩
theorem sigAll1_0 : ∀ j, j < NS0 → outsideSig 1 (sigDec (getW SA0 j)).1 (sigDec (getW SA0 j)).2.1 (sigDec (getW SA0 j)).2.2.1 (sigDec (getW SA0 j)).2.2.2.1 (sigDec (getW SA0 j)).2.2.2.2 = false := by
  intro j hj
  by_cases h0 : j < 64
  · exact sigsOKR_spec sg1_0_0 j (by omega) h0
  by_cases h1 : j < 128
  · exact sigsOKR_spec sg1_0_1 j (by omega) h1
  by_cases h2 : j < 192
  · exact sigsOKR_spec sg1_0_2 j (by omega) h2
  by_cases h3 : j < 256
  · exact sigsOKR_spec sg1_0_3 j (by omega) h3
  by_cases h4 : j < 320
  · exact sigsOKR_spec sg1_0_4 j (by omega) h4
  by_cases h5 : j < 384
  · exact sigsOKR_spec sg1_0_5 j (by omega) h5
  by_cases h6 : j < 448
  · exact sigsOKR_spec sg1_0_6 j (by omega) h6
  by_cases h7 : j < 512
  · exact sigsOKR_spec sg1_0_7 j (by omega) h7
  by_cases h8 : j < 576
  · exact sigsOKR_spec sg1_0_8 j (by omega) h8
  by_cases h9 : j < 640
  · exact sigsOKR_spec sg1_0_9 j (by omega) h9
  by_cases h10 : j < 704
  · exact sigsOKR_spec sg1_0_10 j (by omega) h10
  by_cases h11 : j < 768
  · exact sigsOKR_spec sg1_0_11 j (by omega) h11
  · exact sigsOKR_spec sg1_0_12 j (by omega) (by simpa [NS0] using hj)
theorem finU1_0 : ∀ p ∈ UL36, finalOK 6 6 1 (none) p.1 p.2 = true := by
  exact AllP.mem (L := UL36) ⟨(final_of_sigs' sigAll1_0 fsig0_0), (final_of_sigs' sigAll1_0 fsig0_1), (final_of_sigs' sigAll1_0 fsig0_2), (final_of_sigs' sigAll1_0 fsig0_3), (final_of_sigs' sigAll1_0 fsig0_4), (final_of_sigs' sigAll1_0 fsig0_5), (final_of_sigs' sigAll1_0 fsig0_6), (final_of_sigs' sigAll1_0 fsig0_7), (final_of_sigs' sigAll1_0 fsig0_8), (final_of_sigs' sigAll1_0 fsig0_9), (final_of_sigs' sigAll1_0 fsig0_10), (final_of_sigs' sigAll1_0 fsig0_11), (final_of_sigs' sigAll1_0 fsig0_12), (final_of_sigs' sigAll1_0 fsig0_13), (final_of_sigs' sigAll1_0 fsig0_14), (final_of_sigs' sigAll1_0 fsig0_15), (final_of_sigs' sigAll1_0 fsig0_16), (final_of_sigs' sigAll1_0 fsig0_17), (final_of_sigs' sigAll1_0 fsig0_18), (final_of_sigs' sigAll1_0 fsig0_19), (final_of_sigs' sigAll1_0 fsig0_20), (final_of_sigs' sigAll1_0 fsig0_21), (final_of_sigs' sigAll1_0 fsig0_22), (final_of_sigs' sigAll1_0 fsig0_23), (final_of_sigs' sigAll1_0 fsig0_24), (final_of_sigs' sigAll1_0 fsig0_25), (final_of_sigs' sigAll1_0 fsig0_26), (final_of_sigs' sigAll1_0 fsig0_27), (final_of_sigs' sigAll1_0 fsig0_28), (final_of_sigs' sigAll1_0 fsig0_29), (final_of_sigs' sigAll1_0 fsig0_30), (final_of_sigs' sigAll1_0 fsig0_31), (final_of_sigs' sigAll1_0 fsig0_32), (final_of_sigs' sigAll1_0 fsig0_33), (final_of_sigs' sigAll1_0 fsig0_34), (final_of_sigs' sigAll1_0 fsig0_35), (final_of_sigs' sigAll1_0 fsig0_36), (final_of_sigs' sigAll1_0 fsig0_37), (final_of_sigs' sigAll1_0 fsig0_38), (final_of_sigs' sigAll1_0 fsig0_39), (final_of_sigs' sigAll1_0 fsig0_40), (final_of_sigs' sigAll1_0 fsig0_41), (final_of_sigs' sigAll1_0 fsig0_42), (final_of_sigs' sigAll1_0 fsig0_43), (final_of_sigs' sigAll1_0 fsig0_44), (final_of_sigs' sigAll1_0 fsig0_45), (final_of_sigs' sigAll1_0 fsig0_46), (final_of_sigs' sigAll1_0 fsig0_47), (final_of_sigs' sigAll1_0 fsig0_48), (final_of_sigs' sigAll1_0 fsig0_49), (final_of_sigs' sigAll1_0 fsig0_50), (final_of_sigs' sigAll1_0 fsig0_51), (final_of_sigs' sigAll1_0 fsig0_52), (final_of_sigs' sigAll1_0 fsig0_53), (final_of_sigs' sigAll1_0 fsig0_54), (final_of_sigs' sigAll1_0 fsig0_55), (final_of_sigs' sigAll1_0 fsig0_56), (final_of_sigs' sigAll1_0 fsig0_57), (final_of_sigs' sigAll1_0 fsig0_58), (final_of_sigs' sigAll1_0 fsig0_59), (final_of_sigs' sigAll1_0 fsig0_60), (final_of_sigs' sigAll1_0 fsig0_61), (final_of_sigs' sigAll1_0 fsig0_62), (final_of_sigs' sigAll1_0 fsig0_63), (final_of_sigs' sigAll1_0 fsig0_64), (final_of_sigs' sigAll1_0 fsig0_65), (final_of_sigs' sigAll1_0 fsig0_66), (final_of_sigs' sigAll1_0 fsig0_67), (final_of_sigs' sigAll1_0 fsig0_68), (final_of_sigs' sigAll1_0 fsig0_69), (final_of_sigs' sigAll1_0 fsig0_70), (final_of_sigs' sigAll1_0 fsig0_71), (final_of_sigs' sigAll1_0 fsig0_72), (final_of_sigs' sigAll1_0 fsig0_73), (final_of_sigs' sigAll1_0 fsig0_74), (final_of_sigs' sigAll1_0 fsig0_75), (final_of_sigs' sigAll1_0 fsig0_76), (final_of_sigs' sigAll1_0 fsig0_77), (final_of_sigs' sigAll1_0 fsig0_78), (final_of_sigs' sigAll1_0 fsig0_79), (final_of_sigs' sigAll1_0 fsig0_80), (final_of_sigs' sigAll1_0 fsig0_81), (final_of_sigs' sigAll1_0 fsig0_82), (final_of_sigs' sigAll1_0 fsig0_83), (final_of_sigs' sigAll1_0 fsig0_84), (final_of_sigs' sigAll1_0 fsig0_85), (final_of_sigs' sigAll1_0 fsig0_86), (final_of_sigs' sigAll1_0 fsig0_87), (final_of_sigs' sigAll1_0 fsig0_88), (final_of_sigs' sigAll1_0 fsig0_89), (final_of_sigs' sigAll1_0 fsig0_90), (final_of_sigs' sigAll1_0 fsig0_91), (final_of_sigs' sigAll1_0 fsig0_92), (final_of_sigs' sigAll1_0 fsig0_93), (final_of_sigs' sigAll1_0 fsig0_94), (final_of_sigs' sigAll1_0 fsig0_95), (final_of_sigs' sigAll1_0 fsig0_96), (final_of_sigs' sigAll1_0 fsig0_97), (final_of_sigs' sigAll1_0 fsig0_98), (final_of_sigs' sigAll1_0 fsig0_99), (final_of_sigs' sigAll1_0 fsig0_100), (final_of_sigs' sigAll1_0 fsig0_101), (final_of_sigs' sigAll1_0 fsig0_102), (final_of_sigs' sigAll1_0 fsig0_103), (final_of_sigs' sigAll1_0 fsig0_104), (final_of_sigs' sigAll1_0 fsig0_105), (final_of_sigs' sigAll1_0 fsig0_106), (final_of_sigs' sigAll1_0 fsig0_107), (final_of_sigs' sigAll1_0 fsig0_108), (final_of_sigs' sigAll1_0 fsig0_109), (final_of_sigs' sigAll1_0 fsig0_110), (final_of_sigs' sigAll1_0 fsig0_111), (final_of_sigs' sigAll1_0 fsig0_112), (final_of_sigs' sigAll1_0 fsig0_113), (final_of_sigs' sigAll1_0 fsig0_114), (final_of_sigs' sigAll1_0 fsig0_115), (final_of_sigs' sigAll1_0 fsig0_116), (final_of_sigs' sigAll1_0 fsig0_117), (final_of_sigs' sigAll1_0 fsig0_118), (final_of_sigs' sigAll1_0 fsig0_119), trivial⟩
theorem sigAll0_1 : ∀ j, j < NS1 → outsideSig 0 (sigDec (getW SA1 j)).1 (sigDec (getW SA1 j)).2.1 (sigDec (getW SA1 j)).2.2.1 (sigDec (getW SA1 j)).2.2.2.1 (sigDec (getW SA1 j)).2.2.2.2 = false := by
  intro j hj
  by_cases h0 : j < 64
  · exact sigsOKR_spec sg0_1_0 j (by omega) h0
  by_cases h1 : j < 128
  · exact sigsOKR_spec sg0_1_1 j (by omega) h1
  by_cases h2 : j < 192
  · exact sigsOKR_spec sg0_1_2 j (by omega) h2
  by_cases h3 : j < 256
  · exact sigsOKR_spec sg0_1_3 j (by omega) h3
  by_cases h4 : j < 320
  · exact sigsOKR_spec sg0_1_4 j (by omega) h4
  by_cases h5 : j < 384
  · exact sigsOKR_spec sg0_1_5 j (by omega) h5
  by_cases h6 : j < 448
  · exact sigsOKR_spec sg0_1_6 j (by omega) h6
  by_cases h7 : j < 512
  · exact sigsOKR_spec sg0_1_7 j (by omega) h7
  by_cases h8 : j < 576
  · exact sigsOKR_spec sg0_1_8 j (by omega) h8
  by_cases h9 : j < 640
  · exact sigsOKR_spec sg0_1_9 j (by omega) h9
  by_cases h10 : j < 704
  · exact sigsOKR_spec sg0_1_10 j (by omega) h10
  by_cases h11 : j < 768
  · exact sigsOKR_spec sg0_1_11 j (by omega) h11
  · exact sigsOKR_spec sg0_1_12 j (by omega) (by simpa [NS1] using hj)
theorem finU0_1 : ∀ p ∈ UL36, finalOK 6 6 0 (some (1, (-1 : ℤ), none)) p.1 p.2 = true := by
  exact AllP.mem (L := UL36) ⟨(final_of_sigs' sigAll0_1 fsig1_0), (final_of_sigs' sigAll0_1 fsig1_1), (final_of_sigs' sigAll0_1 fsig1_2), (final_of_sigs' sigAll0_1 fsig1_3), (final_of_sigs' sigAll0_1 fsig1_4), (final_of_sigs' sigAll0_1 fsig1_5), (final_of_sigs' sigAll0_1 fsig1_6), (final_of_sigs' sigAll0_1 fsig1_7), (final_of_sigs' sigAll0_1 fsig1_8), (final_of_sigs' sigAll0_1 fsig1_9), (final_of_sigs' sigAll0_1 fsig1_10), (final_of_sigs' sigAll0_1 fsig1_11), (final_of_sigs' sigAll0_1 fsig1_12), (final_of_sigs' sigAll0_1 fsig1_13), (final_of_sigs' sigAll0_1 fsig1_14), (final_of_sigs' sigAll0_1 fsig1_15), (final_of_sigs' sigAll0_1 fsig1_16), (final_of_sigs' sigAll0_1 fsig1_17), (final_of_sigs' sigAll0_1 fsig1_18), (final_of_sigs' sigAll0_1 fsig1_19), (final_of_sigs' sigAll0_1 fsig1_20), (final_of_sigs' sigAll0_1 fsig1_21), (final_of_sigs' sigAll0_1 fsig1_22), (final_of_sigs' sigAll0_1 fsig1_23), (final_of_sigs' sigAll0_1 fsig1_24), (final_of_sigs' sigAll0_1 fsig1_25), (final_of_sigs' sigAll0_1 fsig1_26), (final_of_sigs' sigAll0_1 fsig1_27), (final_of_sigs' sigAll0_1 fsig1_28), (final_of_sigs' sigAll0_1 fsig1_29), (final_of_sigs' sigAll0_1 fsig1_30), (final_of_sigs' sigAll0_1 fsig1_31), (final_of_sigs' sigAll0_1 fsig1_32), (final_of_sigs' sigAll0_1 fsig1_33), (final_of_sigs' sigAll0_1 fsig1_34), (final_of_sigs' sigAll0_1 fsig1_35), (final_of_sigs' sigAll0_1 fsig1_36), (final_of_sigs' sigAll0_1 fsig1_37), (final_of_sigs' sigAll0_1 fsig1_38), (final_of_sigs' sigAll0_1 fsig1_39), (final_of_sigs' sigAll0_1 fsig1_40), (final_of_sigs' sigAll0_1 fsig1_41), (final_of_sigs' sigAll0_1 fsig1_42), (final_of_sigs' sigAll0_1 fsig1_43), (final_of_sigs' sigAll0_1 fsig1_44), (final_of_sigs' sigAll0_1 fsig1_45), (final_of_sigs' sigAll0_1 fsig1_46), (final_of_sigs' sigAll0_1 fsig1_47), (final_of_sigs' sigAll0_1 fsig1_48), (final_of_sigs' sigAll0_1 fsig1_49), (final_of_sigs' sigAll0_1 fsig1_50), (final_of_sigs' sigAll0_1 fsig1_51), (final_of_sigs' sigAll0_1 fsig1_52), (final_of_sigs' sigAll0_1 fsig1_53), (final_of_sigs' sigAll0_1 fsig1_54), (final_of_sigs' sigAll0_1 fsig1_55), (final_of_sigs' sigAll0_1 fsig1_56), (final_of_sigs' sigAll0_1 fsig1_57), (final_of_sigs' sigAll0_1 fsig1_58), (final_of_sigs' sigAll0_1 fsig1_59), (final_of_sigs' sigAll0_1 fsig1_60), (final_of_sigs' sigAll0_1 fsig1_61), (final_of_sigs' sigAll0_1 fsig1_62), (final_of_sigs' sigAll0_1 fsig1_63), (final_of_sigs' sigAll0_1 fsig1_64), (final_of_sigs' sigAll0_1 fsig1_65), (final_of_sigs' sigAll0_1 fsig1_66), (final_of_sigs' sigAll0_1 fsig1_67), (final_of_sigs' sigAll0_1 fsig1_68), (final_of_sigs' sigAll0_1 fsig1_69), (final_of_sigs' sigAll0_1 fsig1_70), (final_of_sigs' sigAll0_1 fsig1_71), (final_of_sigs' sigAll0_1 fsig1_72), (final_of_sigs' sigAll0_1 fsig1_73), (final_of_sigs' sigAll0_1 fsig1_74), (final_of_sigs' sigAll0_1 fsig1_75), (final_of_sigs' sigAll0_1 fsig1_76), (final_of_sigs' sigAll0_1 fsig1_77), (final_of_sigs' sigAll0_1 fsig1_78), (final_of_sigs' sigAll0_1 fsig1_79), (final_of_sigs' sigAll0_1 fsig1_80), (final_of_sigs' sigAll0_1 fsig1_81), (final_of_sigs' sigAll0_1 fsig1_82), (final_of_sigs' sigAll0_1 fsig1_83), (final_of_sigs' sigAll0_1 fsig1_84), (final_of_sigs' sigAll0_1 fsig1_85), (final_of_sigs' sigAll0_1 fsig1_86), (final_of_sigs' sigAll0_1 fsig1_87), (final_of_sigs' sigAll0_1 fsig1_88), (final_of_sigs' sigAll0_1 fsig1_89), (final_of_sigs' sigAll0_1 fsig1_90), (final_of_sigs' sigAll0_1 fsig1_91), (final_of_sigs' sigAll0_1 fsig1_92), (final_of_sigs' sigAll0_1 fsig1_93), (final_of_sigs' sigAll0_1 fsig1_94), (final_of_sigs' sigAll0_1 fsig1_95), (final_of_sigs' sigAll0_1 fsig1_96), (final_of_sigs' sigAll0_1 fsig1_97), (final_of_sigs' sigAll0_1 fsig1_98), (final_of_sigs' sigAll0_1 fsig1_99), (final_of_sigs' sigAll0_1 fsig1_100), (final_of_sigs' sigAll0_1 fsig1_101), (final_of_sigs' sigAll0_1 fsig1_102), (final_of_sigs' sigAll0_1 fsig1_103), (final_of_sigs' sigAll0_1 fsig1_104), (final_of_sigs' sigAll0_1 fsig1_105), (final_of_sigs' sigAll0_1 fsig1_106), (final_of_sigs' sigAll0_1 fsig1_107), (final_of_sigs' sigAll0_1 fsig1_108), (final_of_sigs' sigAll0_1 fsig1_109), (final_of_sigs' sigAll0_1 fsig1_110), (final_of_sigs' sigAll0_1 fsig1_111), (final_of_sigs' sigAll0_1 fsig1_112), (final_of_sigs' sigAll0_1 fsig1_113), (final_of_sigs' sigAll0_1 fsig1_114), (final_of_sigs' sigAll0_1 fsig1_115), (final_of_sigs' sigAll0_1 fsig1_116), (final_of_sigs' sigAll0_1 fsig1_117), (final_of_sigs' sigAll0_1 fsig1_118), (final_of_sigs' sigAll0_1 fsig1_119), trivial⟩
theorem sigAll0_2 : ∀ j, j < NS2 → outsideSig 0 (sigDec (getW SA2 j)).1 (sigDec (getW SA2 j)).2.1 (sigDec (getW SA2 j)).2.2.1 (sigDec (getW SA2 j)).2.2.2.1 (sigDec (getW SA2 j)).2.2.2.2 = false := by
  intro j hj
  by_cases h0 : j < 64
  · exact sigsOKR_spec sg0_2_0 j (by omega) h0
  by_cases h1 : j < 128
  · exact sigsOKR_spec sg0_2_1 j (by omega) h1
  by_cases h2 : j < 192
  · exact sigsOKR_spec sg0_2_2 j (by omega) h2
  by_cases h3 : j < 256
  · exact sigsOKR_spec sg0_2_3 j (by omega) h3
  by_cases h4 : j < 320
  · exact sigsOKR_spec sg0_2_4 j (by omega) h4
  by_cases h5 : j < 384
  · exact sigsOKR_spec sg0_2_5 j (by omega) h5
  by_cases h6 : j < 448
  · exact sigsOKR_spec sg0_2_6 j (by omega) h6
  by_cases h7 : j < 512
  · exact sigsOKR_spec sg0_2_7 j (by omega) h7
  by_cases h8 : j < 576
  · exact sigsOKR_spec sg0_2_8 j (by omega) h8
  by_cases h9 : j < 640
  · exact sigsOKR_spec sg0_2_9 j (by omega) h9
  by_cases h10 : j < 704
  · exact sigsOKR_spec sg0_2_10 j (by omega) h10
  by_cases h11 : j < 768
  · exact sigsOKR_spec sg0_2_11 j (by omega) h11
  · exact sigsOKR_spec sg0_2_12 j (by omega) (by simpa [NS2] using hj)
theorem finU0_2 : ∀ p ∈ UL36, finalOK 6 6 0 (some (1, (1 : ℤ), none)) p.1 p.2 = true := by
  exact AllP.mem (L := UL36) ⟨(final_of_sigs' sigAll0_2 fsig2_0), (final_of_sigs' sigAll0_2 fsig2_1), (final_of_sigs' sigAll0_2 fsig2_2), (final_of_sigs' sigAll0_2 fsig2_3), (final_of_sigs' sigAll0_2 fsig2_4), (final_of_sigs' sigAll0_2 fsig2_5), (final_of_sigs' sigAll0_2 fsig2_6), (final_of_sigs' sigAll0_2 fsig2_7), (final_of_sigs' sigAll0_2 fsig2_8), (final_of_sigs' sigAll0_2 fsig2_9), (final_of_sigs' sigAll0_2 fsig2_10), (final_of_sigs' sigAll0_2 fsig2_11), (final_of_sigs' sigAll0_2 fsig2_12), (final_of_sigs' sigAll0_2 fsig2_13), (final_of_sigs' sigAll0_2 fsig2_14), (final_of_sigs' sigAll0_2 fsig2_15), (final_of_sigs' sigAll0_2 fsig2_16), (final_of_sigs' sigAll0_2 fsig2_17), (final_of_sigs' sigAll0_2 fsig2_18), (final_of_sigs' sigAll0_2 fsig2_19), (final_of_sigs' sigAll0_2 fsig2_20), (final_of_sigs' sigAll0_2 fsig2_21), (final_of_sigs' sigAll0_2 fsig2_22), (final_of_sigs' sigAll0_2 fsig2_23), (final_of_sigs' sigAll0_2 fsig2_24), (final_of_sigs' sigAll0_2 fsig2_25), (final_of_sigs' sigAll0_2 fsig2_26), (final_of_sigs' sigAll0_2 fsig2_27), (final_of_sigs' sigAll0_2 fsig2_28), (final_of_sigs' sigAll0_2 fsig2_29), (final_of_sigs' sigAll0_2 fsig2_30), (final_of_sigs' sigAll0_2 fsig2_31), (final_of_sigs' sigAll0_2 fsig2_32), (final_of_sigs' sigAll0_2 fsig2_33), (final_of_sigs' sigAll0_2 fsig2_34), (final_of_sigs' sigAll0_2 fsig2_35), (final_of_sigs' sigAll0_2 fsig2_36), (final_of_sigs' sigAll0_2 fsig2_37), (final_of_sigs' sigAll0_2 fsig2_38), (final_of_sigs' sigAll0_2 fsig2_39), (final_of_sigs' sigAll0_2 fsig2_40), (final_of_sigs' sigAll0_2 fsig2_41), (final_of_sigs' sigAll0_2 fsig2_42), (final_of_sigs' sigAll0_2 fsig2_43), (final_of_sigs' sigAll0_2 fsig2_44), (final_of_sigs' sigAll0_2 fsig2_45), (final_of_sigs' sigAll0_2 fsig2_46), (final_of_sigs' sigAll0_2 fsig2_47), (final_of_sigs' sigAll0_2 fsig2_48), (final_of_sigs' sigAll0_2 fsig2_49), (final_of_sigs' sigAll0_2 fsig2_50), (final_of_sigs' sigAll0_2 fsig2_51), (final_of_sigs' sigAll0_2 fsig2_52), (final_of_sigs' sigAll0_2 fsig2_53), (final_of_sigs' sigAll0_2 fsig2_54), (final_of_sigs' sigAll0_2 fsig2_55), (final_of_sigs' sigAll0_2 fsig2_56), (final_of_sigs' sigAll0_2 fsig2_57), (final_of_sigs' sigAll0_2 fsig2_58), (final_of_sigs' sigAll0_2 fsig2_59), (final_of_sigs' sigAll0_2 fsig2_60), (final_of_sigs' sigAll0_2 fsig2_61), (final_of_sigs' sigAll0_2 fsig2_62), (final_of_sigs' sigAll0_2 fsig2_63), (final_of_sigs' sigAll0_2 fsig2_64), (final_of_sigs' sigAll0_2 fsig2_65), (final_of_sigs' sigAll0_2 fsig2_66), (final_of_sigs' sigAll0_2 fsig2_67), (final_of_sigs' sigAll0_2 fsig2_68), (final_of_sigs' sigAll0_2 fsig2_69), (final_of_sigs' sigAll0_2 fsig2_70), (final_of_sigs' sigAll0_2 fsig2_71), (final_of_sigs' sigAll0_2 fsig2_72), (final_of_sigs' sigAll0_2 fsig2_73), (final_of_sigs' sigAll0_2 fsig2_74), (final_of_sigs' sigAll0_2 fsig2_75), (final_of_sigs' sigAll0_2 fsig2_76), (final_of_sigs' sigAll0_2 fsig2_77), (final_of_sigs' sigAll0_2 fsig2_78), (final_of_sigs' sigAll0_2 fsig2_79), (final_of_sigs' sigAll0_2 fsig2_80), (final_of_sigs' sigAll0_2 fsig2_81), (final_of_sigs' sigAll0_2 fsig2_82), (final_of_sigs' sigAll0_2 fsig2_83), (final_of_sigs' sigAll0_2 fsig2_84), (final_of_sigs' sigAll0_2 fsig2_85), (final_of_sigs' sigAll0_2 fsig2_86), (final_of_sigs' sigAll0_2 fsig2_87), (final_of_sigs' sigAll0_2 fsig2_88), (final_of_sigs' sigAll0_2 fsig2_89), (final_of_sigs' sigAll0_2 fsig2_90), (final_of_sigs' sigAll0_2 fsig2_91), (final_of_sigs' sigAll0_2 fsig2_92), (final_of_sigs' sigAll0_2 fsig2_93), (final_of_sigs' sigAll0_2 fsig2_94), (final_of_sigs' sigAll0_2 fsig2_95), (final_of_sigs' sigAll0_2 fsig2_96), (final_of_sigs' sigAll0_2 fsig2_97), (final_of_sigs' sigAll0_2 fsig2_98), (final_of_sigs' sigAll0_2 fsig2_99), (final_of_sigs' sigAll0_2 fsig2_100), (final_of_sigs' sigAll0_2 fsig2_101), (final_of_sigs' sigAll0_2 fsig2_102), (final_of_sigs' sigAll0_2 fsig2_103), (final_of_sigs' sigAll0_2 fsig2_104), (final_of_sigs' sigAll0_2 fsig2_105), (final_of_sigs' sigAll0_2 fsig2_106), (final_of_sigs' sigAll0_2 fsig2_107), (final_of_sigs' sigAll0_2 fsig2_108), (final_of_sigs' sigAll0_2 fsig2_109), (final_of_sigs' sigAll0_2 fsig2_110), (final_of_sigs' sigAll0_2 fsig2_111), (final_of_sigs' sigAll0_2 fsig2_112), (final_of_sigs' sigAll0_2 fsig2_113), (final_of_sigs' sigAll0_2 fsig2_114), (final_of_sigs' sigAll0_2 fsig2_115), (final_of_sigs' sigAll0_2 fsig2_116), (final_of_sigs' sigAll0_2 fsig2_117), (final_of_sigs' sigAll0_2 fsig2_118), (final_of_sigs' sigAll0_2 fsig2_119), trivial⟩
theorem sigAll0_3 : ∀ j, j < NS3 → outsideSig 0 (sigDec (getW SA3 j)).1 (sigDec (getW SA3 j)).2.1 (sigDec (getW SA3 j)).2.2.1 (sigDec (getW SA3 j)).2.2.2.1 (sigDec (getW SA3 j)).2.2.2.2 = false := by
  intro j hj
  by_cases h0 : j < 64
  · exact sigsOKR_spec sg0_3_0 j (by omega) h0
  by_cases h1 : j < 128
  · exact sigsOKR_spec sg0_3_1 j (by omega) h1
  by_cases h2 : j < 192
  · exact sigsOKR_spec sg0_3_2 j (by omega) h2
  by_cases h3 : j < 256
  · exact sigsOKR_spec sg0_3_3 j (by omega) h3
  by_cases h4 : j < 320
  · exact sigsOKR_spec sg0_3_4 j (by omega) h4
  by_cases h5 : j < 384
  · exact sigsOKR_spec sg0_3_5 j (by omega) h5
  by_cases h6 : j < 448
  · exact sigsOKR_spec sg0_3_6 j (by omega) h6
  by_cases h7 : j < 512
  · exact sigsOKR_spec sg0_3_7 j (by omega) h7
  by_cases h8 : j < 576
  · exact sigsOKR_spec sg0_3_8 j (by omega) h8
  by_cases h9 : j < 640
  · exact sigsOKR_spec sg0_3_9 j (by omega) h9
  by_cases h10 : j < 704
  · exact sigsOKR_spec sg0_3_10 j (by omega) h10
  by_cases h11 : j < 768
  · exact sigsOKR_spec sg0_3_11 j (by omega) h11
  by_cases h12 : j < 832
  · exact sigsOKR_spec sg0_3_12 j (by omega) h12
  by_cases h13 : j < 896
  · exact sigsOKR_spec sg0_3_13 j (by omega) h13
  by_cases h14 : j < 960
  · exact sigsOKR_spec sg0_3_14 j (by omega) h14
  by_cases h15 : j < 1024
  · exact sigsOKR_spec sg0_3_15 j (by omega) h15
  by_cases h16 : j < 1088
  · exact sigsOKR_spec sg0_3_16 j (by omega) h16
  · exact sigsOKR_spec sg0_3_17 j (by omega) (by simpa [NS3] using hj)
theorem finU0_3 : ∀ p ∈ UL36, finalOK 6 6 0 (some (1, (1 : ℤ), some 0)) p.1 p.2 = true := by
  exact AllP.mem (L := UL36) ⟨(final_of_sigs' sigAll0_3 fsig3_0), (final_of_sigs' sigAll0_3 fsig3_1), (final_of_sigs' sigAll0_3 fsig3_2), (final_of_sigs' sigAll0_3 fsig3_3), (final_of_sigs' sigAll0_3 fsig3_4), (final_of_sigs' sigAll0_3 fsig3_5), (final_of_sigs' sigAll0_3 fsig3_6), (final_of_sigs' sigAll0_3 fsig3_7), (final_of_sigs' sigAll0_3 fsig3_8), (final_of_sigs' sigAll0_3 fsig3_9), (final_of_sigs' sigAll0_3 fsig3_10), (final_of_sigs' sigAll0_3 fsig3_11), (final_of_sigs' sigAll0_3 fsig3_12), (final_of_sigs' sigAll0_3 fsig3_13), (final_of_sigs' sigAll0_3 fsig3_14), (final_of_sigs' sigAll0_3 fsig3_15), (final_of_sigs' sigAll0_3 fsig3_16), (final_of_sigs' sigAll0_3 fsig3_17), (final_of_sigs' sigAll0_3 fsig3_18), (final_of_sigs' sigAll0_3 fsig3_19), (final_of_sigs' sigAll0_3 fsig3_20), (final_of_sigs' sigAll0_3 fsig3_21), (final_of_sigs' sigAll0_3 fsig3_22), (final_of_sigs' sigAll0_3 fsig3_23), (final_of_sigs' sigAll0_3 fsig3_24), (final_of_sigs' sigAll0_3 fsig3_25), (final_of_sigs' sigAll0_3 fsig3_26), (final_of_sigs' sigAll0_3 fsig3_27), (final_of_sigs' sigAll0_3 fsig3_28), (final_of_sigs' sigAll0_3 fsig3_29), (final_of_sigs' sigAll0_3 fsig3_30), (final_of_sigs' sigAll0_3 fsig3_31), (final_of_sigs' sigAll0_3 fsig3_32), (final_of_sigs' sigAll0_3 fsig3_33), (final_of_sigs' sigAll0_3 fsig3_34), (final_of_sigs' sigAll0_3 fsig3_35), (final_of_sigs' sigAll0_3 fsig3_36), (final_of_sigs' sigAll0_3 fsig3_37), (final_of_sigs' sigAll0_3 fsig3_38), (final_of_sigs' sigAll0_3 fsig3_39), (final_of_sigs' sigAll0_3 fsig3_40), (final_of_sigs' sigAll0_3 fsig3_41), (final_of_sigs' sigAll0_3 fsig3_42), (final_of_sigs' sigAll0_3 fsig3_43), (final_of_sigs' sigAll0_3 fsig3_44), (final_of_sigs' sigAll0_3 fsig3_45), (final_of_sigs' sigAll0_3 fsig3_46), (final_of_sigs' sigAll0_3 fsig3_47), (final_of_sigs' sigAll0_3 fsig3_48), (final_of_sigs' sigAll0_3 fsig3_49), (final_of_sigs' sigAll0_3 fsig3_50), (final_of_sigs' sigAll0_3 fsig3_51), (final_of_sigs' sigAll0_3 fsig3_52), (final_of_sigs' sigAll0_3 fsig3_53), (final_of_sigs' sigAll0_3 fsig3_54), (final_of_sigs' sigAll0_3 fsig3_55), (final_of_sigs' sigAll0_3 fsig3_56), (final_of_sigs' sigAll0_3 fsig3_57), (final_of_sigs' sigAll0_3 fsig3_58), (final_of_sigs' sigAll0_3 fsig3_59), (final_of_sigs' sigAll0_3 fsig3_60), (final_of_sigs' sigAll0_3 fsig3_61), (final_of_sigs' sigAll0_3 fsig3_62), (final_of_sigs' sigAll0_3 fsig3_63), (final_of_sigs' sigAll0_3 fsig3_64), (final_of_sigs' sigAll0_3 fsig3_65), (final_of_sigs' sigAll0_3 fsig3_66), (final_of_sigs' sigAll0_3 fsig3_67), (final_of_sigs' sigAll0_3 fsig3_68), (final_of_sigs' sigAll0_3 fsig3_69), (final_of_sigs' sigAll0_3 fsig3_70), (final_of_sigs' sigAll0_3 fsig3_71), (final_of_sigs' sigAll0_3 fsig3_72), (final_of_sigs' sigAll0_3 fsig3_73), (final_of_sigs' sigAll0_3 fsig3_74), (final_of_sigs' sigAll0_3 fsig3_75), (final_of_sigs' sigAll0_3 fsig3_76), (final_of_sigs' sigAll0_3 fsig3_77), (final_of_sigs' sigAll0_3 fsig3_78), (final_of_sigs' sigAll0_3 fsig3_79), (final_of_sigs' sigAll0_3 fsig3_80), (final_of_sigs' sigAll0_3 fsig3_81), (final_of_sigs' sigAll0_3 fsig3_82), (final_of_sigs' sigAll0_3 fsig3_83), (final_of_sigs' sigAll0_3 fsig3_84), (final_of_sigs' sigAll0_3 fsig3_85), (final_of_sigs' sigAll0_3 fsig3_86), (final_of_sigs' sigAll0_3 fsig3_87), (final_of_sigs' sigAll0_3 fsig3_88), (final_of_sigs' sigAll0_3 fsig3_89), (final_of_sigs' sigAll0_3 fsig3_90), (final_of_sigs' sigAll0_3 fsig3_91), (final_of_sigs' sigAll0_3 fsig3_92), (final_of_sigs' sigAll0_3 fsig3_93), (final_of_sigs' sigAll0_3 fsig3_94), (final_of_sigs' sigAll0_3 fsig3_95), (final_of_sigs' sigAll0_3 fsig3_96), (final_of_sigs' sigAll0_3 fsig3_97), (final_of_sigs' sigAll0_3 fsig3_98), (final_of_sigs' sigAll0_3 fsig3_99), (final_of_sigs' sigAll0_3 fsig3_100), (final_of_sigs' sigAll0_3 fsig3_101), (final_of_sigs' sigAll0_3 fsig3_102), (final_of_sigs' sigAll0_3 fsig3_103), (final_of_sigs' sigAll0_3 fsig3_104), (final_of_sigs' sigAll0_3 fsig3_105), (final_of_sigs' sigAll0_3 fsig3_106), (final_of_sigs' sigAll0_3 fsig3_107), (final_of_sigs' sigAll0_3 fsig3_108), (final_of_sigs' sigAll0_3 fsig3_109), (final_of_sigs' sigAll0_3 fsig3_110), (final_of_sigs' sigAll0_3 fsig3_111), (final_of_sigs' sigAll0_3 fsig3_112), (final_of_sigs' sigAll0_3 fsig3_113), (final_of_sigs' sigAll0_3 fsig3_114), (final_of_sigs' sigAll0_3 fsig3_115), (final_of_sigs' sigAll0_3 fsig3_116), (final_of_sigs' sigAll0_3 fsig3_117), (final_of_sigs' sigAll0_3 fsig3_118), (final_of_sigs' sigAll0_3 fsig3_119), trivial⟩
theorem sigAll0_4 : ∀ j, j < NS4 → outsideSig 0 (sigDec (getW SA4 j)).1 (sigDec (getW SA4 j)).2.1 (sigDec (getW SA4 j)).2.2.1 (sigDec (getW SA4 j)).2.2.2.1 (sigDec (getW SA4 j)).2.2.2.2 = false := by
  intro j hj
  by_cases h0 : j < 64
  · exact sigsOKR_spec sg0_4_0 j (by omega) h0
  by_cases h1 : j < 128
  · exact sigsOKR_spec sg0_4_1 j (by omega) h1
  by_cases h2 : j < 192
  · exact sigsOKR_spec sg0_4_2 j (by omega) h2
  by_cases h3 : j < 256
  · exact sigsOKR_spec sg0_4_3 j (by omega) h3
  by_cases h4 : j < 320
  · exact sigsOKR_spec sg0_4_4 j (by omega) h4
  by_cases h5 : j < 384
  · exact sigsOKR_spec sg0_4_5 j (by omega) h5
  by_cases h6 : j < 448
  · exact sigsOKR_spec sg0_4_6 j (by omega) h6
  by_cases h7 : j < 512
  · exact sigsOKR_spec sg0_4_7 j (by omega) h7
  by_cases h8 : j < 576
  · exact sigsOKR_spec sg0_4_8 j (by omega) h8
  by_cases h9 : j < 640
  · exact sigsOKR_spec sg0_4_9 j (by omega) h9
  by_cases h10 : j < 704
  · exact sigsOKR_spec sg0_4_10 j (by omega) h10
  by_cases h11 : j < 768
  · exact sigsOKR_spec sg0_4_11 j (by omega) h11
  by_cases h12 : j < 832
  · exact sigsOKR_spec sg0_4_12 j (by omega) h12
  by_cases h13 : j < 896
  · exact sigsOKR_spec sg0_4_13 j (by omega) h13
  by_cases h14 : j < 960
  · exact sigsOKR_spec sg0_4_14 j (by omega) h14
  by_cases h15 : j < 1024
  · exact sigsOKR_spec sg0_4_15 j (by omega) h15
  by_cases h16 : j < 1088
  · exact sigsOKR_spec sg0_4_16 j (by omega) h16
  · exact sigsOKR_spec sg0_4_17 j (by omega) (by simpa [NS4] using hj)
theorem finU0_4 : ∀ p ∈ UL36, finalOK 6 6 0 (some (1, (1 : ℤ), some 11)) p.1 p.2 = true := by
  exact AllP.mem (L := UL36) ⟨(final_of_sigs' sigAll0_4 fsig4_0), (final_of_sigs' sigAll0_4 fsig4_1), (final_of_sigs' sigAll0_4 fsig4_2), (final_of_sigs' sigAll0_4 fsig4_3), (final_of_sigs' sigAll0_4 fsig4_4), (final_of_sigs' sigAll0_4 fsig4_5), (final_of_sigs' sigAll0_4 fsig4_6), (final_of_sigs' sigAll0_4 fsig4_7), (final_of_sigs' sigAll0_4 fsig4_8), (final_of_sigs' sigAll0_4 fsig4_9), (final_of_sigs' sigAll0_4 fsig4_10), (final_of_sigs' sigAll0_4 fsig4_11), (final_of_sigs' sigAll0_4 fsig4_12), (final_of_sigs' sigAll0_4 fsig4_13), (final_of_sigs' sigAll0_4 fsig4_14), (final_of_sigs' sigAll0_4 fsig4_15), (final_of_sigs' sigAll0_4 fsig4_16), (final_of_sigs' sigAll0_4 fsig4_17), (final_of_sigs' sigAll0_4 fsig4_18), (final_of_sigs' sigAll0_4 fsig4_19), (final_of_sigs' sigAll0_4 fsig4_20), (final_of_sigs' sigAll0_4 fsig4_21), (final_of_sigs' sigAll0_4 fsig4_22), (final_of_sigs' sigAll0_4 fsig4_23), (final_of_sigs' sigAll0_4 fsig4_24), (final_of_sigs' sigAll0_4 fsig4_25), (final_of_sigs' sigAll0_4 fsig4_26), (final_of_sigs' sigAll0_4 fsig4_27), (final_of_sigs' sigAll0_4 fsig4_28), (final_of_sigs' sigAll0_4 fsig4_29), (final_of_sigs' sigAll0_4 fsig4_30), (final_of_sigs' sigAll0_4 fsig4_31), (final_of_sigs' sigAll0_4 fsig4_32), (final_of_sigs' sigAll0_4 fsig4_33), (final_of_sigs' sigAll0_4 fsig4_34), (final_of_sigs' sigAll0_4 fsig4_35), (final_of_sigs' sigAll0_4 fsig4_36), (final_of_sigs' sigAll0_4 fsig4_37), (final_of_sigs' sigAll0_4 fsig4_38), (final_of_sigs' sigAll0_4 fsig4_39), (final_of_sigs' sigAll0_4 fsig4_40), (final_of_sigs' sigAll0_4 fsig4_41), (final_of_sigs' sigAll0_4 fsig4_42), (final_of_sigs' sigAll0_4 fsig4_43), (final_of_sigs' sigAll0_4 fsig4_44), (final_of_sigs' sigAll0_4 fsig4_45), (final_of_sigs' sigAll0_4 fsig4_46), (final_of_sigs' sigAll0_4 fsig4_47), (final_of_sigs' sigAll0_4 fsig4_48), (final_of_sigs' sigAll0_4 fsig4_49), (final_of_sigs' sigAll0_4 fsig4_50), (final_of_sigs' sigAll0_4 fsig4_51), (final_of_sigs' sigAll0_4 fsig4_52), (final_of_sigs' sigAll0_4 fsig4_53), (final_of_sigs' sigAll0_4 fsig4_54), (final_of_sigs' sigAll0_4 fsig4_55), (final_of_sigs' sigAll0_4 fsig4_56), (final_of_sigs' sigAll0_4 fsig4_57), (final_of_sigs' sigAll0_4 fsig4_58), (final_of_sigs' sigAll0_4 fsig4_59), (final_of_sigs' sigAll0_4 fsig4_60), (final_of_sigs' sigAll0_4 fsig4_61), (final_of_sigs' sigAll0_4 fsig4_62), (final_of_sigs' sigAll0_4 fsig4_63), (final_of_sigs' sigAll0_4 fsig4_64), (final_of_sigs' sigAll0_4 fsig4_65), (final_of_sigs' sigAll0_4 fsig4_66), (final_of_sigs' sigAll0_4 fsig4_67), (final_of_sigs' sigAll0_4 fsig4_68), (final_of_sigs' sigAll0_4 fsig4_69), (final_of_sigs' sigAll0_4 fsig4_70), (final_of_sigs' sigAll0_4 fsig4_71), (final_of_sigs' sigAll0_4 fsig4_72), (final_of_sigs' sigAll0_4 fsig4_73), (final_of_sigs' sigAll0_4 fsig4_74), (final_of_sigs' sigAll0_4 fsig4_75), (final_of_sigs' sigAll0_4 fsig4_76), (final_of_sigs' sigAll0_4 fsig4_77), (final_of_sigs' sigAll0_4 fsig4_78), (final_of_sigs' sigAll0_4 fsig4_79), (final_of_sigs' sigAll0_4 fsig4_80), (final_of_sigs' sigAll0_4 fsig4_81), (final_of_sigs' sigAll0_4 fsig4_82), (final_of_sigs' sigAll0_4 fsig4_83), (final_of_sigs' sigAll0_4 fsig4_84), (final_of_sigs' sigAll0_4 fsig4_85), (final_of_sigs' sigAll0_4 fsig4_86), (final_of_sigs' sigAll0_4 fsig4_87), (final_of_sigs' sigAll0_4 fsig4_88), (final_of_sigs' sigAll0_4 fsig4_89), (final_of_sigs' sigAll0_4 fsig4_90), (final_of_sigs' sigAll0_4 fsig4_91), (final_of_sigs' sigAll0_4 fsig4_92), (final_of_sigs' sigAll0_4 fsig4_93), (final_of_sigs' sigAll0_4 fsig4_94), (final_of_sigs' sigAll0_4 fsig4_95), (final_of_sigs' sigAll0_4 fsig4_96), (final_of_sigs' sigAll0_4 fsig4_97), (final_of_sigs' sigAll0_4 fsig4_98), (final_of_sigs' sigAll0_4 fsig4_99), (final_of_sigs' sigAll0_4 fsig4_100), (final_of_sigs' sigAll0_4 fsig4_101), (final_of_sigs' sigAll0_4 fsig4_102), (final_of_sigs' sigAll0_4 fsig4_103), (final_of_sigs' sigAll0_4 fsig4_104), (final_of_sigs' sigAll0_4 fsig4_105), (final_of_sigs' sigAll0_4 fsig4_106), (final_of_sigs' sigAll0_4 fsig4_107), (final_of_sigs' sigAll0_4 fsig4_108), (final_of_sigs' sigAll0_4 fsig4_109), (final_of_sigs' sigAll0_4 fsig4_110), (final_of_sigs' sigAll0_4 fsig4_111), (final_of_sigs' sigAll0_4 fsig4_112), (final_of_sigs' sigAll0_4 fsig4_113), (final_of_sigs' sigAll0_4 fsig4_114), (final_of_sigs' sigAll0_4 fsig4_115), (final_of_sigs' sigAll0_4 fsig4_116), (final_of_sigs' sigAll0_4 fsig4_117), (final_of_sigs' sigAll0_4 fsig4_118), (final_of_sigs' sigAll0_4 fsig4_119), trivial⟩
theorem sigAll1_2 : ∀ j, j < NS2 → outsideSig 1 (sigDec (getW SA2 j)).1 (sigDec (getW SA2 j)).2.1 (sigDec (getW SA2 j)).2.2.1 (sigDec (getW SA2 j)).2.2.2.1 (sigDec (getW SA2 j)).2.2.2.2 = false := by
  intro j hj
  by_cases h0 : j < 64
  · exact sigsOKR_spec sg1_2_0 j (by omega) h0
  by_cases h1 : j < 128
  · exact sigsOKR_spec sg1_2_1 j (by omega) h1
  by_cases h2 : j < 192
  · exact sigsOKR_spec sg1_2_2 j (by omega) h2
  by_cases h3 : j < 256
  · exact sigsOKR_spec sg1_2_3 j (by omega) h3
  by_cases h4 : j < 320
  · exact sigsOKR_spec sg1_2_4 j (by omega) h4
  by_cases h5 : j < 384
  · exact sigsOKR_spec sg1_2_5 j (by omega) h5
  by_cases h6 : j < 448
  · exact sigsOKR_spec sg1_2_6 j (by omega) h6
  by_cases h7 : j < 512
  · exact sigsOKR_spec sg1_2_7 j (by omega) h7
  by_cases h8 : j < 576
  · exact sigsOKR_spec sg1_2_8 j (by omega) h8
  by_cases h9 : j < 640
  · exact sigsOKR_spec sg1_2_9 j (by omega) h9
  by_cases h10 : j < 704
  · exact sigsOKR_spec sg1_2_10 j (by omega) h10
  by_cases h11 : j < 768
  · exact sigsOKR_spec sg1_2_11 j (by omega) h11
  · exact sigsOKR_spec sg1_2_12 j (by omega) (by simpa [NS2] using hj)
theorem finU1_2 : ∀ p ∈ UL36, finalOK 6 6 1 (some (1, (1 : ℤ), none)) p.1 p.2 = true := by
  exact AllP.mem (L := UL36) ⟨(final_of_sigs' sigAll1_2 fsig2_0), (final_of_sigs' sigAll1_2 fsig2_1), (final_of_sigs' sigAll1_2 fsig2_2), (final_of_sigs' sigAll1_2 fsig2_3), (final_of_sigs' sigAll1_2 fsig2_4), (final_of_sigs' sigAll1_2 fsig2_5), (final_of_sigs' sigAll1_2 fsig2_6), (final_of_sigs' sigAll1_2 fsig2_7), (final_of_sigs' sigAll1_2 fsig2_8), (final_of_sigs' sigAll1_2 fsig2_9), (final_of_sigs' sigAll1_2 fsig2_10), (final_of_sigs' sigAll1_2 fsig2_11), (final_of_sigs' sigAll1_2 fsig2_12), (final_of_sigs' sigAll1_2 fsig2_13), (final_of_sigs' sigAll1_2 fsig2_14), (final_of_sigs' sigAll1_2 fsig2_15), (final_of_sigs' sigAll1_2 fsig2_16), (final_of_sigs' sigAll1_2 fsig2_17), (final_of_sigs' sigAll1_2 fsig2_18), (final_of_sigs' sigAll1_2 fsig2_19), (final_of_sigs' sigAll1_2 fsig2_20), (final_of_sigs' sigAll1_2 fsig2_21), (final_of_sigs' sigAll1_2 fsig2_22), (final_of_sigs' sigAll1_2 fsig2_23), (final_of_sigs' sigAll1_2 fsig2_24), (final_of_sigs' sigAll1_2 fsig2_25), (final_of_sigs' sigAll1_2 fsig2_26), (final_of_sigs' sigAll1_2 fsig2_27), (final_of_sigs' sigAll1_2 fsig2_28), (final_of_sigs' sigAll1_2 fsig2_29), (final_of_sigs' sigAll1_2 fsig2_30), (final_of_sigs' sigAll1_2 fsig2_31), (final_of_sigs' sigAll1_2 fsig2_32), (final_of_sigs' sigAll1_2 fsig2_33), (final_of_sigs' sigAll1_2 fsig2_34), (final_of_sigs' sigAll1_2 fsig2_35), (final_of_sigs' sigAll1_2 fsig2_36), (final_of_sigs' sigAll1_2 fsig2_37), (final_of_sigs' sigAll1_2 fsig2_38), (final_of_sigs' sigAll1_2 fsig2_39), (final_of_sigs' sigAll1_2 fsig2_40), (final_of_sigs' sigAll1_2 fsig2_41), (final_of_sigs' sigAll1_2 fsig2_42), (final_of_sigs' sigAll1_2 fsig2_43), (final_of_sigs' sigAll1_2 fsig2_44), (final_of_sigs' sigAll1_2 fsig2_45), (final_of_sigs' sigAll1_2 fsig2_46), (final_of_sigs' sigAll1_2 fsig2_47), (final_of_sigs' sigAll1_2 fsig2_48), (final_of_sigs' sigAll1_2 fsig2_49), (final_of_sigs' sigAll1_2 fsig2_50), (final_of_sigs' sigAll1_2 fsig2_51), (final_of_sigs' sigAll1_2 fsig2_52), (final_of_sigs' sigAll1_2 fsig2_53), (final_of_sigs' sigAll1_2 fsig2_54), (final_of_sigs' sigAll1_2 fsig2_55), (final_of_sigs' sigAll1_2 fsig2_56), (final_of_sigs' sigAll1_2 fsig2_57), (final_of_sigs' sigAll1_2 fsig2_58), (final_of_sigs' sigAll1_2 fsig2_59), (final_of_sigs' sigAll1_2 fsig2_60), (final_of_sigs' sigAll1_2 fsig2_61), (final_of_sigs' sigAll1_2 fsig2_62), (final_of_sigs' sigAll1_2 fsig2_63), (final_of_sigs' sigAll1_2 fsig2_64), (final_of_sigs' sigAll1_2 fsig2_65), (final_of_sigs' sigAll1_2 fsig2_66), (final_of_sigs' sigAll1_2 fsig2_67), (final_of_sigs' sigAll1_2 fsig2_68), (final_of_sigs' sigAll1_2 fsig2_69), (final_of_sigs' sigAll1_2 fsig2_70), (final_of_sigs' sigAll1_2 fsig2_71), (final_of_sigs' sigAll1_2 fsig2_72), (final_of_sigs' sigAll1_2 fsig2_73), (final_of_sigs' sigAll1_2 fsig2_74), (final_of_sigs' sigAll1_2 fsig2_75), (final_of_sigs' sigAll1_2 fsig2_76), (final_of_sigs' sigAll1_2 fsig2_77), (final_of_sigs' sigAll1_2 fsig2_78), (final_of_sigs' sigAll1_2 fsig2_79), (final_of_sigs' sigAll1_2 fsig2_80), (final_of_sigs' sigAll1_2 fsig2_81), (final_of_sigs' sigAll1_2 fsig2_82), (final_of_sigs' sigAll1_2 fsig2_83), (final_of_sigs' sigAll1_2 fsig2_84), (final_of_sigs' sigAll1_2 fsig2_85), (final_of_sigs' sigAll1_2 fsig2_86), (final_of_sigs' sigAll1_2 fsig2_87), (final_of_sigs' sigAll1_2 fsig2_88), (final_of_sigs' sigAll1_2 fsig2_89), (final_of_sigs' sigAll1_2 fsig2_90), (final_of_sigs' sigAll1_2 fsig2_91), (final_of_sigs' sigAll1_2 fsig2_92), (final_of_sigs' sigAll1_2 fsig2_93), (final_of_sigs' sigAll1_2 fsig2_94), (final_of_sigs' sigAll1_2 fsig2_95), (final_of_sigs' sigAll1_2 fsig2_96), (final_of_sigs' sigAll1_2 fsig2_97), (final_of_sigs' sigAll1_2 fsig2_98), (final_of_sigs' sigAll1_2 fsig2_99), (final_of_sigs' sigAll1_2 fsig2_100), (final_of_sigs' sigAll1_2 fsig2_101), (final_of_sigs' sigAll1_2 fsig2_102), (final_of_sigs' sigAll1_2 fsig2_103), (final_of_sigs' sigAll1_2 fsig2_104), (final_of_sigs' sigAll1_2 fsig2_105), (final_of_sigs' sigAll1_2 fsig2_106), (final_of_sigs' sigAll1_2 fsig2_107), (final_of_sigs' sigAll1_2 fsig2_108), (final_of_sigs' sigAll1_2 fsig2_109), (final_of_sigs' sigAll1_2 fsig2_110), (final_of_sigs' sigAll1_2 fsig2_111), (final_of_sigs' sigAll1_2 fsig2_112), (final_of_sigs' sigAll1_2 fsig2_113), (final_of_sigs' sigAll1_2 fsig2_114), (final_of_sigs' sigAll1_2 fsig2_115), (final_of_sigs' sigAll1_2 fsig2_116), (final_of_sigs' sigAll1_2 fsig2_117), (final_of_sigs' sigAll1_2 fsig2_118), (final_of_sigs' sigAll1_2 fsig2_119), trivial⟩
theorem sigAll1_3 : ∀ j, j < NS3 → outsideSig 1 (sigDec (getW SA3 j)).1 (sigDec (getW SA3 j)).2.1 (sigDec (getW SA3 j)).2.2.1 (sigDec (getW SA3 j)).2.2.2.1 (sigDec (getW SA3 j)).2.2.2.2 = false := by
  intro j hj
  by_cases h0 : j < 64
  · exact sigsOKR_spec sg1_3_0 j (by omega) h0
  by_cases h1 : j < 128
  · exact sigsOKR_spec sg1_3_1 j (by omega) h1
  by_cases h2 : j < 192
  · exact sigsOKR_spec sg1_3_2 j (by omega) h2
  by_cases h3 : j < 256
  · exact sigsOKR_spec sg1_3_3 j (by omega) h3
  by_cases h4 : j < 320
  · exact sigsOKR_spec sg1_3_4 j (by omega) h4
  by_cases h5 : j < 384
  · exact sigsOKR_spec sg1_3_5 j (by omega) h5
  by_cases h6 : j < 448
  · exact sigsOKR_spec sg1_3_6 j (by omega) h6
  by_cases h7 : j < 512
  · exact sigsOKR_spec sg1_3_7 j (by omega) h7
  by_cases h8 : j < 576
  · exact sigsOKR_spec sg1_3_8 j (by omega) h8
  by_cases h9 : j < 640
  · exact sigsOKR_spec sg1_3_9 j (by omega) h9
  by_cases h10 : j < 704
  · exact sigsOKR_spec sg1_3_10 j (by omega) h10
  by_cases h11 : j < 768
  · exact sigsOKR_spec sg1_3_11 j (by omega) h11
  by_cases h12 : j < 832
  · exact sigsOKR_spec sg1_3_12 j (by omega) h12
  by_cases h13 : j < 896
  · exact sigsOKR_spec sg1_3_13 j (by omega) h13
  by_cases h14 : j < 960
  · exact sigsOKR_spec sg1_3_14 j (by omega) h14
  by_cases h15 : j < 1024
  · exact sigsOKR_spec sg1_3_15 j (by omega) h15
  by_cases h16 : j < 1088
  · exact sigsOKR_spec sg1_3_16 j (by omega) h16
  · exact sigsOKR_spec sg1_3_17 j (by omega) (by simpa [NS3] using hj)
theorem finU1_3 : ∀ p ∈ UL36, finalOK 6 6 1 (some (1, (1 : ℤ), some 0)) p.1 p.2 = true := by
  exact AllP.mem (L := UL36) ⟨(final_of_sigs' sigAll1_3 fsig3_0), (final_of_sigs' sigAll1_3 fsig3_1), (final_of_sigs' sigAll1_3 fsig3_2), (final_of_sigs' sigAll1_3 fsig3_3), (final_of_sigs' sigAll1_3 fsig3_4), (final_of_sigs' sigAll1_3 fsig3_5), (final_of_sigs' sigAll1_3 fsig3_6), (final_of_sigs' sigAll1_3 fsig3_7), (final_of_sigs' sigAll1_3 fsig3_8), (final_of_sigs' sigAll1_3 fsig3_9), (final_of_sigs' sigAll1_3 fsig3_10), (final_of_sigs' sigAll1_3 fsig3_11), (final_of_sigs' sigAll1_3 fsig3_12), (final_of_sigs' sigAll1_3 fsig3_13), (final_of_sigs' sigAll1_3 fsig3_14), (final_of_sigs' sigAll1_3 fsig3_15), (final_of_sigs' sigAll1_3 fsig3_16), (final_of_sigs' sigAll1_3 fsig3_17), (final_of_sigs' sigAll1_3 fsig3_18), (final_of_sigs' sigAll1_3 fsig3_19), (final_of_sigs' sigAll1_3 fsig3_20), (final_of_sigs' sigAll1_3 fsig3_21), (final_of_sigs' sigAll1_3 fsig3_22), (final_of_sigs' sigAll1_3 fsig3_23), (final_of_sigs' sigAll1_3 fsig3_24), (final_of_sigs' sigAll1_3 fsig3_25), (final_of_sigs' sigAll1_3 fsig3_26), (final_of_sigs' sigAll1_3 fsig3_27), (final_of_sigs' sigAll1_3 fsig3_28), (final_of_sigs' sigAll1_3 fsig3_29), (final_of_sigs' sigAll1_3 fsig3_30), (final_of_sigs' sigAll1_3 fsig3_31), (final_of_sigs' sigAll1_3 fsig3_32), (final_of_sigs' sigAll1_3 fsig3_33), (final_of_sigs' sigAll1_3 fsig3_34), (final_of_sigs' sigAll1_3 fsig3_35), (final_of_sigs' sigAll1_3 fsig3_36), (final_of_sigs' sigAll1_3 fsig3_37), (final_of_sigs' sigAll1_3 fsig3_38), (final_of_sigs' sigAll1_3 fsig3_39), (final_of_sigs' sigAll1_3 fsig3_40), (final_of_sigs' sigAll1_3 fsig3_41), (final_of_sigs' sigAll1_3 fsig3_42), (final_of_sigs' sigAll1_3 fsig3_43), (final_of_sigs' sigAll1_3 fsig3_44), (final_of_sigs' sigAll1_3 fsig3_45), (final_of_sigs' sigAll1_3 fsig3_46), (final_of_sigs' sigAll1_3 fsig3_47), (final_of_sigs' sigAll1_3 fsig3_48), (final_of_sigs' sigAll1_3 fsig3_49), (final_of_sigs' sigAll1_3 fsig3_50), (final_of_sigs' sigAll1_3 fsig3_51), (final_of_sigs' sigAll1_3 fsig3_52), (final_of_sigs' sigAll1_3 fsig3_53), (final_of_sigs' sigAll1_3 fsig3_54), (final_of_sigs' sigAll1_3 fsig3_55), (final_of_sigs' sigAll1_3 fsig3_56), (final_of_sigs' sigAll1_3 fsig3_57), (final_of_sigs' sigAll1_3 fsig3_58), (final_of_sigs' sigAll1_3 fsig3_59), (final_of_sigs' sigAll1_3 fsig3_60), (final_of_sigs' sigAll1_3 fsig3_61), (final_of_sigs' sigAll1_3 fsig3_62), (final_of_sigs' sigAll1_3 fsig3_63), (final_of_sigs' sigAll1_3 fsig3_64), (final_of_sigs' sigAll1_3 fsig3_65), (final_of_sigs' sigAll1_3 fsig3_66), (final_of_sigs' sigAll1_3 fsig3_67), (final_of_sigs' sigAll1_3 fsig3_68), (final_of_sigs' sigAll1_3 fsig3_69), (final_of_sigs' sigAll1_3 fsig3_70), (final_of_sigs' sigAll1_3 fsig3_71), (final_of_sigs' sigAll1_3 fsig3_72), (final_of_sigs' sigAll1_3 fsig3_73), (final_of_sigs' sigAll1_3 fsig3_74), (final_of_sigs' sigAll1_3 fsig3_75), (final_of_sigs' sigAll1_3 fsig3_76), (final_of_sigs' sigAll1_3 fsig3_77), (final_of_sigs' sigAll1_3 fsig3_78), (final_of_sigs' sigAll1_3 fsig3_79), (final_of_sigs' sigAll1_3 fsig3_80), (final_of_sigs' sigAll1_3 fsig3_81), (final_of_sigs' sigAll1_3 fsig3_82), (final_of_sigs' sigAll1_3 fsig3_83), (final_of_sigs' sigAll1_3 fsig3_84), (final_of_sigs' sigAll1_3 fsig3_85), (final_of_sigs' sigAll1_3 fsig3_86), (final_of_sigs' sigAll1_3 fsig3_87), (final_of_sigs' sigAll1_3 fsig3_88), (final_of_sigs' sigAll1_3 fsig3_89), (final_of_sigs' sigAll1_3 fsig3_90), (final_of_sigs' sigAll1_3 fsig3_91), (final_of_sigs' sigAll1_3 fsig3_92), (final_of_sigs' sigAll1_3 fsig3_93), (final_of_sigs' sigAll1_3 fsig3_94), (final_of_sigs' sigAll1_3 fsig3_95), (final_of_sigs' sigAll1_3 fsig3_96), (final_of_sigs' sigAll1_3 fsig3_97), (final_of_sigs' sigAll1_3 fsig3_98), (final_of_sigs' sigAll1_3 fsig3_99), (final_of_sigs' sigAll1_3 fsig3_100), (final_of_sigs' sigAll1_3 fsig3_101), (final_of_sigs' sigAll1_3 fsig3_102), (final_of_sigs' sigAll1_3 fsig3_103), (final_of_sigs' sigAll1_3 fsig3_104), (final_of_sigs' sigAll1_3 fsig3_105), (final_of_sigs' sigAll1_3 fsig3_106), (final_of_sigs' sigAll1_3 fsig3_107), (final_of_sigs' sigAll1_3 fsig3_108), (final_of_sigs' sigAll1_3 fsig3_109), (final_of_sigs' sigAll1_3 fsig3_110), (final_of_sigs' sigAll1_3 fsig3_111), (final_of_sigs' sigAll1_3 fsig3_112), (final_of_sigs' sigAll1_3 fsig3_113), (final_of_sigs' sigAll1_3 fsig3_114), (final_of_sigs' sigAll1_3 fsig3_115), (final_of_sigs' sigAll1_3 fsig3_116), (final_of_sigs' sigAll1_3 fsig3_117), (final_of_sigs' sigAll1_3 fsig3_118), (final_of_sigs' sigAll1_3 fsig3_119), trivial⟩
theorem sigAll1_4 : ∀ j, j < NS4 → outsideSig 1 (sigDec (getW SA4 j)).1 (sigDec (getW SA4 j)).2.1 (sigDec (getW SA4 j)).2.2.1 (sigDec (getW SA4 j)).2.2.2.1 (sigDec (getW SA4 j)).2.2.2.2 = false := by
  intro j hj
  by_cases h0 : j < 64
  · exact sigsOKR_spec sg1_4_0 j (by omega) h0
  by_cases h1 : j < 128
  · exact sigsOKR_spec sg1_4_1 j (by omega) h1
  by_cases h2 : j < 192
  · exact sigsOKR_spec sg1_4_2 j (by omega) h2
  by_cases h3 : j < 256
  · exact sigsOKR_spec sg1_4_3 j (by omega) h3
  by_cases h4 : j < 320
  · exact sigsOKR_spec sg1_4_4 j (by omega) h4
  by_cases h5 : j < 384
  · exact sigsOKR_spec sg1_4_5 j (by omega) h5
  by_cases h6 : j < 448
  · exact sigsOKR_spec sg1_4_6 j (by omega) h6
  by_cases h7 : j < 512
  · exact sigsOKR_spec sg1_4_7 j (by omega) h7
  by_cases h8 : j < 576
  · exact sigsOKR_spec sg1_4_8 j (by omega) h8
  by_cases h9 : j < 640
  · exact sigsOKR_spec sg1_4_9 j (by omega) h9
  by_cases h10 : j < 704
  · exact sigsOKR_spec sg1_4_10 j (by omega) h10
  by_cases h11 : j < 768
  · exact sigsOKR_spec sg1_4_11 j (by omega) h11
  by_cases h12 : j < 832
  · exact sigsOKR_spec sg1_4_12 j (by omega) h12
  by_cases h13 : j < 896
  · exact sigsOKR_spec sg1_4_13 j (by omega) h13
  by_cases h14 : j < 960
  · exact sigsOKR_spec sg1_4_14 j (by omega) h14
  by_cases h15 : j < 1024
  · exact sigsOKR_spec sg1_4_15 j (by omega) h15
  by_cases h16 : j < 1088
  · exact sigsOKR_spec sg1_4_16 j (by omega) h16
  · exact sigsOKR_spec sg1_4_17 j (by omega) (by simpa [NS4] using hj)
theorem finU1_4 : ∀ p ∈ UL36, finalOK 6 6 1 (some (1, (1 : ℤ), some 11)) p.1 p.2 = true := by
  exact AllP.mem (L := UL36) ⟨(final_of_sigs' sigAll1_4 fsig4_0), (final_of_sigs' sigAll1_4 fsig4_1), (final_of_sigs' sigAll1_4 fsig4_2), (final_of_sigs' sigAll1_4 fsig4_3), (final_of_sigs' sigAll1_4 fsig4_4), (final_of_sigs' sigAll1_4 fsig4_5), (final_of_sigs' sigAll1_4 fsig4_6), (final_of_sigs' sigAll1_4 fsig4_7), (final_of_sigs' sigAll1_4 fsig4_8), (final_of_sigs' sigAll1_4 fsig4_9), (final_of_sigs' sigAll1_4 fsig4_10), (final_of_sigs' sigAll1_4 fsig4_11), (final_of_sigs' sigAll1_4 fsig4_12), (final_of_sigs' sigAll1_4 fsig4_13), (final_of_sigs' sigAll1_4 fsig4_14), (final_of_sigs' sigAll1_4 fsig4_15), (final_of_sigs' sigAll1_4 fsig4_16), (final_of_sigs' sigAll1_4 fsig4_17), (final_of_sigs' sigAll1_4 fsig4_18), (final_of_sigs' sigAll1_4 fsig4_19), (final_of_sigs' sigAll1_4 fsig4_20), (final_of_sigs' sigAll1_4 fsig4_21), (final_of_sigs' sigAll1_4 fsig4_22), (final_of_sigs' sigAll1_4 fsig4_23), (final_of_sigs' sigAll1_4 fsig4_24), (final_of_sigs' sigAll1_4 fsig4_25), (final_of_sigs' sigAll1_4 fsig4_26), (final_of_sigs' sigAll1_4 fsig4_27), (final_of_sigs' sigAll1_4 fsig4_28), (final_of_sigs' sigAll1_4 fsig4_29), (final_of_sigs' sigAll1_4 fsig4_30), (final_of_sigs' sigAll1_4 fsig4_31), (final_of_sigs' sigAll1_4 fsig4_32), (final_of_sigs' sigAll1_4 fsig4_33), (final_of_sigs' sigAll1_4 fsig4_34), (final_of_sigs' sigAll1_4 fsig4_35), (final_of_sigs' sigAll1_4 fsig4_36), (final_of_sigs' sigAll1_4 fsig4_37), (final_of_sigs' sigAll1_4 fsig4_38), (final_of_sigs' sigAll1_4 fsig4_39), (final_of_sigs' sigAll1_4 fsig4_40), (final_of_sigs' sigAll1_4 fsig4_41), (final_of_sigs' sigAll1_4 fsig4_42), (final_of_sigs' sigAll1_4 fsig4_43), (final_of_sigs' sigAll1_4 fsig4_44), (final_of_sigs' sigAll1_4 fsig4_45), (final_of_sigs' sigAll1_4 fsig4_46), (final_of_sigs' sigAll1_4 fsig4_47), (final_of_sigs' sigAll1_4 fsig4_48), (final_of_sigs' sigAll1_4 fsig4_49), (final_of_sigs' sigAll1_4 fsig4_50), (final_of_sigs' sigAll1_4 fsig4_51), (final_of_sigs' sigAll1_4 fsig4_52), (final_of_sigs' sigAll1_4 fsig4_53), (final_of_sigs' sigAll1_4 fsig4_54), (final_of_sigs' sigAll1_4 fsig4_55), (final_of_sigs' sigAll1_4 fsig4_56), (final_of_sigs' sigAll1_4 fsig4_57), (final_of_sigs' sigAll1_4 fsig4_58), (final_of_sigs' sigAll1_4 fsig4_59), (final_of_sigs' sigAll1_4 fsig4_60), (final_of_sigs' sigAll1_4 fsig4_61), (final_of_sigs' sigAll1_4 fsig4_62), (final_of_sigs' sigAll1_4 fsig4_63), (final_of_sigs' sigAll1_4 fsig4_64), (final_of_sigs' sigAll1_4 fsig4_65), (final_of_sigs' sigAll1_4 fsig4_66), (final_of_sigs' sigAll1_4 fsig4_67), (final_of_sigs' sigAll1_4 fsig4_68), (final_of_sigs' sigAll1_4 fsig4_69), (final_of_sigs' sigAll1_4 fsig4_70), (final_of_sigs' sigAll1_4 fsig4_71), (final_of_sigs' sigAll1_4 fsig4_72), (final_of_sigs' sigAll1_4 fsig4_73), (final_of_sigs' sigAll1_4 fsig4_74), (final_of_sigs' sigAll1_4 fsig4_75), (final_of_sigs' sigAll1_4 fsig4_76), (final_of_sigs' sigAll1_4 fsig4_77), (final_of_sigs' sigAll1_4 fsig4_78), (final_of_sigs' sigAll1_4 fsig4_79), (final_of_sigs' sigAll1_4 fsig4_80), (final_of_sigs' sigAll1_4 fsig4_81), (final_of_sigs' sigAll1_4 fsig4_82), (final_of_sigs' sigAll1_4 fsig4_83), (final_of_sigs' sigAll1_4 fsig4_84), (final_of_sigs' sigAll1_4 fsig4_85), (final_of_sigs' sigAll1_4 fsig4_86), (final_of_sigs' sigAll1_4 fsig4_87), (final_of_sigs' sigAll1_4 fsig4_88), (final_of_sigs' sigAll1_4 fsig4_89), (final_of_sigs' sigAll1_4 fsig4_90), (final_of_sigs' sigAll1_4 fsig4_91), (final_of_sigs' sigAll1_4 fsig4_92), (final_of_sigs' sigAll1_4 fsig4_93), (final_of_sigs' sigAll1_4 fsig4_94), (final_of_sigs' sigAll1_4 fsig4_95), (final_of_sigs' sigAll1_4 fsig4_96), (final_of_sigs' sigAll1_4 fsig4_97), (final_of_sigs' sigAll1_4 fsig4_98), (final_of_sigs' sigAll1_4 fsig4_99), (final_of_sigs' sigAll1_4 fsig4_100), (final_of_sigs' sigAll1_4 fsig4_101), (final_of_sigs' sigAll1_4 fsig4_102), (final_of_sigs' sigAll1_4 fsig4_103), (final_of_sigs' sigAll1_4 fsig4_104), (final_of_sigs' sigAll1_4 fsig4_105), (final_of_sigs' sigAll1_4 fsig4_106), (final_of_sigs' sigAll1_4 fsig4_107), (final_of_sigs' sigAll1_4 fsig4_108), (final_of_sigs' sigAll1_4 fsig4_109), (final_of_sigs' sigAll1_4 fsig4_110), (final_of_sigs' sigAll1_4 fsig4_111), (final_of_sigs' sigAll1_4 fsig4_112), (final_of_sigs' sigAll1_4 fsig4_113), (final_of_sigs' sigAll1_4 fsig4_114), (final_of_sigs' sigAll1_4 fsig4_115), (final_of_sigs' sigAll1_4 fsig4_116), (final_of_sigs' sigAll1_4 fsig4_117), (final_of_sigs' sigAll1_4 fsig4_118), (final_of_sigs' sigAll1_4 fsig4_119), trivial⟩
theorem sigAll1_1 : ∀ j, j < NS1 → outsideSig 1 (sigDec (getW SA1 j)).1 (sigDec (getW SA1 j)).2.1 (sigDec (getW SA1 j)).2.2.1 (sigDec (getW SA1 j)).2.2.2.1 (sigDec (getW SA1 j)).2.2.2.2 = false := by
  intro j hj
  by_cases h0 : j < 64
  · exact sigsOKR_spec sg1_1_0 j (by omega) h0
  by_cases h1 : j < 128
  · exact sigsOKR_spec sg1_1_1 j (by omega) h1
  by_cases h2 : j < 192
  · exact sigsOKR_spec sg1_1_2 j (by omega) h2
  by_cases h3 : j < 256
  · exact sigsOKR_spec sg1_1_3 j (by omega) h3
  by_cases h4 : j < 320
  · exact sigsOKR_spec sg1_1_4 j (by omega) h4
  by_cases h5 : j < 384
  · exact sigsOKR_spec sg1_1_5 j (by omega) h5
  by_cases h6 : j < 448
  · exact sigsOKR_spec sg1_1_6 j (by omega) h6
  by_cases h7 : j < 512
  · exact sigsOKR_spec sg1_1_7 j (by omega) h7
  by_cases h8 : j < 576
  · exact sigsOKR_spec sg1_1_8 j (by omega) h8
  by_cases h9 : j < 640
  · exact sigsOKR_spec sg1_1_9 j (by omega) h9
  by_cases h10 : j < 704
  · exact sigsOKR_spec sg1_1_10 j (by omega) h10
  by_cases h11 : j < 768
  · exact sigsOKR_spec sg1_1_11 j (by omega) h11
  · exact sigsOKR_spec sg1_1_12 j (by omega) (by simpa [NS1] using hj)
theorem finU1_1 : ∀ p ∈ UL36, finalOK 6 6 1 (some (1, (-1 : ℤ), none)) p.1 p.2 = true := by
  exact AllP.mem (L := UL36) ⟨(final_of_sigs' sigAll1_1 fsig1_0), (final_of_sigs' sigAll1_1 fsig1_1), (final_of_sigs' sigAll1_1 fsig1_2), (final_of_sigs' sigAll1_1 fsig1_3), (final_of_sigs' sigAll1_1 fsig1_4), (final_of_sigs' sigAll1_1 fsig1_5), (final_of_sigs' sigAll1_1 fsig1_6), (final_of_sigs' sigAll1_1 fsig1_7), (final_of_sigs' sigAll1_1 fsig1_8), (final_of_sigs' sigAll1_1 fsig1_9), (final_of_sigs' sigAll1_1 fsig1_10), (final_of_sigs' sigAll1_1 fsig1_11), (final_of_sigs' sigAll1_1 fsig1_12), (final_of_sigs' sigAll1_1 fsig1_13), (final_of_sigs' sigAll1_1 fsig1_14), (final_of_sigs' sigAll1_1 fsig1_15), (final_of_sigs' sigAll1_1 fsig1_16), (final_of_sigs' sigAll1_1 fsig1_17), (final_of_sigs' sigAll1_1 fsig1_18), (final_of_sigs' sigAll1_1 fsig1_19), (final_of_sigs' sigAll1_1 fsig1_20), (final_of_sigs' sigAll1_1 fsig1_21), (final_of_sigs' sigAll1_1 fsig1_22), (final_of_sigs' sigAll1_1 fsig1_23), (final_of_sigs' sigAll1_1 fsig1_24), (final_of_sigs' sigAll1_1 fsig1_25), (final_of_sigs' sigAll1_1 fsig1_26), (final_of_sigs' sigAll1_1 fsig1_27), (final_of_sigs' sigAll1_1 fsig1_28), (final_of_sigs' sigAll1_1 fsig1_29), (final_of_sigs' sigAll1_1 fsig1_30), (final_of_sigs' sigAll1_1 fsig1_31), (final_of_sigs' sigAll1_1 fsig1_32), (final_of_sigs' sigAll1_1 fsig1_33), (final_of_sigs' sigAll1_1 fsig1_34), (final_of_sigs' sigAll1_1 fsig1_35), (final_of_sigs' sigAll1_1 fsig1_36), (final_of_sigs' sigAll1_1 fsig1_37), (final_of_sigs' sigAll1_1 fsig1_38), (final_of_sigs' sigAll1_1 fsig1_39), (final_of_sigs' sigAll1_1 fsig1_40), (final_of_sigs' sigAll1_1 fsig1_41), (final_of_sigs' sigAll1_1 fsig1_42), (final_of_sigs' sigAll1_1 fsig1_43), (final_of_sigs' sigAll1_1 fsig1_44), (final_of_sigs' sigAll1_1 fsig1_45), (final_of_sigs' sigAll1_1 fsig1_46), (final_of_sigs' sigAll1_1 fsig1_47), (final_of_sigs' sigAll1_1 fsig1_48), (final_of_sigs' sigAll1_1 fsig1_49), (final_of_sigs' sigAll1_1 fsig1_50), (final_of_sigs' sigAll1_1 fsig1_51), (final_of_sigs' sigAll1_1 fsig1_52), (final_of_sigs' sigAll1_1 fsig1_53), (final_of_sigs' sigAll1_1 fsig1_54), (final_of_sigs' sigAll1_1 fsig1_55), (final_of_sigs' sigAll1_1 fsig1_56), (final_of_sigs' sigAll1_1 fsig1_57), (final_of_sigs' sigAll1_1 fsig1_58), (final_of_sigs' sigAll1_1 fsig1_59), (final_of_sigs' sigAll1_1 fsig1_60), (final_of_sigs' sigAll1_1 fsig1_61), (final_of_sigs' sigAll1_1 fsig1_62), (final_of_sigs' sigAll1_1 fsig1_63), (final_of_sigs' sigAll1_1 fsig1_64), (final_of_sigs' sigAll1_1 fsig1_65), (final_of_sigs' sigAll1_1 fsig1_66), (final_of_sigs' sigAll1_1 fsig1_67), (final_of_sigs' sigAll1_1 fsig1_68), (final_of_sigs' sigAll1_1 fsig1_69), (final_of_sigs' sigAll1_1 fsig1_70), (final_of_sigs' sigAll1_1 fsig1_71), (final_of_sigs' sigAll1_1 fsig1_72), (final_of_sigs' sigAll1_1 fsig1_73), (final_of_sigs' sigAll1_1 fsig1_74), (final_of_sigs' sigAll1_1 fsig1_75), (final_of_sigs' sigAll1_1 fsig1_76), (final_of_sigs' sigAll1_1 fsig1_77), (final_of_sigs' sigAll1_1 fsig1_78), (final_of_sigs' sigAll1_1 fsig1_79), (final_of_sigs' sigAll1_1 fsig1_80), (final_of_sigs' sigAll1_1 fsig1_81), (final_of_sigs' sigAll1_1 fsig1_82), (final_of_sigs' sigAll1_1 fsig1_83), (final_of_sigs' sigAll1_1 fsig1_84), (final_of_sigs' sigAll1_1 fsig1_85), (final_of_sigs' sigAll1_1 fsig1_86), (final_of_sigs' sigAll1_1 fsig1_87), (final_of_sigs' sigAll1_1 fsig1_88), (final_of_sigs' sigAll1_1 fsig1_89), (final_of_sigs' sigAll1_1 fsig1_90), (final_of_sigs' sigAll1_1 fsig1_91), (final_of_sigs' sigAll1_1 fsig1_92), (final_of_sigs' sigAll1_1 fsig1_93), (final_of_sigs' sigAll1_1 fsig1_94), (final_of_sigs' sigAll1_1 fsig1_95), (final_of_sigs' sigAll1_1 fsig1_96), (final_of_sigs' sigAll1_1 fsig1_97), (final_of_sigs' sigAll1_1 fsig1_98), (final_of_sigs' sigAll1_1 fsig1_99), (final_of_sigs' sigAll1_1 fsig1_100), (final_of_sigs' sigAll1_1 fsig1_101), (final_of_sigs' sigAll1_1 fsig1_102), (final_of_sigs' sigAll1_1 fsig1_103), (final_of_sigs' sigAll1_1 fsig1_104), (final_of_sigs' sigAll1_1 fsig1_105), (final_of_sigs' sigAll1_1 fsig1_106), (final_of_sigs' sigAll1_1 fsig1_107), (final_of_sigs' sigAll1_1 fsig1_108), (final_of_sigs' sigAll1_1 fsig1_109), (final_of_sigs' sigAll1_1 fsig1_110), (final_of_sigs' sigAll1_1 fsig1_111), (final_of_sigs' sigAll1_1 fsig1_112), (final_of_sigs' sigAll1_1 fsig1_113), (final_of_sigs' sigAll1_1 fsig1_114), (final_of_sigs' sigAll1_1 fsig1_115), (final_of_sigs' sigAll1_1 fsig1_116), (final_of_sigs' sigAll1_1 fsig1_117), (final_of_sigs' sigAll1_1 fsig1_118), (final_of_sigs' sigAll1_1 fsig1_119), trivial⟩
end WinKU.Shared
