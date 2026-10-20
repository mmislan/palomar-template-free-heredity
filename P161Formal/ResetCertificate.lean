module

public import P161Formal.ResetRows16To31
public import P161Formal.ResetRows32To47
public import P161Formal.ResetRows48To63
public import P161Formal.ResetRows64To79
public import P161Formal.ResetRows80To95
public import P161Formal.ResetRows96To111
public import P161Formal.ResetRows112To127
public import P161Formal.ResetRows128To143
public import P161Formal.ResetRows144To159
public import P161Formal.ResetRows160To175
public import P161Formal.ResetRows176To191
public import P161Formal.ResetRows192To207
public import P161Formal.ResetRows208To223
public import P161Formal.ResetRows224To239
public import P161Formal.ResetRows240To255
public import P161Formal.ResetRows256To271
public import P161Formal.ResetRows272To287
public import P161Formal.ResetRows288To303
public import P161Formal.ResetRows304To319
public import P161Formal.ResetRows320To335
public import P161Formal.ResetRows336To351
public import P161Formal.ResetRows352To367
public import P161Formal.ResetRows368To383
public import P161Formal.ResetRows384To399
public import P161Formal.ResetRows400To415
public import P161Formal.ResetRows416To431
public import P161Formal.ResetRows432To447
public import P161Formal.ResetRows448To463
public import P161Formal.ResetRows464To479
public import P161Formal.ResetRows480To495
public import P161Formal.ResetRows496To511
public import P161Formal.ResetRows512To527
public import P161Formal.ResetRows528To543
public import P161Formal.ResetRows544To559
public import P161Formal.ResetRows560To575
public import P161Formal.ResetRows576To591
public import P161Formal.ResetRows592To607
public import P161Formal.ResetRows608To623
public import P161Formal.ResetRows624To639
public import P161Formal.ResetRows640To655
public import P161Formal.ResetRows656To671
public import P161Formal.ResetRows672To687
public import P161Formal.ResetRows688To703
public import P161Formal.ResetRows704To719
public import P161Formal.ResetRows720To735
public import P161Formal.ResetRows736To751
public import P161Formal.ResetRows752To767
public import P161Formal.ResetRows768To783
public import P161Formal.ResetRows784To799
public import P161Formal.ResetRows800To815
public import P161Formal.ResetRows816To831
public import P161Formal.ResetRows832To847
public import P161Formal.ResetRows848To863
public import P161Formal.ResetRows864To879
public import P161Formal.ResetRows880To895
public import P161Formal.ResetRows896To911
public import P161Formal.ResetRows912To927
public import P161Formal.ResetRows928To943
public import P161Formal.ResetRows944To959
public import P161Formal.ResetRows960To975
public import P161Formal.ResetRows976To991
public import P161Formal.ResetRows992To1007
public import P161Formal.ResetRows1008To1023
public import P161Formal.ResetRows1024To1039
public import P161Formal.ResetRows1040To1055
public import P161Formal.ResetRows1056To1071
public import P161Formal.ResetRows1072To1087
public import P161Formal.ResetRows1088To1103
public import P161Formal.ResetRows1104To1119
public import P161Formal.ResetRows1120To1135
public import P161Formal.ResetRows1136To1151
public import P161Formal.ResetRows1152To1167
public import P161Formal.ResetRows1168To1183
public import P161Formal.ResetRows1184To1199
public import P161Formal.ResetRows1200To1215
public import P161Formal.ResetRows1216To1231
public import P161Formal.ResetRows1232To1247
public import P161Formal.ResetRows1248To1263
public import P161Formal.ResetRows1264To1279
public import P161Formal.ResetRows1280To1295
public import P161Formal.ResetRows1296To1311
public import P161Formal.ResetRows1312To1327
public import P161Formal.ResetRows1328To1343
public import P161Formal.ResetRows1344To1359
public import P161Formal.ResetRows1360To1375
public import P161Formal.ResetRows1376To1391
public import P161Formal.ResetRows1392To1407
public import P161Formal.ResetRows1408To1423
public import P161Formal.ResetRows1424To1439
public import P161Formal.ResetRows1440To1455
public import P161Formal.ResetRows1456To1471
public import P161Formal.ResetRows1472To1487
public import P161Formal.ResetRows1488To1503
public import P161Formal.ResetRows1504To1519
public import P161Formal.ResetRows1520To1535
public import P161Formal.ResetRows1536To1551
public import P161Formal.ResetRows1552To1567
public import P161Formal.ResetRows1568To1583
public import P161Formal.ResetRows1584To1599
public import P161Formal.ResetRows1600To1615
public import P161Formal.ResetRows1616To1631
public import P161Formal.ResetRows1632To1647
public import P161Formal.ResetRows1648To1663
public import P161Formal.ResetRows1664To1679
public import P161Formal.ResetRows1680To1695
public import P161Formal.ResetRows1696To1711
public import P161Formal.ResetRows1712To1727
public import P161Formal.ResetRows1728To1743
public import P161Formal.ResetRows1744To1759
public import P161Formal.ResetRows1760To1775
public import P161Formal.ResetRows1776To1791
public import P161Formal.ResetRows1792To1807
public import P161Formal.ResetRows1808To1823
public import P161Formal.ResetRows1824To1839
public import P161Formal.ResetRows1840To1855
public import P161Formal.ResetRows1856To1871
public import P161Formal.ResetRows1872To1887
public import P161Formal.ResetRows1888To1903
public import P161Formal.ResetRows1904To1919
public import P161Formal.ResetRows1920To1935
public import P161Formal.ResetRows1936To1951
public import P161Formal.ResetRows1952To1967
public import P161Formal.ResetRows1968To1983
public import P161Formal.ResetRows1984To1999
public import P161Formal.ResetRows2000To2015
public import P161Formal.ResetRows2016To2031
public import P161Formal.ResetRows2032To2047
public import P161Formal.ResetRows2048To2048

/-! Complete C11 residual certificate, composed from source-bound finite blocks.
This is not the physical reset-operator bridge or the full P161 mission. -/

@[expose] public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

def allResetParents : List ℕ :=
  resetParents16To31 ++ resetParents32To47 ++ resetParents48To63 ++ resetParents64To79 ++ resetParents80To95 ++ resetParents96To111 ++ resetParents112To127 ++ resetParents128To143 ++ resetParents144To159 ++ resetParents160To175 ++ resetParents176To191 ++ resetParents192To207 ++ resetParents208To223 ++ resetParents224To239 ++ resetParents240To255 ++ resetParents256To271 ++ resetParents272To287 ++ resetParents288To303 ++ resetParents304To319 ++ resetParents320To335 ++ resetParents336To351 ++ resetParents352To367 ++ resetParents368To383 ++ resetParents384To399 ++ resetParents400To415 ++ resetParents416To431 ++ resetParents432To447 ++ resetParents448To463 ++ resetParents464To479 ++ resetParents480To495 ++ resetParents496To511 ++ resetParents512To527 ++ resetParents528To543 ++ resetParents544To559 ++ resetParents560To575 ++ resetParents576To591 ++ resetParents592To607 ++ resetParents608To623 ++ resetParents624To639 ++ resetParents640To655 ++ resetParents656To671 ++ resetParents672To687 ++ resetParents688To703 ++ resetParents704To719 ++ resetParents720To735 ++ resetParents736To751 ++ resetParents752To767 ++ resetParents768To783 ++ resetParents784To799 ++ resetParents800To815 ++ resetParents816To831 ++ resetParents832To847 ++ resetParents848To863 ++ resetParents864To879 ++ resetParents880To895 ++ resetParents896To911 ++ resetParents912To927 ++ resetParents928To943 ++ resetParents944To959 ++ resetParents960To975 ++ resetParents976To991 ++ resetParents992To1007 ++ resetParents1008To1023 ++ resetParents1024To1039 ++ resetParents1040To1055 ++ resetParents1056To1071 ++ resetParents1072To1087 ++ resetParents1088To1103 ++ resetParents1104To1119 ++ resetParents1120To1135 ++ resetParents1136To1151 ++ resetParents1152To1167 ++ resetParents1168To1183 ++ resetParents1184To1199 ++ resetParents1200To1215 ++ resetParents1216To1231 ++ resetParents1232To1247 ++ resetParents1248To1263 ++ resetParents1264To1279 ++ resetParents1280To1295 ++ resetParents1296To1311 ++ resetParents1312To1327 ++ resetParents1328To1343 ++ resetParents1344To1359 ++ resetParents1360To1375 ++ resetParents1376To1391 ++ resetParents1392To1407 ++ resetParents1408To1423 ++ resetParents1424To1439 ++ resetParents1440To1455 ++ resetParents1456To1471 ++ resetParents1472To1487 ++ resetParents1488To1503 ++ resetParents1504To1519 ++ resetParents1520To1535 ++ resetParents1536To1551 ++ resetParents1552To1567 ++ resetParents1568To1583 ++ resetParents1584To1599 ++ resetParents1600To1615 ++ resetParents1616To1631 ++ resetParents1632To1647 ++ resetParents1648To1663 ++ resetParents1664To1679 ++ resetParents1680To1695 ++ resetParents1696To1711 ++ resetParents1712To1727 ++ resetParents1728To1743 ++ resetParents1744To1759 ++ resetParents1760To1775 ++ resetParents1776To1791 ++ resetParents1792To1807 ++ resetParents1808To1823 ++ resetParents1824To1839 ++ resetParents1840To1855 ++ resetParents1856To1871 ++ resetParents1872To1887 ++ resetParents1888To1903 ++ resetParents1904To1919 ++ resetParents1920To1935 ++ resetParents1936To1951 ++ resetParents1952To1967 ++ resetParents1968To1983 ++ resetParents1984To1999 ++ resetParents2000To2015 ++ resetParents2016To2031 ++ resetParents2032To2047 ++ resetParents2048To2048

theorem reset_parents_coverage : allResetParents =
    (List.range 2033).map (fun i => 16 + i) := by decide

theorem all_reset_parents_checked : allResetParents.all resetParentTest = true := by
  simp only [allResetParents, List.all_append, reset_block_16_to_31, reset_block_32_to_47, reset_block_48_to_63, reset_block_64_to_79, reset_block_80_to_95, reset_block_96_to_111, reset_block_112_to_127, reset_block_128_to_143, reset_block_144_to_159, reset_block_160_to_175, reset_block_176_to_191, reset_block_192_to_207, reset_block_208_to_223, reset_block_224_to_239, reset_block_240_to_255, reset_block_256_to_271, reset_block_272_to_287, reset_block_288_to_303, reset_block_304_to_319, reset_block_320_to_335, reset_block_336_to_351, reset_block_352_to_367, reset_block_368_to_383, reset_block_384_to_399, reset_block_400_to_415, reset_block_416_to_431, reset_block_432_to_447, reset_block_448_to_463, reset_block_464_to_479, reset_block_480_to_495, reset_block_496_to_511, reset_block_512_to_527, reset_block_528_to_543, reset_block_544_to_559, reset_block_560_to_575, reset_block_576_to_591, reset_block_592_to_607, reset_block_608_to_623, reset_block_624_to_639, reset_block_640_to_655, reset_block_656_to_671, reset_block_672_to_687, reset_block_688_to_703, reset_block_704_to_719, reset_block_720_to_735, reset_block_736_to_751, reset_block_752_to_767, reset_block_768_to_783, reset_block_784_to_799, reset_block_800_to_815, reset_block_816_to_831, reset_block_832_to_847, reset_block_848_to_863, reset_block_864_to_879, reset_block_880_to_895, reset_block_896_to_911, reset_block_912_to_927, reset_block_928_to_943, reset_block_944_to_959, reset_block_960_to_975, reset_block_976_to_991, reset_block_992_to_1007, reset_block_1008_to_1023, reset_block_1024_to_1039, reset_block_1040_to_1055, reset_block_1056_to_1071, reset_block_1072_to_1087, reset_block_1088_to_1103, reset_block_1104_to_1119, reset_block_1120_to_1135, reset_block_1136_to_1151, reset_block_1152_to_1167, reset_block_1168_to_1183, reset_block_1184_to_1199, reset_block_1200_to_1215, reset_block_1216_to_1231, reset_block_1232_to_1247, reset_block_1248_to_1263, reset_block_1264_to_1279, reset_block_1280_to_1295, reset_block_1296_to_1311, reset_block_1312_to_1327, reset_block_1328_to_1343, reset_block_1344_to_1359, reset_block_1360_to_1375, reset_block_1376_to_1391, reset_block_1392_to_1407, reset_block_1408_to_1423, reset_block_1424_to_1439, reset_block_1440_to_1455, reset_block_1456_to_1471, reset_block_1472_to_1487, reset_block_1488_to_1503, reset_block_1504_to_1519, reset_block_1520_to_1535, reset_block_1536_to_1551, reset_block_1552_to_1567, reset_block_1568_to_1583, reset_block_1584_to_1599, reset_block_1600_to_1615, reset_block_1616_to_1631, reset_block_1632_to_1647, reset_block_1648_to_1663, reset_block_1664_to_1679, reset_block_1680_to_1695, reset_block_1696_to_1711, reset_block_1712_to_1727, reset_block_1728_to_1743, reset_block_1744_to_1759, reset_block_1760_to_1775, reset_block_1776_to_1791, reset_block_1792_to_1807, reset_block_1808_to_1823, reset_block_1824_to_1839, reset_block_1840_to_1855, reset_block_1856_to_1871, reset_block_1872_to_1887, reset_block_1888_to_1903, reset_block_1904_to_1919, reset_block_1920_to_1935, reset_block_1936_to_1951, reset_block_1952_to_1967, reset_block_1968_to_1983, reset_block_1984_to_1999, reset_block_2000_to_2015, reset_block_2016_to_2031, reset_block_2032_to_2047, reset_block_2048_to_2048, Bool.true_and]

theorem all_global_reset_rows (a : ℕ) (fuel : Bool) (ha : 16 ≤ a) (hb : a ≤ 2048) :
    checkGlobalResetRow a fuel = true := by
  have hp := covered_parent_checked allResetParents 16 2033 a
    reset_parents_coverage all_reset_parents_checked ha (by omega)
  have h := parent_test_global a hp
  cases fuel
  · exact h.1
  · exact h.2

theorem all_deficient_reset_rows (a : ℕ) (fuel : Bool) (ha : 16 ≤ a) (hb : a < 512) :
    checkDeficientResetRow a fuel = true := by
  have hp := covered_parent_checked allResetParents 16 2033 a
    reset_parents_coverage all_reset_parents_checked ha (by omega)
  have h := parent_test_deficient a hb hp
  cases fuel
  · exact h.1
  · exact h.2

end P161Formal
