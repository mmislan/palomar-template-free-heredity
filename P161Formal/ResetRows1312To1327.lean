module

public import P161Formal.ResetCertificateInterface
public import P161Formal.ResetPilots
public import P161Formal.ResetSeparatePilot

/-! Exact literal residuals for this finite block. Each new parent is checked
by the ordinary kernel decision procedure. No native evaluator is used. -/

@[expose] public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem reset_cert_a_1312 : resetParentTest 1312 = true := by
  decide

theorem reset_cert_a_1313 : resetParentTest 1313 = true := by
  decide

theorem reset_cert_a_1314 : resetParentTest 1314 = true := by
  decide

theorem reset_cert_a_1315 : resetParentTest 1315 = true := by
  decide

theorem reset_cert_a_1316 : resetParentTest 1316 = true := by
  decide

theorem reset_cert_a_1317 : resetParentTest 1317 = true := by
  decide

theorem reset_cert_a_1318 : resetParentTest 1318 = true := by
  decide

theorem reset_cert_a_1319 : resetParentTest 1319 = true := by
  decide

theorem reset_cert_a_1320 : resetParentTest 1320 = true := by
  decide

theorem reset_cert_a_1321 : resetParentTest 1321 = true := by
  decide

theorem reset_cert_a_1322 : resetParentTest 1322 = true := by
  decide

theorem reset_cert_a_1323 : resetParentTest 1323 = true := by
  decide

theorem reset_cert_a_1324 : resetParentTest 1324 = true := by
  decide

theorem reset_cert_a_1325 : resetParentTest 1325 = true := by
  decide

theorem reset_cert_a_1326 : resetParentTest 1326 = true := by
  decide

theorem reset_cert_a_1327 : resetParentTest 1327 = true := by
  decide

def resetParents1312To1327 : List ℕ := [1312, 1313, 1314, 1315, 1316, 1317, 1318, 1319, 1320, 1321, 1322, 1323, 1324, 1325, 1326, 1327]

theorem reset_block_1312_to_1327 : resetParents1312To1327.all resetParentTest = true := by
  simp only [resetParents1312To1327, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1312, ⟨reset_cert_a_1313, ⟨reset_cert_a_1314, ⟨reset_cert_a_1315, ⟨reset_cert_a_1316, ⟨reset_cert_a_1317, ⟨reset_cert_a_1318, ⟨reset_cert_a_1319, ⟨reset_cert_a_1320, ⟨reset_cert_a_1321, ⟨reset_cert_a_1322, ⟨reset_cert_a_1323, ⟨reset_cert_a_1324, ⟨reset_cert_a_1325, ⟨reset_cert_a_1326, reset_cert_a_1327⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
