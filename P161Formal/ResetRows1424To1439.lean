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

theorem reset_cert_a_1424 : resetParentTest 1424 = true := by
  decide

theorem reset_cert_a_1425 : resetParentTest 1425 = true := by
  decide

theorem reset_cert_a_1426 : resetParentTest 1426 = true := by
  decide

theorem reset_cert_a_1427 : resetParentTest 1427 = true := by
  decide

theorem reset_cert_a_1428 : resetParentTest 1428 = true := by
  decide

theorem reset_cert_a_1429 : resetParentTest 1429 = true := by
  decide

theorem reset_cert_a_1430 : resetParentTest 1430 = true := by
  decide

theorem reset_cert_a_1431 : resetParentTest 1431 = true := by
  decide

theorem reset_cert_a_1432 : resetParentTest 1432 = true := by
  decide

theorem reset_cert_a_1433 : resetParentTest 1433 = true := by
  decide

theorem reset_cert_a_1434 : resetParentTest 1434 = true := by
  decide

theorem reset_cert_a_1435 : resetParentTest 1435 = true := by
  decide

theorem reset_cert_a_1436 : resetParentTest 1436 = true := by
  decide

theorem reset_cert_a_1437 : resetParentTest 1437 = true := by
  decide

theorem reset_cert_a_1438 : resetParentTest 1438 = true := by
  decide

theorem reset_cert_a_1439 : resetParentTest 1439 = true := by
  decide

def resetParents1424To1439 : List ℕ := [1424, 1425, 1426, 1427, 1428, 1429, 1430, 1431, 1432, 1433, 1434, 1435, 1436, 1437, 1438, 1439]

theorem reset_block_1424_to_1439 : resetParents1424To1439.all resetParentTest = true := by
  simp only [resetParents1424To1439, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1424, ⟨reset_cert_a_1425, ⟨reset_cert_a_1426, ⟨reset_cert_a_1427, ⟨reset_cert_a_1428, ⟨reset_cert_a_1429, ⟨reset_cert_a_1430, ⟨reset_cert_a_1431, ⟨reset_cert_a_1432, ⟨reset_cert_a_1433, ⟨reset_cert_a_1434, ⟨reset_cert_a_1435, ⟨reset_cert_a_1436, ⟨reset_cert_a_1437, ⟨reset_cert_a_1438, reset_cert_a_1439⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
