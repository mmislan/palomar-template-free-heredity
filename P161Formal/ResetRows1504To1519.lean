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

theorem reset_cert_a_1504 : resetParentTest 1504 = true := by
  decide

theorem reset_cert_a_1505 : resetParentTest 1505 = true := by
  decide

theorem reset_cert_a_1506 : resetParentTest 1506 = true := by
  decide

theorem reset_cert_a_1507 : resetParentTest 1507 = true := by
  decide

theorem reset_cert_a_1508 : resetParentTest 1508 = true := by
  decide

theorem reset_cert_a_1509 : resetParentTest 1509 = true := by
  decide

theorem reset_cert_a_1510 : resetParentTest 1510 = true := by
  decide

theorem reset_cert_a_1511 : resetParentTest 1511 = true := by
  decide

theorem reset_cert_a_1512 : resetParentTest 1512 = true := by
  decide

theorem reset_cert_a_1513 : resetParentTest 1513 = true := by
  decide

theorem reset_cert_a_1514 : resetParentTest 1514 = true := by
  decide

theorem reset_cert_a_1515 : resetParentTest 1515 = true := by
  decide

theorem reset_cert_a_1516 : resetParentTest 1516 = true := by
  decide

theorem reset_cert_a_1517 : resetParentTest 1517 = true := by
  decide

theorem reset_cert_a_1518 : resetParentTest 1518 = true := by
  decide

theorem reset_cert_a_1519 : resetParentTest 1519 = true := by
  decide

def resetParents1504To1519 : List ℕ := [1504, 1505, 1506, 1507, 1508, 1509, 1510, 1511, 1512, 1513, 1514, 1515, 1516, 1517, 1518, 1519]

theorem reset_block_1504_to_1519 : resetParents1504To1519.all resetParentTest = true := by
  simp only [resetParents1504To1519, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1504, ⟨reset_cert_a_1505, ⟨reset_cert_a_1506, ⟨reset_cert_a_1507, ⟨reset_cert_a_1508, ⟨reset_cert_a_1509, ⟨reset_cert_a_1510, ⟨reset_cert_a_1511, ⟨reset_cert_a_1512, ⟨reset_cert_a_1513, ⟨reset_cert_a_1514, ⟨reset_cert_a_1515, ⟨reset_cert_a_1516, ⟨reset_cert_a_1517, ⟨reset_cert_a_1518, reset_cert_a_1519⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
