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

theorem reset_cert_a_1536 : resetParentTest 1536 = true := by
  decide

theorem reset_cert_a_1537 : resetParentTest 1537 = true := by
  decide

theorem reset_cert_a_1538 : resetParentTest 1538 = true := by
  decide

theorem reset_cert_a_1539 : resetParentTest 1539 = true := by
  decide

theorem reset_cert_a_1540 : resetParentTest 1540 = true := by
  decide

theorem reset_cert_a_1541 : resetParentTest 1541 = true := by
  decide

theorem reset_cert_a_1542 : resetParentTest 1542 = true := by
  decide

theorem reset_cert_a_1543 : resetParentTest 1543 = true := by
  decide

theorem reset_cert_a_1544 : resetParentTest 1544 = true := by
  decide

theorem reset_cert_a_1545 : resetParentTest 1545 = true := by
  decide

theorem reset_cert_a_1546 : resetParentTest 1546 = true := by
  decide

theorem reset_cert_a_1547 : resetParentTest 1547 = true := by
  decide

theorem reset_cert_a_1548 : resetParentTest 1548 = true := by
  decide

theorem reset_cert_a_1549 : resetParentTest 1549 = true := by
  decide

theorem reset_cert_a_1550 : resetParentTest 1550 = true := by
  decide

theorem reset_cert_a_1551 : resetParentTest 1551 = true := by
  decide

def resetParents1536To1551 : List ℕ := [1536, 1537, 1538, 1539, 1540, 1541, 1542, 1543, 1544, 1545, 1546, 1547, 1548, 1549, 1550, 1551]

theorem reset_block_1536_to_1551 : resetParents1536To1551.all resetParentTest = true := by
  simp only [resetParents1536To1551, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1536, ⟨reset_cert_a_1537, ⟨reset_cert_a_1538, ⟨reset_cert_a_1539, ⟨reset_cert_a_1540, ⟨reset_cert_a_1541, ⟨reset_cert_a_1542, ⟨reset_cert_a_1543, ⟨reset_cert_a_1544, ⟨reset_cert_a_1545, ⟨reset_cert_a_1546, ⟨reset_cert_a_1547, ⟨reset_cert_a_1548, ⟨reset_cert_a_1549, ⟨reset_cert_a_1550, reset_cert_a_1551⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
