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

theorem reset_cert_a_1552 : resetParentTest 1552 = true := by
  decide

theorem reset_cert_a_1553 : resetParentTest 1553 = true := by
  decide

theorem reset_cert_a_1554 : resetParentTest 1554 = true := by
  decide

theorem reset_cert_a_1555 : resetParentTest 1555 = true := by
  decide

theorem reset_cert_a_1556 : resetParentTest 1556 = true := by
  decide

theorem reset_cert_a_1557 : resetParentTest 1557 = true := by
  decide

theorem reset_cert_a_1558 : resetParentTest 1558 = true := by
  decide

theorem reset_cert_a_1559 : resetParentTest 1559 = true := by
  decide

theorem reset_cert_a_1560 : resetParentTest 1560 = true := by
  decide

theorem reset_cert_a_1561 : resetParentTest 1561 = true := by
  decide

theorem reset_cert_a_1562 : resetParentTest 1562 = true := by
  decide

theorem reset_cert_a_1563 : resetParentTest 1563 = true := by
  decide

theorem reset_cert_a_1564 : resetParentTest 1564 = true := by
  decide

theorem reset_cert_a_1565 : resetParentTest 1565 = true := by
  decide

theorem reset_cert_a_1566 : resetParentTest 1566 = true := by
  decide

theorem reset_cert_a_1567 : resetParentTest 1567 = true := by
  decide

def resetParents1552To1567 : List ℕ := [1552, 1553, 1554, 1555, 1556, 1557, 1558, 1559, 1560, 1561, 1562, 1563, 1564, 1565, 1566, 1567]

theorem reset_block_1552_to_1567 : resetParents1552To1567.all resetParentTest = true := by
  simp only [resetParents1552To1567, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1552, ⟨reset_cert_a_1553, ⟨reset_cert_a_1554, ⟨reset_cert_a_1555, ⟨reset_cert_a_1556, ⟨reset_cert_a_1557, ⟨reset_cert_a_1558, ⟨reset_cert_a_1559, ⟨reset_cert_a_1560, ⟨reset_cert_a_1561, ⟨reset_cert_a_1562, ⟨reset_cert_a_1563, ⟨reset_cert_a_1564, ⟨reset_cert_a_1565, ⟨reset_cert_a_1566, reset_cert_a_1567⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
