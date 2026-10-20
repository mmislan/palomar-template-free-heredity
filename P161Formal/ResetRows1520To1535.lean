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

theorem reset_cert_a_1520 : resetParentTest 1520 = true := by
  decide

theorem reset_cert_a_1521 : resetParentTest 1521 = true := by
  decide

theorem reset_cert_a_1522 : resetParentTest 1522 = true := by
  decide

theorem reset_cert_a_1523 : resetParentTest 1523 = true := by
  decide

theorem reset_cert_a_1524 : resetParentTest 1524 = true := by
  decide

theorem reset_cert_a_1525 : resetParentTest 1525 = true := by
  decide

theorem reset_cert_a_1526 : resetParentTest 1526 = true := by
  decide

theorem reset_cert_a_1527 : resetParentTest 1527 = true := by
  decide

theorem reset_cert_a_1528 : resetParentTest 1528 = true := by
  decide

theorem reset_cert_a_1529 : resetParentTest 1529 = true := by
  decide

theorem reset_cert_a_1530 : resetParentTest 1530 = true := by
  decide

theorem reset_cert_a_1531 : resetParentTest 1531 = true := by
  decide

theorem reset_cert_a_1532 : resetParentTest 1532 = true := by
  decide

theorem reset_cert_a_1533 : resetParentTest 1533 = true := by
  decide

theorem reset_cert_a_1534 : resetParentTest 1534 = true := by
  decide

theorem reset_cert_a_1535 : resetParentTest 1535 = true := by
  decide

def resetParents1520To1535 : List ℕ := [1520, 1521, 1522, 1523, 1524, 1525, 1526, 1527, 1528, 1529, 1530, 1531, 1532, 1533, 1534, 1535]

theorem reset_block_1520_to_1535 : resetParents1520To1535.all resetParentTest = true := by
  simp only [resetParents1520To1535, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1520, ⟨reset_cert_a_1521, ⟨reset_cert_a_1522, ⟨reset_cert_a_1523, ⟨reset_cert_a_1524, ⟨reset_cert_a_1525, ⟨reset_cert_a_1526, ⟨reset_cert_a_1527, ⟨reset_cert_a_1528, ⟨reset_cert_a_1529, ⟨reset_cert_a_1530, ⟨reset_cert_a_1531, ⟨reset_cert_a_1532, ⟨reset_cert_a_1533, ⟨reset_cert_a_1534, reset_cert_a_1535⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
