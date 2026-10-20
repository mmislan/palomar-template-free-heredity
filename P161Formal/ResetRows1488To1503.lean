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

theorem reset_cert_a_1488 : resetParentTest 1488 = true := by
  decide

theorem reset_cert_a_1489 : resetParentTest 1489 = true := by
  decide

theorem reset_cert_a_1490 : resetParentTest 1490 = true := by
  decide

theorem reset_cert_a_1491 : resetParentTest 1491 = true := by
  decide

theorem reset_cert_a_1492 : resetParentTest 1492 = true := by
  decide

theorem reset_cert_a_1493 : resetParentTest 1493 = true := by
  decide

theorem reset_cert_a_1494 : resetParentTest 1494 = true := by
  decide

theorem reset_cert_a_1495 : resetParentTest 1495 = true := by
  decide

theorem reset_cert_a_1496 : resetParentTest 1496 = true := by
  decide

theorem reset_cert_a_1497 : resetParentTest 1497 = true := by
  decide

theorem reset_cert_a_1498 : resetParentTest 1498 = true := by
  decide

theorem reset_cert_a_1499 : resetParentTest 1499 = true := by
  decide

theorem reset_cert_a_1500 : resetParentTest 1500 = true := by
  decide

theorem reset_cert_a_1501 : resetParentTest 1501 = true := by
  decide

theorem reset_cert_a_1502 : resetParentTest 1502 = true := by
  decide

theorem reset_cert_a_1503 : resetParentTest 1503 = true := by
  decide

def resetParents1488To1503 : List ℕ := [1488, 1489, 1490, 1491, 1492, 1493, 1494, 1495, 1496, 1497, 1498, 1499, 1500, 1501, 1502, 1503]

theorem reset_block_1488_to_1503 : resetParents1488To1503.all resetParentTest = true := by
  simp only [resetParents1488To1503, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1488, ⟨reset_cert_a_1489, ⟨reset_cert_a_1490, ⟨reset_cert_a_1491, ⟨reset_cert_a_1492, ⟨reset_cert_a_1493, ⟨reset_cert_a_1494, ⟨reset_cert_a_1495, ⟨reset_cert_a_1496, ⟨reset_cert_a_1497, ⟨reset_cert_a_1498, ⟨reset_cert_a_1499, ⟨reset_cert_a_1500, ⟨reset_cert_a_1501, ⟨reset_cert_a_1502, reset_cert_a_1503⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
