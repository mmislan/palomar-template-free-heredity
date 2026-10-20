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

theorem reset_cert_a_1472 : resetParentTest 1472 = true := by
  decide

theorem reset_cert_a_1473 : resetParentTest 1473 = true := by
  decide

theorem reset_cert_a_1474 : resetParentTest 1474 = true := by
  decide

theorem reset_cert_a_1475 : resetParentTest 1475 = true := by
  decide

theorem reset_cert_a_1476 : resetParentTest 1476 = true := by
  decide

theorem reset_cert_a_1477 : resetParentTest 1477 = true := by
  decide

theorem reset_cert_a_1478 : resetParentTest 1478 = true := by
  decide

theorem reset_cert_a_1479 : resetParentTest 1479 = true := by
  decide

theorem reset_cert_a_1480 : resetParentTest 1480 = true := by
  decide

theorem reset_cert_a_1481 : resetParentTest 1481 = true := by
  decide

theorem reset_cert_a_1482 : resetParentTest 1482 = true := by
  decide

theorem reset_cert_a_1483 : resetParentTest 1483 = true := by
  decide

theorem reset_cert_a_1484 : resetParentTest 1484 = true := by
  decide

theorem reset_cert_a_1485 : resetParentTest 1485 = true := by
  decide

theorem reset_cert_a_1486 : resetParentTest 1486 = true := by
  decide

theorem reset_cert_a_1487 : resetParentTest 1487 = true := by
  decide

def resetParents1472To1487 : List ℕ := [1472, 1473, 1474, 1475, 1476, 1477, 1478, 1479, 1480, 1481, 1482, 1483, 1484, 1485, 1486, 1487]

theorem reset_block_1472_to_1487 : resetParents1472To1487.all resetParentTest = true := by
  simp only [resetParents1472To1487, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1472, ⟨reset_cert_a_1473, ⟨reset_cert_a_1474, ⟨reset_cert_a_1475, ⟨reset_cert_a_1476, ⟨reset_cert_a_1477, ⟨reset_cert_a_1478, ⟨reset_cert_a_1479, ⟨reset_cert_a_1480, ⟨reset_cert_a_1481, ⟨reset_cert_a_1482, ⟨reset_cert_a_1483, ⟨reset_cert_a_1484, ⟨reset_cert_a_1485, ⟨reset_cert_a_1486, reset_cert_a_1487⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
