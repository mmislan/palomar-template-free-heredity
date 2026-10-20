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

theorem reset_cert_a_1456 : resetParentTest 1456 = true := by
  decide

theorem reset_cert_a_1457 : resetParentTest 1457 = true := by
  decide

theorem reset_cert_a_1458 : resetParentTest 1458 = true := by
  decide

theorem reset_cert_a_1459 : resetParentTest 1459 = true := by
  decide

theorem reset_cert_a_1460 : resetParentTest 1460 = true := by
  decide

theorem reset_cert_a_1461 : resetParentTest 1461 = true := by
  decide

theorem reset_cert_a_1462 : resetParentTest 1462 = true := by
  decide

theorem reset_cert_a_1463 : resetParentTest 1463 = true := by
  decide

theorem reset_cert_a_1464 : resetParentTest 1464 = true := by
  decide

theorem reset_cert_a_1465 : resetParentTest 1465 = true := by
  decide

theorem reset_cert_a_1466 : resetParentTest 1466 = true := by
  decide

theorem reset_cert_a_1467 : resetParentTest 1467 = true := by
  decide

theorem reset_cert_a_1468 : resetParentTest 1468 = true := by
  decide

theorem reset_cert_a_1469 : resetParentTest 1469 = true := by
  decide

theorem reset_cert_a_1470 : resetParentTest 1470 = true := by
  decide

theorem reset_cert_a_1471 : resetParentTest 1471 = true := by
  decide

def resetParents1456To1471 : List ℕ := [1456, 1457, 1458, 1459, 1460, 1461, 1462, 1463, 1464, 1465, 1466, 1467, 1468, 1469, 1470, 1471]

theorem reset_block_1456_to_1471 : resetParents1456To1471.all resetParentTest = true := by
  simp only [resetParents1456To1471, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1456, ⟨reset_cert_a_1457, ⟨reset_cert_a_1458, ⟨reset_cert_a_1459, ⟨reset_cert_a_1460, ⟨reset_cert_a_1461, ⟨reset_cert_a_1462, ⟨reset_cert_a_1463, ⟨reset_cert_a_1464, ⟨reset_cert_a_1465, ⟨reset_cert_a_1466, ⟨reset_cert_a_1467, ⟨reset_cert_a_1468, ⟨reset_cert_a_1469, ⟨reset_cert_a_1470, reset_cert_a_1471⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
