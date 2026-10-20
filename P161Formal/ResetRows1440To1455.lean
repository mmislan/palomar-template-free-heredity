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

theorem reset_cert_a_1440 : resetParentTest 1440 = true := by
  decide

theorem reset_cert_a_1441 : resetParentTest 1441 = true := by
  decide

theorem reset_cert_a_1442 : resetParentTest 1442 = true := by
  decide

theorem reset_cert_a_1443 : resetParentTest 1443 = true := by
  decide

theorem reset_cert_a_1444 : resetParentTest 1444 = true := by
  decide

theorem reset_cert_a_1445 : resetParentTest 1445 = true := by
  decide

theorem reset_cert_a_1446 : resetParentTest 1446 = true := by
  decide

theorem reset_cert_a_1447 : resetParentTest 1447 = true := by
  decide

theorem reset_cert_a_1448 : resetParentTest 1448 = true := by
  decide

theorem reset_cert_a_1449 : resetParentTest 1449 = true := by
  decide

theorem reset_cert_a_1450 : resetParentTest 1450 = true := by
  decide

theorem reset_cert_a_1451 : resetParentTest 1451 = true := by
  decide

theorem reset_cert_a_1452 : resetParentTest 1452 = true := by
  decide

theorem reset_cert_a_1453 : resetParentTest 1453 = true := by
  decide

theorem reset_cert_a_1454 : resetParentTest 1454 = true := by
  decide

theorem reset_cert_a_1455 : resetParentTest 1455 = true := by
  decide

def resetParents1440To1455 : List ℕ := [1440, 1441, 1442, 1443, 1444, 1445, 1446, 1447, 1448, 1449, 1450, 1451, 1452, 1453, 1454, 1455]

theorem reset_block_1440_to_1455 : resetParents1440To1455.all resetParentTest = true := by
  simp only [resetParents1440To1455, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1440, ⟨reset_cert_a_1441, ⟨reset_cert_a_1442, ⟨reset_cert_a_1443, ⟨reset_cert_a_1444, ⟨reset_cert_a_1445, ⟨reset_cert_a_1446, ⟨reset_cert_a_1447, ⟨reset_cert_a_1448, ⟨reset_cert_a_1449, ⟨reset_cert_a_1450, ⟨reset_cert_a_1451, ⟨reset_cert_a_1452, ⟨reset_cert_a_1453, ⟨reset_cert_a_1454, reset_cert_a_1455⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
