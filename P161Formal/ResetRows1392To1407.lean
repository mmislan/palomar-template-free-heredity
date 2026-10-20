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

theorem reset_cert_a_1392 : resetParentTest 1392 = true := by
  decide

theorem reset_cert_a_1393 : resetParentTest 1393 = true := by
  decide

theorem reset_cert_a_1394 : resetParentTest 1394 = true := by
  decide

theorem reset_cert_a_1395 : resetParentTest 1395 = true := by
  decide

theorem reset_cert_a_1396 : resetParentTest 1396 = true := by
  decide

theorem reset_cert_a_1397 : resetParentTest 1397 = true := by
  decide

theorem reset_cert_a_1398 : resetParentTest 1398 = true := by
  decide

theorem reset_cert_a_1399 : resetParentTest 1399 = true := by
  decide

theorem reset_cert_a_1400 : resetParentTest 1400 = true := by
  decide

theorem reset_cert_a_1401 : resetParentTest 1401 = true := by
  decide

theorem reset_cert_a_1402 : resetParentTest 1402 = true := by
  decide

theorem reset_cert_a_1403 : resetParentTest 1403 = true := by
  decide

theorem reset_cert_a_1404 : resetParentTest 1404 = true := by
  decide

theorem reset_cert_a_1405 : resetParentTest 1405 = true := by
  decide

theorem reset_cert_a_1406 : resetParentTest 1406 = true := by
  decide

theorem reset_cert_a_1407 : resetParentTest 1407 = true := by
  decide

def resetParents1392To1407 : List ℕ := [1392, 1393, 1394, 1395, 1396, 1397, 1398, 1399, 1400, 1401, 1402, 1403, 1404, 1405, 1406, 1407]

theorem reset_block_1392_to_1407 : resetParents1392To1407.all resetParentTest = true := by
  simp only [resetParents1392To1407, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1392, ⟨reset_cert_a_1393, ⟨reset_cert_a_1394, ⟨reset_cert_a_1395, ⟨reset_cert_a_1396, ⟨reset_cert_a_1397, ⟨reset_cert_a_1398, ⟨reset_cert_a_1399, ⟨reset_cert_a_1400, ⟨reset_cert_a_1401, ⟨reset_cert_a_1402, ⟨reset_cert_a_1403, ⟨reset_cert_a_1404, ⟨reset_cert_a_1405, ⟨reset_cert_a_1406, reset_cert_a_1407⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
