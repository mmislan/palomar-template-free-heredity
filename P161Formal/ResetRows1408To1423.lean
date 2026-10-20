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

theorem reset_cert_a_1408 : resetParentTest 1408 = true := by
  decide

theorem reset_cert_a_1409 : resetParentTest 1409 = true := by
  decide

theorem reset_cert_a_1410 : resetParentTest 1410 = true := by
  decide

theorem reset_cert_a_1411 : resetParentTest 1411 = true := by
  decide

theorem reset_cert_a_1412 : resetParentTest 1412 = true := by
  decide

theorem reset_cert_a_1413 : resetParentTest 1413 = true := by
  decide

theorem reset_cert_a_1414 : resetParentTest 1414 = true := by
  decide

theorem reset_cert_a_1415 : resetParentTest 1415 = true := by
  decide

theorem reset_cert_a_1416 : resetParentTest 1416 = true := by
  decide

theorem reset_cert_a_1417 : resetParentTest 1417 = true := by
  decide

theorem reset_cert_a_1418 : resetParentTest 1418 = true := by
  decide

theorem reset_cert_a_1419 : resetParentTest 1419 = true := by
  decide

theorem reset_cert_a_1420 : resetParentTest 1420 = true := by
  decide

theorem reset_cert_a_1421 : resetParentTest 1421 = true := by
  decide

theorem reset_cert_a_1422 : resetParentTest 1422 = true := by
  decide

theorem reset_cert_a_1423 : resetParentTest 1423 = true := by
  decide

def resetParents1408To1423 : List ℕ := [1408, 1409, 1410, 1411, 1412, 1413, 1414, 1415, 1416, 1417, 1418, 1419, 1420, 1421, 1422, 1423]

theorem reset_block_1408_to_1423 : resetParents1408To1423.all resetParentTest = true := by
  simp only [resetParents1408To1423, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1408, ⟨reset_cert_a_1409, ⟨reset_cert_a_1410, ⟨reset_cert_a_1411, ⟨reset_cert_a_1412, ⟨reset_cert_a_1413, ⟨reset_cert_a_1414, ⟨reset_cert_a_1415, ⟨reset_cert_a_1416, ⟨reset_cert_a_1417, ⟨reset_cert_a_1418, ⟨reset_cert_a_1419, ⟨reset_cert_a_1420, ⟨reset_cert_a_1421, ⟨reset_cert_a_1422, reset_cert_a_1423⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
