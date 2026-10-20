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

theorem reset_cert_a_1344 : resetParentTest 1344 = true := by
  decide

theorem reset_cert_a_1345 : resetParentTest 1345 = true := by
  decide

theorem reset_cert_a_1346 : resetParentTest 1346 = true := by
  decide

theorem reset_cert_a_1347 : resetParentTest 1347 = true := by
  decide

theorem reset_cert_a_1348 : resetParentTest 1348 = true := by
  decide

theorem reset_cert_a_1349 : resetParentTest 1349 = true := by
  decide

theorem reset_cert_a_1350 : resetParentTest 1350 = true := by
  decide

theorem reset_cert_a_1351 : resetParentTest 1351 = true := by
  decide

theorem reset_cert_a_1352 : resetParentTest 1352 = true := by
  decide

theorem reset_cert_a_1353 : resetParentTest 1353 = true := by
  decide

theorem reset_cert_a_1354 : resetParentTest 1354 = true := by
  decide

theorem reset_cert_a_1355 : resetParentTest 1355 = true := by
  decide

theorem reset_cert_a_1356 : resetParentTest 1356 = true := by
  decide

theorem reset_cert_a_1357 : resetParentTest 1357 = true := by
  decide

theorem reset_cert_a_1358 : resetParentTest 1358 = true := by
  decide

theorem reset_cert_a_1359 : resetParentTest 1359 = true := by
  decide

def resetParents1344To1359 : List ℕ := [1344, 1345, 1346, 1347, 1348, 1349, 1350, 1351, 1352, 1353, 1354, 1355, 1356, 1357, 1358, 1359]

theorem reset_block_1344_to_1359 : resetParents1344To1359.all resetParentTest = true := by
  simp only [resetParents1344To1359, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1344, ⟨reset_cert_a_1345, ⟨reset_cert_a_1346, ⟨reset_cert_a_1347, ⟨reset_cert_a_1348, ⟨reset_cert_a_1349, ⟨reset_cert_a_1350, ⟨reset_cert_a_1351, ⟨reset_cert_a_1352, ⟨reset_cert_a_1353, ⟨reset_cert_a_1354, ⟨reset_cert_a_1355, ⟨reset_cert_a_1356, ⟨reset_cert_a_1357, ⟨reset_cert_a_1358, reset_cert_a_1359⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
