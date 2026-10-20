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

theorem reset_cert_a_1376 : resetParentTest 1376 = true := by
  decide

theorem reset_cert_a_1377 : resetParentTest 1377 = true := by
  decide

theorem reset_cert_a_1378 : resetParentTest 1378 = true := by
  decide

theorem reset_cert_a_1379 : resetParentTest 1379 = true := by
  decide

theorem reset_cert_a_1380 : resetParentTest 1380 = true := by
  decide

theorem reset_cert_a_1381 : resetParentTest 1381 = true := by
  decide

theorem reset_cert_a_1382 : resetParentTest 1382 = true := by
  decide

theorem reset_cert_a_1383 : resetParentTest 1383 = true := by
  decide

theorem reset_cert_a_1384 : resetParentTest 1384 = true := by
  decide

theorem reset_cert_a_1385 : resetParentTest 1385 = true := by
  decide

theorem reset_cert_a_1386 : resetParentTest 1386 = true := by
  decide

theorem reset_cert_a_1387 : resetParentTest 1387 = true := by
  decide

theorem reset_cert_a_1388 : resetParentTest 1388 = true := by
  decide

theorem reset_cert_a_1389 : resetParentTest 1389 = true := by
  decide

theorem reset_cert_a_1390 : resetParentTest 1390 = true := by
  decide

theorem reset_cert_a_1391 : resetParentTest 1391 = true := by
  decide

def resetParents1376To1391 : List ℕ := [1376, 1377, 1378, 1379, 1380, 1381, 1382, 1383, 1384, 1385, 1386, 1387, 1388, 1389, 1390, 1391]

theorem reset_block_1376_to_1391 : resetParents1376To1391.all resetParentTest = true := by
  simp only [resetParents1376To1391, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1376, ⟨reset_cert_a_1377, ⟨reset_cert_a_1378, ⟨reset_cert_a_1379, ⟨reset_cert_a_1380, ⟨reset_cert_a_1381, ⟨reset_cert_a_1382, ⟨reset_cert_a_1383, ⟨reset_cert_a_1384, ⟨reset_cert_a_1385, ⟨reset_cert_a_1386, ⟨reset_cert_a_1387, ⟨reset_cert_a_1388, ⟨reset_cert_a_1389, ⟨reset_cert_a_1390, reset_cert_a_1391⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
