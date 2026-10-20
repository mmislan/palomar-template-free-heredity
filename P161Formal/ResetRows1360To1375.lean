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

theorem reset_cert_a_1360 : resetParentTest 1360 = true := by
  decide

theorem reset_cert_a_1361 : resetParentTest 1361 = true := by
  decide

theorem reset_cert_a_1362 : resetParentTest 1362 = true := by
  decide

theorem reset_cert_a_1363 : resetParentTest 1363 = true := by
  decide

theorem reset_cert_a_1364 : resetParentTest 1364 = true := by
  decide

theorem reset_cert_a_1365 : resetParentTest 1365 = true := by
  decide

theorem reset_cert_a_1366 : resetParentTest 1366 = true := by
  decide

theorem reset_cert_a_1367 : resetParentTest 1367 = true := by
  decide

theorem reset_cert_a_1368 : resetParentTest 1368 = true := by
  decide

theorem reset_cert_a_1369 : resetParentTest 1369 = true := by
  decide

theorem reset_cert_a_1370 : resetParentTest 1370 = true := by
  decide

theorem reset_cert_a_1371 : resetParentTest 1371 = true := by
  decide

theorem reset_cert_a_1372 : resetParentTest 1372 = true := by
  decide

theorem reset_cert_a_1373 : resetParentTest 1373 = true := by
  decide

theorem reset_cert_a_1374 : resetParentTest 1374 = true := by
  decide

theorem reset_cert_a_1375 : resetParentTest 1375 = true := by
  decide

def resetParents1360To1375 : List ℕ := [1360, 1361, 1362, 1363, 1364, 1365, 1366, 1367, 1368, 1369, 1370, 1371, 1372, 1373, 1374, 1375]

theorem reset_block_1360_to_1375 : resetParents1360To1375.all resetParentTest = true := by
  simp only [resetParents1360To1375, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1360, ⟨reset_cert_a_1361, ⟨reset_cert_a_1362, ⟨reset_cert_a_1363, ⟨reset_cert_a_1364, ⟨reset_cert_a_1365, ⟨reset_cert_a_1366, ⟨reset_cert_a_1367, ⟨reset_cert_a_1368, ⟨reset_cert_a_1369, ⟨reset_cert_a_1370, ⟨reset_cert_a_1371, ⟨reset_cert_a_1372, ⟨reset_cert_a_1373, ⟨reset_cert_a_1374, reset_cert_a_1375⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
