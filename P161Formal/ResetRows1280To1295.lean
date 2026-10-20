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

theorem reset_cert_a_1280 : resetParentTest 1280 = true := by
  decide

theorem reset_cert_a_1281 : resetParentTest 1281 = true := by
  decide

theorem reset_cert_a_1282 : resetParentTest 1282 = true := by
  decide

theorem reset_cert_a_1283 : resetParentTest 1283 = true := by
  decide

theorem reset_cert_a_1284 : resetParentTest 1284 = true := by
  decide

theorem reset_cert_a_1285 : resetParentTest 1285 = true := by
  decide

theorem reset_cert_a_1286 : resetParentTest 1286 = true := by
  decide

theorem reset_cert_a_1287 : resetParentTest 1287 = true := by
  decide

theorem reset_cert_a_1288 : resetParentTest 1288 = true := by
  decide

theorem reset_cert_a_1289 : resetParentTest 1289 = true := by
  decide

theorem reset_cert_a_1290 : resetParentTest 1290 = true := by
  decide

theorem reset_cert_a_1291 : resetParentTest 1291 = true := by
  decide

theorem reset_cert_a_1292 : resetParentTest 1292 = true := by
  decide

theorem reset_cert_a_1293 : resetParentTest 1293 = true := by
  decide

theorem reset_cert_a_1294 : resetParentTest 1294 = true := by
  decide

theorem reset_cert_a_1295 : resetParentTest 1295 = true := by
  decide

def resetParents1280To1295 : List ℕ := [1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287, 1288, 1289, 1290, 1291, 1292, 1293, 1294, 1295]

theorem reset_block_1280_to_1295 : resetParents1280To1295.all resetParentTest = true := by
  simp only [resetParents1280To1295, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1280, ⟨reset_cert_a_1281, ⟨reset_cert_a_1282, ⟨reset_cert_a_1283, ⟨reset_cert_a_1284, ⟨reset_cert_a_1285, ⟨reset_cert_a_1286, ⟨reset_cert_a_1287, ⟨reset_cert_a_1288, ⟨reset_cert_a_1289, ⟨reset_cert_a_1290, ⟨reset_cert_a_1291, ⟨reset_cert_a_1292, ⟨reset_cert_a_1293, ⟨reset_cert_a_1294, reset_cert_a_1295⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
