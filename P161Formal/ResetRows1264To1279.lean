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

theorem reset_cert_a_1264 : resetParentTest 1264 = true := by
  decide

theorem reset_cert_a_1265 : resetParentTest 1265 = true := by
  decide

theorem reset_cert_a_1266 : resetParentTest 1266 = true := by
  decide

theorem reset_cert_a_1267 : resetParentTest 1267 = true := by
  decide

theorem reset_cert_a_1268 : resetParentTest 1268 = true := by
  decide

theorem reset_cert_a_1269 : resetParentTest 1269 = true := by
  decide

theorem reset_cert_a_1270 : resetParentTest 1270 = true := by
  decide

theorem reset_cert_a_1271 : resetParentTest 1271 = true := by
  decide

theorem reset_cert_a_1272 : resetParentTest 1272 = true := by
  decide

theorem reset_cert_a_1273 : resetParentTest 1273 = true := by
  decide

theorem reset_cert_a_1274 : resetParentTest 1274 = true := by
  decide

theorem reset_cert_a_1275 : resetParentTest 1275 = true := by
  decide

theorem reset_cert_a_1276 : resetParentTest 1276 = true := by
  decide

theorem reset_cert_a_1277 : resetParentTest 1277 = true := by
  decide

theorem reset_cert_a_1278 : resetParentTest 1278 = true := by
  decide

theorem reset_cert_a_1279 : resetParentTest 1279 = true := by
  decide

def resetParents1264To1279 : List ℕ := [1264, 1265, 1266, 1267, 1268, 1269, 1270, 1271, 1272, 1273, 1274, 1275, 1276, 1277, 1278, 1279]

theorem reset_block_1264_to_1279 : resetParents1264To1279.all resetParentTest = true := by
  simp only [resetParents1264To1279, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1264, ⟨reset_cert_a_1265, ⟨reset_cert_a_1266, ⟨reset_cert_a_1267, ⟨reset_cert_a_1268, ⟨reset_cert_a_1269, ⟨reset_cert_a_1270, ⟨reset_cert_a_1271, ⟨reset_cert_a_1272, ⟨reset_cert_a_1273, ⟨reset_cert_a_1274, ⟨reset_cert_a_1275, ⟨reset_cert_a_1276, ⟨reset_cert_a_1277, ⟨reset_cert_a_1278, reset_cert_a_1279⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
