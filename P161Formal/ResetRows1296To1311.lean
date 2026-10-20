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

theorem reset_cert_a_1296 : resetParentTest 1296 = true := by
  decide

theorem reset_cert_a_1297 : resetParentTest 1297 = true := by
  decide

theorem reset_cert_a_1298 : resetParentTest 1298 = true := by
  decide

theorem reset_cert_a_1299 : resetParentTest 1299 = true := by
  decide

theorem reset_cert_a_1300 : resetParentTest 1300 = true := by
  decide

theorem reset_cert_a_1301 : resetParentTest 1301 = true := by
  decide

theorem reset_cert_a_1302 : resetParentTest 1302 = true := by
  decide

theorem reset_cert_a_1303 : resetParentTest 1303 = true := by
  decide

theorem reset_cert_a_1304 : resetParentTest 1304 = true := by
  decide

theorem reset_cert_a_1305 : resetParentTest 1305 = true := by
  decide

theorem reset_cert_a_1306 : resetParentTest 1306 = true := by
  decide

theorem reset_cert_a_1307 : resetParentTest 1307 = true := by
  decide

theorem reset_cert_a_1308 : resetParentTest 1308 = true := by
  decide

theorem reset_cert_a_1309 : resetParentTest 1309 = true := by
  decide

theorem reset_cert_a_1310 : resetParentTest 1310 = true := by
  decide

theorem reset_cert_a_1311 : resetParentTest 1311 = true := by
  decide

def resetParents1296To1311 : List ℕ := [1296, 1297, 1298, 1299, 1300, 1301, 1302, 1303, 1304, 1305, 1306, 1307, 1308, 1309, 1310, 1311]

theorem reset_block_1296_to_1311 : resetParents1296To1311.all resetParentTest = true := by
  simp only [resetParents1296To1311, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1296, ⟨reset_cert_a_1297, ⟨reset_cert_a_1298, ⟨reset_cert_a_1299, ⟨reset_cert_a_1300, ⟨reset_cert_a_1301, ⟨reset_cert_a_1302, ⟨reset_cert_a_1303, ⟨reset_cert_a_1304, ⟨reset_cert_a_1305, ⟨reset_cert_a_1306, ⟨reset_cert_a_1307, ⟨reset_cert_a_1308, ⟨reset_cert_a_1309, ⟨reset_cert_a_1310, reset_cert_a_1311⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
