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

theorem reset_cert_a_1328 : resetParentTest 1328 = true := by
  decide

theorem reset_cert_a_1329 : resetParentTest 1329 = true := by
  decide

theorem reset_cert_a_1330 : resetParentTest 1330 = true := by
  decide

theorem reset_cert_a_1331 : resetParentTest 1331 = true := by
  decide

theorem reset_cert_a_1332 : resetParentTest 1332 = true := by
  decide

theorem reset_cert_a_1333 : resetParentTest 1333 = true := by
  decide

theorem reset_cert_a_1334 : resetParentTest 1334 = true := by
  decide

theorem reset_cert_a_1335 : resetParentTest 1335 = true := by
  decide

theorem reset_cert_a_1336 : resetParentTest 1336 = true := by
  decide

theorem reset_cert_a_1337 : resetParentTest 1337 = true := by
  decide

theorem reset_cert_a_1338 : resetParentTest 1338 = true := by
  decide

theorem reset_cert_a_1339 : resetParentTest 1339 = true := by
  decide

theorem reset_cert_a_1340 : resetParentTest 1340 = true := by
  decide

theorem reset_cert_a_1341 : resetParentTest 1341 = true := by
  decide

theorem reset_cert_a_1342 : resetParentTest 1342 = true := by
  decide

theorem reset_cert_a_1343 : resetParentTest 1343 = true := by
  decide

def resetParents1328To1343 : List ℕ := [1328, 1329, 1330, 1331, 1332, 1333, 1334, 1335, 1336, 1337, 1338, 1339, 1340, 1341, 1342, 1343]

theorem reset_block_1328_to_1343 : resetParents1328To1343.all resetParentTest = true := by
  simp only [resetParents1328To1343, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1328, ⟨reset_cert_a_1329, ⟨reset_cert_a_1330, ⟨reset_cert_a_1331, ⟨reset_cert_a_1332, ⟨reset_cert_a_1333, ⟨reset_cert_a_1334, ⟨reset_cert_a_1335, ⟨reset_cert_a_1336, ⟨reset_cert_a_1337, ⟨reset_cert_a_1338, ⟨reset_cert_a_1339, ⟨reset_cert_a_1340, ⟨reset_cert_a_1341, ⟨reset_cert_a_1342, reset_cert_a_1343⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
