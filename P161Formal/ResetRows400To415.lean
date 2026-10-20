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

theorem reset_cert_a_400 : resetParentTest 400 = true := by
  decide

theorem reset_cert_a_401 : resetParentTest 401 = true := by
  decide

theorem reset_cert_a_402 : resetParentTest 402 = true := by
  decide

theorem reset_cert_a_403 : resetParentTest 403 = true := by
  decide

theorem reset_cert_a_404 : resetParentTest 404 = true := by
  decide

theorem reset_cert_a_405 : resetParentTest 405 = true := by
  decide

theorem reset_cert_a_406 : resetParentTest 406 = true := by
  decide

theorem reset_cert_a_407 : resetParentTest 407 = true := by
  decide

theorem reset_cert_a_408 : resetParentTest 408 = true := by
  decide

theorem reset_cert_a_409 : resetParentTest 409 = true := by
  decide

theorem reset_cert_a_410 : resetParentTest 410 = true := by
  decide

theorem reset_cert_a_411 : resetParentTest 411 = true := by
  decide

theorem reset_cert_a_412 : resetParentTest 412 = true := by
  decide

theorem reset_cert_a_413 : resetParentTest 413 = true := by
  decide

theorem reset_cert_a_414 : resetParentTest 414 = true := by
  decide

theorem reset_cert_a_415 : resetParentTest 415 = true := by
  decide

def resetParents400To415 : List ℕ := [400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415]

theorem reset_block_400_to_415 : resetParents400To415.all resetParentTest = true := by
  simp only [resetParents400To415, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_400, ⟨reset_cert_a_401, ⟨reset_cert_a_402, ⟨reset_cert_a_403, ⟨reset_cert_a_404, ⟨reset_cert_a_405, ⟨reset_cert_a_406, ⟨reset_cert_a_407, ⟨reset_cert_a_408, ⟨reset_cert_a_409, ⟨reset_cert_a_410, ⟨reset_cert_a_411, ⟨reset_cert_a_412, ⟨reset_cert_a_413, ⟨reset_cert_a_414, reset_cert_a_415⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
