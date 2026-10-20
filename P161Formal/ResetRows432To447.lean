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

theorem reset_cert_a_432 : resetParentTest 432 = true := by
  decide

theorem reset_cert_a_433 : resetParentTest 433 = true := by
  decide

theorem reset_cert_a_434 : resetParentTest 434 = true := by
  decide

theorem reset_cert_a_435 : resetParentTest 435 = true := by
  decide

theorem reset_cert_a_436 : resetParentTest 436 = true := by
  decide

theorem reset_cert_a_437 : resetParentTest 437 = true := by
  decide

theorem reset_cert_a_438 : resetParentTest 438 = true := by
  decide

theorem reset_cert_a_439 : resetParentTest 439 = true := by
  decide

theorem reset_cert_a_440 : resetParentTest 440 = true := by
  decide

theorem reset_cert_a_441 : resetParentTest 441 = true := by
  decide

theorem reset_cert_a_442 : resetParentTest 442 = true := by
  decide

theorem reset_cert_a_443 : resetParentTest 443 = true := by
  decide

theorem reset_cert_a_444 : resetParentTest 444 = true := by
  decide

theorem reset_cert_a_445 : resetParentTest 445 = true := by
  decide

theorem reset_cert_a_446 : resetParentTest 446 = true := by
  decide

theorem reset_cert_a_447 : resetParentTest 447 = true := by
  decide

def resetParents432To447 : List ℕ := [432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447]

theorem reset_block_432_to_447 : resetParents432To447.all resetParentTest = true := by
  simp only [resetParents432To447, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_432, ⟨reset_cert_a_433, ⟨reset_cert_a_434, ⟨reset_cert_a_435, ⟨reset_cert_a_436, ⟨reset_cert_a_437, ⟨reset_cert_a_438, ⟨reset_cert_a_439, ⟨reset_cert_a_440, ⟨reset_cert_a_441, ⟨reset_cert_a_442, ⟨reset_cert_a_443, ⟨reset_cert_a_444, ⟨reset_cert_a_445, ⟨reset_cert_a_446, reset_cert_a_447⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
