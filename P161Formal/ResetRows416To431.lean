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

theorem reset_cert_a_416 : resetParentTest 416 = true := by
  decide

theorem reset_cert_a_417 : resetParentTest 417 = true := by
  decide

theorem reset_cert_a_418 : resetParentTest 418 = true := by
  decide

theorem reset_cert_a_419 : resetParentTest 419 = true := by
  decide

theorem reset_cert_a_420 : resetParentTest 420 = true := by
  decide

theorem reset_cert_a_421 : resetParentTest 421 = true := by
  decide

theorem reset_cert_a_422 : resetParentTest 422 = true := by
  decide

theorem reset_cert_a_423 : resetParentTest 423 = true := by
  decide

theorem reset_cert_a_424 : resetParentTest 424 = true := by
  decide

theorem reset_cert_a_425 : resetParentTest 425 = true := by
  decide

theorem reset_cert_a_426 : resetParentTest 426 = true := by
  decide

theorem reset_cert_a_427 : resetParentTest 427 = true := by
  decide

theorem reset_cert_a_428 : resetParentTest 428 = true := by
  decide

theorem reset_cert_a_429 : resetParentTest 429 = true := by
  decide

theorem reset_cert_a_430 : resetParentTest 430 = true := by
  decide

theorem reset_cert_a_431 : resetParentTest 431 = true := by
  decide

def resetParents416To431 : List ℕ := [416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431]

theorem reset_block_416_to_431 : resetParents416To431.all resetParentTest = true := by
  simp only [resetParents416To431, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_416, ⟨reset_cert_a_417, ⟨reset_cert_a_418, ⟨reset_cert_a_419, ⟨reset_cert_a_420, ⟨reset_cert_a_421, ⟨reset_cert_a_422, ⟨reset_cert_a_423, ⟨reset_cert_a_424, ⟨reset_cert_a_425, ⟨reset_cert_a_426, ⟨reset_cert_a_427, ⟨reset_cert_a_428, ⟨reset_cert_a_429, ⟨reset_cert_a_430, reset_cert_a_431⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
