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

theorem reset_cert_a_480 : resetParentTest 480 = true := by
  decide

theorem reset_cert_a_481 : resetParentTest 481 = true := by
  decide

theorem reset_cert_a_482 : resetParentTest 482 = true := by
  decide

theorem reset_cert_a_483 : resetParentTest 483 = true := by
  decide

theorem reset_cert_a_484 : resetParentTest 484 = true := by
  decide

theorem reset_cert_a_485 : resetParentTest 485 = true := by
  decide

theorem reset_cert_a_486 : resetParentTest 486 = true := by
  decide

theorem reset_cert_a_487 : resetParentTest 487 = true := by
  decide

theorem reset_cert_a_488 : resetParentTest 488 = true := by
  decide

theorem reset_cert_a_489 : resetParentTest 489 = true := by
  decide

theorem reset_cert_a_490 : resetParentTest 490 = true := by
  decide

theorem reset_cert_a_491 : resetParentTest 491 = true := by
  decide

theorem reset_cert_a_492 : resetParentTest 492 = true := by
  decide

theorem reset_cert_a_493 : resetParentTest 493 = true := by
  decide

theorem reset_cert_a_494 : resetParentTest 494 = true := by
  decide

theorem reset_cert_a_495 : resetParentTest 495 = true := by
  decide

def resetParents480To495 : List ℕ := [480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495]

theorem reset_block_480_to_495 : resetParents480To495.all resetParentTest = true := by
  simp only [resetParents480To495, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_480, ⟨reset_cert_a_481, ⟨reset_cert_a_482, ⟨reset_cert_a_483, ⟨reset_cert_a_484, ⟨reset_cert_a_485, ⟨reset_cert_a_486, ⟨reset_cert_a_487, ⟨reset_cert_a_488, ⟨reset_cert_a_489, ⟨reset_cert_a_490, ⟨reset_cert_a_491, ⟨reset_cert_a_492, ⟨reset_cert_a_493, ⟨reset_cert_a_494, reset_cert_a_495⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
