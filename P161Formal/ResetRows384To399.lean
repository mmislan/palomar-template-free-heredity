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

theorem reset_cert_a_384 : resetParentTest 384 = true := by
  decide

theorem reset_cert_a_385 : resetParentTest 385 = true := by
  decide

theorem reset_cert_a_386 : resetParentTest 386 = true := by
  decide

theorem reset_cert_a_387 : resetParentTest 387 = true := by
  decide

theorem reset_cert_a_388 : resetParentTest 388 = true := by
  decide

theorem reset_cert_a_389 : resetParentTest 389 = true := by
  decide

theorem reset_cert_a_390 : resetParentTest 390 = true := by
  decide

theorem reset_cert_a_391 : resetParentTest 391 = true := by
  decide

theorem reset_cert_a_392 : resetParentTest 392 = true := by
  decide

theorem reset_cert_a_393 : resetParentTest 393 = true := by
  decide

theorem reset_cert_a_394 : resetParentTest 394 = true := by
  decide

theorem reset_cert_a_395 : resetParentTest 395 = true := by
  decide

theorem reset_cert_a_396 : resetParentTest 396 = true := by
  decide

theorem reset_cert_a_397 : resetParentTest 397 = true := by
  decide

theorem reset_cert_a_398 : resetParentTest 398 = true := by
  decide

theorem reset_cert_a_399 : resetParentTest 399 = true := by
  decide

def resetParents384To399 : List ℕ := [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399]

theorem reset_block_384_to_399 : resetParents384To399.all resetParentTest = true := by
  simp only [resetParents384To399, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_384, ⟨reset_cert_a_385, ⟨reset_cert_a_386, ⟨reset_cert_a_387, ⟨reset_cert_a_388, ⟨reset_cert_a_389, ⟨reset_cert_a_390, ⟨reset_cert_a_391, ⟨reset_cert_a_392, ⟨reset_cert_a_393, ⟨reset_cert_a_394, ⟨reset_cert_a_395, ⟨reset_cert_a_396, ⟨reset_cert_a_397, ⟨reset_cert_a_398, reset_cert_a_399⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
