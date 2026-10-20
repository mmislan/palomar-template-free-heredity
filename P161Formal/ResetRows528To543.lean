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

theorem reset_cert_a_528 : resetParentTest 528 = true := by
  decide

theorem reset_cert_a_529 : resetParentTest 529 = true := by
  decide

theorem reset_cert_a_530 : resetParentTest 530 = true := by
  decide

theorem reset_cert_a_531 : resetParentTest 531 = true := by
  decide

theorem reset_cert_a_532 : resetParentTest 532 = true := by
  decide

theorem reset_cert_a_533 : resetParentTest 533 = true := by
  decide

theorem reset_cert_a_534 : resetParentTest 534 = true := by
  decide

theorem reset_cert_a_535 : resetParentTest 535 = true := by
  decide

theorem reset_cert_a_536 : resetParentTest 536 = true := by
  decide

theorem reset_cert_a_537 : resetParentTest 537 = true := by
  decide

theorem reset_cert_a_538 : resetParentTest 538 = true := by
  decide

theorem reset_cert_a_539 : resetParentTest 539 = true := by
  decide

theorem reset_cert_a_540 : resetParentTest 540 = true := by
  decide

theorem reset_cert_a_541 : resetParentTest 541 = true := by
  decide

theorem reset_cert_a_542 : resetParentTest 542 = true := by
  decide

theorem reset_cert_a_543 : resetParentTest 543 = true := by
  decide

def resetParents528To543 : List ℕ := [528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543]

theorem reset_block_528_to_543 : resetParents528To543.all resetParentTest = true := by
  simp only [resetParents528To543, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_528, ⟨reset_cert_a_529, ⟨reset_cert_a_530, ⟨reset_cert_a_531, ⟨reset_cert_a_532, ⟨reset_cert_a_533, ⟨reset_cert_a_534, ⟨reset_cert_a_535, ⟨reset_cert_a_536, ⟨reset_cert_a_537, ⟨reset_cert_a_538, ⟨reset_cert_a_539, ⟨reset_cert_a_540, ⟨reset_cert_a_541, ⟨reset_cert_a_542, reset_cert_a_543⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
