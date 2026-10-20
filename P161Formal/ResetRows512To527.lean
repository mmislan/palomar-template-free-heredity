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

theorem reset_cert_a_512 : resetParentTest 512 = true := by
  obtain ⟨_, _, _, _, g0, g1⟩ := reset_join_pilot
  simp [resetParentTest, g0, g1]

theorem reset_cert_a_513 : resetParentTest 513 = true := by
  decide

theorem reset_cert_a_514 : resetParentTest 514 = true := by
  decide

theorem reset_cert_a_515 : resetParentTest 515 = true := by
  decide

theorem reset_cert_a_516 : resetParentTest 516 = true := by
  decide

theorem reset_cert_a_517 : resetParentTest 517 = true := by
  decide

theorem reset_cert_a_518 : resetParentTest 518 = true := by
  decide

theorem reset_cert_a_519 : resetParentTest 519 = true := by
  decide

theorem reset_cert_a_520 : resetParentTest 520 = true := by
  decide

theorem reset_cert_a_521 : resetParentTest 521 = true := by
  decide

theorem reset_cert_a_522 : resetParentTest 522 = true := by
  decide

theorem reset_cert_a_523 : resetParentTest 523 = true := by
  decide

theorem reset_cert_a_524 : resetParentTest 524 = true := by
  decide

theorem reset_cert_a_525 : resetParentTest 525 = true := by
  decide

theorem reset_cert_a_526 : resetParentTest 526 = true := by
  decide

theorem reset_cert_a_527 : resetParentTest 527 = true := by
  decide

def resetParents512To527 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527]

theorem reset_block_512_to_527 : resetParents512To527.all resetParentTest = true := by
  simp only [resetParents512To527, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_512, ⟨reset_cert_a_513, ⟨reset_cert_a_514, ⟨reset_cert_a_515, ⟨reset_cert_a_516, ⟨reset_cert_a_517, ⟨reset_cert_a_518, ⟨reset_cert_a_519, ⟨reset_cert_a_520, ⟨reset_cert_a_521, ⟨reset_cert_a_522, ⟨reset_cert_a_523, ⟨reset_cert_a_524, ⟨reset_cert_a_525, ⟨reset_cert_a_526, reset_cert_a_527⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
