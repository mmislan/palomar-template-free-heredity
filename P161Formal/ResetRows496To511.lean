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

theorem reset_cert_a_496 : resetParentTest 496 = true := by
  decide

theorem reset_cert_a_497 : resetParentTest 497 = true := by
  decide

theorem reset_cert_a_498 : resetParentTest 498 = true := by
  decide

theorem reset_cert_a_499 : resetParentTest 499 = true := by
  decide

theorem reset_cert_a_500 : resetParentTest 500 = true := by
  decide

theorem reset_cert_a_501 : resetParentTest 501 = true := by
  decide

theorem reset_cert_a_502 : resetParentTest 502 = true := by
  decide

theorem reset_cert_a_503 : resetParentTest 503 = true := by
  decide

theorem reset_cert_a_504 : resetParentTest 504 = true := by
  decide

theorem reset_cert_a_505 : resetParentTest 505 = true := by
  decide

theorem reset_cert_a_506 : resetParentTest 506 = true := by
  decide

theorem reset_cert_a_507 : resetParentTest 507 = true := by
  decide

theorem reset_cert_a_508 : resetParentTest 508 = true := by
  decide

theorem reset_cert_a_509 : resetParentTest 509 = true := by
  decide

theorem reset_cert_a_510 : resetParentTest 510 = true := by
  decide

theorem reset_cert_a_511 : resetParentTest 511 = true := by
  obtain ⟨d0, d1, g0, g1, _, _⟩ := reset_join_pilot
  simp [resetParentTest, g0, g1, d0, d1]

def resetParents496To511 : List ℕ := [496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]

theorem reset_block_496_to_511 : resetParents496To511.all resetParentTest = true := by
  simp only [resetParents496To511, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_496, ⟨reset_cert_a_497, ⟨reset_cert_a_498, ⟨reset_cert_a_499, ⟨reset_cert_a_500, ⟨reset_cert_a_501, ⟨reset_cert_a_502, ⟨reset_cert_a_503, ⟨reset_cert_a_504, ⟨reset_cert_a_505, ⟨reset_cert_a_506, ⟨reset_cert_a_507, ⟨reset_cert_a_508, ⟨reset_cert_a_509, ⟨reset_cert_a_510, reset_cert_a_511⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
