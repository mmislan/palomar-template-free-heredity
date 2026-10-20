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

theorem reset_cert_a_560 : resetParentTest 560 = true := by
  decide

theorem reset_cert_a_561 : resetParentTest 561 = true := by
  decide

theorem reset_cert_a_562 : resetParentTest 562 = true := by
  decide

theorem reset_cert_a_563 : resetParentTest 563 = true := by
  decide

theorem reset_cert_a_564 : resetParentTest 564 = true := by
  decide

theorem reset_cert_a_565 : resetParentTest 565 = true := by
  decide

theorem reset_cert_a_566 : resetParentTest 566 = true := by
  decide

theorem reset_cert_a_567 : resetParentTest 567 = true := by
  decide

theorem reset_cert_a_568 : resetParentTest 568 = true := by
  decide

theorem reset_cert_a_569 : resetParentTest 569 = true := by
  decide

theorem reset_cert_a_570 : resetParentTest 570 = true := by
  decide

theorem reset_cert_a_571 : resetParentTest 571 = true := by
  decide

theorem reset_cert_a_572 : resetParentTest 572 = true := by
  decide

theorem reset_cert_a_573 : resetParentTest 573 = true := by
  decide

theorem reset_cert_a_574 : resetParentTest 574 = true := by
  decide

theorem reset_cert_a_575 : resetParentTest 575 = true := by
  decide

def resetParents560To575 : List ℕ := [560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575]

theorem reset_block_560_to_575 : resetParents560To575.all resetParentTest = true := by
  simp only [resetParents560To575, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_560, ⟨reset_cert_a_561, ⟨reset_cert_a_562, ⟨reset_cert_a_563, ⟨reset_cert_a_564, ⟨reset_cert_a_565, ⟨reset_cert_a_566, ⟨reset_cert_a_567, ⟨reset_cert_a_568, ⟨reset_cert_a_569, ⟨reset_cert_a_570, ⟨reset_cert_a_571, ⟨reset_cert_a_572, ⟨reset_cert_a_573, ⟨reset_cert_a_574, reset_cert_a_575⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
