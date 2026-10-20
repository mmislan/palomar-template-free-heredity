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

theorem reset_cert_a_624 : resetParentTest 624 = true := by
  decide

theorem reset_cert_a_625 : resetParentTest 625 = true := by
  decide

theorem reset_cert_a_626 : resetParentTest 626 = true := by
  decide

theorem reset_cert_a_627 : resetParentTest 627 = true := by
  decide

theorem reset_cert_a_628 : resetParentTest 628 = true := by
  decide

theorem reset_cert_a_629 : resetParentTest 629 = true := by
  decide

theorem reset_cert_a_630 : resetParentTest 630 = true := by
  decide

theorem reset_cert_a_631 : resetParentTest 631 = true := by
  decide

theorem reset_cert_a_632 : resetParentTest 632 = true := by
  decide

theorem reset_cert_a_633 : resetParentTest 633 = true := by
  decide

theorem reset_cert_a_634 : resetParentTest 634 = true := by
  decide

theorem reset_cert_a_635 : resetParentTest 635 = true := by
  decide

theorem reset_cert_a_636 : resetParentTest 636 = true := by
  decide

theorem reset_cert_a_637 : resetParentTest 637 = true := by
  decide

theorem reset_cert_a_638 : resetParentTest 638 = true := by
  decide

theorem reset_cert_a_639 : resetParentTest 639 = true := by
  decide

def resetParents624To639 : List ℕ := [624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639]

theorem reset_block_624_to_639 : resetParents624To639.all resetParentTest = true := by
  simp only [resetParents624To639, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_624, ⟨reset_cert_a_625, ⟨reset_cert_a_626, ⟨reset_cert_a_627, ⟨reset_cert_a_628, ⟨reset_cert_a_629, ⟨reset_cert_a_630, ⟨reset_cert_a_631, ⟨reset_cert_a_632, ⟨reset_cert_a_633, ⟨reset_cert_a_634, ⟨reset_cert_a_635, ⟨reset_cert_a_636, ⟨reset_cert_a_637, ⟨reset_cert_a_638, reset_cert_a_639⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
