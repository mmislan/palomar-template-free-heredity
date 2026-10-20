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

theorem reset_cert_a_672 : resetParentTest 672 = true := by
  decide

theorem reset_cert_a_673 : resetParentTest 673 = true := by
  decide

theorem reset_cert_a_674 : resetParentTest 674 = true := by
  decide

theorem reset_cert_a_675 : resetParentTest 675 = true := by
  decide

theorem reset_cert_a_676 : resetParentTest 676 = true := by
  decide

theorem reset_cert_a_677 : resetParentTest 677 = true := by
  decide

theorem reset_cert_a_678 : resetParentTest 678 = true := by
  decide

theorem reset_cert_a_679 : resetParentTest 679 = true := by
  decide

theorem reset_cert_a_680 : resetParentTest 680 = true := by
  decide

theorem reset_cert_a_681 : resetParentTest 681 = true := by
  decide

theorem reset_cert_a_682 : resetParentTest 682 = true := by
  decide

theorem reset_cert_a_683 : resetParentTest 683 = true := by
  decide

theorem reset_cert_a_684 : resetParentTest 684 = true := by
  decide

theorem reset_cert_a_685 : resetParentTest 685 = true := by
  decide

theorem reset_cert_a_686 : resetParentTest 686 = true := by
  decide

theorem reset_cert_a_687 : resetParentTest 687 = true := by
  decide

def resetParents672To687 : List ℕ := [672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687]

theorem reset_block_672_to_687 : resetParents672To687.all resetParentTest = true := by
  simp only [resetParents672To687, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_672, ⟨reset_cert_a_673, ⟨reset_cert_a_674, ⟨reset_cert_a_675, ⟨reset_cert_a_676, ⟨reset_cert_a_677, ⟨reset_cert_a_678, ⟨reset_cert_a_679, ⟨reset_cert_a_680, ⟨reset_cert_a_681, ⟨reset_cert_a_682, ⟨reset_cert_a_683, ⟨reset_cert_a_684, ⟨reset_cert_a_685, ⟨reset_cert_a_686, reset_cert_a_687⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
