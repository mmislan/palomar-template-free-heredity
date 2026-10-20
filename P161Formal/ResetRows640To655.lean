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

theorem reset_cert_a_640 : resetParentTest 640 = true := by
  decide

theorem reset_cert_a_641 : resetParentTest 641 = true := by
  decide

theorem reset_cert_a_642 : resetParentTest 642 = true := by
  decide

theorem reset_cert_a_643 : resetParentTest 643 = true := by
  decide

theorem reset_cert_a_644 : resetParentTest 644 = true := by
  decide

theorem reset_cert_a_645 : resetParentTest 645 = true := by
  decide

theorem reset_cert_a_646 : resetParentTest 646 = true := by
  decide

theorem reset_cert_a_647 : resetParentTest 647 = true := by
  decide

theorem reset_cert_a_648 : resetParentTest 648 = true := by
  decide

theorem reset_cert_a_649 : resetParentTest 649 = true := by
  decide

theorem reset_cert_a_650 : resetParentTest 650 = true := by
  decide

theorem reset_cert_a_651 : resetParentTest 651 = true := by
  decide

theorem reset_cert_a_652 : resetParentTest 652 = true := by
  decide

theorem reset_cert_a_653 : resetParentTest 653 = true := by
  decide

theorem reset_cert_a_654 : resetParentTest 654 = true := by
  decide

theorem reset_cert_a_655 : resetParentTest 655 = true := by
  decide

def resetParents640To655 : List ℕ := [640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655]

theorem reset_block_640_to_655 : resetParents640To655.all resetParentTest = true := by
  simp only [resetParents640To655, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_640, ⟨reset_cert_a_641, ⟨reset_cert_a_642, ⟨reset_cert_a_643, ⟨reset_cert_a_644, ⟨reset_cert_a_645, ⟨reset_cert_a_646, ⟨reset_cert_a_647, ⟨reset_cert_a_648, ⟨reset_cert_a_649, ⟨reset_cert_a_650, ⟨reset_cert_a_651, ⟨reset_cert_a_652, ⟨reset_cert_a_653, ⟨reset_cert_a_654, reset_cert_a_655⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
