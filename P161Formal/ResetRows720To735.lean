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

theorem reset_cert_a_720 : resetParentTest 720 = true := by
  decide

theorem reset_cert_a_721 : resetParentTest 721 = true := by
  decide

theorem reset_cert_a_722 : resetParentTest 722 = true := by
  decide

theorem reset_cert_a_723 : resetParentTest 723 = true := by
  decide

theorem reset_cert_a_724 : resetParentTest 724 = true := by
  decide

theorem reset_cert_a_725 : resetParentTest 725 = true := by
  decide

theorem reset_cert_a_726 : resetParentTest 726 = true := by
  decide

theorem reset_cert_a_727 : resetParentTest 727 = true := by
  decide

theorem reset_cert_a_728 : resetParentTest 728 = true := by
  decide

theorem reset_cert_a_729 : resetParentTest 729 = true := by
  decide

theorem reset_cert_a_730 : resetParentTest 730 = true := by
  decide

theorem reset_cert_a_731 : resetParentTest 731 = true := by
  decide

theorem reset_cert_a_732 : resetParentTest 732 = true := by
  decide

theorem reset_cert_a_733 : resetParentTest 733 = true := by
  decide

theorem reset_cert_a_734 : resetParentTest 734 = true := by
  decide

theorem reset_cert_a_735 : resetParentTest 735 = true := by
  decide

def resetParents720To735 : List ℕ := [720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735]

theorem reset_block_720_to_735 : resetParents720To735.all resetParentTest = true := by
  simp only [resetParents720To735, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_720, ⟨reset_cert_a_721, ⟨reset_cert_a_722, ⟨reset_cert_a_723, ⟨reset_cert_a_724, ⟨reset_cert_a_725, ⟨reset_cert_a_726, ⟨reset_cert_a_727, ⟨reset_cert_a_728, ⟨reset_cert_a_729, ⟨reset_cert_a_730, ⟨reset_cert_a_731, ⟨reset_cert_a_732, ⟨reset_cert_a_733, ⟨reset_cert_a_734, reset_cert_a_735⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
