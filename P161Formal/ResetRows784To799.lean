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

theorem reset_cert_a_784 : resetParentTest 784 = true := by
  decide

theorem reset_cert_a_785 : resetParentTest 785 = true := by
  decide

theorem reset_cert_a_786 : resetParentTest 786 = true := by
  decide

theorem reset_cert_a_787 : resetParentTest 787 = true := by
  decide

theorem reset_cert_a_788 : resetParentTest 788 = true := by
  decide

theorem reset_cert_a_789 : resetParentTest 789 = true := by
  decide

theorem reset_cert_a_790 : resetParentTest 790 = true := by
  decide

theorem reset_cert_a_791 : resetParentTest 791 = true := by
  decide

theorem reset_cert_a_792 : resetParentTest 792 = true := by
  decide

theorem reset_cert_a_793 : resetParentTest 793 = true := by
  decide

theorem reset_cert_a_794 : resetParentTest 794 = true := by
  decide

theorem reset_cert_a_795 : resetParentTest 795 = true := by
  decide

theorem reset_cert_a_796 : resetParentTest 796 = true := by
  decide

theorem reset_cert_a_797 : resetParentTest 797 = true := by
  decide

theorem reset_cert_a_798 : resetParentTest 798 = true := by
  decide

theorem reset_cert_a_799 : resetParentTest 799 = true := by
  decide

def resetParents784To799 : List ℕ := [784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796, 797, 798, 799]

theorem reset_block_784_to_799 : resetParents784To799.all resetParentTest = true := by
  simp only [resetParents784To799, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_784, ⟨reset_cert_a_785, ⟨reset_cert_a_786, ⟨reset_cert_a_787, ⟨reset_cert_a_788, ⟨reset_cert_a_789, ⟨reset_cert_a_790, ⟨reset_cert_a_791, ⟨reset_cert_a_792, ⟨reset_cert_a_793, ⟨reset_cert_a_794, ⟨reset_cert_a_795, ⟨reset_cert_a_796, ⟨reset_cert_a_797, ⟨reset_cert_a_798, reset_cert_a_799⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
