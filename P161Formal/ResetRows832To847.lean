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

theorem reset_cert_a_832 : resetParentTest 832 = true := by
  decide

theorem reset_cert_a_833 : resetParentTest 833 = true := by
  decide

theorem reset_cert_a_834 : resetParentTest 834 = true := by
  decide

theorem reset_cert_a_835 : resetParentTest 835 = true := by
  decide

theorem reset_cert_a_836 : resetParentTest 836 = true := by
  decide

theorem reset_cert_a_837 : resetParentTest 837 = true := by
  decide

theorem reset_cert_a_838 : resetParentTest 838 = true := by
  decide

theorem reset_cert_a_839 : resetParentTest 839 = true := by
  decide

theorem reset_cert_a_840 : resetParentTest 840 = true := by
  decide

theorem reset_cert_a_841 : resetParentTest 841 = true := by
  decide

theorem reset_cert_a_842 : resetParentTest 842 = true := by
  decide

theorem reset_cert_a_843 : resetParentTest 843 = true := by
  decide

theorem reset_cert_a_844 : resetParentTest 844 = true := by
  decide

theorem reset_cert_a_845 : resetParentTest 845 = true := by
  decide

theorem reset_cert_a_846 : resetParentTest 846 = true := by
  decide

theorem reset_cert_a_847 : resetParentTest 847 = true := by
  decide

def resetParents832To847 : List ℕ := [832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847]

theorem reset_block_832_to_847 : resetParents832To847.all resetParentTest = true := by
  simp only [resetParents832To847, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_832, ⟨reset_cert_a_833, ⟨reset_cert_a_834, ⟨reset_cert_a_835, ⟨reset_cert_a_836, ⟨reset_cert_a_837, ⟨reset_cert_a_838, ⟨reset_cert_a_839, ⟨reset_cert_a_840, ⟨reset_cert_a_841, ⟨reset_cert_a_842, ⟨reset_cert_a_843, ⟨reset_cert_a_844, ⟨reset_cert_a_845, ⟨reset_cert_a_846, reset_cert_a_847⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
