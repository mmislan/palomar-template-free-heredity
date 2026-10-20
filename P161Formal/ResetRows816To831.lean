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

theorem reset_cert_a_816 : resetParentTest 816 = true := by
  decide

theorem reset_cert_a_817 : resetParentTest 817 = true := by
  decide

theorem reset_cert_a_818 : resetParentTest 818 = true := by
  decide

theorem reset_cert_a_819 : resetParentTest 819 = true := by
  decide

theorem reset_cert_a_820 : resetParentTest 820 = true := by
  decide

theorem reset_cert_a_821 : resetParentTest 821 = true := by
  decide

theorem reset_cert_a_822 : resetParentTest 822 = true := by
  decide

theorem reset_cert_a_823 : resetParentTest 823 = true := by
  decide

theorem reset_cert_a_824 : resetParentTest 824 = true := by
  decide

theorem reset_cert_a_825 : resetParentTest 825 = true := by
  decide

theorem reset_cert_a_826 : resetParentTest 826 = true := by
  decide

theorem reset_cert_a_827 : resetParentTest 827 = true := by
  decide

theorem reset_cert_a_828 : resetParentTest 828 = true := by
  decide

theorem reset_cert_a_829 : resetParentTest 829 = true := by
  decide

theorem reset_cert_a_830 : resetParentTest 830 = true := by
  decide

theorem reset_cert_a_831 : resetParentTest 831 = true := by
  decide

def resetParents816To831 : List ℕ := [816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831]

theorem reset_block_816_to_831 : resetParents816To831.all resetParentTest = true := by
  simp only [resetParents816To831, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_816, ⟨reset_cert_a_817, ⟨reset_cert_a_818, ⟨reset_cert_a_819, ⟨reset_cert_a_820, ⟨reset_cert_a_821, ⟨reset_cert_a_822, ⟨reset_cert_a_823, ⟨reset_cert_a_824, ⟨reset_cert_a_825, ⟨reset_cert_a_826, ⟨reset_cert_a_827, ⟨reset_cert_a_828, ⟨reset_cert_a_829, ⟨reset_cert_a_830, reset_cert_a_831⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
