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

theorem reset_cert_a_864 : resetParentTest 864 = true := by
  decide

theorem reset_cert_a_865 : resetParentTest 865 = true := by
  decide

theorem reset_cert_a_866 : resetParentTest 866 = true := by
  decide

theorem reset_cert_a_867 : resetParentTest 867 = true := by
  decide

theorem reset_cert_a_868 : resetParentTest 868 = true := by
  decide

theorem reset_cert_a_869 : resetParentTest 869 = true := by
  decide

theorem reset_cert_a_870 : resetParentTest 870 = true := by
  decide

theorem reset_cert_a_871 : resetParentTest 871 = true := by
  decide

theorem reset_cert_a_872 : resetParentTest 872 = true := by
  decide

theorem reset_cert_a_873 : resetParentTest 873 = true := by
  decide

theorem reset_cert_a_874 : resetParentTest 874 = true := by
  decide

theorem reset_cert_a_875 : resetParentTest 875 = true := by
  decide

theorem reset_cert_a_876 : resetParentTest 876 = true := by
  decide

theorem reset_cert_a_877 : resetParentTest 877 = true := by
  decide

theorem reset_cert_a_878 : resetParentTest 878 = true := by
  decide

theorem reset_cert_a_879 : resetParentTest 879 = true := by
  decide

def resetParents864To879 : List ℕ := [864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879]

theorem reset_block_864_to_879 : resetParents864To879.all resetParentTest = true := by
  simp only [resetParents864To879, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_864, ⟨reset_cert_a_865, ⟨reset_cert_a_866, ⟨reset_cert_a_867, ⟨reset_cert_a_868, ⟨reset_cert_a_869, ⟨reset_cert_a_870, ⟨reset_cert_a_871, ⟨reset_cert_a_872, ⟨reset_cert_a_873, ⟨reset_cert_a_874, ⟨reset_cert_a_875, ⟨reset_cert_a_876, ⟨reset_cert_a_877, ⟨reset_cert_a_878, reset_cert_a_879⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
