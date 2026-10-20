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

theorem reset_cert_a_912 : resetParentTest 912 = true := by
  decide

theorem reset_cert_a_913 : resetParentTest 913 = true := by
  decide

theorem reset_cert_a_914 : resetParentTest 914 = true := by
  decide

theorem reset_cert_a_915 : resetParentTest 915 = true := by
  decide

theorem reset_cert_a_916 : resetParentTest 916 = true := by
  decide

theorem reset_cert_a_917 : resetParentTest 917 = true := by
  decide

theorem reset_cert_a_918 : resetParentTest 918 = true := by
  decide

theorem reset_cert_a_919 : resetParentTest 919 = true := by
  decide

theorem reset_cert_a_920 : resetParentTest 920 = true := by
  decide

theorem reset_cert_a_921 : resetParentTest 921 = true := by
  decide

theorem reset_cert_a_922 : resetParentTest 922 = true := by
  decide

theorem reset_cert_a_923 : resetParentTest 923 = true := by
  decide

theorem reset_cert_a_924 : resetParentTest 924 = true := by
  decide

theorem reset_cert_a_925 : resetParentTest 925 = true := by
  decide

theorem reset_cert_a_926 : resetParentTest 926 = true := by
  decide

theorem reset_cert_a_927 : resetParentTest 927 = true := by
  decide

def resetParents912To927 : List ℕ := [912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927]

theorem reset_block_912_to_927 : resetParents912To927.all resetParentTest = true := by
  simp only [resetParents912To927, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_912, ⟨reset_cert_a_913, ⟨reset_cert_a_914, ⟨reset_cert_a_915, ⟨reset_cert_a_916, ⟨reset_cert_a_917, ⟨reset_cert_a_918, ⟨reset_cert_a_919, ⟨reset_cert_a_920, ⟨reset_cert_a_921, ⟨reset_cert_a_922, ⟨reset_cert_a_923, ⟨reset_cert_a_924, ⟨reset_cert_a_925, ⟨reset_cert_a_926, reset_cert_a_927⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
