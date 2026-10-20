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

theorem reset_cert_a_896 : resetParentTest 896 = true := by
  decide

theorem reset_cert_a_897 : resetParentTest 897 = true := by
  decide

theorem reset_cert_a_898 : resetParentTest 898 = true := by
  decide

theorem reset_cert_a_899 : resetParentTest 899 = true := by
  decide

theorem reset_cert_a_900 : resetParentTest 900 = true := by
  decide

theorem reset_cert_a_901 : resetParentTest 901 = true := by
  decide

theorem reset_cert_a_902 : resetParentTest 902 = true := by
  decide

theorem reset_cert_a_903 : resetParentTest 903 = true := by
  decide

theorem reset_cert_a_904 : resetParentTest 904 = true := by
  decide

theorem reset_cert_a_905 : resetParentTest 905 = true := by
  decide

theorem reset_cert_a_906 : resetParentTest 906 = true := by
  decide

theorem reset_cert_a_907 : resetParentTest 907 = true := by
  decide

theorem reset_cert_a_908 : resetParentTest 908 = true := by
  decide

theorem reset_cert_a_909 : resetParentTest 909 = true := by
  decide

theorem reset_cert_a_910 : resetParentTest 910 = true := by
  decide

theorem reset_cert_a_911 : resetParentTest 911 = true := by
  decide

def resetParents896To911 : List ℕ := [896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911]

theorem reset_block_896_to_911 : resetParents896To911.all resetParentTest = true := by
  simp only [resetParents896To911, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_896, ⟨reset_cert_a_897, ⟨reset_cert_a_898, ⟨reset_cert_a_899, ⟨reset_cert_a_900, ⟨reset_cert_a_901, ⟨reset_cert_a_902, ⟨reset_cert_a_903, ⟨reset_cert_a_904, ⟨reset_cert_a_905, ⟨reset_cert_a_906, ⟨reset_cert_a_907, ⟨reset_cert_a_908, ⟨reset_cert_a_909, ⟨reset_cert_a_910, reset_cert_a_911⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
