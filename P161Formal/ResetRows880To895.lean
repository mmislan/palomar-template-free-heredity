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

theorem reset_cert_a_880 : resetParentTest 880 = true := by
  decide

theorem reset_cert_a_881 : resetParentTest 881 = true := by
  decide

theorem reset_cert_a_882 : resetParentTest 882 = true := by
  decide

theorem reset_cert_a_883 : resetParentTest 883 = true := by
  decide

theorem reset_cert_a_884 : resetParentTest 884 = true := by
  decide

theorem reset_cert_a_885 : resetParentTest 885 = true := by
  decide

theorem reset_cert_a_886 : resetParentTest 886 = true := by
  decide

theorem reset_cert_a_887 : resetParentTest 887 = true := by
  decide

theorem reset_cert_a_888 : resetParentTest 888 = true := by
  decide

theorem reset_cert_a_889 : resetParentTest 889 = true := by
  decide

theorem reset_cert_a_890 : resetParentTest 890 = true := by
  decide

theorem reset_cert_a_891 : resetParentTest 891 = true := by
  decide

theorem reset_cert_a_892 : resetParentTest 892 = true := by
  decide

theorem reset_cert_a_893 : resetParentTest 893 = true := by
  decide

theorem reset_cert_a_894 : resetParentTest 894 = true := by
  decide

theorem reset_cert_a_895 : resetParentTest 895 = true := by
  decide

def resetParents880To895 : List ℕ := [880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895]

theorem reset_block_880_to_895 : resetParents880To895.all resetParentTest = true := by
  simp only [resetParents880To895, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_880, ⟨reset_cert_a_881, ⟨reset_cert_a_882, ⟨reset_cert_a_883, ⟨reset_cert_a_884, ⟨reset_cert_a_885, ⟨reset_cert_a_886, ⟨reset_cert_a_887, ⟨reset_cert_a_888, ⟨reset_cert_a_889, ⟨reset_cert_a_890, ⟨reset_cert_a_891, ⟨reset_cert_a_892, ⟨reset_cert_a_893, ⟨reset_cert_a_894, reset_cert_a_895⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
