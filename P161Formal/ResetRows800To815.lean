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

theorem reset_cert_a_800 : resetParentTest 800 = true := by
  decide

theorem reset_cert_a_801 : resetParentTest 801 = true := by
  decide

theorem reset_cert_a_802 : resetParentTest 802 = true := by
  decide

theorem reset_cert_a_803 : resetParentTest 803 = true := by
  decide

theorem reset_cert_a_804 : resetParentTest 804 = true := by
  decide

theorem reset_cert_a_805 : resetParentTest 805 = true := by
  decide

theorem reset_cert_a_806 : resetParentTest 806 = true := by
  decide

theorem reset_cert_a_807 : resetParentTest 807 = true := by
  decide

theorem reset_cert_a_808 : resetParentTest 808 = true := by
  decide

theorem reset_cert_a_809 : resetParentTest 809 = true := by
  decide

theorem reset_cert_a_810 : resetParentTest 810 = true := by
  decide

theorem reset_cert_a_811 : resetParentTest 811 = true := by
  decide

theorem reset_cert_a_812 : resetParentTest 812 = true := by
  decide

theorem reset_cert_a_813 : resetParentTest 813 = true := by
  decide

theorem reset_cert_a_814 : resetParentTest 814 = true := by
  decide

theorem reset_cert_a_815 : resetParentTest 815 = true := by
  decide

def resetParents800To815 : List ℕ := [800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815]

theorem reset_block_800_to_815 : resetParents800To815.all resetParentTest = true := by
  simp only [resetParents800To815, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_800, ⟨reset_cert_a_801, ⟨reset_cert_a_802, ⟨reset_cert_a_803, ⟨reset_cert_a_804, ⟨reset_cert_a_805, ⟨reset_cert_a_806, ⟨reset_cert_a_807, ⟨reset_cert_a_808, ⟨reset_cert_a_809, ⟨reset_cert_a_810, ⟨reset_cert_a_811, ⟨reset_cert_a_812, ⟨reset_cert_a_813, ⟨reset_cert_a_814, reset_cert_a_815⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
