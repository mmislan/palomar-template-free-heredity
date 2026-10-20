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

theorem reset_cert_a_848 : resetParentTest 848 = true := by
  decide

theorem reset_cert_a_849 : resetParentTest 849 = true := by
  decide

theorem reset_cert_a_850 : resetParentTest 850 = true := by
  decide

theorem reset_cert_a_851 : resetParentTest 851 = true := by
  decide

theorem reset_cert_a_852 : resetParentTest 852 = true := by
  decide

theorem reset_cert_a_853 : resetParentTest 853 = true := by
  decide

theorem reset_cert_a_854 : resetParentTest 854 = true := by
  decide

theorem reset_cert_a_855 : resetParentTest 855 = true := by
  decide

theorem reset_cert_a_856 : resetParentTest 856 = true := by
  decide

theorem reset_cert_a_857 : resetParentTest 857 = true := by
  decide

theorem reset_cert_a_858 : resetParentTest 858 = true := by
  decide

theorem reset_cert_a_859 : resetParentTest 859 = true := by
  decide

theorem reset_cert_a_860 : resetParentTest 860 = true := by
  decide

theorem reset_cert_a_861 : resetParentTest 861 = true := by
  decide

theorem reset_cert_a_862 : resetParentTest 862 = true := by
  decide

theorem reset_cert_a_863 : resetParentTest 863 = true := by
  decide

def resetParents848To863 : List ℕ := [848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863]

theorem reset_block_848_to_863 : resetParents848To863.all resetParentTest = true := by
  simp only [resetParents848To863, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_848, ⟨reset_cert_a_849, ⟨reset_cert_a_850, ⟨reset_cert_a_851, ⟨reset_cert_a_852, ⟨reset_cert_a_853, ⟨reset_cert_a_854, ⟨reset_cert_a_855, ⟨reset_cert_a_856, ⟨reset_cert_a_857, ⟨reset_cert_a_858, ⟨reset_cert_a_859, ⟨reset_cert_a_860, ⟨reset_cert_a_861, ⟨reset_cert_a_862, reset_cert_a_863⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
