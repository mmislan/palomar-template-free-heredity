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

theorem reset_cert_a_2016 : resetParentTest 2016 = true := by
  decide

theorem reset_cert_a_2017 : resetParentTest 2017 = true := by
  decide

theorem reset_cert_a_2018 : resetParentTest 2018 = true := by
  decide

theorem reset_cert_a_2019 : resetParentTest 2019 = true := by
  decide

theorem reset_cert_a_2020 : resetParentTest 2020 = true := by
  decide

theorem reset_cert_a_2021 : resetParentTest 2021 = true := by
  decide

theorem reset_cert_a_2022 : resetParentTest 2022 = true := by
  decide

theorem reset_cert_a_2023 : resetParentTest 2023 = true := by
  decide

theorem reset_cert_a_2024 : resetParentTest 2024 = true := by
  decide

theorem reset_cert_a_2025 : resetParentTest 2025 = true := by
  decide

theorem reset_cert_a_2026 : resetParentTest 2026 = true := by
  decide

theorem reset_cert_a_2027 : resetParentTest 2027 = true := by
  decide

theorem reset_cert_a_2028 : resetParentTest 2028 = true := by
  decide

theorem reset_cert_a_2029 : resetParentTest 2029 = true := by
  decide

theorem reset_cert_a_2030 : resetParentTest 2030 = true := by
  decide

theorem reset_cert_a_2031 : resetParentTest 2031 = true := by
  decide

def resetParents2016To2031 : List ℕ := [2016, 2017, 2018, 2019, 2020, 2021, 2022, 2023, 2024, 2025, 2026, 2027, 2028, 2029, 2030, 2031]

theorem reset_block_2016_to_2031 : resetParents2016To2031.all resetParentTest = true := by
  simp only [resetParents2016To2031, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_2016, ⟨reset_cert_a_2017, ⟨reset_cert_a_2018, ⟨reset_cert_a_2019, ⟨reset_cert_a_2020, ⟨reset_cert_a_2021, ⟨reset_cert_a_2022, ⟨reset_cert_a_2023, ⟨reset_cert_a_2024, ⟨reset_cert_a_2025, ⟨reset_cert_a_2026, ⟨reset_cert_a_2027, ⟨reset_cert_a_2028, ⟨reset_cert_a_2029, ⟨reset_cert_a_2030, reset_cert_a_2031⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
