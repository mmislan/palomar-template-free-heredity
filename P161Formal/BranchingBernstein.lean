module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-!
Uniform polynomial certificate for the beta4m high-count branching envelope.
The49 coefficients are data; all polynomial identities and signs are checked
by ordinary Lean tactics. This is not a site/source or mission theorem.
This source is pending until a strict source-bound receipt exists.
-/

@[expose] public section
namespace P161Formal

structure BernsteinSixData where
  b0 : ℚ
  b1 : ℚ
  b2 : ℚ
  b3 : ℚ
  b4 : ℚ
  b5 : ℚ
  b6 : ℚ

abbrev BernsteinSixData.Nonnegative (b : BernsteinSixData) : Prop :=
  0 ≤ b.b0 ∧ 0 ≤ b.b1 ∧ 0 ≤ b.b2 ∧ 0 ≤ b.b3 ∧ 0 ≤ b.b4 ∧ 0 ≤ b.b5 ∧ 0 ≤ b.b6

def BernsteinSixData.eval (b : BernsteinSixData) (t : ℚ) : ℚ :=
  b.b0 * (1-t)^6 + 6*b.b1*t*(1-t)^5 + 15*b.b2*t^2*(1-t)^4 +
    20*b.b3*t^3*(1-t)^3 + 15*b.b4*t^4*(1-t)^2 + 6*b.b5*t^5*(1-t) + b.b6*t^6

theorem bernstein_six_nonnegative (b : BernsteinSixData) (hb : b.Nonnegative)
    (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ b.eval t := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := hb
  have ht : 0 ≤ 1-t := by linarith
  unfold BernsteinSixData.eval
  positivity

def branchingClearedPolynomial (x : ℚ) : ℚ :=
  13*x^6 + 273*x^5 + 2275*x^4 + 127190805*x^3 - 37936305647138*x^2 +
    29093452248685932*x - 271904738941430640

def branchingDenominatorSix (x : ℚ) : ℚ :=
  (x+1)*(x+2)*(x+3)*(x+4)*(x+5)*(x+6)

def branchingFueledNumerator (x : ℚ) : ℚ :=
  36536907/2500 - 10008067509*x/6400000 + 52199939*x^2/25600000 - 7*x^3/1024000

theorem branching_cleared_identity (x : ℚ) : branchingClearedPolynomial x =
    13 * branchingDenominatorSix x - 10000000*1860480*branchingFueledNumerator x := by
  unfold branchingClearedPolynomial branchingDenominatorSix branchingFueledNumerator
  ring

theorem bernstein_interval_sound (b : BernsteinSixData) (P : ℚ → ℚ) (lo hi : ℚ)
    (hw : 0 < hi-lo) (hb : b.Nonnegative)
    (hid : ∀ x, P x = b.eval ((x-lo)/(hi-lo)))
    (x : ℚ) (hlo : lo ≤ x) (hhi : x ≤ hi) : 0 ≤ P x := by
  rw [hid]
  apply bernstein_six_nonnegative b hb
  · exact div_nonneg (by linarith) (le_of_lt hw)
  · exact (div_le_one hw).mpr (by linarith)

def branchingBernstein13To128 : BernsteinSixData :=
  ⟨99899184304406520, 638619997752214315, (3431694062227751570 / 3), (6462972051437137205 / 4), (6162496054130376290 / 3), 2459180345621458170, 2830842621122628240⟩

theorem branchingBernstein13To128_nonnegative : branchingBernstein13To128.Nonnegative := by
  norm_num [BernsteinSixData.Nonnegative, branchingBernstein13To128]

theorem branchingBernstein13To128_identity (x : ℚ) : branchingClearedPolynomial x =
    branchingBernstein13To128.eval ((x-13)/(128-13)) := by
  norm_num [branchingClearedPolynomial, BernsteinSixData.eval, branchingBernstein13To128]
  ring

def branchingBernstein128To256 : BernsteinSixData :=
  ⟨2830842621122628240, 3244518892984800144, (54253134341634518128 / 15), (19739940671323749328 / 5), (63569881399129668208 / 15), 4487142245656770448, 4695928329862250640⟩

theorem branchingBernstein128To256_nonnegative : branchingBernstein128To256.Nonnegative := by
  norm_num [BernsteinSixData.Nonnegative, branchingBernstein128To256]

theorem branchingBernstein128To256_identity (x : ℚ) : branchingClearedPolynomial x =
    branchingBernstein128To256.eval ((x-128)/(256-128)) := by
  norm_num [branchingClearedPolynomial, BernsteinSixData.eval, branchingBernstein128To256]
  ring

def branchingBernstein256To512 : BernsteinSixData :=
  ⟨4695928329862250640, 5113500498273211024, (80544245909703828592 / 15), (27340969623041839312 / 5), (81253663191619092592 / 15), 5230914131897735824, 4940188016705105040⟩

theorem branchingBernstein256To512_nonnegative : branchingBernstein256To512.Nonnegative := by
  norm_num [BernsteinSixData.Nonnegative, branchingBernstein256To512]

theorem branchingBernstein256To512_identity (x : ℚ) : branchingClearedPolynomial x =
    branchingBernstein256To512.eval ((x-256)/(512-256)) := by
  norm_num [branchingClearedPolynomial, BernsteinSixData.eval, branchingBernstein256To512]
  ring

def branchingBernstein512To768 : BernsteinSixData :=
  ⟨4940188016705105040, 4649461901512474256, (63810096280061245552 / 15), (18919029514536398032 / 5), (49255232253869921392 / 15), 2820662795240949392, 2495008862727100560⟩

theorem branchingBernstein512To768_nonnegative : branchingBernstein512To768.Nonnegative := by
  norm_num [BernsteinSixData.Nonnegative, branchingBernstein512To768]

theorem branchingBernstein512To768_identity (x : ℚ) : branchingClearedPolynomial x =
    branchingBernstein512To768.eval ((x-512)/(768-512)) := by
  norm_num [branchingClearedPolynomial, BernsteinSixData.eval, branchingBernstein512To768]
  ring

def branchingBernstein768To1024 : BernsteinSixData :=
  ⟨2495008862727100560, 2169354930213251728, (29715996303038991472 / 15), (10152021787830503632 / 5), (36762947362914232432 / 15), 3420198177534685840, 5175112443826554000⟩

theorem branchingBernstein768To1024_nonnegative : branchingBernstein768To1024.Nonnegative := by
  norm_num [BernsteinSixData.Nonnegative, branchingBernstein768To1024]

theorem branchingBernstein768To1024_identity (x : ℚ) : branchingClearedPolynomial x =
    branchingBernstein768To1024.eval ((x-768)/(1024-768)) := by
  norm_num [branchingClearedPolynomial, BernsteinSixData.eval, branchingBernstein768To1024]
  ring

def branchingBernstein1024To1536 : BernsteinSixData :=
  ⟨5175112443826554000, 8684940976410290320, (230056297411998268528 / 15), (135125866034546373328 / 5), (698789820379794011248 / 15), 78269455810789111952, 128442801806386338960⟩

theorem branchingBernstein1024To1536_nonnegative : branchingBernstein1024To1536.Nonnegative := by
  norm_num [BernsteinSixData.Nonnegative, branchingBernstein1024To1536]

theorem branchingBernstein1024To1536_identity (x : ℚ) : branchingClearedPolynomial x =
    branchingBernstein1024To1536.eval ((x-1024)/(1536-1024)) := by
  norm_num [branchingClearedPolynomial, BernsteinSixData.eval, branchingBernstein1024To1536]
  ring

def branchingBernstein1536To2048 : BernsteinSixData :=
  ⟨128442801806386338960, 178616147801983565968, (3709190580115627631728 / 15), (1703998498333148490448 / 5), (7014924846051889192048 / 15), 639171230655352852624, 870394223283332576400⟩

theorem branchingBernstein1536To2048_nonnegative : branchingBernstein1536To2048.Nonnegative := by
  norm_num [BernsteinSixData.Nonnegative, branchingBernstein1536To2048]

theorem branchingBernstein1536To2048_identity (x : ℚ) : branchingClearedPolynomial x =
    branchingBernstein1536To2048.eval ((x-1536)/(2048-1536)) := by
  norm_num [branchingClearedPolynomial, BernsteinSixData.eval, branchingBernstein1536To2048]
  ring

theorem branching_cleared_nonnegative (x : ℚ) (hx0 : 13 ≤ x) (hx1 : x ≤ 2048) :
    0 ≤ branchingClearedPolynomial x := by
  by_cases h0 : x ≤ 128
  · exact bernstein_interval_sound branchingBernstein13To128 branchingClearedPolynomial 13 128
      (by norm_num) branchingBernstein13To128_nonnegative branchingBernstein13To128_identity x (by linarith) h0
  by_cases h1 : x ≤ 256
  · exact bernstein_interval_sound branchingBernstein128To256 branchingClearedPolynomial 128 256
      (by norm_num) branchingBernstein128To256_nonnegative branchingBernstein128To256_identity x (by linarith) h1
  by_cases h2 : x ≤ 512
  · exact bernstein_interval_sound branchingBernstein256To512 branchingClearedPolynomial 256 512
      (by norm_num) branchingBernstein256To512_nonnegative branchingBernstein256To512_identity x (by linarith) h2
  by_cases h3 : x ≤ 768
  · exact bernstein_interval_sound branchingBernstein512To768 branchingClearedPolynomial 512 768
      (by norm_num) branchingBernstein512To768_nonnegative branchingBernstein512To768_identity x (by linarith) h3
  by_cases h4 : x ≤ 1024
  · exact bernstein_interval_sound branchingBernstein768To1024 branchingClearedPolynomial 768 1024
      (by norm_num) branchingBernstein768To1024_nonnegative branchingBernstein768To1024_identity x (by linarith) h4
  by_cases h5 : x ≤ 1536
  · exact bernstein_interval_sound branchingBernstein1024To1536 branchingClearedPolynomial 1024 1536
      (by norm_num) branchingBernstein1024To1536_nonnegative branchingBernstein1024To1536_identity x (by linarith) h5
  · exact bernstein_interval_sound branchingBernstein1536To2048 branchingClearedPolynomial 1536 2048
      (by norm_num) branchingBernstein1536To2048_nonnegative branchingBernstein1536To2048_identity x (by linarith) hx1

theorem branching_high_rational_bound (x : ℚ) (hx0 : 13 ≤ x) (hx1 : x ≤ 2048) :
    1860480 * branchingFueledNumerator x / branchingDenominatorSix x ≤ 13/10000000 := by
  have hx : 0 < x := by linarith
  have hd : 0 < branchingDenominatorSix x := by
    unfold branchingDenominatorSix
    positivity
  have hp := branching_cleared_nonnegative x hx0 hx1
  rw [branching_cleared_identity] at hp
  apply (div_le_iff₀ hd).mpr
  nlinarith

end P161Formal
