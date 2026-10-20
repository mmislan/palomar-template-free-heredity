module

public import proofs.HeritableCompositions.BinomialMoment

@[expose] public section

namespace CompositionalMemory
open HeritableCompositions

noncomputable def binomialAverage (n : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n+1),fairBinomialWeight n k*f ((k : ℝ)-(n : ℝ)/2)

theorem binomialAverage_const (n : ℕ) (c : ℝ) : binomialAverage n (fun _ => c)=c := by
  unfold binomialAverage
  rw [← Finset.sum_mul,fair_binomial_sum,one_mul]

theorem binomialAverage_add (n : ℕ) (f g : ℝ → ℝ) :
    binomialAverage n (fun x => f x+g x)=binomialAverage n f+binomialAverage n g := by
  simp only [binomialAverage,mul_add,Finset.sum_add_distrib]

theorem binomialAverage_scale (n : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    binomialAverage n (fun x => c*f x)=c*binomialAverage n f := by
  simp only [binomialAverage,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem binomialAverage_succ (n : ℕ) (f : ℝ → ℝ) :
    binomialAverage (n+1) f=
      (binomialAverage n (fun x => f (x-1/2))+binomialAverage n (fun x => f (x+1/2)))/2 := by
  have hs := Finset.sum_choose_succ_mul (fun k _ => f ((k : ℝ)-((n : ℝ)+1)/2)) n
  unfold binomialAverage fairBinomialWeight
  simp_rw [div_mul_eq_mul_div,← Finset.sum_div]
  rw [Nat.cast_add,Nat.cast_one,pow_succ,hs]
  have h1 : (∑ k ∈ Finset.range (n+1),(n.choose k : ℝ)*f ((k : ℝ)-((n : ℝ)+1)/2))=
      ∑ k ∈ Finset.range (n+1),(n.choose k : ℝ)*f (((k : ℝ)-(n : ℝ)/2)-1/2) := by
    apply Finset.sum_congr rfl
    intro k _
    congr 2
    ring
  have h2 : (∑ k ∈ Finset.range (n+1),(n.choose k : ℝ)*f (((k+1 : ℕ) : ℝ)-((n : ℝ)+1)/2))=
      ∑ k ∈ Finset.range (n+1),(n.choose k : ℝ)*f (((k : ℝ)-(n : ℝ)/2)+1/2) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.cast_add,Nat.cast_one]
    congr 2
    ring
  rw [h1,h2]
  ring

theorem binomial_centered_moments (n : ℕ) :
    binomialAverage n (fun x => x)=0 ∧
    binomialAverage n (fun x => x^2)=(n : ℝ)/4 ∧
    binomialAverage n (fun x => x^3)=0 ∧
    binomialAverage n (fun x => x^4)=(3*(n : ℝ)^2-2*n)/16 := by
  induction n with
  | zero => norm_num [binomialAverage,fairBinomialWeight]
  | succ n ih =>
    have hrec (f : ℝ → ℝ) : binomialAverage (n+1) f=
        binomialAverage n (fun x => f (x-1/2)+f (x+1/2))/2 := by
      rw [binomialAverage_succ,binomialAverage_add]
    have h1 : (fun x : ℝ => (x-1/2)+(x+1/2))=(fun x => 2*x) := by funext x; ring
    have h2 : (fun x : ℝ => (x-1/2)^2+(x+1/2)^2)=(fun x => 2*x^2+1/2) := by funext x; ring
    have h3 : (fun x : ℝ => (x-1/2)^3+(x+1/2)^3)=(fun x => 2*x^3+(3/2)*x) := by funext x; ring
    have h4 : (fun x : ℝ => (x-1/2)^4+(x+1/2)^4)=(fun x => 2*x^4+3*x^2+1/8) := by funext x; ring
    constructor
    · rw [hrec,h1,binomialAverage_scale,ih.1]; norm_num
    constructor
    · rw [hrec,h2,binomialAverage_add,binomialAverage_scale,binomialAverage_const,ih.2.1]
      push_cast; ring
    constructor
    · rw [hrec,h3,binomialAverage_add,binomialAverage_scale,binomialAverage_scale,ih.1,ih.2.2.1]; norm_num
    · rw [hrec,h4,binomialAverage_add,binomialAverage_add,binomialAverage_scale,binomialAverage_scale,
        binomialAverage_const,ih.2.1,ih.2.2.2]
      push_cast; ring

end CompositionalMemory
