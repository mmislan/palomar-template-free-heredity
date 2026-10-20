module

public import proofs.HybridCTMCInfrastructure.SkeletonPaths
public import proofs.HybridCTMCInfrastructure.TimedProcess
public import Mathlib.Data.List.OfFn

@[expose] public section

/-! Exact visited prefixes and the forward recursion of the existing finite
trajectory PMF. All statements are uniform in the prefix length. -/
namespace HybridCTMC
open MeasureTheory ProbabilityTheory
open scoped Classical
noncomputable section

theorem pmf_bind_congr_support {A B : Type*} (p : PMF A) (f g : A → PMF B)
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  apply PMF.ext
  intro b
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro a
  by_cases ha : p a = 0
  · simp [ha]
  · rw [h a (by simpa only [PMF.mem_support_iff] using ha)]

namespace Kernel
variable {S : Type*}

def statePrefix (n : ℕ) (w : ℕ → ℝ × S) : List S :=
  List.ofFn (fun i : Fin (n+1) => (w i).2)

theorem statePrefix_zero (w : ℕ → ℝ × S) : statePrefix 0 w = [(w 0).2] := by
  simp [statePrefix, List.ofFn_succ]

theorem statePrefix_succ (n : ℕ) (w : ℕ → ℝ × S) :
    statePrefix (n+1) w = statePrefix n w ++ [(w (n+1)).2] := by
  simpa only [statePrefix, List.concat_eq_append, Fin.val_castSucc, Fin.val_last] using
    (List.ofFn_succ' (fun i : Fin (n+1+1) => (w i).2))

theorem mem_statePrefix (n : ℕ) (w : ℕ → ℝ × S) (s : S) :
    s ∈ statePrefix n w ↔ ∃ i ≤ n, (w i).2 = s := by
  simp only [statePrefix, List.mem_ofFn]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, Nat.le_of_lt_succ i.isLt, hi⟩
  · rintro ⟨i, hi, he⟩
    exact ⟨⟨i, Nat.lt_succ_of_le hi⟩, he⟩

variable [Fintype S]

theorem trajectory_support_nonempty (K : HybridCTMC.Kernel S) (n : ℕ) (x : S)
    (xs : List S) (hx : xs ∈ (K.trajectory n x).support) : xs ≠ [] := by
  cases n with
  | zero =>
    have he : xs = [x] := by simpa only [trajectory, PMF.mem_support_pure_iff] using hx
    rw [he]
    exact List.cons_ne_nil _ _
  | succ n =>
    obtain ⟨y, _, hy⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
    obtain ⟨ys, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
    rw [← he]
    exact List.cons_ne_nil _ _

theorem trajectory_snoc (K : HybridCTMC.Kernel S) (n : ℕ) (x : S) :
    K.trajectory (n+1) x = (K.trajectory n x).bind
      (fun xs => (K.pmf (xs.getLastD x)).map (fun y => xs ++ [y])) := by
  induction n generalizing x with
  | zero => simp [trajectory, PMF.map, PMF.pure_bind, Function.comp_def]
  | succ n ih =>
    calc
      K.trajectory (n+1+1) x = (K.pmf x).bind
          (fun y => (K.trajectory (n+1) y).map (List.cons x)) := rfl
      _ = (K.pmf x).bind (fun y =>
          ((K.trajectory n y).bind
            (fun xs => (K.pmf (xs.getLastD y)).map (fun z => xs ++ [z]))).map
              (List.cons x)) := by simp_rw [ih]
      _ = (K.pmf x).bind (fun y => (K.trajectory n y).bind
          (fun xs => (K.pmf (xs.getLastD y)).map (fun z => x :: (xs ++ [z])))) := by
        simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
      _ = (K.pmf x).bind (fun y => (K.trajectory n y).bind
          (fun xs => (K.pmf ((x :: xs).getLastD x)).map
            (fun z => (x :: xs) ++ [z]))) := by
        apply congrArg (fun f => (K.pmf x).bind f)
        funext y
        apply pmf_bind_congr_support
        intro xs hx
        have hn := K.trajectory_support_nonempty n y xs hx
        cases xs with
        | nil => exact (hn rfl).elim
        | cons a ys => simp [List.getLast?_eq_getLast_of_ne_nil hn]
      _ = (K.trajectory (n+1) x).bind
          (fun xs => (K.pmf (xs.getLastD x)).map (fun y => xs ++ [y])) := by
        change _ = ((K.pmf x).bind (fun y => (K.trajectory n y).map (List.cons x))).bind _
        rw [PMF.bind_bind]
        simp only [PMF.bind_map, Function.comp_def]

end Kernel
end
end HybridCTMC
