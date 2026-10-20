module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Fin.Basic
public import Lean.Elab.Tactic.Omega

/-!
Identical-mark finite-stock stopping on one uninterrupted history. `S` retains
the complete physical state, time and global ledgers; `M` retains the complete
physical mark. No boundary resets a counter or starts another stock allocation.
The first attempted disallowed next state goes to an absorbing failure state.
The source path adapter and high-probability stock estimates are separate.
-/

@[expose] public section
namespace P161Formal

def unlimitedRun {S M : Type} (step : S → M → S) (initial : S) (marks : ℕ → M) : ℕ → S
  | 0 => initial
  | n + 1 => step (unlimitedRun step initial marks n) (marks n)

def stockStoppedRun {S M : Type} (allowed : S → Prop) [DecidablePred allowed]
    (step : S → M → S) (initial : S) (marks : ℕ → M) : ℕ → Option S
  | 0 => if allowed initial then some initial else none
  | n + 1 => match stockStoppedRun allowed step initial marks n with
    | none => none
    | some x => let y := step x (marks n); if allowed y then some y else none

theorem identical_marks_until_exhaustion {S M : Type} (allowed : S → Prop)
    [DecidablePred allowed] (step : S → M → S) (initial : S) (marks : ℕ → M) (n : ℕ)
    (hgood : ∀ k, k ≤ n → allowed (unlimitedRun step initial marks k)) :
    stockStoppedRun allowed step initial marks n = some (unlimitedRun step initial marks n) := by
  induction n with
  | zero =>
      have h := hgood 0 (by omega)
      change allowed initial at h
      simp only [stockStoppedRun, ite_eq_left h, unlimitedRun]
  | succ n ih =>
      have hbefore := ih (fun k hk => hgood k (by omega))
      have hnext := hgood (n + 1) (by omega)
      change allowed (step (unlimitedRun step initial marks n) (marks n)) at hnext
      simp only [stockStoppedRun, hbefore, ite_eq_left hnext, unlimitedRun]

theorem identical_mark_prefix {S M : Type} (allowed : S → Prop)
    [DecidablePred allowed] (step : S → M → S) (initial : S) (marks : ℕ → M) (n : ℕ)
    (hgood : ∀ k, k ≤ n → allowed (unlimitedRun step initial marks k)) :
    (fun k : Fin (n + 1) => stockStoppedRun allowed step initial marks k.val) =
      (fun k : Fin (n + 1) => some (unlimitedRun step initial marks k.val)) := by
  funext k
  apply identical_marks_until_exhaustion
  intro j hj
  exact hgood j (by have hk := k.isLt; omega)

/-- Any joint event on the complete prefix transfers. This includes timing,
service, both-daughter and renewal observations once those are in the state. -/
theorem stock_joint_event_transfer {S M : Type} (allowed : S → Prop)
    [DecidablePred allowed] (step : S → M → S) (initial : S) (marks : ℕ → M) (n : ℕ)
    (mission : (Fin (n + 1) → Option S) → Prop)
    (hgood : ∀ k, k ≤ n → allowed (unlimitedRun step initial marks k))
    (hmission : mission (fun k => some (unlimitedRun step initial marks k.val))) :
    mission (fun k => stockStoppedRun allowed step initial marks k.val) := by
  rw [identical_mark_prefix allowed step initial marks n hgood]
  exact hmission

theorem stock_never_accepts_excess {S M : Type} (allowed : S → Prop)
    [DecidablePred allowed] (step : S → M → S) (initial : S) (marks : ℕ → M)
    (n : ℕ) (x : S) (hx : stockStoppedRun allowed step initial marks n = some x) :
    allowed x := by
  cases n with
  | zero =>
      by_cases h : allowed initial
      · simp [stockStoppedRun, h] at hx
        subst x
        exact h
      · simp [stockStoppedRun, h] at hx
  | succ n =>
      cases hprev : stockStoppedRun allowed step initial marks n with
      | none => simp [stockStoppedRun, hprev] at hx
      | some y =>
          by_cases h : allowed (step y (marks n))
          · simp [stockStoppedRun, hprev, h] at hx
            subst x
            exact h
          · simp [stockStoppedRun, hprev, h] at hx

theorem stock_failure_absorbs {S M : Type} (allowed : S → Prop)
    [DecidablePred allowed] (step : S → M → S) (initial : S) (marks : ℕ → M)
    (n : ℕ) (hn : stockStoppedRun allowed step initial marks n = none) (k : ℕ) :
    stockStoppedRun allowed step initial marks (n + k) = none := by
  induction k with
  | zero => simpa using hn
  | succ k ih =>
      change (match stockStoppedRun allowed step initial marks (n + k) with
        | none => none
        | some x => if allowed (step x (marks (n + k))) then
            some (step x (marks (n + k))) else none) = none
      rw [ih]

end P161Formal
