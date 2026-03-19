import DirectedEnvelopes.Defs
import Mathlib.Tactic
import Mathlib.Order.FixedPoints

noncomputable section
open Finset

namespace DE

variable {n : ℕ} [NeZero n]

def wedgeOp (α : Fin n → Fin n → ℝ) (g : Fin n → ℝ) (y : Fin n → ℝ)
    (θ : Fin n) : ℝ :=
  max (g θ) (univ.sup' univ_nonempty (fun i => α θ i * y i))

theorem wedgeOp_mono (α : Fin n → Fin n → ℝ) (hα : ∀ θ i, 0 ≤ α θ i)
    (g : Fin n → ℝ) : Monotone (fun y => fun θ => wedgeOp α g y θ) := by
  intro y₁ y₂ h θ
  simp only [wedgeOp]
  apply max_le_max_left
  apply sup'_le
  intro i _
  have hi := mul_le_mul_of_nonneg_left (h i) (hα θ i)
  exact le_trans hi (le_sup' (f := fun j => α θ j * y₂ j) (mem_univ i))

theorem postfixed_iff (α : Fin n → Fin n → ℝ) (g y : Fin n → ℝ) :
    (∀ θ, wedgeOp α g y θ ≤ y θ) ↔
    (∀ θ, g θ ≤ y θ) ∧ (∀ θ i, α θ i * y i ≤ y θ) := by
  constructor
  · intro h
    refine ⟨fun θ => ?_, fun θ i => ?_⟩
    · exact le_trans (le_max_left _ _) (h θ)
    · exact le_trans
        (le_trans (le_sup' (f := fun j => α θ j * y j) (mem_univ i)) (le_max_right _ _))
        (h θ)
  · intro ⟨hg, hα⟩ θ
    exact max_le (hg θ) (sup'_le _ _ (fun i _ => hα θ i))

def iterOp (α : Fin n → Fin n → ℝ) (g : Fin n → ℝ) :
    ℕ → (Fin n → ℝ)
  | 0 => g
  | k + 1 => fun θ => wedgeOp α g (iterOp α g k) θ

theorem iterOp_mono (α : Fin n → Fin n → ℝ) (hα : ∀ θ i, 0 ≤ α θ i)
    (g : Fin n → ℝ) : ∀ k, iterOp α g k ≤ iterOp α g (k + 1) := by
  intro k
  induction k with
  | zero =>
    intro θ
    simp only [iterOp, wedgeOp]
    exact le_max_left _ _
  | succ k ih =>
    intro θ
    simp only [iterOp]
    exact wedgeOp_mono α hα g ih θ

theorem iterOp_le_supersol (α : Fin n → Fin n → ℝ) (hα : ∀ θ i, 0 ≤ α θ i)
    (g : Fin n → ℝ) (y : Fin n → ℝ)
    (hy : ∀ θ, wedgeOp α g y θ ≤ y θ) :
    ∀ k, iterOp α g k ≤ y := by
  intro k
  induction k with
  | zero =>
    intro θ
    simp only [iterOp]
    exact ((postfixed_iff α g y).mp hy).1 θ
  | succ k ih =>
    intro θ
    simp only [iterOp]
    calc wedgeOp α g (iterOp α g k) θ
        ≤ wedgeOp α g y θ := wedgeOp_mono α hα g ih θ
      _ ≤ y θ := hy θ

theorem iterOp_ic (α : Fin n → Fin n → ℝ) (hα : ∀ θ i, 0 ≤ α θ i)
    (g : Fin n → ℝ) (k : ℕ) :
    ∀ θ i, α θ i * iterOp α g k i ≤ iterOp α g (k + 1) θ := by
  intro θ i
  simp only [iterOp, wedgeOp]
  exact le_trans (le_sup' (f := fun j => α θ j * iterOp α g k j) (mem_univ i))
    (le_max_right _ _)

end DE
