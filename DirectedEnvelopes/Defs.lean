import Mathlib.Tactic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Order.Lattice
import Mathlib.Data.Finset.Lattice.Fold

noncomputable section
open Finset

namespace DE

variable {n : ℕ} [NeZero n]

abbrev Wt (n : ℕ) := Fin n → Fin n → ℝ

def DC (w : Wt n) (r : Fin n → ℝ) : Prop :=
  ∀ θ i, r i - r θ ≤ w θ i

def LB (g r : Fin n → ℝ) : Prop := ∀ i, g i ≤ r i

def Feas (w : Wt n) (g r : Fin n → ℝ) : Prop := LB g r ∧ DC w r

structure Clos (w : Wt n) where
  d : Wt n
  diag : ∀ i, d i i = 0
  nn : ∀ i j, 0 ≤ d i j
  lew : ∀ i j, d i j ≤ w i j
  tri : ∀ i j k, d i k ≤ d i j + d j k
  tight : ∀ r, DC w r → DC d r

instance : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩

def envSol (d : Wt n) (g : Fin n → ℝ) (θ : Fin n) : ℝ :=
  univ.sup' univ_nonempty (fun j => g j - d θ j)

def CwMin (w : Wt n) (g r : Fin n → ℝ) : Prop :=
  Feas w g r ∧ ∀ r', Feas w g r' → ∀ θ, r θ ≤ r' θ

end DE
