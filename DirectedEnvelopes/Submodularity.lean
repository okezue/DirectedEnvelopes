import DirectedEnvelopes.Defs
import Mathlib.Tactic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Order.MinMax
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax

noncomputable section
open Finset

namespace DE

variable {n : ℕ} [NeZero n]

def wedgeCost (μ : Fin n → ℝ) (c : Fin n → Fin n → ℝ)
    (φ : Fin n → ℝ → ℝ) (q : Fin n → ℝ) : ℝ :=
  ∑ θ : Fin n, μ θ * univ.sup' univ_nonempty (fun j => c θ j * φ j (q j))

private theorem join_term_le (c : Fin n → ℝ) (hc : ∀ j, 0 ≤ c j)
    (φ : Fin n → ℝ → ℝ) (hφ : ∀ j, Monotone (φ j))
    (q q' : Fin n → ℝ) (j : Fin n) :
    c j * φ j ((q ⊔ q') j) ≤
    max (c j * φ j (q j)) (c j * φ j (q' j)) := by
  simp only [Pi.sup_apply]
  rw [Monotone.map_max (hφ j), mul_max_of_nonneg _ _ (hc j)]

private theorem meet_term_le (c : Fin n → ℝ) (hc : ∀ j, 0 ≤ c j)
    (φ : Fin n → ℝ → ℝ) (hφ : ∀ j, Monotone (φ j))
    (q q' : Fin n → ℝ) (j : Fin n) :
    c j * φ j ((q ⊓ q') j) ≤
    min (c j * φ j (q j)) (c j * φ j (q' j)) := by
  simp only [Pi.inf_apply]
  rw [Monotone.map_min (hφ j), mul_min_of_nonneg _ _ (hc j)]

private theorem max_le_sup' (a b : Fin n → ℝ) (j : Fin n) :
    max (a j) (b j) ≤
    max (univ.sup' univ_nonempty a) (univ.sup' univ_nonempty b) :=
  max_le_max (le_sup' a (mem_univ j)) (le_sup' b (mem_univ j))

private theorem min_le_sup' (a b : Fin n → ℝ) (j : Fin n) :
    min (a j) (b j) ≤
    min (univ.sup' univ_nonempty a) (univ.sup' univ_nonempty b) :=
  min_le_min (le_sup' a (mem_univ j)) (le_sup' b (mem_univ j))

theorem fterm_submod (c : Fin n → ℝ) (hc : ∀ j, 0 ≤ c j)
    (φ : Fin n → ℝ → ℝ) (hφ : ∀ j, Monotone (φ j))
    (q q' : Fin n → ℝ) :
    univ.sup' univ_nonempty (fun j => c j * φ j (q j)) +
    univ.sup' univ_nonempty (fun j => c j * φ j (q' j)) ≥
    univ.sup' univ_nonempty (fun j => c j * φ j ((q ⊔ q') j)) +
    univ.sup' univ_nonempty (fun j => c j * φ j ((q ⊓ q') j)) := by
  set a := fun j => c j * φ j (q j)
  set b := fun j => c j * φ j (q' j)
  set A := univ.sup' univ_nonempty a
  set B := univ.sup' univ_nonempty b
  have hJ : univ.sup' univ_nonempty (fun j => c j * φ j ((q ⊔ q') j)) ≤ max A B := by
    apply sup'_le; intro j _
    calc c j * φ j ((q ⊔ q') j)
        ≤ max (a j) (b j) := join_term_le c hc φ hφ q q' j
      _ ≤ max A B := max_le_sup' a b j
  have hM : univ.sup' univ_nonempty (fun j => c j * φ j ((q ⊓ q') j)) ≤ min A B := by
    apply sup'_le; intro j _
    calc c j * φ j ((q ⊓ q') j)
        ≤ min (a j) (b j) := meet_term_le c hc φ hφ q q' j
      _ ≤ min A B := min_le_sup' a b j
  linarith [max_add_min A B]

theorem wedgeCost_submod (μ : Fin n → ℝ) (hμ : ∀ θ, 0 ≤ μ θ)
    (c : Fin n → Fin n → ℝ) (hc : ∀ θ j, 0 ≤ c θ j)
    (φ : Fin n → ℝ → ℝ) (hφ : ∀ j, Monotone (φ j))
    (q q' : Fin n → ℝ) :
    wedgeCost μ c φ q + wedgeCost μ c φ q' ≥
    wedgeCost μ c φ (q ⊔ q') + wedgeCost μ c φ (q ⊓ q') := by
  simp only [wedgeCost]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro θ _
  rw [← mul_add, ← mul_add]
  exact mul_le_mul_of_nonneg_left (fterm_submod (c θ) (hc θ) φ hφ q q') (hμ θ)

end DE
