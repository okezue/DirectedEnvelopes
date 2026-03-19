import DirectedEnvelopes.Defs

noncomputable section
open Finset

namespace DE

variable {n : ℕ} [NeZero n]

theorem closure_backward {w : Wt n} (C : Clos w) (r : Fin n → ℝ)
    (h : DC C.d r) : DC w r := by
  intro θ i
  calc r i - r θ ≤ C.d θ i := h θ i
    _ ≤ w θ i := C.lew θ i

theorem closure_equiv {w : Wt n} (C : Clos w) (r : Fin n → ℝ) :
    DC w r ↔ DC C.d r :=
  ⟨C.tight r, closure_backward C r⟩

end DE
