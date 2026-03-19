import DirectedEnvelopes.Defs
import DirectedEnvelopes.Closure

noncomputable section
open Finset

namespace DE

variable {n : ℕ} [NeZero n]

theorem envSol_lb {w : Wt n} (C : Clos w) (g : Fin n → ℝ) :
    LB g (envSol C.d g) := by
  intro θ
  have : g θ - C.d θ θ ≤ envSol C.d g θ :=
    le_sup' (fun j => g j - C.d θ j) (mem_univ θ)
  simp [C.diag] at this
  exact this

theorem envSol_dc {w : Wt n} (C : Clos w) (g : Fin n → ℝ) :
    DC w (envSol C.d g) := by
  intro θ i
  apply le_trans _ (C.lew θ i)
  show envSol C.d g i - envSol C.d g θ ≤ C.d θ i
  simp only [envSol]
  rw [sub_le_iff_le_add]
  apply sup'_le
  intro j _
  have tri := C.tri θ i j
  have key := le_sup' (fun k => g k - C.d θ k) (mem_univ j)
  linarith

theorem envSol_feas {w : Wt n} (C : Clos w) (g : Fin n → ℝ) :
    Feas w g (envSol C.d g) :=
  ⟨envSol_lb C g, envSol_dc C g⟩

theorem envSol_min {w : Wt n} (C : Clos w) (g : Fin n → ℝ)
    (r : Fin n → ℝ) (hf : Feas w g r) (θ : Fin n) :
    envSol C.d g θ ≤ r θ := by
  simp only [envSol]
  apply sup'_le
  intro j _
  have hdc := C.tight r hf.2 θ j
  have hlb := hf.1 j
  linarith

theorem envelope {w : Wt n} (C : Clos w) (g : Fin n → ℝ) :
    CwMin w g (envSol C.d g) :=
  ⟨envSol_feas C g, fun r' hf' θ => envSol_min C g r' hf' θ⟩

end DE
