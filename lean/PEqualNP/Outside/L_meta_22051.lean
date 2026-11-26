import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22051 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (818745 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [18, 20] }], output := 21 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
