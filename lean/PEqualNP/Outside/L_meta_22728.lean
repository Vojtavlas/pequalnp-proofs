import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22728 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1883445 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 22] }], output := 23 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
