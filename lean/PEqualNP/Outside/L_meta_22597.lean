import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22597 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16916 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 13] }], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
