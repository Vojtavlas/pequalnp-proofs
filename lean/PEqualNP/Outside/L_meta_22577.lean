import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22577_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C : Circuit :=
  { gates := [
    ⟨GateOp.or, [1, 4]⟩,
    ⟨GateOp.not, [6]⟩,
    ⟨GateOp.and, [0, 7]⟩,
    ⟨GateOp.or, [1, 3]⟩,
    ⟨GateOp.and, [2, 9]⟩,
    ⟨GateOp.and, [1, 4]⟩,
    ⟨GateOp.or, [8, 10]⟩,
    ⟨GateOp.or, [12, 11]⟩
    ]
    output := 13 }

theorem C_fanInTwo : FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem C_size : C.size ≤ 8 := by decide

theorem C_rep : ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34093 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  intro i j
  revert i j
  decide

end PEqualNP.Outside.L_meta_22577_aux

theorem PEqualNP.Outside.L_meta_22577 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34093 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_22577_aux.C, PEqualNP.Outside.L_meta_22577_aux.C_fanInTwo, PEqualNP.Outside.L_meta_22577_aux.C_size, PEqualNP.Outside.L_meta_22577_aux.C_rep⟩
