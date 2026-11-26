import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20165_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit :=
  { gates := [
    ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.or, [15, 6]⟩, ⟨GateOp.or, [0, 11]⟩, ⟨GateOp.or, [2, 9]⟩, ⟨GateOp.or, [8, 5]⟩, ⟨GateOp.or, [18, 14]⟩, ⟨GateOp.or, [18, 16]⟩, ⟨GateOp.or, [4, 3]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.or, [23, 12]⟩, ⟨GateOp.or, [25, 13]⟩, ⟨GateOp.or, [22, 20]⟩, ⟨GateOp.and, [12, 24]⟩, ⟨GateOp.or, [7, 20]⟩, ⟨GateOp.and, [27, 19]⟩, ⟨GateOp.and, [26, 21]⟩, ⟨GateOp.or, [25, 8]⟩, ⟨GateOp.or, [30, 28]⟩, ⟨GateOp.or, [29, 13]⟩, ⟨GateOp.or, [16, 17]⟩, ⟨GateOp.or, [14, 3]⟩, ⟨GateOp.or, [31, 33]⟩, ⟨GateOp.and, [17, 36]⟩, ⟨GateOp.and, [34, 35]⟩, ⟨GateOp.or, [25, 14]⟩, ⟨GateOp.or, [38, 39]⟩, ⟨GateOp.or, [37, 41]⟩
    ]
    output := 42 }

theorem C_mono : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem C_size : C.size ≤ 27 := by decide

theorem C_rep : Represents (fun u v : Fin 8 => (10691974706225816370 : ℕ).testBit (8 * u.val + v.val)) C := by
  intro u v
  revert u v
  decide

end PEqualNP.Outside.L_meta_20165_aux

theorem PEqualNP.Outside.L_meta_20165 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10691974706225816370 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨PEqualNP.Outside.L_meta_20165_aux.C, PEqualNP.Outside.L_meta_20165_aux.C_mono, PEqualNP.Outside.L_meta_20165_aux.C_size, PEqualNP.Outside.L_meta_20165_aux.C_rep⟩
