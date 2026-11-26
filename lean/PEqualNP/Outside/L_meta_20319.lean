import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20319_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit :=
  { gates := [
    ⟨GateOp.or, [14, 0]⟩, ⟨GateOp.or, [7, 12]⟩, ⟨GateOp.or, [15, 4]⟩, ⟨GateOp.or, [17, 13]⟩, ⟨GateOp.or, [3, 11]⟩, ⟨GateOp.or, [20, 16]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.or, [22, 18]⟩, ⟨GateOp.or, [3, 19]⟩, ⟨GateOp.or, [2, 10]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.or, [13, 26]⟩, ⟨GateOp.or, [20, 23]⟩, ⟨GateOp.or, [6, 27]⟩, ⟨GateOp.or, [18, 6]⟩, ⟨GateOp.or, [24, 1]⟩, ⟨GateOp.and, [25, 31]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.and, [28, 33]⟩, ⟨GateOp.or, [16, 17]⟩, ⟨GateOp.and, [21, 30]⟩, ⟨GateOp.and, [29, 35]⟩, ⟨GateOp.or, [32, 37]⟩, ⟨GateOp.or, [36, 34]⟩, ⟨GateOp.or, [39, 38]⟩
    ]
    output := 40 }

theorem C_mono : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem C_size : C.size ≤ 25 := by decide

theorem C_rep : Represents (fun u v : Fin 8 => (2691051730525901985 : ℕ).testBit (8 * u.val + v.val)) C := by
  intro u v
  revert u v
  decide

end PEqualNP.Outside.L_meta_20319_aux

theorem PEqualNP.Outside.L_meta_20319 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (2691051730525901985 : ℕ).testBit (8 * u.val + v.val)) 25 :=
  ⟨PEqualNP.Outside.L_meta_20319_aux.C, PEqualNP.Outside.L_meta_20319_aux.C_mono, PEqualNP.Outside.L_meta_20319_aux.C_size, PEqualNP.Outside.L_meta_20319_aux.C_rep⟩
