import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20057_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit :=
  { gates := [
    ⟨GateOp.or, [2, 1]⟩, ⟨GateOp.or, [10, 3]⟩, ⟨GateOp.or, [11, 7]⟩, ⟨GateOp.or, [14, 5]⟩, ⟨GateOp.or, [4, 9]⟩, ⟨GateOp.or, [10, 20]⟩, ⟨GateOp.or, [3, 16]⟩, ⟨GateOp.or, [3, 19]⟩, ⟨GateOp.or, [13, 1]⟩, ⟨GateOp.or, [6, 24]⟩, ⟨GateOp.or, [8, 25]⟩, ⟨GateOp.or, [0, 15]⟩, ⟨GateOp.or, [21, 2]⟩, ⟨GateOp.and, [28, 26]⟩, ⟨GateOp.or, [23, 18]⟩, ⟨GateOp.or, [20, 18]⟩, ⟨GateOp.and, [19, 31]⟩, ⟨GateOp.and, [24, 6]⟩, ⟨GateOp.and, [12, 22]⟩, ⟨GateOp.and, [18, 17]⟩, ⟨GateOp.or, [35, 27]⟩, ⟨GateOp.or, [8, 30]⟩, ⟨GateOp.or, [32, 33]⟩, ⟨GateOp.and, [37, 36]⟩, ⟨GateOp.or, [34, 38]⟩, ⟨GateOp.or, [39, 40]⟩, ⟨GateOp.or, [41, 29]⟩
    ]
    output := 42 }

theorem C_mono : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem C_size : C.size ≤ 27 := by decide

theorem C_rep : Represents (fun u v : Fin 8 => (14134136632318694985 : ℕ).testBit (8 * u.val + v.val)) C := by
  intro u v
  revert u v
  decide

end PEqualNP.Outside.L_meta_20057_aux

theorem PEqualNP.Outside.L_meta_20057 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14134136632318694985 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨PEqualNP.Outside.L_meta_20057_aux.C, PEqualNP.Outside.L_meta_20057_aux.C_mono, PEqualNP.Outside.L_meta_20057_aux.C_size, PEqualNP.Outside.L_meta_20057_aux.C_rep⟩
