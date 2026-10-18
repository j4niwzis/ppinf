/-
  Theorem 10: the translation's environment indexed by paths -- every name is
  `fullName path helper`, so lookups are decided by `fullName_inj`, never by strings.
-/
import Names

namespace PP

def nm (π : List Code) (x : Helper) : BTok := tk (fullName π x)

/-- The helpers of a recursion node, its own macro first. -/
def precHelpers : List Helper :=
  [.self, .SEL, .SEL2, .TH, .STEP, .ITER, .GEN, .GA, .GB, .GAEND, .GBEND, .BRA, .BRB, .BRAEND, .BRBEND,
   .D1, .D0, .OUT, .CAT, .CATu, .CAT2, .CAT2u]

/-- The definition of each helper of the recursion node `π`, its base of arity `m`. -/
def precDef (m : Nat) (π : List Code) : Helper → Def
  | .self => .fn (m + 1) false ([nm π .SEL, tk "(", nm π .ITER, tk "(", prm 0, tk ",", tk "(", tk ",",
      nm (π ++ [.f]) .self, tk "("] ++ joinB ((prms m 1).map ([·])) ++ [tk ")"] ++ tailB (prms m 1) ++
      [tk ")", tk ")", tk ")"])
  | .SEL => .fn 1 false [nm π .SEL2, prm 0]
  | .SEL2 => .fn 2 true [prm 1]
  | .TH => .fn 1 false [nm π .STEP, prm 0]
  | .STEP => .fn (m + 2) false ([tk "(", prm 0, tk "(", tk "~", tk ")", tk ",", nm (π ++ [.r]) .self,
      tk "(", prm 0, tk ",", prm 1] ++ tailB (prms m 2) ++ [tk ")"] ++ tailB (prms m 2) ++ [tk ")"])
  | .ITER => .fn 2 false [nm π .CAT, tk "(", nm π .GEN, tk "(", prm 0, tk ")", prm 1, nm π .BRA, prm 0,
      tk ",", tk "_END", tk ")"]
  | .GEN => .fn 1 false [nm π .CAT2, tk "(", nm π .GA, prm 0, tk ",", tk "_END", tk ")"]
  | .GA => .fn 0 true [nm π .TH, nm π .D1, tk "(", tk ")", nm π .GB]
  | .GB => .fn 0 true [nm π .TH, nm π .D1, tk "(", tk ")", nm π .GA]
  | .GAEND => .obj []
  | .GBEND => .obj []
  | .BRA => .fn 0 true [tk ")", nm π .BRB]
  | .BRB => .fn 0 true [tk ")", nm π .BRA]
  | .BRAEND => .obj []
  | .BRBEND => .obj []
  | .D1 => .fn 0 false [nm π .D0, nm π .OUT, tk "(", tk ")"]
  | .D0 => .fn 0 false [tk "("]
  | .OUT => .obj []
  | .CAT => .fn 2 false [nm π .CATu, tk "(", prm 0, tk ",", prm 1, tk ")"]
  | .CATu => .fn 2 false [prm 0, .paste, prm 1]
  | .CAT2 => .fn 2 false [nm π .CAT2u, tk "(", prm 0, tk ",", prm 1, tk ")"]
  | .CAT2u => .fn 2 false [prm 0, .paste, prm 1]

/-- The definitions of a term at the node `π`. -/
def Term.denvP : Term → List Code → Env
  | .zero _, π => [(fullName π .self, .fn 0 true [])]
  | .succ, π => [(fullName π .self, .fn 1 false [prm 0, tk "(", tk "~", tk ")"])]
  | .proj k i, π => [(fullName π .self, .fn k false [prm i])]
  | .comp k h gs, π =>
    let calls := (List.range gs.length).map fun j =>
      [nm (π ++ [.k j]) .self, tk "("] ++ joinB ((prms k).map ([·])) ++ [tk ")"]
    (fullName π .self, .fn k false ([nm (π ++ [.h]) .self, tk "("] ++ joinB calls ++ [tk ")"])) ::
      (h.denvP (π ++ [.h]) ++ (gs.attach.zipIdx).flatMap fun (⟨g, _⟩, j) => g.denvP (π ++ [.k j]))
  | .prec f g, π => precHelpers.map (fun x => (fullName π x, precDef f.arity π x)) ++ f.denvP (π ++ [.f]) ++ g.denvP (π ++ [.r])

end PP
