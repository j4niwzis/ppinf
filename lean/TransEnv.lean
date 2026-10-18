/-
  Theorem 10: the translation's environment built directly, as `(name, definition)` pairs --
  the same as reading the emitted `#define`s (checked in TransEnvCheck), without the parser.
-/
import Translate

namespace PP

def tk (s : String) : BTok := .tok s
def prm (i : Nat) : BTok := .param i

/-- `a, b, c`. -/
def joinB (xs : List (List BTok)) : List BTok := [tk ","].intercalate xs
/-- `, a, b`. -/
def tailB (xs : List BTok) : List BTok := xs.flatMap fun x => [tk ",", x]
/-- The parameters `0 … k-1`. -/
def prms (k : Nat) (from_ : Nat := 0) : List BTok := (List.range k).map fun i => prm (from_ + i)

/-- The definitions of a term, its own macro named `p`. -/
def Term.denv : Term → String → Env
  | .zero _, p => [(p, .fn 0 true [])]
  | .succ, p => [(p, .fn 1 false [prm 0, tk "(", tk "~", tk ")"])]
  | .proj k i, p => [(p, .fn k false [prm i])]
  | .comp k h gs, p =>
    let gnames := (List.range gs.length).map fun j => s!"{p}g{j}"
    let calls := gnames.map fun g => [tk g, tk "("] ++ joinB ((prms k).map ([·])) ++ [tk ")"]
    (p, .fn k false ([tk s!"{p}h", tk "("] ++ joinB calls ++ [tk ")"])) ::
      (h.denv s!"{p}h" ++ (gs.attach.zip gnames).flatMap fun (⟨g, _⟩, n) => g.denv n)
  | .prec f g, p =>
    let m := f.arity
    [(p, .fn (m + 1) false ([tk s!"{p}SEL", tk "(", tk s!"{p}ITER", tk "(", prm 0, tk ",", tk "(", tk ",",
        tk s!"{p}f", tk "("] ++ joinB ((prms m 1).map ([·])) ++ [tk ")"] ++ tailB (prms m 1) ++ [tk ")", tk ")", tk ")"])),
     (s!"{p}SEL", .fn 1 false [tk s!"{p}SEL2", prm 0]),
     (s!"{p}SEL2", .fn 2 true [prm 1]),
     (s!"{p}TH", .fn 1 false [tk s!"{p}STEP", prm 0]),
     (s!"{p}STEP", .fn (m + 2) false ([tk "(", prm 0, tk "(", tk "~", tk ")", tk ",", tk s!"{p}g", tk "(", prm 0, tk ",", prm 1]
        ++ tailB (prms m 2) ++ [tk ")"] ++ tailB (prms m 2) ++ [tk ")"])),
     (s!"{p}ITER", .fn 2 false [tk s!"{p}CAT", tk "(", tk s!"{p}GEN", tk "(", prm 0, tk ")", prm 1, tk s!"{p}BRA", prm 0,
        tk ",", tk "_END", tk ")"]),
     (s!"{p}GEN", .fn 1 false [tk s!"{p}CAT2", tk "(", tk s!"{p}GA", prm 0, tk ",", tk "_END", tk ")"]),
     (s!"{p}GA", .fn 0 true [tk s!"{p}TH", tk s!"{p}D1", tk "(", tk ")", tk s!"{p}GB"]),
     (s!"{p}GB", .fn 0 true [tk s!"{p}TH", tk s!"{p}D1", tk "(", tk ")", tk s!"{p}GA"]),
     (s!"{p}GA_END", .obj []),
     (s!"{p}GB_END", .obj []),
     (s!"{p}BRA", .fn 0 true [tk ")", tk s!"{p}BRB"]),
     (s!"{p}BRB", .fn 0 true [tk ")", tk s!"{p}BRA"]),
     (s!"{p}BRA_END", .obj []),
     (s!"{p}BRB_END", .obj []),
     (s!"{p}D1", .fn 0 false [tk s!"{p}D0", tk s!"{p}OUT", tk "(", tk ")"]),
     (s!"{p}D0", .fn 0 false [tk "("]),
     (s!"{p}OUT", .obj []),
     (s!"{p}CAT", .fn 2 false [tk s!"{p}CAT_", tk "(", prm 0, tk ",", prm 1, tk ")"]),
     (s!"{p}CAT_", .fn 2 false [prm 0, .paste, prm 1]),
     (s!"{p}CAT2", .fn 2 false [tk s!"{p}CAT2_", tk "(", prm 0, tk ",", prm 1, tk ")"]),
     (s!"{p}CAT2_", .fn 2 false [prm 0, .paste, prm 1])] ++ f.denv s!"{p}f" ++ g.denv s!"{p}g"

end PP
