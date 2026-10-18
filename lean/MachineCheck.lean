import Machine
import Translate
open PP
def same (Γ : Env) (fuel k : Nat) (s : String) : Bool :=
  match expand Γ fuel 1 (input s), mexpand Γ k 1 (input s) with
  | some (o, st, c), some (o', st', c') => o.map (·.s) == o'.map (·.s) && (o.map (·.H)) == (o'.map (·.H)) &&
      st.map (·.id) == st'.map (·.id) && st.map (·.m) == st'.map (·.m) && c == c'
  | none, none => true
  | _, _ => false
#eval ([(addT, [3,2]), (mulT, [3,2]), (subT, [5,3]), (exp2T, [3]), (predT, [4]), (mulT, [2,4])] : List (Term × List Nat)).map fun (t, xs) =>
  (same t.env 100000 1000000 (callOf t xs), (mexpand t.env 1000000 1 (input (callOf t xs))).map fun (q : List Tok × List Step × Nat) => q.1.length)
#eval same (defines "#define A(x) x B\n#define B A(1)\n#define C(x, y) x ## y\n") 1000 100000 (String.join ["A(A(2)) C(a, b) C(, c) C(1 2, 3 4)"])
