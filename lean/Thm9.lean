import Mathlib.Computability.Primrec.List
import MainBound
import Translate

/-!
  Theorem 9 (pp_primrec.tex, §5): every pp-computable function is primitive recursive, against
  Mathlib's `Primrec`.
-/

namespace PP

/-- The call `F(x̄₁, …, x̄ₖ)`, each argument in unary: `(~)` repeated. -/
def call (F : String) (xs : List Nat) : String := s!"{F}({commaJoin (xs.map unary)})"

/-- The token spellings of `n̄`. -/
def unaryToks (n : Nat) : List String := (input (unary n)).map (·.s)

/-- `f : ℕᵏ → ℕ` is pp-computable: some environment `Γ` and macro `F` expand
    `F(x̄₁, …, x̄ₖ)` to exactly `f(x̄)` in unary, for every input. -/
def PpComputable {k : Nat} (f : List.Vector Nat k → Nat) : Prop :=
  ∃ (Γ : Env) (F : String), ∀ xs : List.Vector Nat k, ∃ fuel,
    run Γ fuel (call F xs.toList) = some (unaryToks (f xs))

/-- The statement of Theorem 9. -/
def Theorem9 : Prop := ∀ (k : Nat) (f : List.Vector Nat k → Nat), PpComputable f → Primrec f

example : Primrec (fun n : Nat => n + 1) := Primrec.succ

end PP
