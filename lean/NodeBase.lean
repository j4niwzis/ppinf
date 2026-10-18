/-
  Theorem 10, the node lemma and its base cases: a call of a node's macro on arguments that
  expand to numerals scans to the numeral of the node's value.
-/
import SubstSimple
import Realize

namespace PP

mutual
/-- Arities agree. -/
def Term.WF : Term → Prop
  | .zero _ => True
  | .succ => True
  | .proj k i => i < k
  | .comp k h gs => h.arity = gs.length ∧ h.WF ∧ Term.WFs k gs
  | .prec f g => g.arity = f.arity + 2 ∧ f.WF ∧ g.WF
/-- Each of arity `k` and well formed. -/
def Term.WFs (k : Nat) : List Term → Prop
  | [] => True
  | g :: gs => g.arity = k ∧ g.WF ∧ Term.WFs k gs
end

/-- No macro is named like the numerals' punctuation. -/
def PunctFree (Γ : Env) : Prop :=
  Γ.find "(" = none ∧ Γ.find ")" = none ∧ Γ.find "," = none ∧ Γ.find "~" = none ∧ Γ.find "_END" = none

/-- A name of the node `π` or below it. -/
def Below (π : List Code) (n : Name) : Prop := ∃ q x, n = fullName (π ++ q) x

/-- A macro name of the translation. -/
def IsName (n : Name) : Prop := ∃ π y, n = fullName π y

/-- A hidden name a node `π` may meet in its call: a name, not its own nor below it. -/
def Safe (π : List Code) (n : Name) : Prop := ¬ Below π n ∧ IsName n

/-- The call `p ( A₁ , … , Aₖ )`. -/
def callToks (x lp sep rp : Tok) (as : List (List Tok)) : List Tok := x :: lp :: (joinArgs sep as ++ [rp])

/-- The arguments: shaped, and expanding to the values. -/
def ArgsOK (Γ : Env) (as : List (List Tok)) (vs : List Nat) : Prop :=
  All2 (fun A v => ArgShape A ∧ Expands Γ A v) as vs

/-- **The node lemma**, for the node `π` with term `t`. -/
def NodeOK (Γ : Env) (t : Term) (π : List Code) : Prop :=
  ∀ (x lp sep rp : Tok) (as : List (List Tok)) (vs : List Nat),
    x.s = fullName π .self → x.s ∉ x.H → lp.s = "(" → sep.s = "," → rp.s = ")" →
    as.length = t.arity → ArgsOK Γ as vs → (∀ n ∈ inter x.H rp.H, Safe π n) →
    ∀ c, ∃ N o st c', scan Γ N c (callToks x lp sep rp as) = some (o, st, c') ∧ IsNum o (t.eval vs)

/-! Numerals. -/

theorem unaryList_succ' (v : Nat) : unaryList (v + 1) = unaryList v ++ ["(", "~", ")"] := by
  unfold unaryList
  rw [List.replicate_succ', List.flatten_append]; simp

theorem mem_unaryList {v : Nat} {s : String} (h : s ∈ unaryList v) : s = "(" ∨ s = "~" ∨ s = ")" := by
  unfold unaryList at h
  simp only [List.mem_flatten, List.mem_replicate] at h
  obtain ⟨l, ⟨_, rfl⟩, hs⟩ := h
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs; exact hs

theorem nameFree_num {Γ : Env} (hp : PunctFree Γ) {o : List Tok} {v : Nat} (h : IsNum o v) : NameFree Γ o := by
  intro t ht
  have : t.s ∈ unaryList v := by rw [← h]; exact List.mem_map_of_mem ht
  rcases mem_unaryList this with e | e | e <;> rw [e]
  · exact hp.1
  · exact hp.2.2.2.1
  · exact hp.2.1

theorem isNum_mark {o : List Tok} {v : Nat} (h : IsNum o v) (c : Nat) (K : List Name) : IsNum (mark c K o) v := by
  unfold IsNum mark at *; simp [Function.comp_def, h]

/-- A name-free stream scans to itself. -/
theorem scan_nameFree' {Γ : Env} {xs : List Tok} (h : NameFree Γ xs) (c : Nat) :
    scan Γ (xs.length + 1) c xs = some (xs, [], c) := scan_namefree Γ xs c h _ (by omega)

end PP
