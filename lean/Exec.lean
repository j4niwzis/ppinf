/-
  Running the rules on concrete shapes, for the translation's proof: name-free streams pass
  through; one function-like step, forward; pasting without `##` is the identity.
-/
import Frame

namespace PP

def NameFree (Γ : Env) (xs : List Tok) : Prop := ∀ t ∈ xs, Γ.find t.s = none

/-- A name-free stream is emitted as it is. -/
theorem scan_namefree (Γ : Env) : ∀ (xs : List Tok) (c : Nat), NameFree Γ xs → ∀ n, xs.length < n →
    scan Γ n c xs = some (xs, [], c) := by
  intro xs
  induction xs with
  | nil => intro c _ n hn; obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩; simp [scan]
  | cons x xs ih =>
    intro c h n hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hx : Γ.find x.s = none := h x (by simp)
    have ht := ih c (fun t ht => h t (List.mem_cons_of_mem _ ht)) n (by simp at hn; omega)
    unfold scan
    by_cases hid : x.s ∈ x.H
    · simp [hid, emit, ht]
    · simp [hid, hx, emit, ht]

/-- One step of a function-like macro, forward. -/
theorem scan_fn_step (Γ : Env) (n c : Nat) (x open_ cl : Tok) (inner rest : List Tok) (hid : x.s ∉ x.H)
    {arity : Nat} {variadic : Bool} {body : List BTok} (hf : Γ.find x.s = some (.fn arity variadic body))
    (hop : open_.s = "(") (hc : closeAt 0 (inner ++ cl :: rest) [] = some (inner, cl, rest)) named va r b q
    (hbd : bind arity variadic inner = some (named, va)) (hr : subst Γ n (c + 1) body named va = some r)
    (hb : paste r.1 = some b) (h : scan Γ n r.2.2 (mark c (x.s :: inter x.H cl.H) b ++ rest) = some q) :
    scan Γ (n + 1) c (x :: open_ :: (inner ++ cl :: rest)) = some (q.1, r.2.1 ++ fnStep x cl c :: q.2.1, q.2.2) := by
  unfold scan
  have hne : (open_.s != "(") = false := by simp [hop]
  simp only [hid, ite_false, hf, hne, Bool.false_eq_true, hc, hbd, hr, Option.bind_some, hb, after, h, Option.map_some]
  rfl

/-- An object macro's step, forward. -/
theorem scan_obj_step (Γ : Env) (n c : Nat) (x : Tok) (rest : List Tok) (hid : x.s ∉ x.H) {body : List BTok}
    (hf : Γ.find x.s = some (.obj body)) r b q (hr : subst Γ n (c + 1) body [] [] = some r) (hb : paste r.1 = some b)
    (h : scan Γ n r.2.2 (mark c (x.s :: x.H) b ++ rest) = some q) :
    scan Γ (n + 1) c (x :: rest) = some (q.1, r.2.1 ++ objStep x c :: q.2.1, q.2.2) := by
  unfold scan
  simp only [hid, ite_false, hf, hr, Option.bind_some, hb, after, h, Option.map_some]
  rfl

/-- Pasting where no `##` is left: the tokens, placemarkers dropped. -/
def NoOp : List RTok → Prop
  | [] => True
  | .op :: _ => False
  | _ :: rest => NoOp rest

theorem paste_go_noop : ∀ (xs acc : List RTok), NoOp xs → paste.go acc xs = some (acc.reverse ++ xs)
  | [], acc, _ => by simp [paste.go]
  | .t x :: xs, acc, h => by
    simp only [NoOp] at h
    unfold paste.go
    rw [paste_go_noop xs (.t x :: acc) h]; simp
  | .pm :: xs, acc, h => by
    simp only [NoOp] at h
    unfold paste.go
    rw [paste_go_noop xs (.pm :: acc) h]; simp
  | .op :: _, _, h => by simp [NoOp] at h

def toks : List RTok → List Tok := List.filterMap tokOf

theorem paste_noop (xs : List RTok) (h : NoOp xs) : paste xs = some (toks xs) := by
  unfold paste toks
  rw [paste_go_noop xs [] h]; simp

end PP
