/-
  One iteration of a prefix scan, both ways: what a successful prefix scan of a stream
  with a given head did first, and how to rebuild it at a chosen fuel. And the shape of
  what a prefix scan leaves.
-/
import Size
import Prefix3

namespace PP

/-- The longest body: every body is at most this long. -/
def bodyLen : Def → Nat
  | .obj b => b.length
  | .fn _ _ b => b.length
def maxBody (Γ : Env) : Nat := (Γ.map (fun p => bodyLen p.2)).sum + 1

theorem le_sum_of_mem' : ∀ (l : List Nat) (a : Nat), a ∈ l → a ≤ l.sum
  | [], _, h => by simp at h
  | b :: l, a, h => by
    rcases List.mem_cons.mp h with e | e
    · subst e; simp
    · have := le_sum_of_mem' l a e; simp; omega

theorem body_le (Γ : Env) {m : Name} {d : Def} (h : Γ.find m = some d) : bodyLen d ≤ maxBody Γ := by
  unfold Env.find at h
  cases hf : Γ.find? (·.1 == m) with
  | none => simp [hf] at h
  | some p =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    subst h
    have hp := List.mem_of_find?_eq_some hf
    unfold maxBody
    have : bodyLen p.2 ≤ (Γ.map (fun p => bodyLen p.2)).sum :=
      le_sum_of_mem' _ _ (List.mem_map_of_mem hp)
    omega

/-- When `closeAt` finds nothing in `R` but something in `R ++ A`, the closing parenthesis is
    in `A`. -/
theorem closeAt_past : ∀ (R A : List Tok) (d : Nat) (acc : List Tok) inner cl rest,
    closeAt d R acc = none → closeAt d (R ++ A) acc = some (inner, cl, rest) →
    ∃ pre, inner = acc.reverse ++ R ++ pre ∧ A = pre ++ cl :: rest := by
  intro R A
  induction R with
  | nil =>
    intro d acc inner cl rest _ h
    have := closeAt_eq A d acc inner cl rest h
    -- acc.reverse ++ A = inner ++ cl :: rest; inner begins with acc.reverse
    have key : ∀ (A : List Tok) (d : Nat) (acc : List Tok) inner cl rest, closeAt d A acc = some (inner, cl, rest) →
        ∃ pre, inner = acc.reverse ++ pre ∧ A = pre ++ cl :: rest := by
      intro A
      induction A with
      | nil => intro d acc inner cl rest h; simp [closeAt] at h
      | cons x A ih =>
        intro d acc inner cl rest h
        unfold closeAt at h
        split at h
        · split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨[], by simp, by simp⟩
          · obtain ⟨pre, h1, h2⟩ := ih _ _ _ _ _ h; exact ⟨x :: pre, by simp [h1], by simp [h2]⟩
        · split at h
          · obtain ⟨pre, h1, h2⟩ := ih _ _ _ _ _ h; exact ⟨x :: pre, by simp [h1], by simp [h2]⟩
          · obtain ⟨pre, h1, h2⟩ := ih _ _ _ _ _ h; exact ⟨x :: pre, by simp [h1], by simp [h2]⟩
    obtain ⟨pre, h1, h2⟩ := key A d acc inner cl rest h
    exact ⟨pre, by simp [h1], h2⟩
  | cons x R ih =>
    intro d acc inner cl rest h0 h
    simp only [List.cons_append] at h
    unfold closeAt at h0 h
    split at h0
    · rename_i hx; rw [if_pos hx] at h
      split at h0
      · simp at h0
      · rename_i hd; rw [if_neg hd] at h
        obtain ⟨pre, h1, h2⟩ := ih _ _ _ _ _ h0 h
        exact ⟨pre, by simp [h1], h2⟩
    · rename_i hx; rw [if_neg hx] at h
      split at h0
      · rename_i ho; rw [if_pos ho] at h
        obtain ⟨pre, h1, h2⟩ := ih _ _ _ _ _ h0 h
        exact ⟨pre, by simp [h1], h2⟩
      · rename_i ho; rw [if_neg ho] at h
        obtain ⟨pre, h1, h2⟩ := ih _ _ _ _ _ h0 h
        exact ⟨pre, by simp [h1], h2⟩

end PP

namespace PP

/-- The head passed by: hidden, not a macro, or a function-like macro without `(` next. -/
def Passes (Γ : Env) (x : Tok) (R : List Tok) : Prop :=
  x.s ∈ x.H ∨ (x.s ∉ x.H ∧ Γ.find x.s = none) ∨
  (x.s ∉ x.H ∧ ∃ a v b open_ after, Γ.find x.s = some (.fn a v b) ∧ R = open_ :: after ∧ (open_.s != "(") = true)

/-- The prefix scan stops, needing what is behind. -/
def Stops (Γ : Env) (x : Tok) (R : List Tok) : Prop :=
  x.s ∉ x.H ∧ ∃ a v b, Γ.find x.s = some (.fn a v b) ∧
    (R = [] ∨ ∃ open_ after, R = open_ :: after ∧ open_.s = "(" ∧ closeAt 0 after [] = none)

def objStep (x : Tok) (c : Nat) : Step := { m := x.s, head := x, close := none, mark := x.s :: x.H, id := c }
def fnStep (x cl : Tok) (c : Nat) : Step := { m := x.s, head := x, close := some cl, mark := x.s :: inter x.H cl.H, id := c }

/-- What one iteration of a successful prefix scan did. -/
theorem iter_cases (Γ : Env) (W : List Tok) (n c : Nat) (x : Tok) (R : List Tok) (q : PRes)
    (h : pscan Γ W (n + 1) c (x :: R) = some q) :
    (Passes Γ x R ∧ ∃ q2, pscan Γ W n c R = some q2 ∧ q = (x :: q2.1, q2.2)) ∨
    (∃ body r b q2, x.s ∉ x.H ∧ Γ.find x.s = some (.obj body) ∧ subst Γ n (c + 1) body [] [] = some r ∧
      paste r.1 = some b ∧ pscan Γ W n r.2.2 (mark c (x.s :: x.H) b ++ R) = some q2 ∧
      q = (q2.1, r.2.1 ++ objStep x c :: q2.2.1, q2.2.2)) ∨
    (∃ arity variadic body open_ inner cl rest named va r b q2, x.s ∉ x.H ∧ Γ.find x.s = some (.fn arity variadic body) ∧
      R = open_ :: (inner ++ cl :: rest) ∧ open_.s = "(" ∧ closeAt 0 (inner ++ cl :: rest) [] = some (inner, cl, rest) ∧
      bind arity variadic inner = some (named, va) ∧ subst Γ n (c + 1) body named va = some r ∧ paste r.1 = some b ∧
      pscan Γ W n r.2.2 (mark c (x.s :: inter x.H cl.H) b ++ rest) = some q2 ∧
      q = (q2.1, r.2.1 ++ fnStep x cl c :: q2.2.1, q2.2.2)) ∨
    (Stops Γ x R ∧ q = ([], [], c, x :: R ++ W)) := by
  obtain ⟨qo, qst, qc, qS⟩ := q
  unfold pscan at h
  by_cases hid : x.s ∈ x.H
  · simp only [hid, ite_true] at h
    obtain ⟨o', hr, rfl⟩ := pemit_some h
    exact Or.inl ⟨Or.inl hid, _, hr, rfl⟩
  · simp only [hid, ite_false] at h
    cases hf : Γ.find x.s with
    | none =>
      rw [hf] at h; simp only at h
      obtain ⟨o', hr, rfl⟩ := pemit_some h
      exact Or.inl ⟨Or.inr (Or.inl ⟨hid, hf⟩), _, hr, rfl⟩
    | some d =>
      rw [hf] at h
      cases d with
      | obj body =>
        simp only at h
        obtain ⟨r, hr, h⟩ := bind_some h
        obtain ⟨b, hb, h⟩ := bind_some h
        obtain ⟨st₂, hp, rfl⟩ := pafter_some h
        exact Or.inr (Or.inl ⟨body, r, b, _, hid, rfl, hr, hb, hp, rfl⟩)
      | fn arity variadic body =>
        simp only at h
        cases R with
        | nil =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact Or.inr (Or.inr (Or.inr ⟨⟨hid, arity, variadic, body, hf, Or.inl rfl⟩, by simp⟩))
        | cons open_ after =>
          simp only at h
          by_cases hne : (open_.s != "(") = true
          · simp only [hne, ite_true] at h
            obtain ⟨o', hr, rfl⟩ := pemit_some h
            exact Or.inl ⟨Or.inr (Or.inr ⟨hid, arity, variadic, body, open_, after, hf, rfl, hne⟩), _, hr, rfl⟩
          · simp only [hne, Bool.false_eq_true, ite_false] at h
            have hop : open_.s = "(" := by simpa using hne
            cases hc : closeAt 0 after [] with
            | none =>
              rw [hc] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl, rfl⟩ := h
              exact Or.inr (Or.inr (Or.inr ⟨⟨hid, arity, variadic, body, hf, Or.inr ⟨open_, after, rfl, hop, hc⟩⟩, by simp⟩))
            | some a =>
              rw [hc] at h
              obtain ⟨inner, cl, rest⟩ := a
              have heq := closeAt_eq after 0 [] inner cl rest hc
              simp only [List.reverse_nil, List.nil_append] at heq
              subst heq
              simp only at h
              obtain ⟨⟨named, va⟩, hbd, h⟩ := bind_some h
              obtain ⟨r, hr, h⟩ := bind_some h
              obtain ⟨b, hb, h⟩ := bind_some h
              obtain ⟨st₂, hp, rfl⟩ := pafter_some h
              exact Or.inr (Or.inr (Or.inl ⟨arity, variadic, body, open_, inner, cl, rest, named, va, r, b, _, hid, rfl, rfl, hop,
                hc, hbd, hr, hb, hp, rfl⟩))

theorem rebuild_pass (Γ : Env) (W : List Tok) (f c : Nat) (x : Tok) (R : List Tok) (hp : Passes Γ x R) q2
    (h : pscan Γ W f c R = some q2) : pscan Γ W (f + 1) c (x :: R) = some (x :: q2.1, q2.2) := by
  unfold pscan
  rcases hp with hid | ⟨hid, hf⟩ | ⟨hid, a, v, b, open_, after, hf, rfl, hne⟩
  · simp only [hid, ite_true, pemit, h]; rfl
  · simp only [hid, ite_false, hf, pemit, h]; rfl
  · simp only [hid, ite_false, hf, hne, ite_true, pemit]; rw [h]; rfl

theorem rebuild_obj (Γ : Env) (W : List Tok) (f c : Nat) (x : Tok) (R : List Tok) (hid : x.s ∉ x.H) {body : List BTok}
    (hf : Γ.find x.s = some (.obj body)) r b q2 (hr : subst Γ f (c + 1) body [] [] = some r) (hb : paste r.1 = some b)
    (h : pscan Γ W f r.2.2 (mark c (x.s :: x.H) b ++ R) = some q2) :
    pscan Γ W (f + 1) c (x :: R) = some (q2.1, r.2.1 ++ objStep x c :: q2.2.1, q2.2.2) := by
  unfold pscan
  simp only [hid, ite_false, hf, hr, Option.bind_some, hb, pafter, h, Option.map_some]
  rfl

theorem rebuild_fn (Γ : Env) (W : List Tok) (f c : Nat) (x open_ cl : Tok) (inner rest : List Tok) (hid : x.s ∉ x.H)
    {arity : Nat} {variadic : Bool} {body : List BTok} (hf : Γ.find x.s = some (.fn arity variadic body))
    (hop : open_.s = "(") (hc : closeAt 0 (inner ++ cl :: rest) [] = some (inner, cl, rest)) named va r b q2
    (hbd : bind arity variadic inner = some (named, va)) (hr : subst Γ f (c + 1) body named va = some r)
    (hb : paste r.1 = some b) (h : pscan Γ W f r.2.2 (mark c (x.s :: inter x.H cl.H) b ++ rest) = some q2) :
    pscan Γ W (f + 1) c (x :: open_ :: (inner ++ cl :: rest)) = some (q2.1, r.2.1 ++ fnStep x cl c :: q2.2.1, q2.2.2) := by
  unfold pscan
  have hne : (open_.s != "(") = false := by simp [hop]
  simp only [hid, ite_false, hf, hne, Bool.false_eq_true, hc, hbd, hr, Option.bind_some, hb, pafter, h, Option.map_some]
  rfl

theorem rebuild_stop (Γ : Env) (W : List Tok) (f c : Nat) (x : Tok) (R : List Tok) (hs : Stops Γ x R) :
    pscan Γ W (f + 1) c (x :: R) = some ([], [], c, x :: R ++ W) := by
  obtain ⟨hid, a, v, b, hf, h⟩ := hs
  unfold pscan
  rcases h with rfl | ⟨open_, after, rfl, hop, hc⟩
  · simp [hid, hf]
  · have hne : (open_.s != "(") = false := by simp [hop]
    simp [hid, hf, hne, hc]

end PP
