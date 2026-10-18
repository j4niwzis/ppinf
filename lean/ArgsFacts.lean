/-
  Where an invocation's arguments come from: the tokens between its parentheses, each
  argument a sublist of them, the variadic slot a suffix; and after them the closing
  parenthesis and the rest of the stream.
-/
import Semantics

namespace PP

theorem closeAt_eq : ∀ (xs : List Tok) (d : Nat) (acc : List Tok) inner cl rest,
    closeAt d xs acc = some (inner, cl, rest) → acc.reverse ++ xs = inner ++ cl :: rest := by
  intro xs
  induction xs with
  | nil => intro d acc inner cl rest h; simp [closeAt] at h
  | cons x xs ih =>
    intro d acc inner cl rest h
    unfold closeAt at h
    split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h; rfl
      · have := ih _ _ _ _ _ h; simpa using this
    · split at h
      · have := ih _ _ _ _ _ h; simpa using this
      · have := ih _ _ _ _ _ h; simpa using this

theorem splitTop_sub : ∀ (xs : List Tok) (d : Nat) (cur : List Tok), ∀ a ∈ splitTop d xs cur, a.Sublist (cur.reverse ++ xs) := by
  intro xs
  induction xs with
  | nil => intro d cur a h; simp [splitTop] at h; subst h; simp
  | cons x xs ih =>
    intro d cur a h
    unfold splitTop at h
    split at h
    · rcases List.mem_cons.mp h with e | e
      · subst e; exact List.sublist_append_left _ _
      · have := ih d [] a e
        simp at this
        exact this.trans ((List.sublist_cons_self x xs).trans (List.sublist_append_right _ _))
    · have := ih _ _ a h
      simpa using this

theorem afterCommas_sub : ∀ (k d : Nat) (xs : List Tok), (afterCommas k d xs).Sublist xs := by
  intro k d xs
  induction xs generalizing k d with
  | nil => cases k <;> simp [afterCommas]
  | cons x xs ih =>
    cases k with
    | zero => simp [afterCommas]
    | succ k =>
      unfold afterCommas
      split
      · exact (ih k d).trans (List.sublist_cons_self x xs)
      · exact (ih (k + 1) _).trans (List.sublist_cons_self x xs)

theorem bind_sub (arity : Nat) (variadic : Bool) (inner : List Tok) named va
    (h : bind arity variadic inner = some (named, va)) :
    (∀ a ∈ named, a = [] ∨ a.Sublist inner) ∧ va.Sublist inner := by
  have segs : ∀ a ∈ splitTop 0 inner [], a.Sublist inner := fun a ha => by simpa using splitTop_sub inner 0 [] a ha
  unfold bind at h
  simp only at h
  split at h
  · split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨?_, List.nil_sublist _⟩
        intro a ha
        cases List.mem_append.mp ha with
        | inl e => exact Or.inr (segs a e)
        | inr e => exact Or.inl (List.eq_of_mem_replicate e)
      · simp at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨fun a ha => Or.inr (segs a (List.mem_of_mem_take ha)), afterCommas_sub _ _ _⟩
  · split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨fun a ha => by simp at ha, List.nil_sublist _⟩
      · simp at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨fun a ha => Or.inr (segs a ha), List.nil_sublist _⟩
      · simp at h

end PP
