/-
  Theorem 10, recursion, stage C: `CAT_( A , e )` with body `a ## b` -- both arguments as they
  are, the last token of `A` pasted with `e`.
-/
import D0Stage

namespace PP

theorem paste_go_prefix : ∀ (l : List Tok) (acc rest : List RTok),
    paste.go acc (l.map RTok.t ++ rest) = paste.go ((l.map RTok.t).reverse ++ acc) rest
  | [], acc, rest => by simp
  | x :: l, acc, rest => by
    simp only [List.map_cons, List.cons_append]
    rw [paste.go.eq_4 acc (RTok.t x) _ (fun e => by cases e) (fun _ _ _ _ _ e _ => by cases e), paste_go_prefix l]
    simp

theorem paste_last (A' : List Tok) (z e : Tok) (s : String) (hs : pasted z.s e.s = some s) :
    paste (A'.map RTok.t ++ [RTok.t z, RTok.op, RTok.t e]) = some (A' ++ [{ s, H := inter z.H e.H }]) := by
  unfold paste
  rw [show A'.map RTok.t ++ [RTok.t z, RTok.op, RTok.t e] = (A' ++ [z]).map RTok.t ++ [RTok.op, RTok.t e] by simp,
    paste_go_prefix]
  simp only [List.map_append, List.map_cons, List.map_nil, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, List.append_nil]
  rw [paste.go, pasteTwo, hs]
  simp [paste.go, toks, tokOf, List.filterMap_append, Function.comp_def]

/-- **The paste call.** -/
theorem paste_call (Γ : Env) {x lp sep rp : Tok} (hf : Γ.find x.s = some (.fn 2 false [prm 0, .paste, prm 1]))
    (hid : x.s ∉ x.H) (hlp : lp.s = "(") (hsep : sep.s = ",") (hrp : rp.s = ")") {A' : List Tok} {z e : Tok}
    (hA : ArgShape (A' ++ [z])) (he : ArgShape [e]) {s : String} (hs : pasted z.s e.s = some s)
    {rest : List Tok} {n c : Nat} {q}
    (h : scan Γ n (c + 1) (mark c (x.s :: inter x.H rp.H) (A' ++ [{ s, H := inter z.H e.H }]) ++ rest) = some q) :
    ∃ st, scan Γ (n + 1) c (x :: lp :: (joinArgs sep [A' ++ [z], [e]] ++ rp :: rest)) = some (q.1, st, q.2.2) := by
  have hc := closeAt_args sep rp hsep hrp [A' ++ [z], [e]] rest [] (by intro X hX; simp at hX; rcases hX with rfl | rfl <;> assumption)
  simp only [List.reverse_nil, List.nil_append] at hc
  have hb := bind_plain sep hsep (as := [A' ++ [z], [e]]) (by intro X hX; simp at hX; rcases hX with rfl | rfl <;> assumption)
    2 rfl (Or.inl (by decide))
  have hr : subst Γ n (c + 1) [prm 0, .paste, prm 1] [A' ++ [z], [e]] [] =
      some ((A' ++ [z]).map RTok.t ++ [RTok.op, RTok.t e], [], c + 1) := by
    simp [subst, substFrom, piece, one, adjacentPaste, prm]
  have hp := paste_last A' z e s hs
  have := scan_fn_step Γ n c x lp rp _ rest hid hf hlp hc _ _ _ _ q hb hr (by simpa using hp) h
  exact ⟨_, this⟩

end PP
