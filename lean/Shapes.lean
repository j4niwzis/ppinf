/-
  Theorem 10, recursion: reading streams back into groups -- a numeral into its `( ~ )`
  groups, a ping-pong output into its quadruples -- and pasting a helper's name with `_END`.
-/
import PasteCall

namespace PP

theorem num_groups : ∀ (v : Nat) (o : List Tok), o.map (·.s) = unaryList v →
    ∃ G : List (Tok × Tok × Tok), o = groupToks G ∧ G.length = v ∧ ∀ g ∈ G, Group g
  | 0, o, h => by
    have : o = [] := by simpa [unaryList] using h
    exact ⟨[], this, rfl, by simp⟩
  | v + 1, o, h => by
    rw [show unaryList (v + 1) = ["(", "~", ")"] ++ unaryList v from rfl] at h
    match o, h with
    | a :: b :: d :: o', h =>
      simp only [List.map_cons, List.cons_append, List.nil_append, List.cons.injEq] at h
      obtain ⟨ha, hb, hd, h'⟩ := h
      obtain ⟨G, rfl, hl, hg⟩ := num_groups v o' h'
      refine ⟨(a, b, d) :: G, rfl, by simp [hl], ?_⟩
      intro g hg'; simp at hg'
      rcases hg' with rfl | hg'
      · exact ⟨ha, hb, hd⟩
      · exact hg g hg'
    | [], h => simp at h
    | [_], h => simp at h
    | [_, _], h => simp at h

theorem quad_split (a b c d : String) : ∀ (n : Nat) (E : List Tok) (x : String),
    E.map (·.s) = (List.replicate n [a, b, c, d]).flatten ++ [x] →
    ∃ (Q : List (Tok × Tok × Tok × Tok)) (X : Tok), E = quadToks Q ++ [X] ∧ Q.length = n ∧ X.s = x ∧
      ∀ q ∈ Q, q.1.s = a ∧ q.2.1.s = b ∧ q.2.2.1.s = c ∧ q.2.2.2.s = d
  | 0, E, x, h => by
    match E, h with
    | [X], h => exact ⟨[], X, rfl, rfl, by simpa using h, by simp⟩
    | [], h => simp at h
    | _ :: _ :: _, h => simp at h
  | n + 1, E, x, h => by
    rw [List.replicate_succ, List.flatten_cons] at h
    match E, h with
    | p :: q :: r :: s :: E', h =>
      simp only [List.map_cons, List.cons_append, List.nil_append, List.cons.injEq] at h
      obtain ⟨hp, hq, hr, hs, h'⟩ := h
      obtain ⟨Q, X, rfl, hl, hX, hQ⟩ := quad_split a b c d n E' x h'
      refine ⟨(p, q, r, s) :: Q, X, rfl, by simp [hl], hX, ?_⟩
      intro g hg; simp at hg
      rcases hg with rfl | hg
      · exact ⟨hp, hq, hr, hs⟩
      · exact hQ g hg
    | [], h => simp at h
    | [_], h => simp at h
    | [_, _], h => simp at h
    | [_, _, _], h => simp at h

/-! Names are identifiers, so `X ## _END` is a name too. -/

theorem identChar_code (c : Code) : ∀ ch ∈ c.chars, identChar ch = true := by
  intro ch hc
  cases c with
  | k j =>
    simp [Code.chars] at hc
    rcases hc with e | ⟨_, e⟩ | e
    · rw [e]; decide
    · rw [e]; decide
    · rw [e]; decide
  | h => simp [Code.chars] at hc; rw [hc]; decide
  | f => simp [Code.chars] at hc; rw [hc]; decide
  | r => simp [Code.chars] at hc; rw [hc]; decide

theorem identChar_suffix (x : Helper) : ∀ ch ∈ x.suffix.toList, identChar ch = true := by
  cases x <;> decide

theorem pasted_end (π : List Code) (x y : Helper) (hxy : x.suffix ++ "_END" = y.suffix) :
    pasted (fullName π x) "_END" = some (fullName π y) := by
  have e : fullName π x ++ "_END" = fullName π y := by
    unfold fullName; rw [String.append_assoc, hxy]
  unfold pasted
  rw [e]
  have hall : (fullName π y).all identChar = true := by
    rw [String.all_bool_eq, fullName_toList]
    simp only [List.all_cons, List.all_append, Bool.and_eq_true, List.all_eq_true]
    refine ⟨by decide, fun ch hch => ?_, identChar_suffix y⟩
    obtain ⟨c, _, hc⟩ := List.mem_flatMap.mp hch
    exact identChar_code c ch hc
  have hne : (fullName π y).isEmpty = false := by
    rw [Bool.eq_false_iff]; intro h
    have := String.isEmpty_iff.mp h
    have h2 := congrArg String.toList this
    rw [fullName_toList] at h2; simp at h2
  simp [hall, hne]

end PP
