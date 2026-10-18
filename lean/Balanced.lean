/-
  Theorem 10: arguments that are balanced and have no comma outside parentheses -- how
  `closeAt` and `splitTop` see a call `( A₁ , … , Aₖ )`.
-/
import Semantics

namespace PP

/-- The depth after `xs` from `d`; `none` where `xs` closes below `d = 0` or has a comma at
    depth 0. -/
def walk : Nat → List Tok → Option Nat
  | d, [] => some d
  | d, x :: r =>
    if x.s == ")" then (if d == 0 then none else walk (d - 1) r)
    else if x.s == "(" then walk (d + 1) r
    else if x.s == "," && d == 0 then none
    else walk d r

theorem closeAt_cons (d : Nat) (x : Tok) (r acc : List Tok) : closeAt d (x :: r) acc =
    if x.s == ")" then (if d == 0 then some (acc.reverse, x, r) else closeAt (d - 1) r (x :: acc))
    else if x.s == "(" then closeAt (d + 1) r (x :: acc)
    else closeAt d r (x :: acc) := by rw [closeAt]

theorem splitTop_cons (d : Nat) (x : Tok) (r cur : List Tok) : splitTop d (x :: r) cur =
    if x.s == "," && d == 0 then cur.reverse :: splitTop d r [] else splitTop (depthAfter d x) r (x :: cur) := by
  rw [splitTop]

/-- An argument: balanced, no comma outside its parentheses. -/
def ArgShape (A : List Tok) : Prop := walk 0 A = some 0

theorem closeAt_walk : ∀ (A rest acc : List Tok) (d d' : Nat), walk d A = some d' →
    closeAt d (A ++ rest) acc = closeAt d' rest (A.reverse ++ acc)
  | [], rest, acc, d, d', h => by simp [walk] at h; subst h; rfl
  | x :: A, rest, acc, d, d', h => by
    unfold walk at h
    simp only [List.cons_append, List.reverse_cons, List.append_assoc, List.singleton_append]
    rw [closeAt_cons]
    by_cases h1 : (x.s == ")") = true
    · by_cases h2 : (d == 0) = true
      · simp [h1, h2] at h
      · simp only [h1, h2, ite_true, ite_false, Bool.false_eq_true] at h ⊢
        exact closeAt_walk A rest (x :: acc) _ _ h
    · by_cases h2 : (x.s == "(") = true
      · simp only [h1, h2, ite_true, ite_false, Bool.false_eq_true] at h ⊢
        exact closeAt_walk A rest (x :: acc) _ _ h
      · simp only [h1, h2, ite_false, Bool.false_eq_true] at h ⊢
        split at h
        · simp at h
        · exact closeAt_walk A rest (x :: acc) _ _ h

theorem splitTop_walk : ∀ (A rest cur : List Tok) (d d' : Nat), walk d A = some d' →
    splitTop d (A ++ rest) cur = splitTop d' rest (A.reverse ++ cur)
  | [], rest, cur, d, d', h => by simp [walk] at h; subst h; rfl
  | x :: A, rest, cur, d, d', h => by
    unfold walk at h
    simp only [List.cons_append, List.reverse_cons, List.append_assoc, List.singleton_append]
    rw [splitTop_cons]
    by_cases h1 : (x.s == ")") = true
    · by_cases h2 : (d == 0) = true
      · simp [h1, h2] at h
      · have hc : ¬ ((x.s == ",") = true ∧ (d == 0) = true) := fun e => by simp_all
        simp only [h1, h2, ite_true, ite_false, Bool.false_eq_true] at h
        rw [if_neg (by simpa using hc)]
        have : depthAfter d x = d - 1 := by simp [depthAfter, h1, show (x.s == "(") = false by
          simp only [beq_iff_eq] at h1 ⊢; rw [h1]; decide]
        rw [this]; exact splitTop_walk A rest (x :: cur) _ _ h
    · by_cases h2 : (x.s == "(") = true
      · have hc : ¬ ((x.s == ",") = true ∧ (d == 0) = true) := by
          intro e; simp only [beq_iff_eq] at e h2; rw [h2] at e; exact absurd e.1 (by decide)
        simp only [h1, h2, ite_true, ite_false, Bool.false_eq_true] at h
        rw [if_neg (by simpa using hc)]
        have : depthAfter d x = d + 1 := by simp [depthAfter, h2]
        rw [this]; exact splitTop_walk A rest (x :: cur) _ _ h
      · simp only [h1, h2, ite_false, Bool.false_eq_true] at h
        split at h
        · simp at h
        · rename_i hc
          rw [if_neg (by simpa using hc)]
          have : depthAfter d x = d := by simp [depthAfter, h1, h2]
          rw [this]; exact splitTop_walk A rest (x :: cur) _ _ h

/-- `A₁ , … , Aₖ`, with the comma token `sep`. -/
def joinArgs (sep : Tok) (as : List (List Tok)) : List Tok := [sep].intercalate as

theorem closeAt_args (sep rp : Tok) (hsep : sep.s = ",") (hrp : rp.s = ")") :
    ∀ (as : List (List Tok)) (rest acc : List Tok), (∀ A ∈ as, ArgShape A) →
    closeAt 0 (joinArgs sep as ++ rp :: rest) acc = some ((acc.reverse ++ joinArgs sep as), rp, rest)
  | [], rest, acc, _ => by simp [joinArgs, closeAt, hrp]
  | [A], rest, acc, h => by
    have := closeAt_walk A (rp :: rest) acc 0 0 (h A (by simp))
    simp only [joinArgs, List.intercalate_singleton] at this ⊢
    rw [this]; simp [closeAt, hrp]
  | A :: B :: as, rest, acc, h => by
    have hA := h A (by simp)
    simp only [joinArgs, List.intercalate_cons_cons, List.append_assoc, List.cons_append, List.nil_append] at *
    rw [closeAt_walk A _ acc 0 0 hA]
    have hs : (sep.s == ")") = false := by rw [hsep]; decide
    have hs' : (sep.s == "(") = false := by rw [hsep]; decide
    rw [closeAt_cons]
    simp only [hs, hs', Bool.false_eq_true, ite_false]
    have := closeAt_args sep rp hsep hrp (B :: as) rest (sep :: (A.reverse ++ acc)) (fun X hX => h X (by simp_all))
    simp only [joinArgs] at this
    rw [this]; simp

theorem splitTop_args (sep : Tok) (hsep : sep.s = ",") :
    ∀ (A : List Tok) (as : List (List Tok)) (cur : List Tok), (∀ X ∈ A :: as, ArgShape X) →
    splitTop 0 (joinArgs sep (A :: as)) cur = (cur.reverse ++ A) :: as
  | A, [], cur, h => by
    have := splitTop_walk A [] cur 0 0 (h A (by simp))
    simp only [joinArgs, List.intercalate_singleton, List.append_nil] at this ⊢
    rw [this]; simp [splitTop]
  | A, B :: as, cur, h => by
    simp only [joinArgs, List.intercalate_cons_cons, List.append_assoc, List.cons_append, List.nil_append] at *
    rw [splitTop_walk A _ cur 0 0 (h A (by simp))]
    rw [splitTop_cons]
    simp only [hsep, beq_self_eq_true, Bool.and_self, ite_true]
    have := splitTop_args sep hsep B as [] (fun X hX => h X (by simp_all))
    simp only [joinArgs] at this
    rw [this]; simp

end PP
