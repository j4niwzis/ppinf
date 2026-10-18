/-
  The input of a pp-computation, `F(x̄₁, …, x̄ₖ)`, as tokens (Theorem 9): the tokenizer splits
  at punctuation and spaces, so the call is `F`'s tokens, `(`, the arguments' `( ~ )` groups
  separated by `,`, and `)`.
-/
import Translate

namespace PP

/-- The arguments `x̄₁, …, x̄ₖ`, separated by `, `. -/
def argChars (xs : List Nat) : List Char := [',', ' '].intercalate (xs.map unaryChars)

/-- The call `F(x̄₁, …, x̄ₖ)`, each argument in unary: `(~)` repeated. -/
def call (F : String) (xs : List Nat) : String := String.ofList (F.toList ++ '(' :: argChars xs ++ [')'])

/-- The token spellings of `n̄`. -/
def unaryToks (n : Nat) : List String := (input (unary n)).map (·.s)

def flushOf (cur : String) (acc : List String) : List String := if cur.isEmpty = true then acc else cur :: acc

/-- One character that starts no `##` or `...`. -/
theorem go_other (c : Char) (t : List Char) (cur : String) (acc : List String)
    (h1 : c = '#' → ∀ r, t ≠ '#' :: r) (h2 : c = '.' → ∀ r, t ≠ '.' :: '.' :: r) :
    tokenize.go (c :: t) cur acc =
      if identChar c = true then tokenize.go t (cur.push c) acc
      else if c.isWhitespace = true then tokenize.go t "" (flushOf cur acc)
      else tokenize.go t "" (c.toString :: flushOf cur acc) := by
  rw [tokenize.go.eq_4 cur acc c t (fun r e ht => h1 e r ht) (fun r e ht => h2 e r ht)]; rfl

theorem go_nil (cur : String) (acc : List String) : tokenize.go [] cur acc = (flushOf cur acc).reverse := by
  rw [tokenize.go.eq_1]; rfl

theorem go_hash (r : List Char) (cur : String) (acc : List String) :
    tokenize.go ('#' :: '#' :: r) cur acc = tokenize.go r "" ("##" :: flushOf cur acc) := by
  rw [tokenize.go.eq_2]; rfl

theorem go_dots (r : List Char) (cur : String) (acc : List String) :
    tokenize.go ('.' :: '.' :: '.' :: r) cur acc = tokenize.go r "" ("..." :: flushOf cur acc) := by
  rw [tokenize.go.eq_3]; rfl

/-- What a character `c` that is punctuation (not `#`, not `.`) or a space does next to
    anything before it. -/
theorem go_split (c : Char) (hc3 : c ≠ '#') (hc4 : c ≠ '.') (hc1 : identChar c = false) (out : List String → List String)
    (hout : ∀ cur acc R, tokenize.go (c :: R) cur acc = tokenize.go R "" (out (flushOf cur acc))) :
    ∀ cs cur acc R, tokenize.go (cs ++ c :: R) cur acc = tokenize.go R "" (out (tokenize.go cs cur acc).reverse) := by
  intro cs cur acc
  induction cs, cur, acc using tokenize.go.induct with
  | case1 cur acc => intro R; rw [List.nil_append, hout, go_nil, List.reverse_reverse]
  | case2 cur acc _ r ih =>
    intro R; rw [List.cons_append, List.cons_append, go_hash, go_hash]; exact ih R
  | case3 cur acc _ r ih =>
    intro R; rw [List.cons_append, List.cons_append, List.cons_append, go_dots, go_dots]; exact ih R
  | case4 cur acc c' r n1 n2 hid ih =>
    intro R
    have hne1 : c' ≠ '#' := by intro e; subst e; simp [identChar] at hid
    have hne2 : c' ≠ '.' := by intro e; subst e; simp [identChar] at hid
    rw [List.cons_append, go_other c' _ cur acc (fun e => absurd e hne1) (fun e => absurd e hne2),
      go_other c' r cur acc (fun e => absurd e hne1) (fun e => absurd e hne2), if_pos hid, if_pos hid]
    exact ih R
  | case5 cur acc _ c' r n1 n2 hid hws ih =>
    intro R
    have l1 : c' = '#' → ∀ r1, r ++ c :: R ≠ '#' :: r1 := by
      intro e r1 h'; cases r with
      | nil => simp at h'; exact hc3 h'.1
      | cons a r => simp at h'; exact n1 r e (by rw [h'.1])
    have l2 : c' = '.' → ∀ r1, r ++ c :: R ≠ '.' :: '.' :: r1 := by
      intro e r1 h'; cases r with
      | nil => simp at h'; exact hc4 h'.1
      | cons a r =>
        cases r with
        | nil => simp at h'; exact hc4 h'.2.1
        | cons b r => simp at h'; exact n2 r e (by rw [h'.1, h'.2.1])
    rw [List.cons_append, go_other c' _ cur acc l1 l2, go_other c' r cur acc (fun e r1 h' => n1 r1 e h')
      (fun e r1 h' => n2 r1 e h'), if_neg hid, if_neg hid, if_pos hws, if_pos hws]
    exact ih R
  | case6 cur acc _ c' r n1 n2 hid hws ih =>
    intro R
    have l1 : c' = '#' → ∀ r1, r ++ c :: R ≠ '#' :: r1 := by
      intro e r1 h'; cases r with
      | nil => simp at h'; exact hc3 h'.1
      | cons a r => simp at h'; exact n1 r e (by rw [h'.1])
    have l2 : c' = '.' → ∀ r1, r ++ c :: R ≠ '.' :: '.' :: r1 := by
      intro e r1 h'; cases r with
      | nil => simp at h'; exact hc4 h'.1
      | cons a r =>
        cases r with
        | nil => simp at h'; exact hc4 h'.2.1
        | cons b r => simp at h'; exact n2 r e (by rw [h'.1, h'.2.1])
    rw [List.cons_append, go_other c' _ cur acc l1 l2, go_other c' r cur acc (fun e r1 h' => n1 r1 e h')
      (fun e r1 h' => n2 r1 e h'), if_neg hid, if_neg hid, if_neg hws, if_neg hws]
    exact ih R

/-- The tokens of `n̄`, and of the arguments. -/
def unaryList (n : Nat) : List String := (List.replicate n ["(", "~", ")"]).flatten
def argToks (xs : List Nat) : List String := [","].intercalate (xs.map unaryList)

theorem go_punct (c : Char) (h3 : c ≠ '#') (h4 : c ≠ '.') (h1 : identChar c = false) (h2 : c.isWhitespace = false)
    (R : List Char) (cur : String) (acc : List String) :
    tokenize.go (c :: R) cur acc = tokenize.go R "" (c.toString :: flushOf cur acc) := by
  rw [go_other c R cur acc (fun e => absurd e h3) (fun e => absurd e h4)]; simp [h1, h2]

theorem go_space (R : List Char) (cur : String) (acc : List String) :
    tokenize.go (' ' :: R) cur acc = tokenize.go R "" (flushOf cur acc) := by
  rw [go_other ' ' R cur acc (fun e => by simp at e) (fun e => by simp at e)]
  have h1 : identChar ' ' = false := by decide
  have h2 : ' '.isWhitespace = true := by decide
  simp [h1, h2]

theorem flushOf_empty (acc : List String) : flushOf "" acc = acc := rfl

theorem go_unary : ∀ (n : Nat) (R : List Char) (acc : List String),
    tokenize.go (unaryChars n ++ R) "" acc = tokenize.go R "" ((unaryList n).reverse ++ acc)
  | 0, R, acc => by simp [unaryChars, unaryList]
  | n + 1, R, acc => by
    simp only [unaryChars, unaryList, List.replicate_succ, List.flatten_cons, List.cons_append, List.nil_append,
      List.append_assoc]
    rw [go_punct '(' (by decide) (by decide) (by decide) (by decide), flushOf_empty,
      go_punct '~' (by decide) (by decide) (by decide) (by decide), flushOf_empty,
      go_punct ')' (by decide) (by decide) (by decide) (by decide), flushOf_empty]
    have := go_unary n R (')'.toString :: '~'.toString :: '('.toString :: acc)
    simp only [unaryChars, unaryList] at this
    rw [this]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.append_assoc,
      List.cons_append, List.singleton_append]
    rfl

theorem go_args_cons : ∀ (a : Nat) (l : List Nat) (R : List Char) (acc : List String),
    tokenize.go (argChars (a :: l) ++ R) "" acc = tokenize.go R "" ((argToks (a :: l)).reverse ++ acc)
  | a, [], R, acc => by simp [argChars, argToks, go_unary]
  | a, b :: l, R, acc => by
    simp only [argChars, argToks, List.map_cons, List.intercalate_cons_cons, List.append_assoc, List.cons_append,
      List.nil_append]
    rw [go_unary, go_punct ',' (by decide) (by decide) (by decide) (by decide), flushOf_empty, go_space, flushOf_empty]
    have := go_args_cons b l R (','.toString :: ((unaryList a).reverse ++ acc))
    simp only [argChars, argToks, List.map_cons] at this
    rw [this]
    simp only [List.reverse_append, List.reverse_cons, List.append_assoc, List.singleton_append]
    rfl

theorem go_args (xs : List Nat) (R : List Char) (acc : List String) :
    tokenize.go (argChars xs ++ R) "" acc = tokenize.go R "" ((argToks xs).reverse ++ acc) := by
  cases xs with
  | nil => simp [argChars, argToks]
  | cons a l => exact go_args_cons a l R acc

/-- **The input.** -/
theorem input_call (F : String) (xs : List Nat) :
    input (call F xs) = (tokenize F ++ "(" :: argToks xs ++ [")"]).map fun t => { s := t } := by
  unfold input call tokenize
  rw [String.toList_ofList, List.append_assoc, List.cons_append, go_split '(' (by decide) (by decide) (by decide) (fun f => "(" :: f)
    (fun cur acc R => go_punct '(' (by decide) (by decide) (by decide) (by decide) R cur acc) F.toList "" [] (argChars xs ++ [')'])]
  rw [go_args, go_punct ')' (by decide) (by decide) (by decide) (by decide), flushOf_empty, go_nil, flushOf_empty]
  simp only [List.reverse_cons, List.reverse_append, List.reverse_reverse, List.append_assoc, List.cons_append,
    List.singleton_append, List.nil_append]
  rfl

end PP
