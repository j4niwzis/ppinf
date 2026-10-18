/-
  Theorem 9: the machine's list scans (`closeAt`, `splitTop`, `afterCommas`, `paste`) as left
  folds over an explicit state -- the form Mathlib's `Primrec.list_foldl` takes.
-/
import Semantics

namespace PP

/-! `closeAt`: depth, tokens so far, what is left, and the answer once found. -/

abbrev CState := Nat × List Tok × List Tok × Option (List Tok × Tok × List Tok)

def closeStep (s : CState) (x : Tok) : CState :=
  match s.2.2.2 with
  | some _ => s
  | none =>
    let rem := s.2.2.1.tail
    if x.s == ")" then
      (if s.1 == 0 then (s.1, s.2.1, rem, some (s.2.1.reverse, x, rem)) else (s.1 - 1, x :: s.2.1, rem, none))
    else if x.s == "(" then (s.1 + 1, x :: s.2.1, rem, none)
    else (s.1, x :: s.2.1, rem, none)

theorem closeStep_found (s : CState) (r : List Tok × Tok × List Tok) (h : s.2.2.2 = some r) : ∀ xs : List Tok, (xs.foldl closeStep s) = s
  | [] => rfl
  | x :: xs => by
    have : closeStep s x = s := by unfold closeStep; rw [h]
    simp only [List.foldl_cons, this]; exact closeStep_found s r h xs

theorem closeAt_fold : ∀ (xs : List Tok) (d : Nat) (acc : List Tok),
    (xs.foldl closeStep (d, acc, xs, none)).2.2.2 = closeAt d xs acc
  | [], d, acc => by simp [closeAt]
  | x :: xs, d, acc => by
    simp only [List.foldl_cons]
    unfold closeAt
    by_cases h1 : (x.s == ")") = true
    · by_cases h2 : (d == 0) = true
      · have : closeStep (d, acc, x :: xs, none) x = (d, acc, xs, some (acc.reverse, x, xs)) := by
          simp [closeStep, h1, h2]
        rw [this, closeStep_found _ _ rfl]; simp [h1, h2]
      · have : closeStep (d, acc, x :: xs, none) x = (d - 1, x :: acc, xs, none) := by
          simp [closeStep, h1, h2]
        rw [this, closeAt_fold xs]; simp [h1, h2]
    · by_cases h2 : (x.s == "(") = true
      · have : closeStep (d, acc, x :: xs, none) x = (d + 1, x :: acc, xs, none) := by
          simp [closeStep, h1, h2]
        rw [this, closeAt_fold xs]; simp [h1, h2]
      · have : closeStep (d, acc, x :: xs, none) x = (d, x :: acc, xs, none) := by
          simp [closeStep, h1, h2]
        rw [this, closeAt_fold xs]; simp [h1, h2]

/-! `splitTop`: depth, the current argument (reversed), the finished ones (reversed). -/

abbrev SState := Nat × List Tok × List (List Tok)

def splitStep (s : SState) (x : Tok) : SState :=
  if x.s == "," && s.1 == 0 then (s.1, [], s.2.1.reverse :: s.2.2) else (depthAfter s.1 x, x :: s.2.1, s.2.2)

def splitEnd (s : SState) : List (List Tok) := (s.2.1.reverse :: s.2.2).reverse

theorem splitTop_fold : ∀ (xs : List Tok) (d : Nat) (cur : List Tok) (G : List (List Tok)),
    splitEnd (xs.foldl splitStep (d, cur, G)) = G.reverse ++ splitTop d xs cur
  | [], d, cur, G => by simp [splitEnd, splitTop]
  | x :: xs, d, cur, G => by
    simp only [List.foldl_cons]
    unfold splitTop
    by_cases h : (x.s == "," && d == 0) = true
    · have : splitStep (d, cur, G) x = (d, [], cur.reverse :: G) := by simp [splitStep, h]
      rw [this, splitTop_fold xs]
      have h' : (x.s == "," && d == 0) = true := h
      simp only [Bool.and_eq_true] at h'
      simp [h'.1, h'.2]
    · have : splitStep (d, cur, G) x = (depthAfter d x, x :: cur, G) := by simp [splitStep, h]
      rw [this, splitTop_fold xs]
      have h' : ¬ ((x.s == ",") = true ∧ (d == 0) = true) := by simpa using h
      rw [if_neg (by simpa using h')]

/-! `afterCommas`: commas still to pass, depth, what is left, the answer once found. -/

abbrev AState := Nat × Nat × List Tok × Option (List Tok)

def commaStep (s : AState) (x : Tok) : AState :=
  match s.2.2.2 with
  | some _ => s
  | none =>
    let rem := s.2.2.1.tail
    if x.s == "," && s.2.1 == 0 then
      (if s.1 == 1 then (0, s.2.1, rem, some rem) else (s.1 - 1, s.2.1, rem, none))
    else (s.1, depthAfter s.2.1 x, rem, none)

theorem commaStep_found (s : AState) (r : List Tok) (h : s.2.2.2 = some r) : ∀ xs : List Tok, (xs.foldl commaStep s) = s
  | [] => rfl
  | x :: xs => by
    have : commaStep s x = s := by unfold commaStep; rw [h]
    simp only [List.foldl_cons, this]; exact commaStep_found s r h xs

theorem afterCommas_fold : ∀ (xs : List Tok) (k d : Nat),
    ((xs.foldl commaStep (k + 1, d, xs, none)).2.2.2).getD [] = afterCommas (k + 1) d xs
  | [], k, d => by simp [afterCommas]
  | x :: xs, k, d => by
    simp only [List.foldl_cons]
    unfold afterCommas
    by_cases h : (x.s == "," && d == 0) = true
    · have h' : (x.s == ",") = true ∧ (d == 0) = true := by simpa using h
      cases k with
      | zero =>
        have : commaStep (0 + 1, d, x :: xs, none) x = (0, d, xs, some xs) := by simp [commaStep, h]
        rw [this, commaStep_found _ _ rfl]; simp [h'.1, h'.2, afterCommas]
      | succ k =>
        have : commaStep (k + 1 + 1, d, x :: xs, none) x = (k + 1, d, xs, none) := by simp [commaStep, h]
        rw [this, afterCommas_fold xs k d]; simp [h'.1, h'.2]
    · have : commaStep (k + 1, d, x :: xs, none) x = (k + 1, depthAfter d x, xs, none) := by simp [commaStep, h]
      rw [this, afterCommas_fold xs k]
      have h' : ¬ ((x.s == ",") = true ∧ (d == 0) = true) := by simpa using h
      rw [if_neg (by simpa using h')]

/-! `paste`: the replacement so far (reversed) and whether a `##` waits for its right side;
    `none` once a paste fails. -/

def RTok.isOp : RTok → Bool
  | .op => true
  | _ => false

abbrev PState := Option (List RTok × Bool)

def pasteStep (s : PState) (x : RTok) : PState :=
  match s with
  | none => none
  | some (acc, true) =>
    match acc with
    | a :: acc' => (pasteTwo a x).map fun c => (c :: acc', false)
    | [] => none
  | some (acc, false) =>
    if x.isOp then (if acc.isEmpty then none else some (acc, true)) else some (x :: acc, false)

def pasteEnd : PState → Option (List RTok)
  | some (acc, false) => some acc.reverse
  | _ => none

theorem pasteStep_none : ∀ xs : List RTok, xs.foldl pasteStep none = none
  | [] => rfl
  | _ :: xs => pasteStep_none xs

theorem paste_fold : ∀ (acc xs : List RTok), pasteEnd (xs.foldl pasteStep (some (acc, false))) = paste.go acc xs := by
  intro acc xs
  induction acc, xs using paste.go.induct with
  | case1 acc => simp [pasteEnd, paste.go]
  | case2 a acc b rest ih =>
    simp only [List.foldl_cons]
    have h1 : pasteStep (some (a :: acc, false)) .op = some (a :: acc, true) := by simp [pasteStep, RTok.isOp]
    rw [h1, paste.go]
    cases hp : pasteTwo a b with
    | none => simp [pasteStep, hp, pasteStep_none, pasteEnd]
    | some c =>
      have h2 : pasteStep (some (a :: acc, true)) b = some (c :: acc, false) := by simp [pasteStep, hp]
      rw [h2]; simpa using ih c
  | case3 x tail h =>
    rw [paste.go.eq_3 x tail h]
    cases x with
    | nil => simp [pasteStep, RTok.isOp, pasteStep_none, pasteEnd]
    | cons a acc =>
      cases tail with
      | nil => simp [pasteStep, RTok.isOp, pasteEnd]
      | cons b rest => exact absurd rfl (fun e => h a acc b rest rfl e)
  | case4 acc x rest h hx ih =>
    rw [paste.go.eq_4 acc x rest hx (fun _ _ _ _ _ e _ => hx e)]
    have : x.isOp = false := by cases x <;> simp_all [RTok.isOp]
    simp only [List.foldl_cons, pasteStep, this]
    exact ih

end PP
