/-
  Theorem 10, composition: the shape of a composition's replacement -- `h ( g₀ ( ā ) , … )`
  -- and of the marked tokens it is made of.
-/
import NodeLeaf

namespace PP

/-! `All2` splits along appends. -/

theorem all2_append {α β : Type} {R : α → β → Prop} : ∀ {l1 l2 : List α} {outs : List β}, All2 R (l1 ++ l2) outs →
    ∃ o1 o2, outs = o1 ++ o2 ∧ All2 R l1 o1 ∧ All2 R l2 o2
  | [], _, outs, h => ⟨[], outs, rfl, .nil, h⟩
  | a :: l1, l2, outs, h => by
    cases h with
    | cons hr hrest =>
      obtain ⟨o1, o2, rfl, h1, h2⟩ := all2_append hrest
      exact ⟨_ :: o1, o2, rfl, .cons hr h1, h2⟩

theorem all2_length {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {outs : List β}, All2 R l outs → outs.length = l.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ h => by simp [all2_length h]

/-! `paramIdx` and `plainOut` along appends. -/

theorem paramIdx_append : ∀ (b1 b2 : List BTok), paramIdx (b1 ++ b2) = paramIdx b1 ++ paramIdx b2
  | [], _ => rfl
  | .param j :: b1, b2 => by simp [paramIdx, paramIdx_append b1 b2]
  | .tok _ :: b1, b2 => by simp [paramIdx, paramIdx_append b1 b2]
  | .paste :: b1, b2 => by simp [paramIdx, paramIdx_append b1 b2]
  | .va :: b1, b2 => by simp [paramIdx, paramIdx_append b1 b2]

theorem plainOut_append : ∀ (b1 b2 : List BTok) (o1 o2 : List (List Tok)), o1.length = (paramIdx b1).length →
    plainOut (b1 ++ b2) (o1 ++ o2) = plainOut b1 o1 ++ plainOut b2 o2
  | [], _, [], _, _ => rfl
  | [], _, _ :: _, _, h => by simp [paramIdx] at h
  | .param j :: b1, b2, [], _, h => by simp [paramIdx] at h
  | .param j :: b1, b2, o :: o1, o2, h => by
    simp only [paramIdx, List.length_cons, Nat.add_right_cancel_iff] at h
    simp [plainOut, plainOut_append b1 b2 o1 o2 h]
  | .tok _ :: b1, b2, o1, o2, h => by simp only [paramIdx] at h; simp [plainOut, plainOut_append b1 b2 o1 o2 h]
  | .paste :: b1, b2, o1, o2, h => by simp only [paramIdx] at h; simp [plainOut, plainOut_append b1 b2 o1 o2 h]
  | .va :: b1, b2, o1, o2, h => by simp only [paramIdx] at h; simp [plainOut, plainOut_append b1 b2 o1 o2 h]

theorem toks_append (a b : List RTok) : toks (a ++ b) = toks a ++ toks b := by simp [toks]

/-- A plain body of tokens only. -/
theorem plainOut_toks (l : List String) (outs : List (List Tok)) :
    toks (plainOut (l.map tk) outs) = l.map fun s => { s } := by
  induction l with
  | nil => simp [plainOut, toks]
  | cons s l ih => simp only [List.map_cons, tk, plainOut, toks_t]; rw [ih]

/-! The arguments `ā`: `x₀ , … , xₖ₋₁`. -/

def argsBody (k : Nat) : List BTok := joinB ((prms k).map ([·]))

theorem joinB_cons_cons (a b : List BTok) (l : List (List BTok)) : joinB (a :: b :: l) = a ++ ([tk ","] ++ joinB (b :: l)) := by
  simp [joinB, List.intercalate_cons_cons]

theorem joinArgs_cons_cons (sep : Tok) (a b : List Tok) (l : List (List Tok)) :
    joinArgs sep (a :: b :: l) = a ++ (sep :: joinArgs sep (b :: l)) := by
  simp [joinArgs, List.intercalate_cons_cons]

theorem toks_map (l : List Tok) : toks (l.map RTok.t) = l := by have := toks_map_t l []; simpa [toks] using this

theorem paramIdx_joinB_single : ∀ (ps : List Nat), paramIdx (joinB (ps.map fun i => [prm i])) = ps
  | [] => rfl
  | [i] => by simp [joinB, prm, paramIdx]
  | i :: j :: ps => by
    have ih : paramIdx (joinB ([prm j] :: ps.map fun i => [prm i])) = j :: ps := by
      simpa using paramIdx_joinB_single (j :: ps)
    rw [List.map_cons, List.map_cons, joinB_cons_cons, paramIdx_append, paramIdx_append, ih]
    rfl

/-- The comma token of a body, as `toks` gives it. -/
def comma : Tok := { s := "," }

theorem toks_joinB_single : ∀ (ps : List Nat) (outs : List (List Tok)), outs.length = ps.length →
    toks (plainOut (joinB (ps.map fun i => [prm i])) outs) = joinArgs comma outs
  | [], [], _ => by simp [joinB, plainOut, toks, joinArgs]
  | [i], [o], _ => by simp [joinB, prm, plainOut, toks_map_t, toks_map, joinArgs]
  | i :: j :: ps, o :: o' :: outs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    have ih : toks (plainOut (joinB ([prm j] :: ps.map fun i => [prm i])) (o' :: outs)) = joinArgs comma (o' :: outs) := by
      simpa using toks_joinB_single (j :: ps) (o' :: outs) (by simpa using h)
    rw [List.map_cons, List.map_cons, joinB_cons_cons]
    simp only [List.cons_append, List.nil_append, prm, tk, plainOut]
    rw [toks_map_t, toks_t]
    simp only [prm, tk] at ih
    rw [ih, joinArgs_cons_cons]; rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | [_], _ :: _ :: _, h => by simp at h

/-! Lists of bodies joined by commas. -/

theorem paramIdx_joinB : ∀ (bs : List (List BTok)), paramIdx (joinB bs) = (bs.map paramIdx).flatten
  | [] => rfl
  | [b] => by simp [joinB]
  | a :: b :: bs => by
    rw [joinB_cons_cons, paramIdx_append, paramIdx_append, paramIdx_joinB (b :: bs)]
    simp [tk, paramIdx]

theorem all2_flatten {α β : Type} {R : α → β → Prop} : ∀ {L : List (List α)} {outs : List β}, All2 R L.flatten outs →
    ∃ chunks : List (List β), outs = chunks.flatten ∧ All2 (All2 R) L chunks
  | [], outs, h => by cases h; exact ⟨[], rfl, .nil⟩
  | l :: L, outs, h => by
    obtain ⟨o1, o2, rfl, h1, h2⟩ := all2_append (by simpa using h)
    obtain ⟨chunks, rfl, hc⟩ := all2_flatten h2
    exact ⟨o1 :: chunks, rfl, .cons h1 hc⟩

theorem toks_joinB : ∀ (bs : List (List BTok)) (chunks : List (List (List Tok))),
    All2 (fun b ch => ch.length = (paramIdx b).length) bs chunks →
    toks (plainOut (joinB bs) chunks.flatten) = joinArgs comma (List.zipWith (fun b ch => toks (plainOut b ch)) bs chunks)
  | [], [], _ => by simp [joinB, plainOut, toks, joinArgs]
  | [b], [ch], _ => by simp [joinB, joinArgs]
  | a :: b :: bs, ca :: cb :: cs, .cons ha hrest => by
    have ih := toks_joinB (b :: bs) (cb :: cs) hrest
    rw [joinB_cons_cons, List.flatten_cons, plainOut_append _ _ _ _ ha]
    rw [show (cb :: cs).flatten = [] ++ (cb :: cs).flatten by simp, plainOut_append [tk ","] _ [] _ (by simp [tk, paramIdx])]
    rw [toks_append, toks_append, ih]
    simp only [tk, plainOut, List.zipWith_cons_cons, joinArgs_cons_cons]
    rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | [_], _ :: _ :: _, h => by cases h with | cons _ h2 => cases h2
  | _ :: _ :: _, [_], h => by cases h with | cons _ h2 => cases h2

/-! Marking a call. -/

def markOne (c : Nat) (K : List Name) (x : Tok) : Tok := { x with H := union K x.H, o := c, P := K }

theorem mark_eq (c : Nat) (K : List Name) (xs : List Tok) : mark c K xs = xs.map (markOne c K) := rfl

theorem map_joinArgs (f : Tok → Tok) (sep : Tok) : ∀ (as : List (List Tok)),
    (joinArgs sep as).map f = joinArgs (f sep) (as.map (List.map f))
  | [] => rfl
  | [a] => by simp [joinArgs]
  | a :: b :: as => by
    rw [joinArgs_cons_cons, List.map_append, List.map_cons, map_joinArgs f sep (b :: as)]
    simp [joinArgs_cons_cons]

theorem mark_callToks (c : Nat) (K : List Name) (x lp sep rp : Tok) (as : List (List Tok)) :
    mark c K (callToks x lp sep rp as) =
      callToks (markOne c K x) (markOne c K lp) (markOne c K sep) (markOne c K rp) (as.map (mark c K)) := by
  simp only [mark_eq, callToks, List.map_cons, List.map_append, map_joinArgs]; rfl

end PP
