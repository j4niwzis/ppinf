/-
  Theorem 10: one call of a function-like macro with a plain body, on arguments that expand
  to numerals -- the call becomes the rescan of its marked replacement.
-/
import NodeBase

namespace PP

theorem toks_map_t (l : List Tok) (r : List RTok) : toks (l.map RTok.t ++ r) = l ++ toks r := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, List.cons_append, toks, List.filterMap_cons, tokOf] at ih ⊢; rw [ih]

theorem toks_t (x : Tok) (r : List RTok) : toks (RTok.t x :: r) = x :: toks r := rfl

theorem argShape_of_ok {Γ : Env} : ∀ {as : List (List Tok)} {vs : List Nat}, ArgsOK Γ as vs → ∀ A ∈ as, ArgShape A
  | [], [], .nil, _, h => by simp at h
  | _ :: _, _ :: _, .cons hA hrest, A, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact hA.1
    · exact argShape_of_ok hrest A h

theorem expands_nil (Γ : Env) : Expands Γ [] 0 := fun c => ⟨1, [], [], c, by simp [expand, scan, finalize], rfl⟩

theorem expands_getD {Γ : Env} : ∀ {as : List (List Tok)} {vs : List Nat}, ArgsOK Γ as vs → ∀ j,
    Expands Γ (as.getD j []) (vs.getD j 0)
  | [], [], .nil, j => by simpa using expands_nil Γ
  | _ :: _, _ :: _, .cons hA _, 0 => by simpa using hA.2
  | _ :: _, _ :: _, .cons _ hrest, j + 1 => by simpa using expands_getD hrest j

theorem argsOK_length {Γ : Env} {as : List (List Tok)} {vs : List Nat} (h : ArgsOK Γ as vs) : as.length = vs.length :=
  (all2_length h).symm

theorem bind_plain {as : List (List Tok)} (sep : Tok) (hsep : sep.s = ",") (hs : ∀ A ∈ as, ArgShape A) (k : Nat)
    (hk : as.length = k) (hne : k ≠ 0 ∨ as = []) : bind k false (joinArgs sep as) = some (as, []) := by
  unfold bind
  rcases hne with hne | rfl
  · cases as with
    | nil => simp at hk; omega
    | cons A as =>
    rw [splitTop_args sep hsep A as [] hs]
    subst hk
    simp
  · subst hk; simp [joinArgs, splitTop]

/-- **A plain call.** -/
theorem call_plain (Γ : Env) {x lp sep rp : Tok} {as : List (List Tok)} {vs : List Nat} {k : Nat} {body : List BTok}
    (hf : Γ.find x.s = some (.fn k false body)) (hid : x.s ∉ x.H) (hlp : lp.s = "(") (hsep : sep.s = ",")
    (hrp : rp.s = ")") (hk : as.length = k) (hne : k ≠ 0 ∨ as = []) (hargs : ArgsOK Γ as vs) (hplain : Plain body)
    (c : Nat) : ∃ N outs c1, All2 (fun j o => IsNum o (vs.getD j 0) ∧ Fin o) (paramIdx body) outs ∧
      ∀ n, N ≤ n → ∀ q, scan Γ n c1 (mark c (x.s :: inter x.H rp.H) (toks (plainOut body outs))) = some q →
        ∃ st', scan Γ (n + 1) c (callToks x lp sep rp as) = some (q.1, st', q.2.2) := by
  have hs := argShape_of_ok hargs
  obtain ⟨N, outs, st, c1, e, hos⟩ := subst_plain Γ body hplain as (fun j => vs.getD j 0) (expands_getD hargs) (c + 1)
  refine ⟨N, outs, c1, hos, fun n hn q hq => ?_⟩
  have hc := closeAt_args sep rp hsep hrp as [] [] hs
  simp only [List.reverse_nil, List.nil_append] at hc
  have hb := bind_plain sep hsep hs k hk hne
  have hr := subst_mono Γ e n hn
  have hpaste := paste_noop _ (noOp_plainOut body outs)
  have := scan_fn_step Γ n c x lp rp (joinArgs sep as) ([] : List Tok) hid hf hlp hc as ([] : List Tok) _ _ q hb hr hpaste
    (by simpa using hq)
  exact ⟨_, this⟩

end PP
