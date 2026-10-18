/-
  Theorem 10: plain calls whose arguments expand to anything described by a predicate --
  tuples, streams with names -- not only numerals.
-/
import Frame2
import BraPong

namespace PP

def ExpandsP (Γ : Env) (A : List Tok) (P : List Tok → Prop) : Prop :=
  ∀ c, ∃ N o st c', expand Γ N c A = some (o, st, c') ∧ P o

theorem substFrom_plainP (Γ : Env) (whole : List BTok) (hw : Plain whole) (named : List (List Tok))
    (Ps : Nat → List Tok → Prop) (hv : ∀ j, ExpandsP Γ (named.getD j []) (Ps j)) :
    ∀ (bs : List BTok) (i : Nat), (∀ b ∈ bs, b ∈ whole) → ∀ c, ∃ N outs st c',
      substFrom Γ N whole bs i c named [] = some (plainOut bs outs, st, c') ∧
      All2 (fun j o => Ps j o ∧ Fin o) (paramIdx bs) outs
  | [], i, _, c => ⟨1, [], [], c, by simp [substFrom, plainOut], by simpa [paramIdx] using All2.nil⟩
  | b :: bs, i, hb, c => by
    have hbw := hw b (hb b (by simp))
    have hbs : ∀ b ∈ bs, b ∈ whole := fun b h => hb b (by simp [h])
    cases b with
    | paste => exact absurd rfl hbw.1
    | va => exact absurd rfl hbw.2
    | tok s =>
      obtain ⟨N, outs, st, c', e, hos⟩ := substFrom_plainP Γ whole hw named Ps hv bs (i + 1) hbs c
      exact ⟨N, outs, st, c', by simp [substFrom, piece, e, plainOut], by simpa [paramIdx] using hos⟩
    | param j =>
      obtain ⟨N1, o, st0, c0, e0, ho⟩ := hv j c
      obtain ⟨N2, outs, st, c', e, hos⟩ := substFrom_plainP Γ whole hw named Ps hv bs (i + 1) hbs c0
      refine ⟨max N1 N2, o :: outs, st0 ++ st, c', ?_, ?_⟩
      · have e0' := expand_mono (scanMono Γ N1) c _ _ e0 (max N1 N2) (Nat.le_max_left _ _)
        have e' := substMono_of_scan (scanMono Γ N2) whole bs (i + 1) c0 named [] _ e (max N1 N2) (Nat.le_max_right _ _)
        simp only [substFrom, piece, one, adjacent_plain hw, Bool.false_eq_true, ite_false, e0', Option.map_some,
          Option.bind_some, e', plainOut]
      · exact All2.cons ⟨ho, expand_fin e0⟩ hos

/-- **A plain call**, its arguments described by predicates. -/
theorem call_plainP (Γ : Env) {x lp sep rp : Tok} {as : List (List Tok)} {k : Nat} {body : List BTok}
    (hf : Γ.find x.s = some (.fn k false body)) (hid : x.s ∉ x.H) (hlp : lp.s = "(") (hsep : sep.s = ",")
    (hrp : rp.s = ")") (hk : as.length = k) (hne : k ≠ 0 ∨ as = []) (hs : ∀ A ∈ as, ArgShape A)
    (Ps : Nat → List Tok → Prop) (hargs : ∀ j, ExpandsP Γ (as.getD j []) (Ps j)) (hplain : Plain body)
    (c : Nat) : ∃ N outs c1, All2 (fun j o => Ps j o ∧ Fin o) (paramIdx body) outs ∧
      ∀ n, N ≤ n → ∀ q, scan Γ n c1 (mark c (x.s :: inter x.H rp.H) (toks (plainOut body outs))) = some q →
        ∃ st', scan Γ (n + 1) c (callToks x lp sep rp as) = some (q.1, st', q.2.2) := by
  obtain ⟨N, outs, st, c1, e, hos⟩ := substFrom_plainP Γ body hplain as Ps hargs body 0 (fun _ h => h) (c + 1)
  refine ⟨N, outs, c1, hos, fun n hn q hq => ?_⟩
  have hc := closeAt_args sep rp hsep hrp as [] [] hs
  simp only [List.reverse_nil, List.nil_append] at hc
  have hb := bind_plain sep hsep hs k hk hne
  have hr := subst_mono Γ (by unfold subst; exact e) n hn
  have hpaste := paste_noop _ (noOp_plainOut body outs)
  have := scan_fn_step Γ n c x lp rp (joinArgs sep as) ([] : List Tok) hid hf hlp hc as ([] : List Tok) _ _ q hb hr hpaste
    (by simpa using hq)
  exact ⟨_, this⟩

end PP
