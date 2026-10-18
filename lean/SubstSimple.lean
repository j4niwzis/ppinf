/-
  Theorem 10: substitution into a body with no `##` and no `__VA_ARGS__` -- every parameter
  occurrence becomes its argument, expanded alone and finalized.
-/
import Mono
import Balanced
import Exec
import Input

namespace PP

/-- Two lists related element by element. -/
inductive All2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : All2 R [] []
  | cons {a b as bs} : R a b → All2 R as bs → All2 R (a :: as) (b :: bs)

/-- Spelled `n̄`. -/
def IsNum (xs : List Tok) (v : Nat) : Prop := xs.map (·.s) = unaryList v

/-- `A` expands to `v̄` from any counter, with some fuel (and so with any more). -/
def Expands (Γ : Env) (A : List Tok) (v : Nat) : Prop :=
  ∀ c, ∃ N o st c', expand Γ N c A = some (o, st, c') ∧ IsNum o v

/-- Finalized: hiding at most its own name. -/
def Fin (xs : List Tok) : Prop := ∀ t ∈ xs, ∀ m ∈ t.H, m = t.s

/-- A body with only tokens and named parameters. -/
def Plain (body : List BTok) : Prop := ∀ b ∈ body, b ≠ .paste ∧ b ≠ .va

/-- The parameters a body uses, in order, with repeats. -/
def paramIdx : List BTok → List Nat
  | [] => []
  | .param j :: bs => j :: paramIdx bs
  | _ :: bs => paramIdx bs

/-- The replacement of a plain body, its parameter occurrences given in order. -/
def plainOut : List BTok → List (List Tok) → List RTok
  | [], _ => []
  | .tok s :: bs, outs => RTok.t { s } :: plainOut bs outs
  | .param _ :: bs, o :: outs => o.map RTok.t ++ plainOut bs outs
  | .param _ :: bs, [] => plainOut bs []
  | _ :: bs, outs => plainOut bs outs

theorem adjacent_plain {body : List BTok} (h : Plain body) (i : Nat) : adjacentPaste body i = false := by
  unfold adjacentPaste
  have h1 : body[i - 1]? ≠ some .paste := by
    intro e; exact (h _ (List.mem_of_getElem? e)).1 rfl
  have h2 : body[i + 1]? ≠ some .paste := by
    intro e; exact (h _ (List.mem_of_getElem? e)).1 rfl
  simp [h1, h2]

theorem fin_finalize (xs : List Tok) : Fin (finalize xs) := by
  intro t ht m hm
  simp only [finalize, List.mem_map] at ht
  obtain ⟨x, _, rfl⟩ := ht
  simp only at hm
  split at hm <;> simp_all

theorem isNum_finalize {xs : List Tok} {v : Nat} (h : IsNum xs v) : IsNum (finalize xs) v := by
  unfold IsNum at *; simp [finalize, Function.comp_def, h]

theorem expand_fin {Γ : Env} {n c : Nat} {A o : List Tok} {st : List Step} {c' : Nat}
    (h : expand Γ n c A = some (o, st, c')) : Fin o := by
  unfold expand at h
  obtain ⟨q, _, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  rw [← e.1]; exact fin_finalize _

theorem substFrom_plain (Γ : Env) (whole : List BTok) (hw : Plain whole) (named : List (List Tok)) (vs : Nat → Nat)
    (hv : ∀ j, Expands Γ (named.getD j []) (vs j)) :
    ∀ (bs : List BTok) (i : Nat), (∀ b ∈ bs, b ∈ whole) → ∀ c, ∃ N outs st c',
      substFrom Γ N whole bs i c named [] = some (plainOut bs outs, st, c') ∧
      All2 (fun j o => IsNum o (vs j) ∧ Fin o) (paramIdx bs) outs
  | [], i, _, c => ⟨1, [], [], c, by simp [substFrom, plainOut], by simpa [paramIdx] using All2.nil⟩
  | b :: bs, i, hb, c => by
    have hbw := hw b (hb b (by simp))
    have hbs : ∀ b ∈ bs, b ∈ whole := fun b h => hb b (by simp [h])
    cases b with
    | paste => exact absurd rfl hbw.1
    | va => exact absurd rfl hbw.2
    | tok s =>
      obtain ⟨N, outs, st, c', e, hos⟩ := substFrom_plain Γ whole hw named vs hv bs (i + 1) hbs c
      exact ⟨N, outs, st, c', by simp [substFrom, piece, e, plainOut], by simpa [paramIdx] using hos⟩
    | param j =>
      obtain ⟨N1, o, st0, c0, e0, ho⟩ := hv j c
      obtain ⟨N2, outs, st, c', e, hos⟩ := substFrom_plain Γ whole hw named vs hv bs (i + 1) hbs c0
      refine ⟨max N1 N2, o :: outs, st0 ++ st, c', ?_, ?_⟩
      · have e0' := expand_mono (scanMono Γ N1) c _ _ e0 (max N1 N2) (Nat.le_max_left _ _)
        have e' := substMono_of_scan (scanMono Γ N2) whole bs (i + 1) c0 named [] _ e (max N1 N2) (Nat.le_max_right _ _)
        simp only [substFrom, piece, one, adjacent_plain hw, Bool.false_eq_true, ite_false, e0', Option.map_some,
          Option.bind_some, e', plainOut]
      · exact All2.cons ⟨ho, expand_fin e0⟩ hos

theorem subst_plain (Γ : Env) (body : List BTok) (hw : Plain body) (named : List (List Tok)) (vs : Nat → Nat)
    (hv : ∀ j, Expands Γ (named.getD j []) (vs j)) (c : Nat) : ∃ N outs st c',
      subst Γ N c body named [] = some (plainOut body outs, st, c') ∧
      All2 (fun j o => IsNum o (vs j) ∧ Fin o) (paramIdx body) outs :=
  by unfold subst; exact substFrom_plain Γ body hw named vs hv body 0 (fun _ h => h) c

theorem noOp_plainOut : ∀ (body : List BTok) (outs : List (List Tok)), NoOp (plainOut body outs)
  | [], _ => trivial
  | .tok _ :: bs, outs => by simp only [plainOut, NoOp]; exact noOp_plainOut bs outs
  | .param _ :: bs, o :: outs => by
    simp only [plainOut]
    have : ∀ (l : List Tok) (r : List RTok), NoOp r → NoOp (l.map RTok.t ++ r) := by
      intro l r hr; induction l with
      | nil => simpa using hr
      | cons x l ih => simpa [NoOp] using ih
    exact this o _ (noOp_plainOut bs outs)
  | .param _ :: bs, [] => by simp only [plainOut]; exact noOp_plainOut bs []
  | .paste :: bs, outs => by simp only [plainOut]; exact noOp_plainOut bs outs
  | .va :: bs, outs => by simp only [plainOut]; exact noOp_plainOut bs outs

end PP
