/-
  Lemma 5 (cycles need the trick), on the semantics: along a parent chain of steps without
  trick steps, every macro occurs at most once.

  A step's parent is the step its head came from (`head.o`). A step is a trick step when its
  closing parenthesis comes from another origin than its head.
-/
import Consistent

namespace PP

def Trick (s : Step) : Prop := ∃ cl, s.close = some cl ∧ cl.o ≠ s.head.o

/-- A parent chain: each step's head was made by the step before it. -/
def ParentChain : List Step → Prop
  | a :: b :: rest => b.head.o = a.id ∧ ParentChain (b :: rest)
  | _ => True

/-- What one link gives: the parent's mark kept, the child's macro new to it. -/
structure Link (a b : Step) : Prop where
  keeps : Sub a.mark b.mark
  fresh : b.m ∉ a.mark
  own : b.m ∈ b.mark

theorem link_of_run (Γ : Env) (n : Nat) (xs : List Tok) (h : ∀ t ∈ xs, t.o = 0 ∧ t.P = []) out st c'
    (e : expand Γ n 1 xs = some (out, st, c')) (a b : Step) (ha : a ∈ st) (hb : b ∈ st)
    (hp : b.head.o = a.id) (nt : ¬ Trick b) : Link a b := by
  have good := lemma1 Γ n 1 xs (fun t ht => (h t ht).2) out st c' e b hb
  have cons := consistent Γ n xs h out st c' e b hb
  have ⟨nd, _⟩ := steps_numbered Γ n 1 xs out st c' e
  have hP : b.head.P = a.mark := by
    rw [cons.1, hp, markOf_step st nd a ha]
  have facts : b.m ∉ b.head.P ∧ Sub b.head.P b.mark ∧ b.m ∈ b.mark := by
    cases hc : b.close with
    | none => exact lemma2_obj b good hc
    | some cl =>
      have same : cl.o = b.head.o := Classical.byContradiction fun ne => nt ⟨cl, hc, ne⟩
      have : cl.P = b.head.P := by rw [cons.2 cl hc, cons.1, same]
      exact lemma2 b good cl hc this
  rw [hP] at facts
  exact ⟨facts.2.1, facts.1, facts.2.2⟩

theorem own_mark (Γ : Env) (n : Nat) (xs : List Tok) (h : ∀ t ∈ xs, t.P = []) out st c'
    (e : expand Γ n 1 xs = some (out, st, c')) (a : Step) (ha : a ∈ st) : a.m ∈ a.mark := by
  have ⟨hm, _, _, rest⟩ := lemma1 Γ n 1 xs h out st c' e a ha
  cases hc : a.close with
  | none => rw [hc] at rest; rw [rest]; simp
  | some cl => rw [hc] at rest; rw [rest.2]; simp

inductive Linked : List Step → Prop where
  | nil : Linked []
  | one (a : Step) : Linked [a]
  | cons (a b : Step) (rest : List Step) : Link a b → Linked (b :: rest) → Linked (a :: b :: rest)

theorem linked_below : ∀ (a : Step) (L : List Step), Linked (a :: L) → ∀ s ∈ L, Sub a.mark s.mark ∧ s.m ∉ a.mark
  | _, [], _ => by simp
  | a, b :: rest, h => by
    cases h with
    | cons _ _ _ l hl =>
      have ih := linked_below b rest hl
      intro s hs
      rcases List.mem_cons.mp hs with e | e
      · subst e; exact ⟨l.keeps, l.fresh⟩
      · have ⟨k, f⟩ := ih s e
        exact ⟨fun x hx => k x (l.keeps x hx), fun hm => f (l.keeps _ hm)⟩

theorem linked_tail {a : Step} {L : List Step} (h : Linked (a :: L)) : Linked L := by
  cases h with
  | one => exact .nil
  | cons _ _ _ _ hl => exact hl

theorem linked_nodup : ∀ (L : List Step), Linked L → (∀ s ∈ L, s.m ∈ s.mark) → (L.map (·.m)).Nodup
  | [], _, _ => by simp
  | a :: L, h, own => by
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, linked_nodup L (linked_tail h) (fun s hs => own s (List.mem_cons_of_mem _ hs))⟩
    intro hm
    obtain ⟨s, hs, e⟩ := List.mem_map.mp hm
    exact (linked_below a L h s hs).2 (e ▸ own a (List.mem_cons_self ..))

/-- A parent chain of steps of a run, none of them -- after its first -- a trick step. -/
inductive TrickFreeChain (st : List Step) : List Step → Prop where
  | nil : TrickFreeChain st []
  | one (a : Step) : a ∈ st → TrickFreeChain st [a]
  | cons (a b : Step) (rest : List Step) : a ∈ st → b.head.o = a.id → ¬ Trick b →
      TrickFreeChain st (b :: rest) → TrickFreeChain st (a :: b :: rest)

theorem TrickFreeChain.mem {st : List Step} : ∀ {L : List Step}, TrickFreeChain st L → ∀ s ∈ L, s ∈ st
  | _, .nil => by simp
  | _, .one a ha => by simp; exact ha
  | _, .cons a b rest ha _ _ h => by
    intro s hs
    rcases List.mem_cons.mp hs with e | e
    · exact e ▸ ha
    · exact h.mem s e

/-- Lemma 5. In a run from input tokens, along a parent chain without trick steps every
    macro occurs at most once. -/
theorem lemma5 (Γ : Env) (n : Nat) (xs : List Tok) (h : ∀ t ∈ xs, t.o = 0 ∧ t.P = []) out st c'
    (e : expand Γ n 1 xs = some (out, st, c')) (L : List Step) (hL : TrickFreeChain st L) :
    (L.map (·.m)).Nodup := by
  have linked : ∀ L, TrickFreeChain st L → Linked L := by
    intro L hL
    induction hL with
    | nil => exact .nil
    | one a _ => exact .one a
    | cons a b rest ha hp nt hrest ih =>
      exact .cons a b rest (link_of_run Γ n xs h out st c' e a b ha (hrest.mem b (by simp)) hp nt) ih
  exact linked_nodup L (linked L hL)
    (fun s hs => own_mark Γ n xs (fun t ht => (h t ht).2) out st c' e s (hL.mem s hs))

theorem nodup_length_le {α : Type} [DecidableEq α] : ∀ (l m : List α), l.Nodup → l ⊆ m → l.length ≤ m.length
  | [], _, _, _ => by simp
  | a :: l, m, nd, sub => by
    rw [List.nodup_cons] at nd
    have ha : a ∈ m := sub (List.mem_cons_self ..)
    have sub' : l ⊆ m.erase a := by
      intro x hx
      have hne : x ≠ a := fun e => nd.1 (e ▸ hx)
      exact (List.mem_erase_of_ne hne).mpr (sub (List.mem_cons_of_mem _ hx))
    have := nodup_length_le l (m.erase a) nd.2 sub'
    rw [List.length_erase_of_mem ha] at this
    have : 0 < m.length := List.length_pos_of_mem ha
    simp; omega

/-- So a trick-free parent chain is at most as long as the environment has macros. -/
theorem lemma5_length (Γ : Env) (n : Nat) (xs : List Tok) (h : ∀ t ∈ xs, t.o = 0 ∧ t.P = []) out st c'
    (e : expand Γ n 1 xs = some (out, st, c')) (L : List Step) (hL : TrickFreeChain st L)
    (inΓ : ∀ s ∈ L, s.m ∈ Γ.map (·.1)) : L.length ≤ (Γ.map (·.1)).eraseDups.length := by
  have nd := lemma5 Γ n xs h out st c' e L hL
  have sub : (L.map (·.m)) ⊆ (Γ.map (·.1)).eraseDups := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
    exact (List.mem_eraseDups).mpr (inΓ s hs)
  have := nodup_length_le _ _ nd sub
  simpa using this

end PP
