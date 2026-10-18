/-
  A token's origin determines its mark: tokens of one origin `e` all carry the mark of step
  `e` (input tokens, origin 0, the empty one). So a closing parenthesis of the same origin as
  its head -- a step that is not a trick step -- has the head's mark (Lemma 2's hypothesis).
-/
import Ids

namespace PP

def All (Q : Tok → Prop) (xs : List Tok) : Prop := ∀ t ∈ xs, Q t

theorem all_cons {Q : Tok → Prop} {x xs} : All Q (x :: xs) ↔ Q x ∧ All Q xs := by
  constructor
  · intro h; exact ⟨h x (List.mem_cons_self ..), fun t ht => h t (List.mem_cons_of_mem _ ht)⟩
  · intro ⟨h1, h2⟩ t ht
    cases List.mem_cons.mp ht with
    | inl e => exact e ▸ h1
    | inr e => exact h2 t e
theorem all_append {Q : Tok → Prop} {xs ys} : All Q (xs ++ ys) ↔ All Q xs ∧ All Q ys := by
  constructor
  · intro h; exact ⟨fun t ht => h t (List.mem_append_left _ ht), fun t ht => h t (List.mem_append_right _ ht)⟩
  · intro ⟨h1, h2⟩ t ht
    cases List.mem_append.mp ht with
    | inl e => exact h1 t e
    | inr e => exact h2 t e

theorem all_sublist {Q : Tok → Prop} {l m : List Tok} (h : l.Sublist m) (g : All Q m) : All Q l :=
  fun t ht => g t (h.subset ht)

/-! The mark of an origin, as a function `μ` given with the steps it covers. -/

def Cons (μ : Nat → List Name) (t : Tok) : Prop := t.P = μ t.o

def ConsStep (μ : Nat → List Name) (s : Step) : Prop :=
  Cons μ s.head ∧ ∀ cl, s.close = some cl → Cons μ cl

def ScanCons (Γ : Env) (n : Nat) : Prop :=
  ∀ μ : Nat → List Name, μ 0 = [] → ∀ c xs out st c', scan Γ n c xs = some (out, st, c') →
    (∀ s ∈ st, μ s.id = s.mark) → All (Cons μ) xs → (∀ s ∈ st, ConsStep μ s) ∧ All (Cons μ) out
def SubstCons (Γ : Env) (n : Nat) : Prop :=
  ∀ μ : Nat → List Name, μ 0 = [] → ∀ whole bs i c named va r st c', substFrom Γ n whole bs i c named va = some (r, st, c') →
    (∀ s ∈ st, μ s.id = s.mark) → (∀ a ∈ named, All (Cons μ) a) → All (Cons μ) va → ∀ s ∈ st, ConsStep μ s

theorem all_getD {Q : Tok → Prop} (named : List (List Tok)) (j : Nat) (h : ∀ a ∈ named, All Q a) : All Q (named.getD j []) := by
  unfold List.getD
  cases hj : named[j]? with
  | none => exact fun _ h => nomatch h
  | some a => exact h a (List.mem_of_getElem? hj)

theorem substCons_of_scan {Γ : Env} {n : Nat} (h : ScanCons Γ n) : SubstCons Γ n := by
  intro μ μ0 whole bs
  induction bs with
  | nil => intro i c named va r st c' e _ _ _; simp [substFrom] at e; obtain ⟨_, rfl, _⟩ := e; simp
  | cons b bs ih =>
    intro i c named va r st c' e hμ gn gv
    simp only [substFrom] at e
    obtain ⟨⟨here, st₁, c₁⟩, hp, e⟩ := bind_some e
    cases hm : substFrom Γ n whole bs (i + 1) c₁ named va with
    | none => simp [hm] at e
    | some q =>
      obtain ⟨more, st₂, c₂⟩ := q
      simp only [hm, Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨_, rfl, _⟩ := e
      have hμ₁ : ∀ s ∈ st₁, μ s.id = s.mark := fun s hs => hμ s (List.mem_append_left _ hs)
      have hμ₂ : ∀ s ∈ st₂, μ s.id = s.mark := fun s hs => hμ s (List.mem_append_right _ hs)
      have one_ok : ∀ a r st c', one Γ n whole a i c = some (r, st, c') → (∀ s ∈ st, μ s.id = s.mark) →
          All (Cons μ) a → ∀ s ∈ st, ConsStep μ s := by
        intro a r st c' e hμ' g
        unfold one at e
        split at e
        · simp only [Option.some.injEq, Prod.mk.injEq] at e; obtain ⟨_, rfl, _⟩ := e; simp
        · cases he : scan Γ n c a with
          | none => simp [expand, he] at e
          | some q =>
            obtain ⟨o, st₀, c₀⟩ := q
            simp only [expand, he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
            obtain ⟨_, rfl, _⟩ := e
            exact (h μ μ0 c a o st₀ c₀ he hμ' g).1
      intro s hs
      cases List.mem_append.mp hs with
      | inr e2 => exact ih _ _ _ _ _ _ _ hm hμ₂ gn gv s e2
      | inl e1 =>
        unfold piece at hp
        cases b with
        | tok x => simp at hp; obtain ⟨_, rfl, _⟩ := hp; simp at e1
        | paste => simp at hp; obtain ⟨_, rfl, _⟩ := hp; simp at e1
        | param j => exact one_ok _ _ _ _ hp hμ₁ (all_getD named j gn) s e1
        | va => exact one_ok _ _ _ _ hp hμ₁ gv s e1

theorem all_mark (μ : Nat → List Name) (c : Nat) (K : List Name) (hK : μ c = K) (xs : List Tok) :
    All (Cons μ) (mark c K xs) := by
  intro t ht
  simp only [mark, List.mem_map] at ht
  obtain ⟨x, _, rfl⟩ := ht
  exact hK.symm

theorem scanCons (Γ : Env) : ∀ n, ScanCons Γ n := by
  intro n
  induction n with
  | zero => intro μ _ c xs out st c' e; simp [scan] at e
  | succ n ih =>
    have sub := substCons_of_scan ih
    intro μ μ0 c xs out st c' e hμ g
    cases xs with
    | nil => simp [scan] at e; obtain ⟨rfl, rfl, rfl⟩ := e; exact ⟨by simp, fun _ h => nomatch h⟩
    | cons x rest =>
      have ⟨gx, gr⟩ := all_cons.mp g
      unfold scan at e
      split at e
      · obtain ⟨out', hr, rfl⟩ := emit_some e
        have := ih μ μ0 c rest out' st c' hr hμ gr
        exact ⟨this.1, all_cons.mpr ⟨gx, this.2⟩⟩
      · split at e
        · rename_i body _
          obtain ⟨⟨r, st₁, c₁⟩, hs, e⟩ := bind_some e
          obtain ⟨b, _, e⟩ := bind_some e
          obtain ⟨st₂, hr, rfl⟩ := after_some e
          have hstep := hμ _ (List.mem_append_right _ (List.mem_cons_self ..))
          have h₂ := ih μ μ0 _ _ out st₂ c' hr (fun s hs => hμ s (List.mem_append_right _ (List.mem_cons_of_mem _ hs)))
            (all_append.mpr ⟨all_mark μ c _ hstep _, gr⟩)
          have h₁ := sub μ μ0 body body 0 (c + 1) [] [] r st₁ c₁ (by unfold subst at hs; exact hs)
            (fun s hs => hμ s (List.mem_append_left _ hs)) (by simp) (fun _ h => nomatch h)
          refine ⟨?_, h₂.2⟩
          intro s hs'
          rcases List.mem_append.mp hs' with h | h
          · exact h₁ s h
          · rcases List.mem_cons.mp h with h | h
            · subst h; exact ⟨gx, fun _ h => nomatch h⟩
            · exact h₂.1 s h
        · split at e
          · split at e
            · obtain ⟨out', hr, rfl⟩ := emit_some e
              have := ih μ μ0 c _ out' st c' hr hμ gr
              exact ⟨this.1, all_cons.mpr ⟨gx, this.2⟩⟩
            · have ⟨_, ga⟩ := all_cons.mp gr
              obtain ⟨⟨inner, cl, rest'⟩, ha, e⟩ := bind_some e
              obtain ⟨⟨named, va⟩, hb, e⟩ := bind_some e
              obtain ⟨⟨r, st₁, c₁⟩, hs, e⟩ := bind_some e
              obtain ⟨b, _, e⟩ := bind_some e
              obtain ⟨st₂, hr, rfl⟩ := after_some e
              have heq := closeAt_eq _ _ _ _ _ _ ha
              simp only [List.reverse_nil, List.nil_append] at heq
              rw [heq] at ga
              have ⟨gin, gcr⟩ := all_append.mp ga
              have ⟨gcl, grest⟩ := all_cons.mp gcr
              have ⟨hn, hv⟩ := bind_sub _ _ _ _ _ hb
              have gn : ∀ a ∈ named, All (Cons μ) a := fun a ha =>
                (hn a ha).elim (fun e => e ▸ (fun _ h => nomatch h)) (fun sl => all_sublist sl gin)
              have gv := all_sublist hv gin
              have hstep := hμ _ (List.mem_append_right _ (List.mem_cons_self ..))
              have h₂ := ih μ μ0 _ _ out st₂ c' hr (fun s hs => hμ s (List.mem_append_right _ (List.mem_cons_of_mem _ hs)))
                (all_append.mpr ⟨all_mark μ c _ hstep _, grest⟩)
              have h₁ := sub μ μ0 _ _ 0 (c + 1) named va r st₁ c₁ (by unfold subst at hs; exact hs)
                (fun s hs => hμ s (List.mem_append_left _ hs)) gn gv
              refine ⟨?_, h₂.2⟩
              intro s hs'
              rcases List.mem_append.mp hs' with h | h
              · exact h₁ s h
              · rcases List.mem_cons.mp h with h | h
                · subst h; exact ⟨gx, fun c' hc => by simp at hc; exact hc ▸ gcl⟩
                · exact h₂.1 s h
          · simp only [Option.some.injEq, Prod.mk.injEq] at e
            obtain ⟨rfl, rfl, rfl⟩ := e
            exact ⟨by simp, all_cons.mpr ⟨gx, fun _ h => nomatch h⟩⟩
        · obtain ⟨out', hr, rfl⟩ := emit_some e
          have := ih μ μ0 c rest out' st c' hr hμ gr
          exact ⟨this.1, all_cons.mpr ⟨gx, this.2⟩⟩

/-- The mark of origin `e` in a run: step `e`'s, the empty one for the input's origin 0. -/
def markOf (st : List Step) (e : Nat) : List Name := ((st.find? (·.id == e)).map (·.mark)).getD []

theorem markOf_step (st : List Step) (nd : (st.map (·.id)).Nodup) (s : Step) (hs : s ∈ st) : markOf st s.id = s.mark := by
  induction st with
  | nil => simp at hs
  | cons t st ih =>
    simp only [List.map_cons, List.nodup_cons] at nd
    unfold markOf
    rcases List.mem_cons.mp hs with h | h
    · subst h; simp
    · have hne : t.id ≠ s.id := fun e => nd.1 (e ▸ List.mem_map_of_mem h)
      have := ih nd.2 h
      unfold markOf at this
      simp [hne, this]

theorem markOf_zero (st : List Step) (h : ∀ s ∈ st, 1 ≤ s.id) : markOf st 0 = [] := by
  unfold markOf
  cases hf : st.find? (·.id == 0) with
  | none => rfl
  | some s =>
    have := h s (List.mem_of_find?_eq_some hf)
    have := List.find?_some hf
    simp at this; omega

/-- In a run from input tokens, tokens of one origin carry one mark: every step's head and
    closing parenthesis carry the mark of their origin. -/
theorem consistent (Γ : Env) (n : Nat) (xs : List Tok) (h : ∀ t ∈ xs, t.o = 0 ∧ t.P = []) out st c'
    (e : expand Γ n 1 xs = some (out, st, c')) : ∀ s ∈ st, ConsStep (markOf st) s := by
  have ⟨nd, ge⟩ := steps_numbered Γ n 1 xs out st c' e
  unfold expand at e
  cases hs : scan Γ n 1 xs with
  | none => simp [hs] at e
  | some q =>
    obtain ⟨o, st₀, c₀⟩ := q
    simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨_, rfl, rfl⟩ := e
    have μ0 := markOf_zero st₀ ge
    refine (scanCons Γ n (markOf st₀) μ0 1 xs o st₀ c₀ hs (fun s hs => markOf_step st₀ nd s hs) ?_).1
    intro t ht
    obtain ⟨h1, h2⟩ := h t ht
    unfold Cons; rw [h1, h2, μ0]

end PP
