/-
  pp_primrec.tex §2 on the semantics: origins, marks and trick steps.

  Lemma 1 (`inv`): every token, while it is scanned, has a hidden set containing the mark of
  its origin; and every step's head is eligible, its mark is {m} ∪ H (object) or
  {m} ∪ (H ∩ J) (function).
-/
import Semantics

namespace PP

def Sub (A B : List Name) : Prop := ∀ a ∈ A, a ∈ B

/-- Every token's hidden set contains the mark of its origin. -/
def Good (xs : List Tok) : Prop := ∀ t ∈ xs, Sub t.P t.H

/-- What a step is, as the rules make it. -/
def GoodStep (s : Step) : Prop :=
  s.m = s.head.s ∧ s.head.s ∉ s.head.H ∧ Sub s.head.P s.head.H ∧
  match s.close with
  | none => s.mark = s.m :: s.head.H
  | some cl => Sub cl.P cl.H ∧ s.mark = s.m :: inter s.head.H cl.H

theorem good_nil : Good [] := fun _ h => nomatch h
theorem good_cons {x : Tok} {xs : List Tok} : Good (x :: xs) ↔ Sub x.P x.H ∧ Good xs := by
  constructor
  · intro h; exact ⟨h x (List.mem_cons_self ..), fun t ht => h t (List.mem_cons_of_mem _ ht)⟩
  · intro ⟨h1, h2⟩ t ht
    cases List.mem_cons.mp ht with
    | inl e => exact e ▸ h1
    | inr e => exact h2 t e
theorem good_append {xs ys : List Tok} : Good (xs ++ ys) ↔ Good xs ∧ Good ys := by
  constructor
  · intro h; exact ⟨fun t ht => h t (List.mem_append_left _ ht), fun t ht => h t (List.mem_append_right _ ht)⟩
  · intro ⟨h1, h2⟩ t ht
    cases List.mem_append.mp ht with
    | inl e => exact h1 t e
    | inr e => exact h2 t e

theorem sub_union (K H : List Name) : Sub K (union K H) := fun _ h => List.mem_append_left _ h

theorem good_mark (e : Nat) (K : List Name) (xs : List Tok) : Good (mark e K xs) := by
  intro t ht
  simp only [mark, List.mem_map] at ht
  obtain ⟨x, _, rfl⟩ := ht
  exact sub_union K x.H

/-- The arguments and the closing parenthesis come from the stream: good where it is. -/
theorem args_good : ∀ (xs : List Tok) (d : Nat) (cur : List Tok) (done : List (List Tok)) (acc : List Tok) as cl rest,
    args d xs cur done acc = some (as, cl, rest) → Good xs → Good cur → (∀ a ∈ done, Good a) →
    (∀ a ∈ as, Good a) ∧ Sub cl.P cl.H ∧ Good rest := by
  intro xs
  induction xs with
  | nil => intro d cur done acc as cl rest h; simp [args] at h
  | cons x xs ih =>
    intro d cur done acc as cl rest h gx gc gd
    have ⟨gx1, gx2⟩ := good_cons.mp gx
    have grev : ∀ l : List Tok, Good l → Good l.reverse := fun l g t ht => g t (List.mem_reverse.mp ht)
    unfold args at h
    split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨?_, gx1, gx2⟩
        intro a ha
        cases List.mem_append.mp ha with
        | inl e => exact gd a e
        | inr e => simp at e; exact e ▸ grev _ gc
      · exact ih _ _ _ _ _ _ _ h gx2 (good_cons.mpr ⟨gx1, gc⟩) gd
    · split at h
      · exact ih _ _ _ _ _ _ _ h gx2 (good_cons.mpr ⟨gx1, gc⟩) gd
      · split at h
        · refine ih _ _ _ _ _ _ _ h gx2 good_nil ?_
          intro a ha
          cases List.mem_append.mp ha with
          | inl e => exact gd a e
          | inr e => simp at e; exact e ▸ grev _ gc
        · exact ih _ _ _ _ _ _ _ h gx2 (good_cons.mpr ⟨gx1, gc⟩) gd

theorem good_intercalate : ∀ (as : List (List Tok)), (∀ a ∈ as, Good a) →
    Good (List.intercalate [{ s := "," }] as)
  | [], _ => by simp [List.intercalate]; exact good_nil
  | [a], h => by simp [List.intercalate]; exact h a (by simp)
  | a :: b :: rest, h => by
    rw [List.intercalate_cons_cons]
    refine good_append.mpr ⟨good_append.mpr ⟨h a (by simp), ?_⟩, ?_⟩
    · intro t ht; simp at ht; subst ht; intro x hx; simp at hx
    · exact good_intercalate (b :: rest) (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem bind_good (arity : Nat) (variadic : Bool) (as : List (List Tok)) named va
    (h : bind arity variadic as = some (named, va)) (g : ∀ a ∈ as, Good a) :
    (∀ a ∈ named, Good a) ∧ Good va := by
  unfold bind at h
  split at h
  · split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨?_, good_nil⟩
        intro a ha
        cases List.mem_append.mp ha with
        | inl e => exact g a e
        | inr e => rw [List.eq_of_mem_replicate e]; exact good_nil
      · simp at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨fun a ha => g a (List.mem_of_mem_take ha),
             good_intercalate _ (fun a ha => g a (List.mem_of_mem_drop ha))⟩
  · split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨fun a ha => by simp at ha, good_nil⟩
      · simp at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨g, good_nil⟩
      · simp at h

theorem emit_some {x : Tok} {r : Option (List Tok × List Step × Nat)} {out st c'}
    (h : emit x r = some (out, st, c')) : ∃ out', r = some (out', st, c') ∧ out = x :: out' := by
  unfold emit at h
  cases r with
  | none => simp at h
  | some q =>
    obtain ⟨o, st₀, c₀⟩ := q
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨o, rfl, rfl⟩

theorem after_some {step : Step} {st₁ : List Step} {r : Option (List Tok × List Step × Nat)} {out st c'}
    (h : after step st₁ r = some (out, st, c')) : ∃ st₂, r = some (out, st₂, c') ∧ st = st₁ ++ step :: st₂ := by
  unfold after at h
  cases r with
  | none => simp at h
  | some q =>
    obtain ⟨o, st₀, c₀⟩ := q
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨st₀, rfl, rfl⟩

theorem bind_some {α β : Type} {o : Option α} {f : α → Option β} {b : β} (h : o.bind f = some b) :
    ∃ a, o = some a ∧ f a = some b := by
  cases o with
  | none => simp at h
  | some a => exact ⟨a, rfl, h⟩

def ScanInv (Γ : Env) (n : Nat) : Prop :=
  ∀ c xs out st c', scan Γ n c xs = some (out, st, c') → Good xs → (∀ s ∈ st, GoodStep s) ∧ Good out
def ExpandInv (Γ : Env) (n : Nat) : Prop :=
  ∀ c xs out st c', expand Γ n c xs = some (out, st, c') → Good xs → ∀ s ∈ st, GoodStep s
def SubstInv (Γ : Env) (n : Nat) : Prop :=
  ∀ whole bs i c named va r st c', substFrom Γ n whole bs i c named va = some (r, st, c') →
    (∀ a ∈ named, Good a) → Good va → ∀ s ∈ st, GoodStep s

theorem expandInv_of_scan {Γ : Env} {n : Nat} (h : ScanInv Γ n) : ExpandInv Γ n := by
  intro c xs out st c' e g
  unfold expand at e
  cases hs : scan Γ n c xs with
  | none => simp [hs] at e
  | some r =>
    obtain ⟨o, st₀, c₀⟩ := r
    simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨_, rfl, _⟩ := e
    exact (h c xs o st₀ c₀ hs g).1

theorem good_getD (named : List (List Tok)) (j : Nat) (h : ∀ a ∈ named, Good a) : Good (named.getD j []) := by
  unfold List.getD
  cases hj : named[j]? with
  | none => exact good_nil
  | some a => exact h a (List.mem_of_getElem? hj)

theorem one_inv {Γ : Env} {n : Nat} (h : ExpandInv Γ n) whole a i c r st c'
    (e : one Γ n whole a i c = some (r, st, c')) (g : Good a) : ∀ s ∈ st, GoodStep s := by
  unfold one at e
  split at e
  · simp only [Option.some.injEq, Prod.mk.injEq] at e; obtain ⟨_, rfl, _⟩ := e; simp
  · cases he : expand Γ n c a with
    | none => simp [he] at e
    | some q =>
      obtain ⟨o, st₀, c₀⟩ := q
      simp only [he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨_, rfl, _⟩ := e
      exact h c a o st₀ c₀ he g

theorem substInv_of_expand {Γ : Env} {n : Nat} (h : ExpandInv Γ n) : SubstInv Γ n := by
  intro whole bs
  induction bs with
  | nil => intro i c named va r st c' e _ _; simp [substFrom] at e; obtain ⟨_, rfl, _⟩ := e; simp
  | cons b bs ih =>
    intro i c named va r st c' e gn gv
    simp only [substFrom] at e
    obtain ⟨⟨here, st₁, c₁⟩, hp, e⟩ := bind_some e
    cases hm : substFrom Γ n whole bs (i + 1) c₁ named va with
    | none => simp [hm] at e
    | some q =>
      obtain ⟨more, st₂, c₂⟩ := q
      simp only [hm, Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨_, rfl, _⟩ := e
      intro s hs
      cases List.mem_append.mp hs with
      | inr e2 => exact ih _ _ _ _ _ _ _ hm gn gv s e2
      | inl e1 =>
        unfold piece at hp
        cases b with
        | tok x => simp at hp; obtain ⟨_, rfl, _⟩ := hp; simp at e1
        | paste => simp at hp; obtain ⟨_, rfl, _⟩ := hp; simp at e1
        | param j => exact one_inv h _ _ _ _ _ _ _ hp (good_getD named j gn) s e1
        | va => exact one_inv h _ _ _ _ _ _ _ hp gv s e1

/-- Lemma 1, with what every step is: by induction on the fuel. -/
theorem scanInv (Γ : Env) : ∀ n, ScanInv Γ n := by
  intro n
  induction n with
  | zero => intro c xs out st c' e; simp [scan] at e
  | succ n ih =>
    have sub := substInv_of_expand (expandInv_of_scan ih)
    intro c xs out st c' e g
    cases xs with
    | nil => simp [scan] at e; obtain ⟨rfl, rfl, rfl⟩ := e; exact ⟨by simp, good_nil⟩
    | cons x rest =>
      have ⟨gx, gr⟩ := good_cons.mp g
      unfold scan at e
      split at e
      · obtain ⟨out', hr, rfl⟩ := emit_some e
        have := ih c rest out' st c' hr gr
        exact ⟨this.1, good_cons.mpr ⟨gx, this.2⟩⟩
      · rename_i hid
        split at e
        · -- an object macro
          rename_i body _
          obtain ⟨⟨r, st₁, c₁⟩, hs, e⟩ := bind_some e
          obtain ⟨b, _, e⟩ := bind_some e
          obtain ⟨st₂, hr, rfl⟩ := after_some e
          have h₂ := ih _ _ out st₂ c' hr (good_append.mpr ⟨good_mark _ _ _, gr⟩)
          have h₁ := sub body body 0 (c + 1) [] [] r st₁ c₁ (by unfold subst at hs; exact hs) (by simp) good_nil
          refine ⟨?_, h₂.2⟩
          intro s hs'
          rcases List.mem_append.mp hs' with h | h
          · exact h₁ s h
          · rcases List.mem_cons.mp h with h | h
            · subst h; exact ⟨rfl, hid, gx, rfl⟩
            · exact h₂.1 s h
        · -- a function-like macro
          rename_i arity variadic body _
          split at e
          · rename_i open_ after'
            split at e
            · obtain ⟨out', hr, rfl⟩ := emit_some e
              have := ih c _ out' st c' hr gr
              exact ⟨this.1, good_cons.mpr ⟨gx, this.2⟩⟩
            · have ⟨_, ga⟩ := good_cons.mp gr
              obtain ⟨⟨as, cl, rest'⟩, ha, e⟩ := bind_some e
              obtain ⟨⟨named, va⟩, hb, e⟩ := bind_some e
              obtain ⟨⟨r, st₁, c₁⟩, hs, e⟩ := bind_some e
              obtain ⟨b, _, e⟩ := bind_some e
              obtain ⟨st₂, hr, rfl⟩ := after_some e
              have ⟨gas, gcl, grest⟩ := args_good _ _ _ _ _ _ _ _ ha ga good_nil (by simp)
              have ⟨gn, gv⟩ := bind_good _ _ _ _ _ hb gas
              have h₂ := ih _ _ out st₂ c' hr (good_append.mpr ⟨good_mark _ _ _, grest⟩)
              have h₁ := sub body body 0 (c + 1) named va r st₁ c₁ (by unfold subst at hs; exact hs) gn gv
              refine ⟨?_, h₂.2⟩
              intro s hs'
              rcases List.mem_append.mp hs' with h | h
              · exact h₁ s h
              · rcases List.mem_cons.mp h with h | h
                · subst h; exact ⟨rfl, hid, gx, gcl, rfl⟩
                · exact h₂.1 s h
          · simp only [Option.some.injEq, Prod.mk.injEq] at e
            obtain ⟨rfl, rfl, rfl⟩ := e
            exact ⟨by simp, good_cons.mpr ⟨gx, good_nil⟩⟩
        · obtain ⟨out', hr, rfl⟩ := emit_some e
          have := ih c rest out' st c' hr gr
          exact ⟨this.1, good_cons.mpr ⟨gx, this.2⟩⟩

/-- Lemma 1 for a whole run: from input tokens (no origin, empty marks), every step is as
    the rules make it, its head and closing parenthesis carrying their origins' marks. -/
theorem lemma1 (Γ : Env) (n c : Nat) (xs : List Tok) (h : ∀ t ∈ xs, t.P = []) out st c'
    (e : expand Γ n c xs = some (out, st, c')) : ∀ s ∈ st, GoodStep s :=
  expandInv_of_scan (scanInv Γ n) c xs out st c' e (fun t ht => by rw [h t ht]; intro a ha; simp at ha)

/-- Lemma 2: a step whose closing parenthesis has the mark of its head's origin (so, by
    Lemma 1, of the same origin: not a trick step) has `m ∉ P_e` and a mark ⊇ P_e ∪ {m}. -/
theorem lemma2 (s : Step) (g : GoodStep s) (cl : Tok) (hc : s.close = some cl) (same : cl.P = s.head.P) :
    s.m ∉ s.head.P ∧ Sub s.head.P s.mark ∧ s.m ∈ s.mark := by
  obtain ⟨hm, elig, hP, rest⟩ := g
  rw [hc] at rest
  obtain ⟨hcl, hmark⟩ := rest
  refine ⟨fun h => elig (hm ▸ hP _ h), ?_, by rw [hmark]; simp⟩
  intro a ha
  rw [hmark]
  apply List.mem_cons_of_mem
  simp only [inter, List.mem_filter, decide_eq_true_eq]
  exact ⟨hP a ha, hcl a (same ▸ ha)⟩

/-- And an object macro's step always: its mark is {m} ∪ H. -/
theorem lemma2_obj (s : Step) (g : GoodStep s) (hc : s.close = none) :
    s.m ∉ s.head.P ∧ Sub s.head.P s.mark ∧ s.m ∈ s.mark := by
  obtain ⟨hm, elig, hP, rest⟩ := g
  rw [hc] at rest
  refine ⟨fun h => elig (hm ▸ hP _ h), ?_, by rw [rest]; simp⟩
  intro a ha; rw [rest]; exact List.mem_cons_of_mem _ (hP a ha)

end PP
