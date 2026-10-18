/-
  Along the stream being scanned, marks only shrink: a later token's origin mark is
  contained in every earlier token's (`Desc`). So at every step the closing parenthesis has
  a mark within the head's, and the new mark contains the closing parenthesis's and `m`.
-/
import Consistent

namespace PP

def Desc (xs : List Tok) : Prop := xs.Pairwise fun a b => Sub b.P a.P

def CloseBelow (s : Step) : Prop := ∀ cl, s.close = some cl → Sub cl.P s.head.P

def ScanDesc (Γ : Env) (n : Nat) : Prop :=
  ∀ c xs out st c', scan Γ n c xs = some (out, st, c') → Good xs → Desc xs → ∀ s ∈ st, CloseBelow s
def SubstDesc (Γ : Env) (n : Nat) : Prop :=
  ∀ whole bs i c named va r st c', substFrom Γ n whole bs i c named va = some (r, st, c') →
    (∀ a ∈ named, Good a ∧ Desc a) → Good va → Desc va → ∀ s ∈ st, CloseBelow s

theorem desc_mark_append (e : Nat) (K : List Name) (b rest : List Tok) (h : ∀ t ∈ rest, Sub t.P K)
    (hr : Desc rest) : Desc (mark e K b ++ rest) := by
  unfold Desc
  rw [List.pairwise_append]
  refine ⟨?_, hr, ?_⟩
  · unfold mark
    rw [List.pairwise_map]
    exact List.pairwise_of_forall (fun _ _ => fun _ h => h)
  · intro a ha t ht
    simp only [mark, List.mem_map] at ha
    obtain ⟨x, _, rfl⟩ := ha
    exact h t ht

theorem substDesc_of_scan {Γ : Env} {n : Nat} (h : ScanDesc Γ n) : SubstDesc Γ n := by
  intro whole bs
  induction bs with
  | nil => intro i c named va r st c' e _ _ _; simp [substFrom] at e; obtain ⟨_, rfl, _⟩ := e; simp
  | cons b bs ih =>
    intro i c named va r st c' e gn gv dv
    simp only [substFrom] at e
    obtain ⟨⟨here, st₁, c₁⟩, hp, e⟩ := bind_some e
    cases hm : substFrom Γ n whole bs (i + 1) c₁ named va with
    | none => simp [hm] at e
    | some q =>
      obtain ⟨more, st₂, c₂⟩ := q
      simp only [hm, Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨_, rfl, _⟩ := e
      have one_ok : ∀ a r st c', one Γ n whole a i c = some (r, st, c') → Good a → Desc a → ∀ s ∈ st, CloseBelow s := by
        intro a r st c' e g d
        unfold one at e
        split at e
        · simp only [Option.some.injEq, Prod.mk.injEq] at e; obtain ⟨_, rfl, _⟩ := e; simp
        · cases he : scan Γ n c a with
          | none => simp [expand, he] at e
          | some q =>
            obtain ⟨o, st₀, c₀⟩ := q
            simp only [expand, he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
            obtain ⟨_, rfl, _⟩ := e
            exact h c a o st₀ c₀ he g d
      intro s hs
      cases List.mem_append.mp hs with
      | inr e2 => exact ih _ _ _ _ _ _ _ hm gn gv dv s e2
      | inl e1 =>
        unfold piece at hp
        cases b with
        | tok x => simp at hp; obtain ⟨_, rfl, _⟩ := hp; simp at e1
        | paste => simp at hp; obtain ⟨_, rfl, _⟩ := hp; simp at e1
        | param j =>
          have gd : Good (named.getD j []) ∧ Desc (named.getD j []) := by
            unfold List.getD
            cases hj : named[j]? with
            | none => exact ⟨good_nil, List.Pairwise.nil⟩
            | some a => exact gn a (List.mem_of_getElem? hj)
          exact one_ok _ _ _ _ hp gd.1 gd.2 s e1
        | va => exact one_ok _ _ _ _ hp gv dv s e1

theorem scanDesc (Γ : Env) : ∀ n, ScanDesc Γ n := by
  intro n
  induction n with
  | zero => intro c xs out st c' e; simp [scan] at e
  | succ n ih =>
    have sub := substDesc_of_scan ih
    intro c xs out st c' e g d
    cases xs with
    | nil => simp [scan] at e; obtain ⟨rfl, rfl, rfl⟩ := e; simp
    | cons x rest =>
      have ⟨gx, gr⟩ := good_cons.mp g
      have ⟨dx, dr⟩ := List.pairwise_cons.mp d
      unfold scan at e
      split at e
      · obtain ⟨out', hr, rfl⟩ := emit_some e
        exact ih c rest out' st c' hr gr dr
      · split at e
        · rename_i body _
          obtain ⟨⟨r, st₁, c₁⟩, hs, e⟩ := bind_some e
          obtain ⟨b, _, e⟩ := bind_some e
          obtain ⟨st₂, hr, rfl⟩ := after_some e
          have d₂ : Desc (mark c (x.s :: x.H) b ++ rest) :=
            desc_mark_append _ _ _ _ (fun t ht a ha => List.mem_cons_of_mem _ (gx a (dx t ht a ha))) dr
          have h₂ := ih _ _ out st₂ c' hr (good_append.mpr ⟨good_mark _ _ _, gr⟩) d₂
          have h₁ := sub body body 0 (c + 1) [] [] r st₁ c₁ (by unfold subst at hs; exact hs) (by simp) good_nil List.Pairwise.nil
          intro s hs'
          rcases List.mem_append.mp hs' with h | h
          · exact h₁ s h
          · rcases List.mem_cons.mp h with h | h
            · subst h; intro cl hc; simp at hc
            · exact h₂ s h
        · split at e
          · split at e
            · obtain ⟨out', hr, rfl⟩ := emit_some e
              exact ih c _ out' st c' hr gr dr
            · have ⟨_, ga⟩ := good_cons.mp gr
              have ⟨_, da⟩ := List.pairwise_cons.mp dr
              obtain ⟨⟨inner, cl, rest'⟩, ha, e⟩ := bind_some e
              obtain ⟨⟨named, va⟩, hb, e⟩ := bind_some e
              obtain ⟨⟨r, st₁, c₁⟩, hs, e⟩ := bind_some e
              obtain ⟨b, _, e⟩ := bind_some e
              obtain ⟨st₂, hr, rfl⟩ := after_some e
              have heq := closeAt_eq _ _ _ _ _ _ ha
              simp only [List.reverse_nil, List.nil_append] at heq
              rw [heq] at ga da dx
              have ⟨gin, gcr⟩ := good_append.mp ga
              have ⟨gcl, grest⟩ := good_cons.mp gcr
              have ⟨din, dcr, dcross⟩ := List.pairwise_append.mp da
              have ⟨dcl, drest⟩ := List.pairwise_cons.mp dcr
              have ⟨hn, hv⟩ := bind_sub _ _ _ _ _ hb
              have gn : ∀ a ∈ named, Good a ∧ Desc a := fun a ha =>
                (hn a ha).elim (fun e => e ▸ ⟨good_nil, List.Pairwise.nil⟩)
                  (fun sl => ⟨good_sublist sl gin, din.sublist sl⟩)
              have hxcl : Sub cl.P x.P := dx cl (by simp)
              have d₂ : Desc (mark c (x.s :: inter x.H cl.H) b ++ rest') := by
                refine desc_mark_append _ _ _ _ (fun t ht a ha => ?_) drest
                apply List.mem_cons_of_mem
                simp only [inter, List.mem_filter, decide_eq_true_eq]
                have hcl : a ∈ cl.P := dcl t ht a ha
                exact ⟨gx a (hxcl a hcl), gcl a hcl⟩
              have h₂ := ih _ _ out st₂ c' hr (good_append.mpr ⟨good_mark _ _ _, grest⟩) d₂
              have h₁ := sub _ _ 0 (c + 1) named va r st₁ c₁ (by unfold subst at hs; exact hs) gn
                (good_sublist hv gin) (din.sublist hv)
              intro s hs'
              rcases List.mem_append.mp hs' with h | h
              · exact h₁ s h
              · rcases List.mem_cons.mp h with h | h
                · subst h; intro cl' hc; simp at hc; exact hc ▸ hxcl
                · exact h₂ s h
          · simp only [Option.some.injEq, Prod.mk.injEq] at e
            obtain ⟨rfl, rfl, rfl⟩ := e
            simp
        · obtain ⟨out', hr, rfl⟩ := emit_some e
          exact ih c rest out' st c' hr gr dr

theorem desc_of_input : ∀ (xs : List Tok), (∀ t ∈ xs, t.P = []) → Desc xs
  | [], _ => List.Pairwise.nil
  | x :: xs, h => List.pairwise_cons.mpr
      ⟨fun b hb => by rw [h b (List.mem_cons_of_mem _ hb)]; intro a ha; simp at ha,
       desc_of_input xs (fun t ht => h t (List.mem_cons_of_mem _ ht))⟩

/-- In a run from input tokens, every step's closing parenthesis has a mark within its
    head's; so its new mark contains the closing parenthesis's mark and `m`, which that mark
    lacks. -/
theorem close_below (Γ : Env) (n c : Nat) (xs : List Tok) (h : ∀ t ∈ xs, t.P = []) out st c'
    (e : expand Γ n c xs = some (out, st, c')) (s : Step) (hs : s ∈ st) (cl : Tok) (hc : s.close = some cl) :
    Sub cl.P s.mark ∧ s.m ∉ cl.P := by
  have good := lemma1 Γ n c xs h out st c' e s hs
  unfold expand at e
  cases hsc : scan Γ n c xs with
  | none => simp [hsc] at e
  | some q =>
    obtain ⟨o, st₀, c₀⟩ := q
    simp only [hsc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨_, rfl, _⟩ := e
    have below := scanDesc Γ n c xs o st₀ c₀ hsc (fun t ht => by rw [h t ht]; intro a ha; simp at ha)
      (desc_of_input xs h) s hs cl hc
    obtain ⟨hm, elig, hP, rest⟩ := good
    rw [hc] at rest
    obtain ⟨hcl, hmark⟩ := rest
    refine ⟨fun a ha => ?_, fun hin => elig (hm ▸ hP _ (below _ hin))⟩
    rw [hmark]; apply List.mem_cons_of_mem
    simp only [inter, List.mem_filter, decide_eq_true_eq]
    exact ⟨hP a (below a ha), hcl a ha⟩

end PP
