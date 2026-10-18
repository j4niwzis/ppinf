/-
  Theorem 10: in the translation's environment every name belongs to one entry, so looking
  a name up finds its definition; and a node's part is found the same way inside the whole.
-/
import TransEnvP

namespace PP

theorem path_ne_ext (π q : List Code) (c : Code) : π ≠ π ++ c :: q := by
  intro h; have := congrArg List.length h; simp at this

theorem path_ext_inj {π q q' : List Code} {c c' : Code} (h : π ++ c :: q = π ++ c' :: q') : c = c' ∧ q = q' := by
  simpa using h

/-- Every name of the definitions at `π` is a name below `π`. -/
theorem mem_names : (t : Term) → ∀ (π : List Code) (e : Name × Def), e ∈ t.denvP π →
    ∃ q x, e.1 = fullName (π ++ q) x
  | .zero _, π, e, he => by simp [Term.denvP] at he; subst he; exact ⟨[], .self, by simp⟩
  | .succ, π, e, he => by simp [Term.denvP] at he; subst he; exact ⟨[], .self, by simp⟩
  | .proj _ _, π, e, he => by simp [Term.denvP] at he; subst he; exact ⟨[], .self, by simp⟩
  | .comp k h gs, π, e, he => by
    simp only [Term.denvP, List.mem_cons, List.mem_append, List.mem_flatMap] at he
    rcases he with rfl | hh | ⟨⟨⟨g, hg⟩, j⟩, _, hgj⟩
    · exact ⟨[], .self, by simp⟩
    · obtain ⟨q, x, e1⟩ := mem_names h _ e hh; exact ⟨.h :: q, x, by simpa using e1⟩
    · obtain ⟨q, x, e1⟩ := mem_names g _ e hgj; exact ⟨.k j :: q, x, by simpa using e1⟩
  | .prec f g, π, e, he => by
    simp only [Term.denvP, List.mem_append, List.mem_map] at he
    rcases he with (⟨x, _, rfl⟩ | hf) | hg
    · exact ⟨[], x, by simp⟩
    · obtain ⟨q, x, e1⟩ := mem_names f _ e hf; exact ⟨.f :: q, x, by simpa using e1⟩
    · obtain ⟨q, x, e1⟩ := mem_names g _ e hg; exact ⟨.r :: q, x, by simpa using e1⟩

/-- Names determine entries. -/
def Functional (L : Env) : Prop := ∀ e ∈ L, ∀ e' ∈ L, e.1 = e'.1 → e = e'

/-- Names below `π ++ c :: _` and below `π ++ c' :: _`, `c ≠ c'`, differ. -/
theorem names_apart {π : List Code} {c c' : Code} (hc : c ≠ c') {q q' : List Code} {x x' : Helper}
    (h : fullName (π ++ [c] ++ q) x = fullName (π ++ [c'] ++ q') x') : False :=
  hc (path_ext_inj (π := π) (q := q) (q' := q') (by simpa using (fullName_inj h).1)).1

theorem names_own {π : List Code} {c : Code} {q : List Code} {x x' : Helper}
    (h : fullName π x = fullName (π ++ [c] ++ q) x') : False :=
  path_ne_ext π q c (by simpa using (fullName_inj h).1)

theorem names_apart' {e e' : Name × Def} {π : List Code} {c c' : Code} (hc : c ≠ c') {q q' : List Code} {x x' : Helper}
    (e1 : e.1 = fullName (π ++ [c] ++ q) x) (e2 : e'.1 = fullName (π ++ [c'] ++ q') x') (hn : e.1 = e'.1) : False :=
  names_apart hc (by rw [← e1, ← e2]; exact hn)

theorem names_own' {e : Name × Def} {π : List Code} {c : Code} {q : List Code} {x x' : Helper}
    (e1 : e.1 = fullName (π ++ [c] ++ q) x') (hn : e.1 = fullName π x) : False :=
  names_own (by rw [← hn, e1])

theorem functional : (t : Term) → ∀ π, Functional (t.denvP π)
  | .zero _, π => by intro e he e' he' _; simp [Term.denvP] at he he'; rw [he, he']
  | .succ, π => by intro e he e' he' _; simp [Term.denvP] at he he'; rw [he, he']
  | .proj _ _, π => by intro e he e' he' _; simp [Term.denvP] at he he'; rw [he, he']
  | .comp k h gs, π => by
    intro e he e' he' hn
    have own : ∀ e ∈ (h.denvP (π ++ [.h]) ++ (gs.attach.zipIdx).flatMap fun (⟨g, _⟩, j) => g.denvP (π ++ [.k j])),
        e.1 ≠ fullName π .self := by
      intro e he hname
      simp only [List.mem_append, List.mem_flatMap] at he
      rcases he with hh | ⟨⟨⟨g, hg⟩, j⟩, _, hgj⟩
      · obtain ⟨q, x, e1⟩ := mem_names h _ e hh
        exact names_own' e1 hname
      · obtain ⟨q, x, e1⟩ := mem_names g _ e hgj
        exact names_own' e1 hname
    simp only [Term.denvP, List.mem_cons] at he he'
    rcases he with rfl | he <;> rcases he' with rfl | he'
    · rfl
    · exact absurd hn.symm (own _ he')
    · exact absurd hn (own _ he)
    simp only [List.mem_append, List.mem_flatMap] at he he'
    rcases he with hh | ⟨⟨⟨g, hg⟩, j⟩, hm, hgj⟩ <;> rcases he' with hh' | ⟨⟨⟨g', hg'⟩, j'⟩, hm', hgj'⟩
    · exact functional h _ e hh e' hh' hn
    · obtain ⟨q, x, e1⟩ := mem_names h _ e hh
      obtain ⟨q', x', e2⟩ := mem_names g' _ e' hgj'
      exact (names_apart' (by simp) e1 e2 hn).elim
    · obtain ⟨q, x, e1⟩ := mem_names g _ e hgj
      obtain ⟨q', x', e2⟩ := mem_names h _ e' hh'
      exact (names_apart' (by simp) e1 e2 hn).elim
    · obtain ⟨q, x, e1⟩ := mem_names g _ e hgj
      obtain ⟨q', x', e2⟩ := mem_names g' _ e' hgj'
      have hjj : j = j' := by
        by_cases hne : j = j'
        · exact hne
        · exact (names_apart' (c := .k j) (c' := .k j') (by simpa using hne) e1 e2 hn).elim
      subst hjj
      have hgg : g = g' := by
        have a := List.mem_zipIdx_iff_getElem?.mp hm
        have b := List.mem_zipIdx_iff_getElem?.mp hm'
        rw [a] at b
        simpa using b
      subst hgg
      exact functional g _ e hgj e' hgj' hn
  | .prec f g, π => by
    intro e he e' he' hn
    simp only [Term.denvP, List.mem_append, List.mem_map] at he he'
    have fn : ∀ e ∈ f.denvP (π ++ [.f]), ∀ x, e.1 ≠ fullName π x := by
      intro e he x hname
      obtain ⟨q, y, e1⟩ := mem_names f _ e he
      exact names_own' e1 hname
    have gn : ∀ e ∈ g.denvP (π ++ [.r]), ∀ x, e.1 ≠ fullName π x := by
      intro e he x hname
      obtain ⟨q, y, e1⟩ := mem_names g _ e he
      exact names_own' e1 hname
    rcases he with (⟨x, _, rfl⟩ | hf) | hg <;> rcases he' with (⟨x', _, rfl⟩ | hf') | hg'
    · have := (fullName_inj hn).2; subst this; rfl
    · exact absurd hn.symm (fn _ hf' x)
    · exact absurd hn.symm (gn _ hg' x)
    · exact absurd hn (fn _ hf x')
    · exact functional f _ e hf e' hf' hn
    · obtain ⟨q, x, e1⟩ := mem_names f _ e hf
      obtain ⟨q', x', e2⟩ := mem_names g _ e' hg'
      exact (names_apart' (by simp) e1 e2 hn).elim
    · exact absurd hn (gn _ hg x')
    · obtain ⟨q, x, e1⟩ := mem_names g _ e hg
      obtain ⟨q', x', e2⟩ := mem_names f _ e' hf'
      exact (names_apart' (by simp) e1 e2 hn).elim
    · exact functional g _ e hg e' hg' hn

theorem find_of_mem {L : Env} (hL : Functional L) {e : Name × Def} (he : e ∈ L) : L.find e.1 = some e.2 := by
  unfold Env.find
  cases hf : L.find? (·.1 == e.1) with
  | none => exact absurd (List.find?_eq_none.mp hf e he) (by simp)
  | some e' =>
    have hm := List.mem_of_find?_eq_some hf
    have hn : e'.1 = e.1 := by simpa using List.find?_some hf
    simp [hL e' hm e he hn]

/-- `Γ` has the definitions of the node `π`, its parts included. -/
def Realizes (Γ : Env) (t : Term) (π : List Code) : Prop := ∀ e ∈ t.denvP π, Γ.find e.1 = some e.2

theorem realizes_root (t : Term) : Realizes (t.denvP []) t [] := fun _ he => find_of_mem (functional t []) he

end PP
