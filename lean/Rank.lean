/-
  Ranks: a token's rank is the number of the environment's macro names not in its origin
  mark. Along a stream (Desc) ranks never decrease; a step's new tokens have a rank below
  its closing parenthesis's (its head's, for an object macro); at rank 0 nothing expands.
  And the invariant Good ∧ Desc, step by step.
-/
import Desc

namespace PP

def names (Γ : Env) : List Name := Γ.map (·.1)

def rk (Γ : Env) (P : List Name) : Nat := ((names Γ).filter fun a => decide (a ∉ P)).length

def rank (Γ : Env) (t : Tok) : Nat := rk Γ t.P

theorem filter_len_le {p q : Name → Bool} (h : ∀ a, p a = true → q a = true) :
    ∀ l : List Name, (l.filter p).length ≤ (l.filter q).length
  | [] => by simp
  | a :: l => by
    have ih := filter_len_le h l
    simp only [List.filter_cons]
    by_cases hp : p a = true
    · have hq := h a hp; simp [hp, hq]; omega
    · by_cases hq : q a = true
      · simp [hp, hq]; omega
      · simp [hp, hq]; omega

theorem filter_len_lt {p q : Name → Bool} (h : ∀ a, p a = true → q a = true) (m : Name) (hm : q m = true ∧ p m = false) :
    ∀ l : List Name, m ∈ l → (l.filter p).length < (l.filter q).length
  | [], hl => by simp at hl
  | a :: l, hl => by
    simp only [List.filter_cons]
    rcases List.mem_cons.mp hl with e | e
    · subst e
      have := filter_len_le h l
      simp [hm.1, hm.2]; omega
    · have ih := filter_len_lt h m hm l e
      by_cases hp : p a = true
      · have hq := h a hp; simp [hp, hq]; omega
      · by_cases hq : q a = true
        · simp [hp, hq]; omega
        · simp [hp, hq]; omega

theorem rk_anti (Γ : Env) {P Q : List Name} (h : Sub P Q) : rk Γ Q ≤ rk Γ P := by
  unfold rk
  apply filter_len_le
  intro a ha
  simp only [decide_eq_true_eq] at ha ⊢
  exact fun hp => ha (h a hp)

theorem rk_lt (Γ : Env) {P Q : List Name} (h : Sub P Q) (m : Name) (hmQ : m ∈ Q) (hmP : m ∉ P) (hmn : m ∈ names Γ) :
    rk Γ Q < rk Γ P := by
  unfold rk
  apply filter_len_lt (m := m)
  · intro a ha
    simp only [decide_eq_true_eq] at ha ⊢
    exact fun hp => ha (h a hp)
  · simp [hmQ, hmP]
  · exact hmn

theorem find_mem (Γ : Env) {m : Name} {d : Def} (h : Γ.find m = some d) : m ∈ names Γ := by
  unfold Env.find at h
  cases hf : Γ.find? (·.1 == m) with
  | none => simp [hf] at h
  | some p =>
    have hp := List.mem_of_find?_eq_some hf
    have he := List.find?_some hf
    simp at he
    unfold names
    exact List.mem_map.mpr ⟨p, hp, he⟩

/-- At rank 0 every macro name is in the mark, so hidden: nothing is eligible. -/
theorem rank_zero_hidden (Γ : Env) (t : Tok) (g : Sub t.P t.H) (h0 : rank Γ t = 0) {d : Def}
    (hf : Γ.find t.s = some d) : t.s ∈ t.H := by
  have hn := find_mem Γ hf
  unfold rank rk at h0
  have : t.s ∉ (names Γ).filter (fun a => decide (a ∉ t.P)) := by
    rw [List.length_eq_zero_iff] at h0; rw [h0]; simp
  simp only [List.mem_filter, decide_eq_true_eq, not_and, Classical.not_not] at this
  exact g _ (this hn)

/-! The invariant, step by step. -/

def Inv (xs : List Tok) : Prop := Good xs ∧ Desc xs

theorem inv_sublist {l m : List Tok} (h : l.Sublist m) (i : Inv m) : Inv l :=
  ⟨good_sublist h i.1, i.2.sublist h⟩

theorem inv_tail {x : Tok} {xs : List Tok} (i : Inv (x :: xs)) : Inv xs :=
  inv_sublist (List.sublist_cons_self x xs) i

theorem ranks_up (Γ : Env) {xs : List Tok} (d : Desc xs) : xs.Pairwise fun a b => rank Γ a ≤ rank Γ b :=
  d.imp fun h => rk_anti Γ h

/-- After an object macro's step: the new tokens, of a rank below the head's, then the rest. -/
theorem obj_next (Γ : Env) {x : Tok} {rest : List Tok} (i : Inv (x :: rest)) (hid : x.s ∉ x.H) {body : List BTok}
    (hf : Γ.find x.s = some (.obj body)) (c : Nat) (b : List Tok) :
    Inv (mark c (x.s :: x.H) b ++ rest) ∧ rk Γ (x.s :: x.H) < rank Γ x := by
  have ⟨gx, gr⟩ := good_cons.mp i.1
  have ⟨dx, dr⟩ := List.pairwise_cons.mp i.2
  refine ⟨⟨good_append.mpr ⟨good_mark _ _ _, gr⟩,
    desc_mark_append _ _ _ _ (fun t ht a ha => List.mem_cons_of_mem _ (gx a (dx t ht a ha))) dr⟩, ?_⟩
  exact rk_lt Γ (fun a ha => List.mem_cons_of_mem _ (gx a ha)) x.s (by simp) (fun h => hid (gx _ h)) (find_mem Γ hf)

/-- After a function-like macro's step: the new tokens, of a rank below the closing
    parenthesis's, then what follows it; and the arguments, each a sublist of the stream. -/
theorem fn_next (Γ : Env) {x open_ cl : Tok} {inner rest : List Tok} (i : Inv (x :: open_ :: (inner ++ cl :: rest)))
    (hid : x.s ∉ x.H) {d : Def} (hf : Γ.find x.s = some d) (c : Nat) (b : List Tok) :
    Inv (mark c (x.s :: inter x.H cl.H) b ++ rest) ∧ rk Γ (x.s :: inter x.H cl.H) < rank Γ cl ∧ Inv inner ∧
      rank Γ x ≤ rank Γ cl := by
  have ⟨gx, gr⟩ := good_cons.mp i.1
  have ⟨dx, dr⟩ := List.pairwise_cons.mp i.2
  have ga := (good_cons.mp gr).2
  have da := (List.pairwise_cons.mp dr).2
  have ⟨gin, gcr⟩ := good_append.mp ga
  have ⟨gcl, grest⟩ := good_cons.mp gcr
  have ⟨din, dcr, _⟩ := List.pairwise_append.mp da
  have ⟨dcl, drest⟩ := List.pairwise_cons.mp dcr
  have hxcl : Sub cl.P x.P := dx cl (by simp)
  have sub : Sub cl.P (x.s :: inter x.H cl.H) := by
    intro a ha
    apply List.mem_cons_of_mem
    simp only [inter, List.mem_filter, decide_eq_true_eq]
    exact ⟨gx a (hxcl a ha), gcl a ha⟩
  refine ⟨⟨good_append.mpr ⟨good_mark _ _ _, grest⟩, ?_⟩, ?_, ⟨gin, din⟩, rk_anti Γ hxcl⟩
  · refine desc_mark_append _ _ _ _ (fun t ht a ha => ?_) drest
    exact sub a (dcl t ht a ha)
  · exact rk_lt Γ sub x.s (by simp) (fun h => hid (gx _ (hxcl _ h))) (find_mem Γ hf)

end PP
