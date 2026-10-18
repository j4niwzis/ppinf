/-
  Lengths: pasting does not lengthen; marking keeps the length; a substitution's length and
  its steps are bounded by its arguments' expansions -- and it is the same with any fuel at
  which those expansions are.
-/
import Rank

namespace PP

theorem paste_go_len : ∀ (acc xs : List RTok) ys, paste.go acc xs = some ys → ys.length ≤ acc.length + xs.length
  | acc, [], ys, h => by unfold paste.go at h; simp only [Option.some.injEq] at h; subst h; simp
  | a :: acc, .op :: b :: rest, ys, h => by
    unfold paste.go at h
    cases hc : pasteTwo a b with
    | none => simp [hc] at h
    | some c' =>
      rw [hc] at h
      have := paste_go_len (c' :: acc) rest ys (by simpa using h)
      simp at this ⊢; omega
  | [], .op :: _, ys, h => by unfold paste.go at h; simp at h
  | _ :: _, [.op], ys, h => by unfold paste.go at h; simp at h
  | acc, .t x :: rest, ys, h => by
    have := paste_go_len (.t x :: acc) rest ys (by unfold paste.go at h; simpa using h)
    simp at this ⊢; omega
  | acc, .pm :: rest, ys, h => by
    have := paste_go_len (.pm :: acc) rest ys (by unfold paste.go at h; simpa using h)
    simp at this ⊢; omega

theorem paste_len (xs : List RTok) ys (h : paste xs = some ys) : ys.length ≤ xs.length := by
  unfold paste at h
  cases hg : paste.go [] xs with
  | none => simp [hg] at h
  | some zs =>
    simp only [hg, Option.map_some, Option.some.injEq] at h
    subst h
    have h1 := paste_go_len [] xs zs hg
    simp only [List.length_nil, Nat.zero_add] at h1
    exact Nat.le_trans (List.length_filterMap_le _ _) h1

theorem mark_len (e : Nat) (K : List Name) (b : List Tok) : (mark e K b).length = b.length := by simp [mark]

theorem expand_nil (Γ : Env) (f c : Nat) (hf : 1 ≤ f) : expand Γ f c [] = some ([], [], c) := by
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  simp [expand, scan, finalize]

theorem expand_nil_eq (Γ : Env) (n c : Nat) q (h : expand Γ n c [] = some q) : q = ([], [], c) := by
  cases n with
  | zero => simp [expand, scan] at h
  | succ n => simp [expand, scan, finalize] at h; exact h.symm

/-- A substitution, bounded by its arguments' expansions; and the same with any fuel `f` at
    which they are the same. -/
theorem subst_bound (Γ : Env) (n : Nat) (whole : List BTok) (named : List (List Tok)) (va : List Tok)
    (S T f : Nat) (hf : 1 ≤ f)
    (hlen : ∀ a, (a ∈ named ∨ a = va) → a.length ≤ S)
    (hexp : ∀ a, (a ∈ named ∨ a = va) → ∀ c0 q, expand Γ n c0 a = some q →
      q.1.length ≤ S ∧ q.2.1.length ≤ T ∧ expand Γ f c0 a = some q) :
    ∀ bs i c r st c', substFrom Γ n whole bs i c named va = some (r, st, c') →
      r.length ≤ bs.length * (S + 1) ∧ st.length ≤ bs.length * T ∧ substFrom Γ f whole bs i c named va = some (r, st, c') := by
  intro bs
  induction bs with
  | nil => intro i c r st c' h; simp [substFrom] at h ⊢; obtain ⟨rfl, rfl, rfl⟩ := h; simp
  | cons b bs ih =>
    intro i c r st c' h
    simp only [substFrom] at h
    obtain ⟨⟨here, st₁, c₁⟩, hp, h⟩ := bind_some h
    cases hm : substFrom Γ n whole bs (i + 1) c₁ named va with
    | none => simp [hm] at h
    | some q =>
      obtain ⟨more, st₂, c₂⟩ := q
      simp only [hm, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have ⟨l2, s2, e2⟩ := ih _ _ _ _ _ hm
      -- the piece
      have one_ok : ∀ a, (a = [] ∨ a ∈ named ∨ a = va) → ∀ here st₁ c₁, one Γ n whole a i c = some (here, st₁, c₁) →
          here.length ≤ S + 1 ∧ st₁.length ≤ T ∧ one Γ f whole a i c = some (here, st₁, c₁) := by
        intro a ha here st₁ c₁ e
        unfold one at e ⊢
        by_cases hadj : adjacentPaste whole i = true
        · simp only [hadj, ite_true, Option.some.injEq, Prod.mk.injEq] at e ⊢
          obtain ⟨rfl, rfl, rfl⟩ := e
          refine ⟨?_, by simp, ⟨rfl, rfl, rfl⟩⟩
          by_cases he : a.isEmpty = true
          · simp [he]
          · simp only [he]
            rcases ha with rfl | ha
            · simp
            · simp; have := hlen a ha; omega
        · simp only [hadj] at e ⊢
          cases hx : expand Γ n c a with
          | none => simp [hx] at e
          | some q =>
            rw [hx] at e
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
            obtain ⟨rfl, rfl, rfl⟩ := e
            rcases ha with rfl | ha
            · have hq := expand_nil_eq Γ n c q hx
              subst hq
              simp [expand_nil Γ f c hf]
            · have ⟨l, s, e⟩ := hexp a ha c q hx
              refine ⟨by simp; omega, s, ?_⟩
              rw [e]; rfl
      have ⟨l1, s1, e1⟩ : here.length ≤ S + 1 ∧ st₁.length ≤ T ∧ piece Γ f whole b i c named va = some (here, st₁, c₁) := by
        cases b with
        | tok x => simp [piece] at hp ⊢; obtain ⟨rfl, rfl, rfl⟩ := hp; simp
        | paste => simp [piece] at hp ⊢; obtain ⟨rfl, rfl, rfl⟩ := hp; simp
        | param j =>
          simp only [piece] at hp ⊢
          apply one_ok _ _ _ _ _ hp
          unfold List.getD
          cases hj : named[j]? with
          | none => exact Or.inl rfl
          | some a => exact Or.inr (Or.inl (List.mem_of_getElem? hj))
        | va => simp only [piece] at hp ⊢; exact one_ok _ (Or.inr (Or.inr rfl)) _ _ _ hp
      refine ⟨?_, ?_, ?_⟩
      · simp [List.length_append, List.length_cons, Nat.succ_mul]; omega
      · simp [List.length_append, List.length_cons, Nat.succ_mul]; omega
      · simp only [substFrom]; rw [e1]; simp only [Option.bind_some]; rw [e2]; rfl

end PP
