/-
  Steps are numbered apart: every step of a run has its own number, from the counter the
  scan threads. With it, a token's origin determines its mark (Consistent.lean).
-/
import Origins

namespace PP

/-- The steps of a call numbered within [c, c'), each once. -/
def Numbered (c c' : Nat) (st : List Step) : Prop :=
  c ≤ c' ∧ (∀ s ∈ st, c ≤ s.id ∧ s.id < c') ∧ (st.map (·.id)).Nodup

theorem numbered_nil (c : Nat) : Numbered c c [] := ⟨Nat.le_refl c, by simp, by simp⟩

theorem numbered_append {c m c' : Nat} {a b : List Step} (ha : Numbered c m a) (hb : Numbered m c' b) :
    Numbered c c' (a ++ b) := by
  refine ⟨Nat.le_trans ha.1 hb.1, ?_, ?_⟩
  · intro s hs
    rcases List.mem_append.mp hs with h | h
    · have := ha.2.1 s h; exact ⟨this.1, Nat.lt_of_lt_of_le this.2 hb.1⟩
    · have := hb.2.1 s h; exact ⟨Nat.le_trans ha.1 this.1, this.2⟩
  · rw [List.map_append, List.nodup_append]
    refine ⟨ha.2.2, hb.2.2, ?_⟩
    intro x hx y hy
    simp only [List.mem_map] at hx hy
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    have := (ha.2.1 s hs).2; have := (hb.2.1 t ht).1; omega

/-- A step numbered `c`, its arguments' steps after it, then the rescan's. -/
theorem numbered_step {c c₁ c' : Nat} {st₁ st₂ : List Step} (step : Step) (hid : step.id = c)
    (h₁ : Numbered (c + 1) c₁ st₁) (h₂ : Numbered c₁ c' st₂) : Numbered c c' (st₁ ++ step :: st₂) := by
  have hs : Numbered c (c + 1) [step] := ⟨by omega, by simp [hid], by simp⟩
  -- reorder: [step] ++ st₁ ++ st₂ has the same members
  have whole := numbered_append (numbered_append hs h₁) h₂
  refine ⟨whole.1, ?_, ?_⟩
  · intro s h
    apply whole.2.1
    simp only [List.mem_append, List.mem_cons] at h ⊢
    rcases h with h | h | h <;> simp_all
  · have p : (st₁ ++ step :: st₂).map (·.id) = st₁.map (·.id) ++ step.id :: st₂.map (·.id) := by simp
    rw [p]
    have q : ((([step] ++ st₁) ++ st₂).map (·.id)) = step.id :: (st₁.map (·.id) ++ st₂.map (·.id)) := by simp
    have w := whole.2.2; rw [q] at w
    exact (List.perm_middle).nodup_iff.mpr w

def ScanIds (Γ : Env) (n : Nat) : Prop := ∀ c xs out st c', scan Γ n c xs = some (out, st, c') → Numbered c c' st
def SubstIds (Γ : Env) (n : Nat) : Prop :=
  ∀ whole bs i c named va r st c', substFrom Γ n whole bs i c named va = some (r, st, c') → Numbered c c' st

theorem substIds_of_scan {Γ : Env} {n : Nat} (h : ScanIds Γ n) : SubstIds Γ n := by
  intro whole bs
  induction bs with
  | nil => intro i c named va r st c' e; simp [substFrom] at e; obtain ⟨_, rfl, rfl⟩ := e; exact numbered_nil c
  | cons b bs ih =>
    intro i c named va r st c' e
    simp only [substFrom] at e
    obtain ⟨⟨here, st₁, c₁⟩, hp, e⟩ := bind_some e
    cases hm : substFrom Γ n whole bs (i + 1) c₁ named va with
    | none => simp [hm] at e
    | some q =>
      obtain ⟨more, st₂, c₂⟩ := q
      simp only [hm, Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨_, rfl, rfl⟩ := e
      refine numbered_append ?_ (ih _ _ _ _ _ _ _ hm)
      have one_ok : ∀ a r st c', one Γ n whole a i c = some (r, st, c') → Numbered c c' st := by
        intro a r st c' e
        unfold one at e
        split at e
        · simp only [Option.some.injEq, Prod.mk.injEq] at e; obtain ⟨_, rfl, rfl⟩ := e; exact numbered_nil c
        · cases he : scan Γ n c a with
          | none => simp [expand, he] at e
          | some q =>
            obtain ⟨o, st₀, c₀⟩ := q
            simp only [expand, he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
            obtain ⟨_, rfl, rfl⟩ := e
            exact h c a o st₀ c₀ he
      unfold piece at hp
      cases b with
      | tok x => simp at hp; obtain ⟨_, rfl, rfl⟩ := hp; exact numbered_nil c
      | paste => simp at hp; obtain ⟨_, rfl, rfl⟩ := hp; exact numbered_nil c
      | param j => exact one_ok _ _ _ _ hp
      | va => exact one_ok _ _ _ _ hp

theorem emit_numbered {x : Tok} {r} {out st} {c c' : Nat} (h : emit x r = some (out, st, c'))
    (k : ∀ out' st', r = some (out', st', c') → Numbered c c' st') : Numbered c c' st := by
  obtain ⟨out', hr, _⟩ := emit_some h; exact k _ _ hr

theorem scanIds (Γ : Env) : ∀ n, ScanIds Γ n := by
  intro n
  induction n with
  | zero => intro c xs out st c' e; simp [scan] at e
  | succ n ih =>
    have sub := substIds_of_scan ih
    intro c xs out st c' e
    cases xs with
    | nil => simp [scan] at e; obtain ⟨rfl, rfl, rfl⟩ := e; exact numbered_nil c
    | cons x rest =>
      unfold scan at e
      split at e
      · exact emit_numbered e (fun _ _ hr => ih _ _ _ _ _ hr)
      · split at e
        · rename_i body _
          obtain ⟨⟨r, st₁, c₁⟩, hs, e⟩ := bind_some e
          obtain ⟨b, _, e⟩ := bind_some e
          obtain ⟨st₂, hr, rfl⟩ := after_some e
          exact numbered_step _ rfl (sub _ _ _ _ _ _ _ _ _ (by unfold subst at hs; exact hs)) (ih _ _ _ _ _ hr)
        · split at e
          · split at e
            · exact emit_numbered e (fun _ _ hr => ih _ _ _ _ _ hr)
            · obtain ⟨_, _, e⟩ := bind_some e
              obtain ⟨_, _, e⟩ := bind_some e
              obtain ⟨⟨r, st₁, c₁⟩, hs, e⟩ := bind_some e
              obtain ⟨b, _, e⟩ := bind_some e
              obtain ⟨st₂, hr, rfl⟩ := after_some e
              exact numbered_step _ rfl (sub _ _ _ _ _ _ _ _ _ (by unfold subst at hs; exact hs)) (ih _ _ _ _ _ hr)
          · simp only [Option.some.injEq, Prod.mk.injEq] at e
            obtain ⟨rfl, rfl, rfl⟩ := e
            exact numbered_nil c
        · exact emit_numbered e (fun _ _ hr => ih _ _ _ _ _ hr)

/-- Every run numbers its steps apart. -/
theorem steps_numbered (Γ : Env) (n c : Nat) (xs : List Tok) out st c'
    (e : expand Γ n c xs = some (out, st, c')) : (st.map (·.id)).Nodup ∧ ∀ s ∈ st, c ≤ s.id := by
  unfold expand at e
  cases hs : scan Γ n c xs with
  | none => simp [hs] at e
  | some q =>
    obtain ⟨o, st₀, c₀⟩ := q
    simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨_, rfl, rfl⟩ := e
    have := scanIds Γ n c xs o st₀ c₀ hs
    exact ⟨this.2.2, fun s h => (this.2.1 s h).1⟩

end PP
