/-
  A scan that finishes on its own: when the scan of `X` succeeds and emits no macro name,
  whatever follows does not change it -- the scan of `X ++ W` is the scan of `X`, then the
  scan of `W`.
-/
import Bound

namespace PP

/-- A prefix scan does not look at what is behind except to hand it back. -/
theorem pscan_W (Γ : Env) (W W' : List Tok) : ∀ n c A o st c' S, pscan Γ W n c A = some (o, st, c', S ++ W) →
    pscan Γ W' n c A = some (o, st, c', S ++ W') := by
  intro n
  induction n with
  | zero => intro c A o st c' S h; simp [pscan] at h
  | succ n ih =>
    intro c A o st c' S h
    cases A with
    | nil =>
      simp [pscan] at h
      obtain ⟨rfl, rfl, rfl, hS⟩ := h
      have : S = [] := List.append_cancel_right (by simpa using hS.symm : S ++ W = [] ++ W)
      subst this; simp [pscan]
    | cons x R =>
      rcases iter_cases Γ W n c x R _ h with ⟨hp, q2, h2, he⟩ | ⟨body, r, b, q2, hid, hf, hr, hb, h2, he⟩ |
          ⟨arity, variadic, body, open_, inner, cl, rest, named, va, r, b, q2, hid, hf, hR, hop, hc, hbd, hr, hb, h2, he⟩ |
          ⟨hs, he⟩
      · obtain ⟨o2, st2, c2, S2⟩ := q2
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl, rfl⟩ := he
        have := rebuild_pass Γ W' n c x R hp _ (ih _ _ _ _ _ S h2)
        simpa using this
      · obtain ⟨o2, st2, c2, S2⟩ := q2
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl, rfl⟩ := he
        have := rebuild_obj Γ W' n c x R hid hf r b _ hr hb (ih _ _ _ _ _ S h2)
        simpa using this
      · subst hR
        obtain ⟨o2, st2, c2, S2⟩ := q2
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl, rfl⟩ := he
        have := rebuild_fn Γ W' n c x open_ cl inner rest hid hf hop hc named va r b _ hbd hr hb (ih _ _ _ _ _ S h2)
        simpa using this
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl, hS⟩ := he
        have : S = x :: R := List.append_cancel_right (by simpa using hS : S ++ W = (x :: R) ++ W)
        subst this
        have := rebuild_stop Γ W' n c' x R hs
        simpa using this

/-- The frame lemma. -/
theorem scan_frame (Γ : Env) (X W : List Tok) (n c : Nat) (r : List Tok × List Step × Nat)
    (h : scan Γ n c X = some r) (clean : ∀ t ∈ r.1, Γ.find t.s = none) (m : Nat) (q : List Tok × List Step × Nat)
    (hq : scan Γ m r.2.2 W = some q) : scan Γ (n + m) c (X ++ W) = some (r.1 ++ q.1, r.2.1 ++ q.2.1, q.2.2) := by
  obtain ⟨o, st, c', S', q', k, hp, _, hq', rfl⟩ := scan_pscan Γ [] n c X r (by simpa using h)
  rcases pscan_stop_shape Γ [] n c X _ hp with hS | ⟨x, R, hS, hs⟩
  · simp only at hS; subst hS
    have hq0 : q' = ([], [], c') := by
      cases k with
      | zero => simp [scan] at hq'
      | succ k => simp [scan] at hq'; exact hq'.symm
    subst hq0
    have hp' := pscan_W Γ [] W n c X o st c' [] (by simpa using hp)
    have := pscan_scan Γ W n c X o st c' ([] ++ W) hp' m q (by simpa using hq)
    simpa using this
  · simp only [List.append_nil] at hS; subst hS
    have ⟨hR, hq0⟩ := scan_stop Γ x R hs k c' q' hq'
    subst hq0
    obtain ⟨_, a, v, b, hf, _⟩ := hs
    exact absurd (clean x (by simp)) (by rw [hf]; simp)

end PP
