/-
  When the whole scan succeeds, so does the prefix scan, within the same fuel; what it
  leaves ends with W; and prefix scans compose.
-/
import Prefix

namespace PP

/-- What a prefix scan leaves ends with what was behind it. -/
theorem pscan_rest (Γ : Env) (W : List Tok) : ∀ n c A o st c' S, pscan Γ W n c A = some (o, st, c', S) →
    ∃ T, S = T ++ W := by
  intro n
  induction n with
  | zero => intro c A o st c' S h; simp [pscan] at h
  | succ n ih =>
    intro c A o st c' S h
    cases A with
    | nil => simp [pscan] at h; exact ⟨[], by simp [h.2.2.2]⟩
    | cons x rest =>
      unfold pscan at h
      by_cases hid : x.s ∈ x.H
      · simp only [hid, ite_true] at h
        obtain ⟨_, hr, _⟩ := pemit_some h; exact ih _ _ _ _ _ _ hr
      · simp only [hid, ite_false] at h
        cases hf : Γ.find x.s with
        | none => rw [hf] at h; simp only at h; obtain ⟨_, hr, _⟩ := pemit_some h; exact ih _ _ _ _ _ _ hr
        | some d =>
          rw [hf] at h
          cases d with
          | obj body =>
            simp only at h
            obtain ⟨_, _, h⟩ := bind_some h
            obtain ⟨_, _, h⟩ := bind_some h
            obtain ⟨_, hr, _⟩ := pafter_some h
            exact ih _ _ _ _ _ _ hr
          | fn arity variadic body =>
            simp only at h
            cases rest with
            | nil => simp at h; exact ⟨[x], by simp [h.2.2.2]⟩
            | cons open_ after' =>
              simp only at h
              by_cases hne : (open_.s != "(") = true
              · simp only [hne, ite_true] at h
                obtain ⟨_, hr, _⟩ := pemit_some h; exact ih _ _ _ _ _ _ hr
              · simp only [hne, Bool.false_eq_true, ite_false] at h
                cases hc : closeAt 0 after' [] with
                | none => rw [hc] at h; simp at h; exact ⟨x :: open_ :: after', by simp [h.2.2.2]⟩
                | some a =>
                  rw [hc] at h
                  simp only at h
                  obtain ⟨_, _, h⟩ := bind_some h
                  obtain ⟨_, _, h⟩ := bind_some h
                  obtain ⟨_, _, h⟩ := bind_some h
                  obtain ⟨_, hr, _⟩ := pafter_some h
                  exact ih _ _ _ _ _ _ hr

/-- A scan of `A ++ W` that succeeds goes through the prefix scan of `A`: within the same
    fuel, and then the scan of what it leaves. -/
theorem scan_pscan (Γ : Env) (W : List Tok) : ∀ n c A r, scan Γ n c (A ++ W) = some r →
    ∃ o st c' S q k, pscan Γ W n c A = some (o, st, c', S) ∧ k ≤ n ∧ scan Γ k c' S = some q ∧
      r = (o ++ q.1, st ++ q.2.1, q.2.2) := by
  intro n
  induction n with
  | zero => intro c A r h; simp [scan] at h
  | succ n ih =>
    intro c A r h
    obtain ⟨ro, rst, rc⟩ := r
    cases A with
    | nil => exact ⟨[], [], c, W, (ro, rst, rc), n + 1, by simp [pscan], Nat.le_refl _, by simpa using h, by simp⟩
    | cons x rest =>
      have emit_case : ∀ ys, emit x (scan Γ n c (ys ++ W)) = some (ro, rst, rc) →
          ∃ o st c' S q k, pemit x (pscan Γ W n c ys) = some (o, st, c', S) ∧ k ≤ n + 1 ∧ scan Γ k c' S = some q ∧
            (ro, rst, rc) = (o ++ q.1, st ++ q.2.1, q.2.2) := by
        intro ys e
        obtain ⟨out', hr, rfl⟩ := emit_some e
        obtain ⟨o, st, c', S, q, k, hp, hk, hq, he⟩ := ih c ys _ hr
        refine ⟨x :: o, st, c', S, q, k, by unfold pemit; rw [hp]; rfl, by omega, hq, ?_⟩
        simp only [Prod.mk.injEq] at he
        obtain ⟨h1, h2, h3⟩ := he
        simp [h1, h2, h3]
      rw [List.cons_append] at h
      unfold scan at h
      unfold pscan
      by_cases hid : x.s ∈ x.H
      · simp only [hid, ite_true] at h ⊢; exact emit_case rest h
      · simp only [hid, ite_false] at h ⊢
        cases hf : Γ.find x.s with
        | none => rw [hf] at h; simp only at h ⊢; exact emit_case rest h
        | some d =>
          rw [hf] at h
          cases d with
          | obj body =>
            simp only at h ⊢
            obtain ⟨p, hp, h⟩ := bind_some h
            rw [hp]; simp only [Option.bind_some]
            obtain ⟨b, hb, h⟩ := bind_some h
            rw [hb]; simp only [Option.bind_some]
            obtain ⟨st₂, hr, rfl⟩ := after_some h
            rw [← List.append_assoc] at hr
            obtain ⟨o, st, c', S, q, k, hps, hk, hq, he⟩ := ih _ _ _ hr
            refine ⟨o, p.2.1 ++ { m := x.s, head := x, close := none, mark := x.s :: x.H, id := c } :: st, c', S, q, k,
              by unfold pafter; rw [hps]; rfl, by omega, hq, ?_⟩
            simp only [Prod.mk.injEq] at he
            obtain ⟨h1, h2, h3⟩ := he
            simp [h1, h2, h3]
          | fn arity variadic body =>
            simp only at h ⊢
            cases rest with
            | nil =>
              simp only [List.nil_append] at h
              refine ⟨[], [], c, x :: W, (ro, rst, rc), n + 1, rfl, Nat.le_refl _, ?_, by simp⟩
              unfold scan; simp only [hid, ite_false, hf]; exact h
            | cons open_ after' =>
              simp only [List.cons_append] at h ⊢
              by_cases hne : (open_.s != "(") = true
              · simp only [hne, ite_true] at h ⊢
                have := emit_case (open_ :: after') (by simpa using h)
                exact this
              · simp only [hne, Bool.false_eq_true, ite_false] at h ⊢
                cases hc : closeAt 0 after' [] with
                | none =>
                  refine ⟨[], [], c, x :: open_ :: after' ++ W, (ro, rst, rc), n + 1, rfl, Nat.le_refl _, ?_, by simp⟩
                  unfold scan; simp only [hid, ite_false, hf, List.cons_append, hne, Bool.false_eq_true]; exact h
                | some a =>
                  obtain ⟨inner, cl, rst⟩ := a
                  rw [closeAt_append after' W 0 [] inner cl rst hc] at h
                  simp only [Option.bind_some] at h ⊢
                  obtain ⟨bd, hbd, h⟩ := bind_some h
                  rw [hbd]; simp only [Option.bind_some]
                  obtain ⟨p, hp, h⟩ := bind_some h
                  rw [hp]; simp only [Option.bind_some]
                  obtain ⟨b, hb, h⟩ := bind_some h
                  rw [hb]; simp only [Option.bind_some]
                  obtain ⟨st₂, hr, rfl⟩ := after_some h
                  rw [← List.append_assoc] at hr
                  obtain ⟨o, st, c', S, q, k, hps, hk, hq, he⟩ := ih _ _ _ hr
                  refine ⟨o, p.2.1 ++ { m := x.s, head := x, close := some cl, mark := x.s :: inter x.H cl.H, id := c } :: st,
                    c', S, q, k, by unfold pafter; rw [hps]; rfl, by omega, hq, ?_⟩
                  simp only [Prod.mk.injEq] at he
                  obtain ⟨h1, h2, h3⟩ := he
                  simp [h1, h2, h3]

end PP
