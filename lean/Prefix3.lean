/-
  Prefix scans: more fuel changes nothing; and they compose -- the prefix scan of
  `A1 ++ A2` behind `W` is the prefix scan of `A1` behind `A2 ++ W`, then the prefix scan of
  what that leaves before `W`.
-/
import Prefix2

namespace PP

theorem pscan_mono (Γ : Env) (W : List Tok) : ∀ n c A q, pscan Γ W n c A = some q → ∀ m, n ≤ m → pscan Γ W m c A = some q := by
  intro n
  induction n with
  | zero => intro c A q h; simp [pscan] at h
  | succ n ih =>
    intro c A q h m hm
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hm' : n ≤ m := by omega
    cases A with
    | nil => simpa [pscan] using h
    | cons x rest =>
      unfold pscan at h ⊢
      have emit_mono : ∀ ys, pemit x (pscan Γ W n c ys) = some q → pemit x (pscan Γ W m c ys) = some q := by
        intro ys e'
        cases hs : pscan Γ W n c ys with
        | none => simp [hs, pemit] at e'
        | some r => rw [ih c ys r hs m hm']; rw [hs] at e'; exact e'
      by_cases hid : x.s ∈ x.H
      · simp only [hid, ite_true] at h ⊢; exact emit_mono rest h
      · simp only [hid, ite_false] at h ⊢
        cases hf : Γ.find x.s with
        | none => rw [hf] at h; simp only at h ⊢; exact emit_mono rest h
        | some d =>
          rw [hf] at h
          cases d with
          | obj body =>
            simp only at h ⊢
            obtain ⟨p, hp, h⟩ := bind_some h
            rw [subst_mono Γ hp m hm']; simp only [Option.bind_some]
            obtain ⟨b, hb, h⟩ := bind_some h
            rw [hb]; simp only [Option.bind_some]
            unfold pafter at h ⊢
            cases hs : pscan Γ W n p.2.2 (mark c (x.s :: x.H) b ++ rest) with
            | none => simp [hs] at h
            | some r => rw [ih _ _ r hs m hm']; rw [hs] at h; exact h
          | fn arity variadic body =>
            simp only at h ⊢
            cases rest with
            | nil => exact h
            | cons open_ after' =>
              simp only at h ⊢
              by_cases hne : (open_.s != "(") = true
              · simp only [hne, ite_true] at h ⊢; exact emit_mono _ h
              · simp only [hne, Bool.false_eq_true, ite_false] at h ⊢
                cases hc : closeAt 0 after' [] with
                | none => rw [hc] at h; exact h
                | some a =>
                  rw [hc] at h; simp only at h ⊢
                  obtain ⟨bd, hbd, h⟩ := bind_some h
                  rw [hbd]; simp only [Option.bind_some]
                  obtain ⟨p, hp, h⟩ := bind_some h
                  rw [subst_mono Γ hp m hm']; simp only [Option.bind_some]
                  obtain ⟨b, hb, h⟩ := bind_some h
                  rw [hb]; simp only [Option.bind_some]
                  unfold pafter at h ⊢
                  cases hs : pscan Γ W n p.2.2 (mark c (x.s :: inter x.H a.2.1.H) b ++ a.2.2) with
                  | none => simp [hs] at h
                  | some r => rw [ih _ _ r hs m hm']; rw [hs] at h; exact h

/-- Joining: the prefix scan of `A1` behind `A2 ++ W`, leaving `T ++ A2 ++ W`, then the prefix
    scan of `T ++ A2` behind `W`. -/
theorem pscan_join (Γ : Env) (A2 W : List Tok) : ∀ n c A1 o st c' T, pscan Γ (A2 ++ W) n c A1 = some (o, st, c', T ++ A2 ++ W) →
    ∀ m q, pscan Γ W m c' (T ++ A2) = some q →
      pscan Γ W (n + m) c (A1 ++ A2) = some (o ++ q.1, st ++ q.2.1, q.2.2.1, q.2.2.2) := by
  intro n
  induction n with
  | zero => intro c A1 o st c' T h; simp [pscan] at h
  | succ n ih =>
    intro c A1 o st c' T h m q hq
    have mono : ∀ ys, pscan Γ W m c ys = some q → pscan Γ W (n + 1 + m) c ys = some q :=
      fun ys e => pscan_mono Γ W m c ys q e _ (by omega)
    have hn : n + 1 + m = (n + m) + 1 := by omega
    cases A1 with
    | nil =>
      simp [pscan] at h; obtain ⟨rfl, rfl, rfl, hT⟩ := h
      have : T = [] := List.append_cancel_right (by simpa using hT.symm : T ++ (A2 ++ W) = [] ++ (A2 ++ W))
      subst this
      simpa using mono A2 hq
    | cons x rest =>
      unfold pscan at h
      rw [hn, List.cons_append]
      unfold pscan
      have emit_ok : ∀ ys o st c' T, pemit x (pscan Γ (A2 ++ W) n c ys) = some (o, st, c', T ++ A2 ++ W) →
          pscan Γ W m c' (T ++ A2) = some q →
          pemit x (pscan Γ W (n + m) c (ys ++ A2)) = some (o ++ q.1, st ++ q.2.1, q.2.2.1, q.2.2.2) := by
        intro ys o st c' T e hq'
        obtain ⟨o', hr, rfl⟩ := pemit_some e
        have := ih c ys o' st c' T hr m q hq'
        unfold pemit; rw [this]; rfl
      by_cases hid : x.s ∈ x.H
      · simp only [hid, ite_true] at h ⊢; exact emit_ok rest _ _ _ _ h hq
      · simp only [hid, ite_false] at h ⊢
        cases hf : Γ.find x.s with
        | none => rw [hf] at h; simp only at h ⊢; exact emit_ok rest _ _ _ _ h hq
        | some d =>
          rw [hf] at h
          cases d with
          | obj body =>
            simp only at h ⊢
            obtain ⟨p, hp, h⟩ := bind_some h
            rw [subst_mono Γ hp (n + m) (by omega)]; simp only [Option.bind_some]
            obtain ⟨b, hb, h⟩ := bind_some h
            rw [hb]; simp only [Option.bind_some]
            obtain ⟨st₂, hr, rfl⟩ := pafter_some h
            have := ih _ _ _ _ _ _ hr m q hq
            rw [List.append_assoc] at this
            unfold pafter; rw [this]; simp
          | fn arity variadic body =>
            simp only at h ⊢
            cases rest with
            | nil =>
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl, hT⟩ := h
              have : T = [x] := List.append_cancel_right (by simpa using hT.symm : T ++ (A2 ++ W) = [x] ++ (A2 ++ W))
              subst this
              have := mono (x :: A2) hq
              rw [hn] at this
              unfold pscan at this
              simp only [hid, ite_false, hf] at this
              simpa using this
            | cons open_ after' =>
              simp only [List.cons_append] at h ⊢
              by_cases hne : (open_.s != "(") = true
              · simp only [hne, ite_true] at h ⊢
                have := emit_ok (open_ :: after') _ _ _ _ h hq
                simpa using this
              · simp only [hne, Bool.false_eq_true, ite_false] at h ⊢
                cases hc : closeAt 0 after' [] with
                | none =>
                  rw [hc] at h
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl, rfl, hT⟩ := h
                  have : T = x :: open_ :: after' :=
                    List.append_cancel_right (by simpa using hT.symm : T ++ (A2 ++ W) = (x :: open_ :: after') ++ (A2 ++ W))
                  subst this
                  have := mono (x :: open_ :: after' ++ A2) hq
                  rw [hn] at this
                  unfold pscan at this
                  simp only [hid, ite_false, hf, List.cons_append, hne, Bool.false_eq_true] at this
                  simpa using this
                | some a =>
                  rw [hc] at h
                  obtain ⟨inner, cl, rst⟩ := a
                  rw [closeAt_append after' A2 0 [] inner cl rst hc]
                  simp only [Option.bind_some] at h ⊢
                  obtain ⟨bd, hbd, h⟩ := bind_some h
                  rw [hbd]; simp only [Option.bind_some]
                  obtain ⟨p, hp, h⟩ := bind_some h
                  rw [subst_mono Γ hp (n + m) (by omega)]; simp only [Option.bind_some]
                  obtain ⟨b, hb, h⟩ := bind_some h
                  rw [hb]; simp only [Option.bind_some]
                  obtain ⟨st₂, hr, rfl⟩ := pafter_some h
                  have := ih _ _ _ _ _ _ hr m q hq
                  rw [List.append_assoc] at this
                  unfold pafter; rw [this]; simp

end PP

namespace PP

/-- Splitting: a prefix scan of `A1 ++ A2` that succeeds goes through the prefix scan of `A1`
    behind `A2 ++ W`, within the same fuel. -/
theorem pscan_split (Γ : Env) (A2 W : List Tok) : ∀ n c A1 q, pscan Γ W n c (A1 ++ A2) = some q →
    ∃ o st c' T q' k, pscan Γ (A2 ++ W) n c A1 = some (o, st, c', T ++ A2 ++ W) ∧ k ≤ n ∧
      pscan Γ W k c' (T ++ A2) = some q' ∧ q = (o ++ q'.1, st ++ q'.2.1, q'.2.2.1, q'.2.2.2) := by
  intro n
  induction n with
  | zero => intro c A1 q h; simp [pscan] at h
  | succ n ih =>
    intro c A1 q h
    obtain ⟨qo, qst, qc, qS⟩ := q
    cases A1 with
    | nil => exact ⟨[], [], c, [], (qo, qst, qc, qS), n + 1, by simp [pscan], Nat.le_refl _, by simpa using h, by simp⟩
    | cons x rest =>
      have emit_case : ∀ ys, pemit x (pscan Γ W n c (ys ++ A2)) = some (qo, qst, qc, qS) →
          ∃ o st c' T q' k, pemit x (pscan Γ (A2 ++ W) n c ys) = some (o, st, c', T ++ A2 ++ W) ∧ k ≤ n + 1 ∧
            pscan Γ W k c' (T ++ A2) = some q' ∧ (qo, qst, qc, qS) = (o ++ q'.1, st ++ q'.2.1, q'.2.2.1, q'.2.2.2) := by
        intro ys e
        obtain ⟨o', hr, rfl⟩ := pemit_some e
        obtain ⟨o, st, c', T, q', k, hp, hk, hq, he⟩ := ih c ys _ hr
        refine ⟨x :: o, st, c', T, q', k, by unfold pemit; rw [hp]; rfl, by omega, hq, ?_⟩
        simp only [Prod.mk.injEq] at he
        obtain ⟨h1, h2, h3, h4⟩ := he
        simp [h1, h2, h3, h4]
      rw [List.cons_append] at h
      unfold pscan at h
      simp only [pscan]
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
            obtain ⟨st₂, hr, rfl⟩ := pafter_some h
            rw [← List.append_assoc] at hr
            obtain ⟨o, st, c', T, q', k, hps, hk, hq, he⟩ := ih _ _ _ hr
            refine ⟨o, p.2.1 ++ { m := x.s, head := x, close := none, mark := x.s :: x.H, id := c } :: st, c', T, q', k,
              by unfold pafter; rw [hps]; rfl, by omega, hq, ?_⟩
            simp only [Prod.mk.injEq] at he
            obtain ⟨h1, h2, h3, h4⟩ := he
            simp [h1, h2, h3, h4]
          | fn arity variadic body =>
            simp only at h ⊢
            cases rest with
            | nil =>
              simp only [List.nil_append] at h
              refine ⟨[], [], c, [x], (qo, qst, qc, qS), n + 1, by simp, Nat.le_refl _, ?_, by simp⟩
              unfold pscan; simp only [hid, ite_false, hf, List.singleton_append]; exact h
            | cons open_ after' =>
              simp only [List.cons_append] at h ⊢
              by_cases hne : (open_.s != "(") = true
              · simp only [hne, ite_true] at h ⊢
                exact emit_case (open_ :: after') (by simpa using h)
              · simp only [hne, Bool.false_eq_true, ite_false] at h ⊢
                cases hc : closeAt 0 after' [] with
                | none =>
                  refine ⟨[], [], c, x :: open_ :: after', (qo, qst, qc, qS), n + 1, by simp, Nat.le_refl _, ?_, by simp⟩
                  unfold pscan; simp only [hid, ite_false, hf, List.cons_append, hne, Bool.false_eq_true]; exact h
                | some a =>
                  obtain ⟨inner, cl, rst⟩ := a
                  rw [closeAt_append after' A2 0 [] inner cl rst hc] at h
                  simp only [Option.bind_some] at h ⊢
                  obtain ⟨bd, hbd, h⟩ := bind_some h
                  rw [hbd]; simp only [Option.bind_some]
                  obtain ⟨p, hp, h⟩ := bind_some h
                  rw [hp]; simp only [Option.bind_some]
                  obtain ⟨b, hb, h⟩ := bind_some h
                  rw [hb]; simp only [Option.bind_some]
                  obtain ⟨st₂, hr, rfl⟩ := pafter_some h
                  rw [← List.append_assoc] at hr
                  obtain ⟨o, st, c', T, q', k, hps, hk, hq, he⟩ := ih _ _ _ hr
                  refine ⟨o, p.2.1 ++ { m := x.s, head := x, close := some cl, mark := x.s :: inter x.H cl.H, id := c } :: st,
                    c', T, q', k, by unfold pafter; rw [hps]; rfl, by omega, hq, ?_⟩
                  simp only [Prod.mk.injEq] at he
                  obtain ⟨h1, h2, h3, h4⟩ := he
                  simp [h1, h2, h3, h4]

end PP
