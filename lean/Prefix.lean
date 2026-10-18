/-
  Scanning a prefix: `pscan Γ n c A W` scans `A` as the front of `A ++ W`, and stops at the
  first point where the scan needs `W`: an invocation whose closing parenthesis is not in
  what is left of `A`, or a function-like name at its end. It returns what it emitted, its
  steps, the next number, and the stream left -- what the real scan then goes on with
  (`pscan_scan`).
-/
import Mono

namespace PP

theorem closeAt_append : ∀ (A : List Tok) (W : List Tok) (d : Nat) (acc : List Tok) inner cl rest,
    closeAt d A acc = some (inner, cl, rest) → closeAt d (A ++ W) acc = some (inner, cl, rest ++ W) := by
  intro A W
  induction A with
  | nil => intro d acc inner cl rest h; simp [closeAt] at h
  | cons x A ih =>
    intro d acc inner cl rest h
    simp only [List.cons_append]
    unfold closeAt at h ⊢
    split at h
    · rename_i hx; rw [if_pos hx]
      split at h
      · rename_i hd; rw [if_pos hd]
        simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
        obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩
      · rename_i hd; rw [if_neg hd]; exact ih _ _ _ _ _ h
    · rename_i hx; rw [if_neg hx]
      split at h
      · rename_i ho; rw [if_pos ho]; exact ih _ _ _ _ _ h
      · rename_i ho; rw [if_neg ho]; exact ih _ _ _ _ _ h

abbrev PRes := List Tok × List Step × Nat × List Tok

def pemit (x : Tok) (r : Option PRes) : Option PRes := r.map fun q => (x :: q.1, q.2.1, q.2.2.1, q.2.2.2)
def pafter (step : Step) (st₁ : List Step) (r : Option PRes) : Option PRes :=
  r.map fun q => (q.1, st₁ ++ step :: q.2.1, q.2.2.1, q.2.2.2)

def pscan (Γ : Env) (W : List Tok) : Nat → Nat → List Tok → Option PRes
  | 0, _, _ => none
  | _ + 1, c, [] => some ([], [], c, W)
  | n + 1, c, x :: rest =>
    if x.s ∈ x.H then pemit x (pscan Γ W n c rest) else
    match Γ.find x.s with
    | some (.obj body) =>
      (subst Γ n (c + 1) body [] []).bind fun r =>
      (paste r.1).bind fun b =>
      pafter { m := x.s, head := x, close := none, mark := x.s :: x.H, id := c } r.2.1
        (pscan Γ W n r.2.2 (mark c (x.s :: x.H) b ++ rest))
    | some (.fn arity variadic body) =>
      match rest with
      | open_ :: after' =>
        if open_.s != "(" then pemit x (pscan Γ W n c rest) else
        match closeAt 0 after' [] with
        | none => some ([], [], c, x :: rest ++ W)
        | some a =>
          (bind arity variadic a.1).bind fun bd =>
          (subst Γ n (c + 1) body bd.1 bd.2).bind fun r =>
          (paste r.1).bind fun b =>
          pafter { m := x.s, head := x, close := some a.2.1, mark := x.s :: inter x.H a.2.1.H, id := c } r.2.1
            (pscan Γ W n r.2.2 (mark c (x.s :: inter x.H a.2.1.H) b ++ a.2.2))
      | [] => some ([], [], c, x :: W)
    | none => pemit x (pscan Γ W n c rest)

theorem pemit_some {x : Tok} {r : Option PRes} {o st c S} (h : pemit x r = some (o, st, c, S)) :
    ∃ o', r = some (o', st, c, S) ∧ o = x :: o' := by
  unfold pemit at h
  cases r with
  | none => simp at h
  | some q =>
    obtain ⟨a, b, d, e⟩ := q
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨a, rfl, rfl⟩

theorem pafter_some {step : Step} {st₁ : List Step} {r : Option PRes} {o st c S}
    (h : pafter step st₁ r = some (o, st, c, S)) : ∃ st₂, r = some (o, st₂, c, S) ∧ st = st₁ ++ step :: st₂ := by
  unfold pafter at h
  cases r with
  | none => simp at h
  | some q =>
    obtain ⟨a, b, d, e⟩ := q
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨b, rfl, rfl⟩

/-- The real scan of `A ++ W` is the prefix scan, then the scan of what it leaves. -/
theorem pscan_scan (Γ : Env) (W : List Tok) : ∀ n c A o st c' S, pscan Γ W n c A = some (o, st, c', S) →
    ∀ m q, scan Γ m c' S = some q → scan Γ (n + m) c (A ++ W) = some (o ++ q.1, st ++ q.2.1, q.2.2) := by
  intro n
  induction n with
  | zero => intro c A o st c' S h; simp [pscan] at h
  | succ n ih =>
    intro c A o st c' S h m q hq
    have mono : ∀ ys, scan Γ m c ys = some q → scan Γ (n + 1 + m) c ys = some q :=
      fun ys e => scanMono Γ m c ys q e _ (by omega)
    cases A with
    | nil =>
      simp [pscan] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      simpa using mono W hq
    | cons x rest =>
      have hn : n + 1 + m = (n + m) + 1 := by omega
      unfold pscan at h
      rw [hn, List.cons_append]
      unfold scan
      have emit_ok : ∀ ys o st c' S, pemit x (pscan Γ W n c ys) = some (o, st, c', S) →
          scan Γ m c' S = some q → emit x (scan Γ (n + m) c (ys ++ W)) = some (o ++ q.1, st ++ q.2.1, q.2.2) := by
        intro ys o st c' S e hq'
        obtain ⟨o', hr, rfl⟩ := pemit_some e
        have := ih c ys o' st c' S hr m q hq'
        unfold emit; rw [this]; rfl
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
            unfold after; rw [this]; simp
          | fn arity variadic body =>
            simp only at h ⊢
            cases rest with
            | nil =>
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl, rfl⟩ := h
              have := mono (x :: W) hq
              rw [hn] at this
              unfold scan at this
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
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
                  have := mono (x :: open_ :: after' ++ W) hq
                  rw [hn] at this
                  unfold scan at this
                  simp only [hid, ite_false, hf, List.cons_append, hne, Bool.false_eq_true] at this
                  simpa using this
                | some a =>
                  rw [hc] at h
                  obtain ⟨inner, cl, rst⟩ := a
                  rw [closeAt_append after' W 0 [] inner cl rst hc]
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
                  unfold after; rw [this]; simp

end PP
