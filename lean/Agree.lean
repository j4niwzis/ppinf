/-
  The machine computes the scan (Theorem 9): what a scan of fuel `n` returns, the machine
  reaches within `mcost (maxBody Γ) n` actions.
-/
import Machine
import Steps

namespace PP

theorem mrun_add (Γ : Env) : ∀ a b st, mrun Γ (a + b) st = mrun Γ b (mrun Γ a st)
  | 0, b, st => by simp [mrun]
  | a + 1, b, st => by
    rw [Nat.add_right_comm]
    show mrun Γ (a + b) (mstep Γ st) = mrun Γ b (mrun Γ a (mstep Γ st))
    exact mrun_add Γ a b _

/-- `t` within `k` actions of `s`. -/
def Reach (Γ : Env) (k : Nat) (s t : MState) : Prop := ∃ j ≤ k, mrun Γ j s = t

theorem Reach.refl (Γ : Env) (s : MState) : Reach Γ 0 s s := ⟨0, Nat.le_refl _, rfl⟩

theorem Reach.trans {Γ : Env} {a b s t u} (h1 : Reach Γ a s t) (h2 : Reach Γ b t u) : Reach Γ (a + b) s u := by
  obtain ⟨j1, hj1, e1⟩ := h1
  obtain ⟨j2, hj2, e2⟩ := h2
  exact ⟨j1 + j2, by omega, by rw [mrun_add, e1, e2]⟩

theorem Reach.mono {Γ : Env} {a b s t} (h : Reach Γ a s t) (hab : a ≤ b) : Reach Γ b s t := by
  obtain ⟨j, hj, e⟩ := h; exact ⟨j, by omega, e⟩

theorem Reach.step {Γ : Env} {s t} (h : mstep Γ s = t) : Reach Γ 1 s t := ⟨1, Nat.le_refl _, by simp [mrun, h]⟩

/-- A scanning state. -/
def sc (out inp : List Tok) (fs : List Frame) (steps : List Step) (c : Nat) : MState :=
  ⟨.scan ⟨out, inp⟩ fs, steps, c⟩

/-- What the scan of fuel `n` does, the machine does too. -/
def ScanAgrees (Γ : Env) (n : Nat) : Prop :=
  ∀ c xs out fs steps o st c', scan Γ n c xs = some (o, st, c') →
    Reach Γ (mcost (maxBody Γ) n) (sc out xs fs steps c) (sc (o.reverse ++ out) [] fs (st.reverse ++ steps) c')

/-- A body substituted element by element. -/
theorem body_agrees (Γ : Env) (n : Nat) (hA : ScanAgrees Γ n) : ∀ (bs : List BTok) (f : Frame) fs steps c rs st c',
    f.bs = bs → substFrom Γ n f.whole bs f.i c f.named f.va = some (rs, st, c') →
    Reach Γ (bs.length * (mcost (maxBody Γ) n + 2)) ⟨.body f fs, steps, c⟩
      ⟨.body { f with bs := [], i := f.i + bs.length, acc := f.acc ++ rs } fs, st.reverse ++ steps, c'⟩ := by
  intro bs
  induction bs with
  | nil =>
    intro f fs steps c rs st c' hbs h
    simp [substFrom] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have : { f with bs := [], i := f.i + 0, acc := f.acc ++ [] } = f := by cases f; simp_all
    simp only [List.length_nil, Nat.zero_mul, List.reverse_nil, List.nil_append]
    rw [this]; exact Reach.refl Γ _
  | cons b bs ih =>
    intro f fs steps c rs st c' hbs h
    simp only [substFrom, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨p, hp, q, hq, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    -- after placing `b`: the frame `f1` with the rest of the body
    have finish : ∀ (f1 : Frame) (j : Nat), f1.bs = bs → f1.whole = f.whole → f1.i = f.i + 1 →
        f1.named = f.named → f1.va = f.va → f1.acc = f.acc ++ p.1 → f1.lvl = f.lvl → f1.step = f.step → j ≤ mcost (maxBody Γ) n + 2 →
        Reach Γ j ⟨.body f fs, steps, c⟩ ⟨.body f1 fs, p.2.1.reverse ++ steps, p.2.2⟩ →
        Reach Γ ((b :: bs).length * (mcost (maxBody Γ) n + 2)) ⟨.body f fs, steps, c⟩
          ⟨.body { f with bs := [], i := f.i + (b :: bs).length, acc := f.acc ++ (p.1 ++ q.1) } fs,
            (p.2.1 ++ q.2.1).reverse ++ steps, q.2.2⟩ := by
      intro f1 j h1 h2 h3 h4 h5 h6 h7 h8 hj hr
      have hq' : substFrom Γ n f1.whole bs f1.i p.2.2 f1.named f1.va = some (q.1, q.2.1, q.2.2) := by
        rw [h2, h3, h4, h5]; exact hq
      have := Reach.trans hr (ih f1 fs _ p.2.2 q.1 q.2.1 q.2.2 h1 hq')
      have e : { f1 with bs := [], i := f1.i + bs.length, acc := f1.acc ++ q.1 } =
          { f with bs := [], i := f.i + (b :: bs).length, acc := f.acc ++ (p.1 ++ q.1) } := by
        cases f; cases f1
        simp only [Frame.mk.injEq] at h1 h2 h3 h4 h5 h6 h7 h8 ⊢
        subst h2 h3 h4 h5 h6 h7 h8
        simp only [List.length_cons, List.append_assoc, true_and, and_true]
        omega
      rw [e] at this
      simp only [List.reverse_append, List.append_assoc] at this ⊢
      exact this.mono (by rw [List.length_cons, Nat.succ_mul]; omega)
    -- placing without a scan
    have placed : ∀ xs : List RTok, p = (xs, [], c) →
        mstep Γ ⟨.body f fs, steps, c⟩ = ⟨.body { f with bs := bs, i := f.i + 1, acc := f.acc ++ xs } fs, steps, c⟩ →
        Reach Γ ((b :: bs).length * (mcost (maxBody Γ) n + 2)) ⟨.body f fs, steps, c⟩
          ⟨.body { f with bs := [], i := f.i + (b :: bs).length, acc := f.acc ++ (p.1 ++ q.1) } fs,
            (p.2.1 ++ q.2.1).reverse ++ steps, q.2.2⟩ := by
      intro xs hpx hm
      subst hpx
      exact finish { f with bs := bs, i := f.i + 1, acc := f.acc ++ xs } 1 rfl rfl rfl rfl rfl rfl rfl rfl (by omega) (Reach.step hm)
    -- an argument, as it is or expanded alone
    have argCase : ∀ a : List Tok, one Γ n f.whole a f.i c = some p →
        mstep Γ ⟨.body f fs, steps, c⟩ =
          (if adjacentPaste f.whole f.i then
            ⟨.body { f with bs := bs, i := f.i + 1, acc := f.acc ++ (if a.isEmpty then [RTok.pm] else a.map RTok.t) } fs, steps, c⟩
           else sc [] a (f :: fs) steps c) →
        Reach Γ ((b :: bs).length * (mcost (maxBody Γ) n + 2)) ⟨.body f fs, steps, c⟩
          ⟨.body { f with bs := [], i := f.i + (b :: bs).length, acc := f.acc ++ (p.1 ++ q.1) } fs,
            (p.2.1 ++ q.2.1).reverse ++ steps, q.2.2⟩ := by
      intro a ho hm
      unfold one at ho
      split at ho
      · rename_i hadj
        simp only [Option.some.injEq] at ho
        exact placed _ ho.symm (by rw [hm, if_pos hadj])
      · rename_i hadj
        simp only [expand, Option.map_eq_some_iff] at ho
        obtain ⟨⟨o1, st1, c1⟩, ⟨⟨o, st0, c0⟩, hs, he⟩, rfl⟩ := ho
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        have h1 : mstep Γ ⟨.body f fs, steps, c⟩ = sc [] a (f :: fs) steps c := by rw [hm, if_neg hadj]
        have h2 := hA c a [] (f :: fs) steps o st0 c0 hs
        have h3 : mstep Γ (sc (o.reverse ++ []) [] (f :: fs) (st0.reverse ++ steps) c0) =
            ⟨.body { f with bs := f.bs.tail, i := f.i + 1, acc := f.acc ++ (finalize o).map RTok.t } fs,
              st0.reverse ++ steps, c0⟩ := by simp [mstep, sc]
        exact finish { f with bs := f.bs.tail, i := f.i + 1, acc := f.acc ++ (finalize o).map RTok.t } _
          (by simp [hbs]) rfl rfl rfl rfl rfl rfl rfl (by omega)
          (((Reach.step h1).trans h2).trans (Reach.step h3))
    cases b with
    | tok s =>
      simp only [piece] at hp
      exact placed _ (by simpa using hp.symm) (by simp [mstep, hbs])
    | paste =>
      simp only [piece] at hp
      exact placed _ (by simpa using hp.symm) (by simp [mstep, hbs])
    | param j =>
      simp only [piece] at hp
      exact argCase _ hp (by simp [mstep, hbs, sc])
    | va =>
      simp only [piece] at hp
      exact argCase _ hp (by simp [mstep, hbs, sc])

theorem mcost_succ (b n : Nat) : mcost b (n + 1) = (b + 1) * mcost b n + 2 * b + 3 := rfl

/-- **The machine computes the scan.** -/
theorem scan_agrees (Γ : Env) : ∀ n, ScanAgrees Γ n
  | 0 => by intro c xs out fs steps o st c' h; simp [scan] at h
  | n + 1 => by
    have hA := scan_agrees Γ n
    intro c xs out fs steps o st c' h
    have hle : mcost (maxBody Γ) n ≤ mcost (maxBody Γ) (n + 1) := by
      rw [mcost_succ, Nat.succ_mul]; omega
    cases xs with
    | nil =>
      simp [scan] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact (Reach.refl Γ _).mono (Nat.zero_le _)
    | cons x rest =>
    -- a token passed by
    have emitCase : emit x (scan Γ n c rest) = some (o, st, c') →
        mstep Γ (sc out (x :: rest) fs steps c) = sc (x :: out) rest fs steps c →
        Reach Γ (mcost (maxBody Γ) (n + 1)) (sc out (x :: rest) fs steps c) (sc (o.reverse ++ out) [] fs (st.reverse ++ steps) c') := by
      intro he hm
      unfold emit at he
      obtain ⟨⟨q1, q2, q3⟩, hq, e⟩ := Option.map_eq_some_iff.mp he
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      have := (Reach.step hm).trans (hA c rest (x :: out) fs steps q1 q2 q3 hq)
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
      exact this.mono (by rw [mcost_succ, Nat.succ_mul]; omega)
    -- a macro: open, substitute, close, rescan
    have macroCase : ∀ (R : List Tok) (stp : Step) (body : List BTok) named va r bb q, stp.id = c →
        mstep Γ (sc out (x :: rest) fs steps c) = ⟨.body (Frame.start ⟨out, R⟩ stp body named va) fs, steps, c + 1⟩ →
        subst Γ n (c + 1) body named va = some r → paste r.1 = some bb →
        scan Γ n r.2.2 (mark c stp.mark bb ++ R) = some q → (q.1, r.2.1 ++ stp :: q.2.1, q.2.2) = (o, st, c') →
        body.length ≤ maxBody Γ →
        Reach Γ (mcost (maxBody Γ) (n + 1)) (sc out (x :: rest) fs steps c) (sc (o.reverse ++ out) [] fs (st.reverse ++ steps) c') := by
      intro R stp body named va r bb q hid' hm hsub hpaste hscan he hlen
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      have s2 := body_agrees Γ n hA body (Frame.start ⟨out, R⟩ stp body named va) fs steps (c + 1) r.1 r.2.1 r.2.2 rfl
        (by simpa [subst, Frame.start] using hsub)
      let F := Frame.start ⟨out, R⟩ stp body named va
      have s3 : mstep Γ ⟨.body { F with bs := [], i := F.i + body.length, acc := F.acc ++ r.1 } fs, r.2.1.reverse ++ steps, r.2.2⟩ =
          sc out (mark c stp.mark bb ++ R) fs (stp :: (r.2.1.reverse ++ steps)) r.2.2 := by
        simp [F, mstep, Frame.start, hpaste, sc, hid']
      have s4 := hA r.2.2 (mark c stp.mark bb ++ R) out fs (stp :: (r.2.1.reverse ++ steps)) q.1 q.2.1 q.2.2 hscan
      have := (((Reach.step hm).trans s2).trans (Reach.step s3)).trans s4
      simp only [List.reverse_append, List.reverse_cons, List.append_assoc, List.singleton_append]
      refine this.mono ?_
      have h1 : body.length * (mcost (maxBody Γ) n + 2) ≤ maxBody Γ * (mcost (maxBody Γ) n + 2) :=
        Nat.mul_le_mul_right _ hlen
      simp only [Nat.mul_add, Nat.succ_mul, mcost_succ] at h1 ⊢
      omega
    unfold scan at h
    by_cases hid : x.s ∈ x.H
    · rw [if_pos hid] at h
      exact emitCase h (by simp [mstep, sc, hid])
    · rw [if_neg hid] at h
      cases hf : Γ.find x.s with
      | none =>
        rw [hf] at h
        exact emitCase h (by simp [mstep, sc, hid, hf])
      | some d =>
        rw [hf] at h
        have hlen := body_le Γ hf
        cases d with
        | obj body =>
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨r, hr, bb, hb, h⟩ := h
          unfold after at h
          obtain ⟨q, hq, e⟩ := Option.map_eq_some_iff.mp h
          exact macroCase rest _ body [] [] r bb q rfl (by simp [mstep, sc, hid, hf, openM, Frame.start]) hr hb hq e
            (by simpa [bodyLen] using hlen)
        | fn arity variadic body =>
          dsimp only at h
          cases rest with
          | nil =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            have hm : mstep Γ (sc out [x] fs steps c) = sc (x :: out) [] fs steps c := by simp [mstep, sc, hid, hf]
            simpa using (Reach.step hm).mono (by rw [mcost_succ]; omega)
          | cons open_ after' =>
            dsimp only at h
            by_cases hop : (open_.s != "(") = true
            · rw [if_pos hop] at h
              exact emitCase h (by simp [mstep, sc, hid, hf, hop])
            · rw [if_neg hop] at h
              simp only [Option.bind_eq_some_iff] at h
              obtain ⟨⟨inner, cl, rest'⟩, hc, ⟨named, va⟩, hbd, r, hr, bb, hb, h⟩ := h
              unfold after at h
              obtain ⟨q, hq, e⟩ := Option.map_eq_some_iff.mp h
              have hop' : open_.s = "(" := by simpa using hop
              exact macroCase rest' _ body named va r bb q rfl
                (by simp [mstep, sc, hid, hf, hop', hc, hbd, openM, Frame.start]) hr hb hq e
                (by simpa [bodyLen] using hlen)

theorem mrun_done (Γ : Env) : ∀ k out steps c, mrun Γ k ⟨.done out, steps, c⟩ = ⟨.done out, steps, c⟩
  | 0, _, _, _ => rfl
  | k + 1, out, steps, c => by
    show mrun Γ k (mstep Γ ⟨.done out, steps, c⟩) = _
    simp only [mstep]; exact mrun_done Γ k out steps c

/-- **Whole runs.** Where `expand` succeeds with fuel `n`, the machine gives the same answer
    after any number of actions from `mcost (maxBody Γ) n + 1` on. -/
theorem mexpand_of_expand (Γ : Env) (n c : Nat) (xs : List Tok) r (h : expand Γ n c xs = some r) (k : Nat)
    (hk : mcost (maxBody Γ) n + 1 ≤ k) : mexpand Γ k c xs = some r := by
  unfold expand at h
  obtain ⟨⟨o, st, c'⟩, hs, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨j, hj, e⟩ := scan_agrees Γ n c xs [] [] [] o st c' hs
  have hd : mstep Γ (sc (o.reverse ++ []) [] [] (st.reverse ++ []) c') = ⟨.done o, st.reverse, c'⟩ := by
    simp [mstep, sc]
  obtain ⟨m, rfl⟩ : ∃ m, k = j + 1 + m := ⟨k - (j + 1), by omega⟩
  unfold mexpand
  have : mrun Γ (j + 1 + m) { mode := .scan ⟨[], xs⟩ [], steps := [], c } = ⟨.done o, st.reverse, c'⟩ := by
    rw [mrun_add, mrun_add]
    have e' : mrun Γ j { mode := .scan ⟨[], xs⟩ [], steps := [], c } = sc (o.reverse ++ []) [] [] (st.reverse ++ []) c' := e
    rw [e']
    show mrun Γ m (mrun Γ 0 (mstep Γ _)) = _
    rw [hd]; exact mrun_done Γ m o _ c'
  rw [this]; simp

end PP
