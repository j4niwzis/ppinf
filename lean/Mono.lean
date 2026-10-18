/-
  More fuel never changes a result: once a scan succeeds, it succeeds the same with any
  larger fuel.
-/
import Origins

namespace PP

def ScanMono (Γ : Env) (n : Nat) : Prop :=
  ∀ c xs r, scan Γ n c xs = some r → ∀ m, n ≤ m → scan Γ m c xs = some r
def SubstMono (Γ : Env) (n : Nat) : Prop :=
  ∀ whole bs i c named va r, substFrom Γ n whole bs i c named va = some r →
    ∀ m, n ≤ m → substFrom Γ m whole bs i c named va = some r

theorem expand_mono {Γ : Env} {n : Nat} (h : ScanMono Γ n) c xs r (e : expand Γ n c xs = some r) m (hm : n ≤ m) :
    expand Γ m c xs = some r := by
  unfold expand at e ⊢
  cases hs : scan Γ n c xs with
  | none => simp [hs] at e
  | some q => rw [h c xs q hs m hm]; rw [hs] at e; exact e

theorem substMono_of_scan {Γ : Env} {n : Nat} (h : ScanMono Γ n) : SubstMono Γ n := by
  intro whole bs
  induction bs with
  | nil => intro i c named va r e m _; simpa [substFrom] using e
  | cons b bs ih =>
    intro i c named va r e m hm
    simp only [substFrom] at e ⊢
    obtain ⟨p, hp, e⟩ := bind_some e
    have one_mono : ∀ a, one Γ n whole a i c = some p → one Γ m whole a i c = some p := by
      intro a hp
      unfold one at hp ⊢
      by_cases hadj : adjacentPaste whole i = true
      · simp only [hadj, ite_true] at hp ⊢; exact hp
      · simp only [hadj] at hp ⊢
        cases he : expand Γ n c a with
        | none => simp [he] at hp
        | some q => rw [expand_mono h _ _ _ he m hm]; rw [he] at hp; exact hp
    have hp' : piece Γ m whole b i c named va = some p := by
      cases b with
      | tok x => simpa [piece] using hp
      | paste => simpa [piece] using hp
      | param j => simp only [piece] at hp ⊢; exact one_mono _ hp
      | va => simp only [piece] at hp ⊢; exact one_mono _ hp
    rw [hp']
    simp only [Option.bind_some]
    cases hq : substFrom Γ n whole bs (i + 1) p.2.2 named va with
    | none => simp [hq] at e
    | some q => rw [ih _ _ _ _ _ hq m hm]; rw [hq] at e; exact e

theorem scanMono (Γ : Env) : ∀ n, ScanMono Γ n := by
  intro n
  induction n with
  | zero => intro c xs r e; simp [scan] at e
  | succ n ih =>
    have sub := substMono_of_scan ih
    have subst_mono : ∀ c body named va p, subst Γ n c body named va = some p → ∀ m, n ≤ m →
        subst Γ m c body named va = some p := fun c body named va p e m hm => by
      unfold subst at e ⊢; exact sub _ _ _ _ _ _ _ e m hm
    intro c xs r e m hm
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hm' : n ≤ m := by omega
    cases xs with
    | nil => simpa [scan] using e
    | cons x rest =>
      unfold scan at e ⊢
      have emit_mono : ∀ ys, emit x (scan Γ n c ys) = some r → emit x (scan Γ m c ys) = some r := by
        intro ys e'
        cases hs : scan Γ n c ys with
        | none => simp [hs, emit] at e'
        | some q => rw [ih c ys q hs m hm']; rw [hs] at e'; exact e'
      by_cases hid : x.s ∈ x.H
      · simp only [hid, ite_true] at e ⊢; exact emit_mono rest e
      · simp only [hid, ite_false] at e ⊢
        cases hf : Γ.find x.s with
        | none => rw [hf] at e; simp only at e ⊢; exact emit_mono rest e
        | some d =>
          rw [hf] at e
          cases d with
          | obj body =>
            simp only at e ⊢
            obtain ⟨p, hp, e⟩ := bind_some e
            rw [subst_mono _ _ _ _ _ hp m hm']
            simp only [Option.bind_some]
            obtain ⟨b, hb, e⟩ := bind_some e
            rw [hb]; simp only [Option.bind_some]
            unfold after at e ⊢
            cases hs : scan Γ n p.2.2 (mark c (x.s :: x.H) b ++ rest) with
            | none => simp [hs] at e
            | some q => rw [ih _ _ q hs m hm']; rw [hs] at e; exact e
          | fn arity variadic body =>
            simp only at e ⊢
            cases rest with
            | nil => exact e
            | cons open_ after' =>
              simp only at e ⊢
              by_cases hne : (open_.s != "(") = true
              · simp only [hne, ite_true] at e ⊢; exact emit_mono _ e
              · simp only [hne] at e ⊢
                obtain ⟨a, ha, e⟩ := bind_some e
                rw [ha]; simp only [Option.bind_some]
                obtain ⟨bd, hbd, e⟩ := bind_some e
                rw [hbd]; simp only [Option.bind_some]
                obtain ⟨p, hp, e⟩ := bind_some e
                rw [subst_mono _ _ _ _ _ hp m hm']
                simp only [Option.bind_some]
                obtain ⟨b, hb, e⟩ := bind_some e
                rw [hb]; simp only [Option.bind_some]
                unfold after at e ⊢
                cases hs : scan Γ n p.2.2 (mark c (x.s :: inter x.H a.2.1.H) b ++ a.2.2) with
                | none => simp [hs] at e
                | some q => rw [ih _ _ q hs m hm']; rw [hs] at e; exact e

end PP

namespace PP
theorem subst_mono (Γ : Env) {n c body named va p} (e : subst Γ n c body named va = some p) (m : Nat) (hm : n ≤ m) :
    subst Γ m c body named va = some p := by
  unfold subst at e ⊢; exact substMono_of_scan (scanMono Γ n) _ _ _ _ _ _ _ e m hm
end PP
