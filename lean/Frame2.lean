/-
  A sharper frame lemma: a scan composes with what follows unless its last output token is a
  function-like name left waiting for its arguments.
-/
import Frame

namespace PP

def LastOK (Γ : Env) (o : List Tok) : Prop :=
  ∀ x, o.getLast? = some x → x.s ∈ x.H ∨ ∀ a v b, Γ.find x.s ≠ some (.fn a v b)

theorem scan_frame2 (Γ : Env) (X W : List Tok) (n c : Nat) (r : List Tok × List Step × Nat)
    (h : scan Γ n c X = some r) (hl : LastOK Γ r.1) (m : Nat) (q : List Tok × List Step × Nat)
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
    obtain ⟨hid, a, v, b, hf, _⟩ := hs
    rcases hl x (by simp) with h1 | h1
    · exact absurd h1 hid
    · exact absurd hf (h1 a v b)

end PP
