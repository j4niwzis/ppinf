/-
  The upper bound: every successful run is within an explicit fuel, output length and
  number of steps, given by functions defined by primitive recursion on the rank and on the
  number of top-rank tokens.
-/
import Steps

namespace PP

/-- Below a rank bound `Bρ`: streams with at most `w` tokens of the next rank and `a` below it. -/
def G (Lb : Nat) (Bρ : Nat → Nat) : Nat → Nat → Nat
  | 0, a => Bρ a + 2
  | w + 1, a =>
    let p := Bρ a
    let s := G Lb Bρ w (p + w + 1) + 2
    let nl := Lb * (s + p + w + 2)
    p + 2 * (Lb * s + s + nl + G Lb Bρ w nl) + 10

/-- Streams of rank at most ρ and length at most `a`. -/
def B (Lb : Nat) : Nat → Nat → Nat
  | 0, a => a + 1
  | ρ + 1, a => G Lb (B Lb ρ) a a

def Mono (f : Nat → Nat) : Prop := ∀ a b, a ≤ b → f a ≤ f b

theorem G_mono (Lb : Nat) (Bρ : Nat → Nat) (hB : Mono Bρ) : ∀ w, Mono (G Lb Bρ w) := by
  intro w
  induction w with
  | zero => intro a b h; simp only [G]; have := hB a b h; omega
  | succ w ih =>
    intro a b h
    simp only [G]
    have hp := hB a b h
    have hs := ih _ _ (show Bρ a + w + 1 ≤ Bρ b + w + 1 by omega)
    have hnl : Lb * (G Lb Bρ w (Bρ a + w + 1) + 2 + Bρ a + w + 2) ≤ Lb * (G Lb Bρ w (Bρ b + w + 1) + 2 + Bρ b + w + 2) :=
      Nat.mul_le_mul_left _ (by omega)
    have hg := ih _ _ hnl
    have hls : Lb * (G Lb Bρ w (Bρ a + w + 1) + 2) ≤ Lb * (G Lb Bρ w (Bρ b + w + 1) + 2) := Nat.mul_le_mul_left _ (by omega)
    omega

theorem G_ge (Lb : Nat) (Bρ : Nat → Nat) : ∀ w a, Bρ a + 2 ≤ G Lb Bρ w a := by
  intro w
  induction w with
  | zero => intro a; simp [G]
  | succ w _ => intro a; simp only [G]; omega

theorem B_ge (Lb : Nat) : ∀ ρ a, a + 1 ≤ B Lb ρ a := by
  intro ρ
  induction ρ with
  | zero => intro a; simp [B]
  | succ ρ ih => intro a; simp only [B]; have := G_ge Lb (B Lb ρ) a a; have := ih a; omega

theorem B_mono (Lb : Nat) : ∀ ρ, Mono (B Lb ρ) := by
  intro ρ
  induction ρ with
  | zero => intro a b h; simp [B]; omega
  | succ ρ ih =>
    intro a b h
    simp only [B]
    -- G w a monotone in both
    have h1 : G Lb (B Lb ρ) a a ≤ G Lb (B Lb ρ) a b := G_mono Lb _ ih a a b h
    have h2 : G Lb (B Lb ρ) a b ≤ G Lb (B Lb ρ) b b := by
      have key : ∀ w v x, w ≤ v → G Lb (B Lb ρ) w x ≤ G Lb (B Lb ρ) v x := by
        intro w v x hwv
        induction hwv with
        | refl => exact Nat.le_refl _
        | step _ ih' =>
          rename_i m _
          refine Nat.le_trans ih' ?_
          -- G m x ≤ G (m+1) x
          cases m with
          | zero =>
            simp only [G]
            have := G_ge Lb (B Lb ρ) 0 x
            omega
          | succ m =>
            have gx : G Lb (B Lb ρ) (m + 1) x ≤ G Lb (B Lb ρ) (m + 1) (B Lb ρ x + (m + 1) + 1) :=
              G_mono Lb _ ih (m + 1) _ _ (by have := B_ge Lb ρ x; omega)
            simp only [G] at gx ⊢
            omega
      exact key a b b h
    exact Nat.le_trans h1 h2

/-- What a prefix scan leaves: what was behind, or a stop before it. -/
theorem pscan_stop_shape (Γ : Env) (W : List Tok) : ∀ n c A q, pscan Γ W n c A = some q →
    q.2.2.2 = W ∨ ∃ x R, q.2.2.2 = x :: R ++ W ∧ Stops Γ x R := by
  intro n
  induction n with
  | zero => intro c A q h; simp [pscan] at h
  | succ n ih =>
    intro c A q h
    cases A with
    | nil => simp [pscan] at h; subst h; exact Or.inl rfl
    | cons x R =>
      rcases iter_cases Γ W n c x R q h with ⟨_, q2, h2, rfl⟩ | ⟨_, _, _, q2, _, _, _, _, h2, rfl⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, q2, _, _, _, _, _, _, _, _, h2, rfl⟩ | ⟨hs, rfl⟩
      · have := ih _ _ _ h2; simpa using this
      · have := ih _ _ _ h2; simpa using this
      · have := ih _ _ _ h2; simpa using this
      · exact Or.inr ⟨x, R, rfl, hs⟩

/-- A stop cannot be scanned through on its own: a function-like name at the very end is
    emitted, an unclosed invocation fails. -/
theorem scan_stop (Γ : Env) (x : Tok) (R : List Tok) (hs : Stops Γ x R) (k c : Nat) q
    (h : scan Γ k c (x :: R) = some q) : R = [] ∧ q = ([x], [], c) := by
  obtain ⟨hid, a, v, b, hf, hR⟩ := hs
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by cases k <;> simp_all [scan]⟩
  unfold scan at h
  rcases hR with rfl | ⟨open_, after, rfl, hop, hc⟩
  · simp [hid, hf] at h; exact ⟨rfl, h.symm⟩
  · have hne : (open_.s != "(") = false := by simp [hop]
    simp [hid, hf, hne, hc] at h

/-- From a bound on prefix scans of a stream with nothing behind it, a bound on its scan. -/
theorem full_of_pre (Γ : Env) (S : List Tok) (F : Nat)
    (hpre : ∀ n c q, pscan Γ [] n c S = some q → pscan Γ [] F c S = some q ∧ q.1.length ≤ F ∧ q.2.1.length ≤ F) :
    ∀ n c r, scan Γ n c S = some r → scan Γ (F + 2) c S = some r ∧ r.1.length ≤ F + 1 ∧ r.2.1.length ≤ F := by
  intro n c r h
  obtain ⟨o, st, c', S', q', k, hp, _, hq, rfl⟩ := scan_pscan Γ [] n c S r (by simpa using h)
  have ⟨hF, ho, hst⟩ := hpre n c _ hp
  rcases pscan_stop_shape Γ [] n c S _ hp with hS | ⟨x, R, hS, hs⟩
  · simp only at hS; subst hS
    have hq0 : q' = ([], [], c') := by
      cases k with
      | zero => simp [scan] at hq
      | succ k => simp [scan] at hq; exact hq.symm
    subst hq0
    have := pscan_scan Γ [] F c S o st c' [] hF 2 ([], [], c') (by simp [scan])
    simp at this ⊢
    exact ⟨by simpa using this, by simp at ho; omega, by simpa using hst⟩
  · simp only [List.append_nil] at hS; subst hS
    have ⟨hR, hq0⟩ := scan_stop Γ x R hs k c' q' hq
    subst hR; subst hq0
    have h2 : scan Γ 2 c' [x] = some ([x], [], c') := by
      obtain ⟨hid, a, v, b, hf, _⟩ := hs
      simp [scan, hid, hf]
    have := pscan_scan Γ [] F c S o st c' [x] hF 2 ([x], [], c') h2
    simp at this ⊢
    exact ⟨by simpa using this, by simp at ho; omega, by simpa using hst⟩

end PP
