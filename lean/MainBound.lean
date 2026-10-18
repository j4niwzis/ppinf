/-
  The upper bound, proved: every successful prefix scan of a stream of rank at most ρ and
  length at most a is within fuel, output, steps and remainder B ρ a; so every successful
  run from input tokens is within B R n, R the number of the environment's macros.
-/
import Bound

namespace PP

/-- A prefix scan within `F`: the same result at fuel `F`, and its output, steps and
    remainder at most `F`, the remainder a good stream of rank at most ρ before `W`. -/
def PreB (Γ : Env) (ρ F : Nat) (A W : List Tok) : Prop :=
  ∀ n c q, pscan Γ W n c A = some q → pscan Γ W F c A = some q ∧ q.1.length ≤ F ∧ q.2.1.length ≤ F ∧
    ∃ T, q.2.2.2 = T ++ W ∧ T.length ≤ F ∧ Inv (T ++ W) ∧ ∀ t ∈ T, rank Γ t ≤ ρ

theorem preB_mono {Γ : Env} {ρ F F' : Nat} {A W : List Tok} (h : PreB Γ ρ F A W) (hF : F ≤ F') : PreB Γ ρ F' A W := by
  intro n c q e
  obtain ⟨h1, h2, h3, T, h4, h5, h6, h7⟩ := h n c q e
  exact ⟨pscan_mono Γ W F c A q h1 F' hF, by omega, by omega, T, h4, by omega, h6, h7⟩

/-- Rank 0: nothing expands; the scan passes every token. -/
theorem pre_zero (Γ : Env) : ∀ (A W : List Tok), Inv (A ++ W) → (∀ t ∈ A, rank Γ t ≤ 0) →
    PreB Γ 0 (A.length + 1) A W := by
  intro A W
  induction A with
  | nil =>
    intro i _ n c q e
    cases n with
    | zero => simp [pscan] at e
    | succ n =>
      simp [pscan] at e; subst e
      exact ⟨by simp [pscan], by simp, by simp, [], by simp, by simp, by simpa using i, by simp⟩
  | cons x R ih =>
    intro i hr n c q e
    cases n with
    | zero => simp [pscan] at e
    | succ n =>
      have gx := (good_cons.mp i.1).1
      have h0 : rank Γ x = 0 := Nat.le_zero.mp (hr x (by simp))
      have notelig : ∀ d, Γ.find x.s = some d → x.s ∈ x.H := fun d hf => rank_zero_hidden Γ x gx h0 hf
      rcases iter_cases Γ W n c x R q e with ⟨hp, q2, h2, rfl⟩ | ⟨_, _, _, _, hid, hf, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, _, hid, hf, _⟩ | ⟨⟨hid, _, _, _, hf, _⟩, _⟩
      · obtain ⟨h1, h2', h3, T, h4, h5, h6, h7⟩ := ih (inv_tail i) (fun t ht => hr t (List.mem_cons_of_mem _ ht)) n c q2 h2
        refine ⟨?_, by simp; omega, by simp; omega, T, h4, by simp; omega, h6, h7⟩
        have := rebuild_pass Γ W (R.length + 1) c x R hp q2 h1
        simpa using this
      · exact absurd (notelig _ hf) hid
      · exact absurd (notelig _ hf) hid
      · exact absurd (notelig _ hf) hid

/-- The hypothesis at `w`: streams of a lower part of rank ≤ ρ and at most `w` more of rank ≤ ρ+1. -/
def GLAt (Γ : Env) (ρ w : Nat) : Prop :=
  ∀ a A1 A2 W, Inv (A1 ++ A2 ++ W) → (∀ t ∈ A1, rank Γ t ≤ ρ) → (∀ t ∈ A2, rank Γ t ≤ ρ + 1) →
    A1.length ≤ a → A2.length ≤ w → PreB Γ (ρ + 1) (G (maxBody Γ) (B (maxBody Γ) ρ) w a) (A1 ++ A2) W

/-- An argument's expansion, bounded from the hypothesis at `w`. -/
theorem arg_bound (Γ : Env) (ρ w : Nat) (IH : GLAt Γ ρ w) (a1 a2 : List Tok) (i : Inv (a1 ++ a2))
    (r1 : ∀ t ∈ a1, rank Γ t ≤ ρ) (r2 : ∀ t ∈ a2, rank Γ t ≤ ρ + 1) (a : Nat) (h1 : a1.length ≤ a) (h2 : a2.length ≤ w) :
    ∀ n c q, expand Γ n c (a1 ++ a2) = some q →
      q.1.length ≤ G (maxBody Γ) (B (maxBody Γ) ρ) w a + 1 ∧ q.2.1.length ≤ G (maxBody Γ) (B (maxBody Γ) ρ) w a ∧
      ∀ f, G (maxBody Γ) (B (maxBody Γ) ρ) w a + 2 ≤ f → expand Γ f c (a1 ++ a2) = some q := by
  intro n c q e
  have pre := IH a a1 a2 [] (by simpa using i) r1 r2 h1 h2
  have full := full_of_pre Γ (a1 ++ a2) _ (fun n c q h => by
    obtain ⟨x1, x2, x3, _⟩ := pre n c q h; exact ⟨x1, x2, x3⟩)
  unfold expand at e
  cases hs : scan Γ n c (a1 ++ a2) with
  | none => simp [hs] at e
  | some r =>
    rw [hs] at e
    simp only [Option.map_some, Option.some.injEq] at e
    subst e
    obtain ⟨hF, ho, hst⟩ := full n c r hs
    refine ⟨by simp [finalize]; exact ho, hst, fun f hf => ?_⟩
    unfold expand
    rw [scanMono Γ _ c _ r hF f hf]
    rfl

theorem rank_mark (Γ : Env) (e : Nat) (K : List Name) (b : List Tok) : ∀ t ∈ mark e K b, rank Γ t = rk Γ K := by
  intro t ht
  simp only [mark, List.mem_map] at ht
  obtain ⟨x, _, rfl⟩ := ht
  rfl

theorem maxBody_pos (Γ : Env) : 1 ≤ maxBody Γ := by unfold maxBody; omega

/-- A function-like macro's step in a round, and everything after it: within `K + 4`. -/
theorem fn_round (Γ : Env) (ρ w : Nat) (IH : GLAt Γ ρ w) (W : List Tok) (p k c : Nat) (x open_ cl : Tok)
    (i1 i2 rest : List Tok) (hid : x.s ∉ x.H) {arity : Nat} {variadic : Bool} {body : List BTok}
    (hf : Γ.find x.s = some (.fn arity variadic body)) (hop : open_.s = "(")
    (hc : closeAt 0 ((i1 ++ i2) ++ cl :: rest) [] = some (i1 ++ i2, cl, rest)) named va r b q2
    (hbd : bind arity variadic (i1 ++ i2) = some (named, va)) (hr : subst Γ k (c + 1) body named va = some r)
    (hb : paste r.1 = some b) (hp : pscan Γ W k r.2.2 (mark c (x.s :: inter x.H cl.H) b ++ rest) = some q2)
    (inv : Inv (x :: open_ :: ((i1 ++ i2) ++ cl :: rest) ++ W))
    (ri1 : ∀ t ∈ i1, rank Γ t ≤ ρ) (ri2 : ∀ t ∈ i2, rank Γ t ≤ ρ + 1) (rcl : rank Γ cl ≤ ρ + 1)
    (rrest : ∀ t ∈ rest, rank Γ t ≤ ρ + 1) (hi1 : i1.length ≤ p) (hi2 : i2.length ≤ w) (hrest : rest.length ≤ w) :
    let Lb := maxBody Γ
    let g := G Lb (B Lb ρ) w
    let s := g (p + w + 1) + 2
    let nl := Lb * (s + p + w + 2)
    let K := Lb * s + s + nl + g nl
    let q : PRes := (q2.1, r.2.1 ++ fnStep x cl c :: q2.2.1, q2.2.2)
    pscan Γ W (K + 4) c (x :: open_ :: ((i1 ++ i2) ++ cl :: rest)) = some q ∧ q.1.length ≤ K + 4 ∧ q.2.1.length ≤ K + 4 ∧
      ∃ T, q.2.2.2 = T ++ W ∧ T.length ≤ K + 4 ∧ Inv (T ++ W) ∧ ∀ t ∈ T, rank Γ t ≤ ρ + 1 := by
  intro Lb g s nl K q
  have hs : s = g (p + w + 1) + 2 := rfl
  have hnl : nl = Lb * (s + p + w + 2) := rfl
  have hK : K = Lb * s + s + nl + g nl := rfl
  have hLb := maxBody_pos Γ
  have ⟨invN, rkN, invIn, _⟩ := fn_next Γ (open_ := open_) (cl := cl) (inner := i1 ++ i2) (rest := rest ++ W) (by simpa using inv) hid hf c b
  -- the arguments
  have ⟨hn, hv⟩ := bind_sub _ _ _ _ _ hbd
  have argOk : ∀ a, (a ∈ named ∨ a = va) → a.length ≤ p + w ∧ ∀ c0 q, expand Γ k c0 a = some q →
      q.1.length ≤ s + p + w ∧ q.2.1.length ≤ s ∧ expand Γ (s + g nl) c0 a = some q := by
    intro a ha
    have sub : a = [] ∨ a.Sublist (i1 ++ i2) := by
      rcases ha with ha | rfl
      · exact hn a ha
      · exact Or.inr hv
    obtain ⟨a1, a2, rfl, h1, h2⟩ : ∃ a1 a2, a = a1 ++ a2 ∧ a1.Sublist i1 ∧ a2.Sublist i2 := by
      rcases sub with rfl | sl
      · exact ⟨[], [], rfl, List.nil_sublist _, List.nil_sublist _⟩
      · exact List.sublist_append_iff.mp sl
    have ia : Inv (a1 ++ a2) := inv_sublist (List.Sublist.append h1 h2) invIn
    have l1 := h1.length_le; have l2 := h2.length_le
    refine ⟨by simp; omega, ?_⟩
    intro c0 q e
    have ⟨b1, b2, b3⟩ := arg_bound Γ ρ w IH a1 a2 ia (fun t ht => ri1 t (h1.subset ht)) (fun t ht => ri2 t (h2.subset ht))
      (p + w + 1) (by omega) (by omega) k c0 q e
    have b1' : q.1.length ≤ g (p + w + 1) + 1 := b1
    have b2' : q.2.1.length ≤ g (p + w + 1) := b2
    exact ⟨by omega, by omega, b3 _ (by show g (p + w + 1) + 2 ≤ s + g nl; omega)⟩
  have ⟨lr, sr, er⟩ := subst_bound Γ k body named va (s + p + w) s (s + g nl) (by omega)
    (fun a ha => by have := (argOk a ha).1; omega) (fun a ha => (argOk a ha).2) body 0 (c + 1) r.1 r.2.1 r.2.2
    (by unfold subst at hr; exact hr)
  have hbody : body.length ≤ Lb := by have := body_le Γ hf; simpa [bodyLen] using this
  have hblen : b.length ≤ nl := by
    have := paste_len _ _ hb
    have : body.length * (s + p + w + 1) ≤ Lb * (s + p + w + 2) :=
      Nat.mul_le_mul hbody (by omega)
    omega
  -- what follows
  have pre := IH nl (mark c (x.s :: inter x.H cl.H) b) rest W (by simpa using invN)
    (fun t ht => by rw [rank_mark Γ _ _ _ t ht]; omega) rrest (by rw [mark_len]; exact hblen) hrest
  obtain ⟨c1, c2, c3, T, c4, c5, c6, c7⟩ := pre k r.2.2 q2 hp
  have c1' : pscan Γ W (g nl) r.2.2 (mark c (x.s :: inter x.H cl.H) b ++ rest) = some q2 := c1
  have c2' : q2.1.length ≤ g nl := c2
  have c3' : q2.2.1.length ≤ g nl := c3
  have c5' : T.length ≤ g nl := c5
  have hsteps : r.2.1.length ≤ Lb * s := by
    have : body.length * s ≤ Lb * s := Nat.mul_le_mul_right _ hbody
    omega
  refine ⟨?_, by show q2.1.length ≤ K + 4; omega,
    by show (r.2.1 ++ fnStep x cl c :: q2.2.1).length ≤ K + 4; simp; omega, T, c4, by omega, c6, c7⟩
  have ers : subst Γ (s + g nl) (c + 1) body named va = some r := by unfold subst; exact er
  have cont := pscan_mono Γ W _ _ _ q2 c1' (s + g nl) (by omega)
  have := rebuild_fn Γ W (s + g nl) c x open_ cl (i1 ++ i2) rest hid hf hop hc named va r b q2 hbd ers hb cont
  have hfu : s + g nl + 1 ≤ K + 4 := by omega
  exact pscan_mono Γ W _ _ _ _ this _ hfu

end PP
