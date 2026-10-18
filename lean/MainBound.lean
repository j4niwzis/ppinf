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

/-- One result `q` of a prefix scan, within `F`. -/
def PreBAt (Γ : Env) (ρ F : Nat) (W A : List Tok) (c : Nat) (q : PRes) : Prop :=
  pscan Γ W F c A = some q ∧ q.1.length ≤ F ∧ q.2.1.length ≤ F ∧
    ∃ T, q.2.2.2 = T ++ W ∧ T.length ≤ F ∧ Inv (T ++ W) ∧ ∀ t ∈ T, rank Γ t ≤ ρ

theorem preBAt_mono {Γ : Env} {ρ F F' : Nat} {W A : List Tok} {c : Nat} {q : PRes} (h : PreBAt Γ ρ F W A c q) (hF : F ≤ F') :
    PreBAt Γ ρ F' W A c q := by
  obtain ⟨h1, h2, h3, T, h4, h5, h6, h7⟩ := h
  exact ⟨pscan_mono Γ W F c A q h1 F' hF, by omega, by omega, T, h4, by omega, h6, h7⟩

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

/-- The round's bound, as `G` spells it. -/
def Kf (Γ : Env) (ρ w p : Nat) : Nat :=
  let Lb := maxBody Γ
  let g := G Lb (B Lb ρ) w
  let s := g (p + w + 1) + 2
  let nl := Lb * (s + p + w + 2)
  Lb * s + s + nl + g nl

theorem G_succ (Γ : Env) (ρ w a : Nat) :
    G (maxBody Γ) (B (maxBody Γ) ρ) (w + 1) a = B (maxBody Γ) ρ a + 2 * Kf Γ ρ w (B (maxBody Γ) ρ a) + 10 := rfl

/-- What `Kf` holds: the next steps' bounds. -/
theorem Kf_facts (Γ : Env) (ρ w p : Nat) :
    G (maxBody Γ) (B (maxBody Γ) ρ) w 0 + 2 ≤ Kf Γ ρ w p ∧
    G (maxBody Γ) (B (maxBody Γ) ρ) w (maxBody Γ) + 2 + maxBody Γ ≤ Kf Γ ρ w p ∧ p + w + 2 ≤ Kf Γ ρ w p := by
  have hLb := maxBody_pos Γ
  have mono := G_mono (maxBody Γ) _ (B_mono (maxBody Γ) ρ) w
  unfold Kf
  simp only
  generalize G (maxBody Γ) (B (maxBody Γ) ρ) w = g at mono ⊢
  generalize maxBody Γ = Lb at hLb ⊢
  have h1 : g 0 ≤ g (p + w + 1) := mono _ _ (by omega)
  have hnl : Lb ≤ Lb * (g (p + w + 1) + 2 + p + w + 2) := Nat.le_mul_of_pos_right _ (by omega)
  have hnl2 : g (p + w + 1) + 2 + p + w + 2 ≤ Lb * (g (p + w + 1) + 2 + p + w + 2) := Nat.le_mul_of_pos_left _ hLb
  have h2 : g Lb ≤ g (Lb * (g (p + w + 1) + 2 + p + w + 2)) := mono _ _ hnl
  have h3 : g 0 ≤ g (Lb * (g (p + w + 1) + 2 + p + w + 2)) := mono _ _ (by omega)
  refine ⟨by omega, by omega, by omega⟩

/-- `fn_round`, in `Kf`'s terms. -/
theorem fn_round' (Γ : Env) (ρ w : Nat) (IH : GLAt Γ ρ w) (W : List Tok) (p k c : Nat) (x open_ cl : Tok)
    (i1 i2 rest : List Tok) (hid : x.s ∉ x.H) {arity : Nat} {variadic : Bool} {body : List BTok}
    (hf : Γ.find x.s = some (.fn arity variadic body)) (hop : open_.s = "(")
    (hc : closeAt 0 ((i1 ++ i2) ++ cl :: rest) [] = some (i1 ++ i2, cl, rest)) named va r b q2
    (hbd : bind arity variadic (i1 ++ i2) = some (named, va)) (hr : subst Γ k (c + 1) body named va = some r)
    (hb : paste r.1 = some b) (hp : pscan Γ W k r.2.2 (mark c (x.s :: inter x.H cl.H) b ++ rest) = some q2)
    (inv : Inv (x :: open_ :: ((i1 ++ i2) ++ cl :: rest) ++ W))
    (ri1 : ∀ t ∈ i1, rank Γ t ≤ ρ) (ri2 : ∀ t ∈ i2, rank Γ t ≤ ρ + 1) (rcl : rank Γ cl ≤ ρ + 1)
    (rrest : ∀ t ∈ rest, rank Γ t ≤ ρ + 1) (hi1 : i1.length ≤ p) (hi2 : i2.length ≤ w) (hrest : rest.length ≤ w) :
    PreBAt Γ (ρ + 1) (Kf Γ ρ w p + 4) W (x :: open_ :: ((i1 ++ i2) ++ cl :: rest)) c
      (q2.1, r.2.1 ++ fnStep x cl c :: q2.2.1, q2.2.2) :=
  fn_round Γ ρ w IH W p k c x open_ cl i1 i2 rest hid hf hop hc named va r b q2 hbd hr hb hp inv ri1 ri2 rcl rrest hi1 hi2 hrest

theorem preBAt_nil (Γ : Env) (ρ F : Nat) (hF : 1 ≤ F) (W : List Tok) (c : Nat) (i : Inv W) :
    PreBAt Γ ρ F W [] c ([], [], c, W) := by
  obtain ⟨F, rfl⟩ : ∃ G, F = G + 1 := ⟨F - 1, by omega⟩
  exact ⟨by simp [pscan], by simp, by simp, [], by simp, by simp, by simpa using i, by simp⟩

/-- A round with nothing below the top rank: at most `w + 1` tokens. -/
theorem lower_empty (Γ : Env) (ρ w : Nat) (IH : GLAt Γ ρ w) (p : Nat) :
    ∀ A2 W n c q, Inv (A2 ++ W) → (∀ t ∈ A2, rank Γ t ≤ ρ + 1) → A2.length ≤ w + 1 →
      pscan Γ W n c A2 = some q → PreBAt Γ (ρ + 1) (Kf Γ ρ w p + 5) W A2 c q := by
  intro A2 W n c q i hr hl e
  have ⟨kf1, kf2, kf3⟩ := Kf_facts Γ ρ w p
  have hLb := maxBody_pos Γ
  cases A2 with
  | nil =>
    cases n with
    | zero => simp [pscan] at e
    | succ n => simp [pscan] at e; subst e; exact preBAt_nil Γ _ _ (by omega) W c (by simpa using i)
  | cons y R =>
    cases n with
    | zero => simp [pscan] at e
    | succ k =>
      have hry : rank Γ y ≤ ρ + 1 := hr y (by simp)
      have hrR : ∀ t ∈ R, rank Γ t ≤ ρ + 1 := fun t ht => hr t (List.mem_cons_of_mem _ ht)
      rcases iter_cases Γ W k c y R q e with ⟨hp, q2, h2, rfl⟩ | ⟨body, r, b, q2, hid, hf, hrs, hb, h2, rfl⟩ |
          ⟨arity, variadic, body, open_, inner, cl, rest, named, va, r, b, q2, hid, hf, hR, hop, hc, hbd, hrs, hb, h2, rfl⟩ |
          ⟨hs, rfl⟩
      · -- passed by
        have pre := IH 0 [] R W (by simpa using inv_tail (x := y) (by simpa using i)) (by simp) hrR (by simp)
          (by simp at hl; omega)
        obtain ⟨c1, c2, c3, T, c4, c5, c6, c7⟩ := pre k c q2 (by simpa using h2)
        refine ⟨?_, by simp; omega, by simp; omega, T, c4, by omega, c6, c7⟩
        have := rebuild_pass Γ W _ c y R hp q2 (by simpa using c1)
        exact pscan_mono Γ W _ _ _ _ this _ (by omega)
      · -- an object macro
        have ⟨invN, rkN⟩ := obj_next Γ (rest := R ++ W) (by simpa using i) hid hf c b
        have hbody : body.length ≤ maxBody Γ := by have := body_le Γ hf; simpa [bodyLen] using this
        have g2 := G_ge (maxBody Γ) (B (maxBody Γ) ρ) w (maxBody Γ)
        have ⟨lr, sr, er⟩ := subst_bound Γ k body [] [] 0 0 (G (maxBody Γ) (B (maxBody Γ) ρ) w (maxBody Γ)) (by omega)
          (fun a ha => by simp at ha; subst ha; simp)
          (fun a ha c0 q he => by
            simp at ha; subst ha
            have := expand_nil_eq Γ k c0 q he; subst this
            exact ⟨by simp, by simp, expand_nil Γ _ c0 (by omega)⟩)
          body 0 (c + 1) r.1 r.2.1 r.2.2 (by unfold subst at hrs; exact hrs)
        have hblen : b.length ≤ maxBody Γ := by have := paste_len _ _ hb; simp at lr; omega
        have pre := IH (maxBody Γ) (mark c (y.s :: y.H) b) R W (by simpa using invN)
          (fun t ht => by rw [rank_mark Γ _ _ _ t ht]; omega) hrR (by rw [mark_len]; exact hblen) (by simp at hl; omega)
        obtain ⟨c1, c2, c3, T, c4, c5, c6, c7⟩ := pre k r.2.2 q2 h2
        have sr0 : r.2.1.length = 0 := by rw [Nat.mul_zero] at sr; omega
        refine ⟨?_, by simp; omega, by simp; omega, T, c4, by omega, c6, c7⟩
        have := rebuild_obj Γ W _ c y R hid hf r b q2 (by unfold subst; exact er) hb c1
        exact pscan_mono Γ W _ _ _ _ this _ (by omega)
      · -- a function-like macro
        subst hR
        have hlen : inner.length + rest.length + 2 ≤ w := by simp at hl; omega
        have hc' : closeAt 0 (([] ++ inner) ++ cl :: rest) [] = some ([] ++ inner, cl, rest) := by simpa using hc
        have hbd' : bind arity variadic ([] ++ inner) = some (named, va) := by simpa using hbd
        have h := fn_round' Γ ρ w IH W p k c y open_ cl [] inner rest hid hf hop hc' named va r b q2 hbd' hrs hb h2
          (by simpa using i) (by simp) (fun t ht => hr t (by simp [ht])) (hr cl (by simp))
          (fun t ht => hr t (by simp [ht])) (by simp) (by omega) (by omega)
        have := preBAt_mono h (show Kf Γ ρ w p + 4 ≤ Kf Γ ρ w p + 5 by omega)
        simpa using this
      · -- a stop
        refine ⟨?_, by simp, by simp, y :: R, by simp, by simp at hl ⊢; omega, i, hr⟩
        have := rebuild_stop Γ W 0 c y R hs
        exact pscan_mono Γ W _ _ _ _ this _ (by omega)

/-- A round after the lower part stopped: its stop, then at most `w + 1` top tokens. -/
theorem stop_round (Γ : Env) (ρ w : Nat) (IH : GLAt Γ ρ w) (p : Nat) :
    ∀ x R A2 W n c q, Stops Γ x R → Inv (x :: R ++ A2 ++ W) → (∀ t ∈ x :: R, rank Γ t ≤ ρ) → (x :: R).length ≤ p →
      (∀ t ∈ A2, rank Γ t ≤ ρ + 1) → A2.length ≤ w + 1 →
      pscan Γ W n c (x :: R ++ A2) = some q → PreBAt Γ (ρ + 1) (Kf Γ ρ w p + 6) W (x :: R ++ A2) c q := by
  intro x R A2 W n c q hs i hxR hlxR hA2 hl e
  have ⟨kf1, kf2, kf3⟩ := Kf_facts Γ ρ w p
  obtain ⟨hid', ar, vr, bd, hf', hR⟩ := hs
  cases n with
  | zero => simp [pscan] at e
  | succ k =>
    rcases iter_cases Γ W k c x (R ++ A2) q (by simpa using e) with ⟨hp, q2, h2, rfl⟩ | ⟨body, _, _, _, _, hf, _⟩ |
        ⟨arity, variadic, body, open_, inner, cl, rest, named, va, r, b, q2, hid, hf, hRA, hop, hc, hbd, hrs, hb, h2, rfl⟩ |
        ⟨hs2, rfl⟩
    · -- x passed by: then R is empty and A2 begins with something other than `(`
      rcases hp with hh | ⟨_, hn⟩ | ⟨_, a', v', b', open_, after, hf2, hRA, hne⟩
      · exact absurd hh hid'
      · rw [hf'] at hn; simp at hn
      · rcases hR with rfl | ⟨open', after0, rfl, hop', _⟩
        · simp at hRA
          have := lower_empty Γ ρ w IH p A2 W k c q2 (inv_tail (by simpa using i)) hA2 hl (by simpa using h2)
          obtain ⟨c1, c2, c3, T, c4, c5, c6, c7⟩ := this
          refine ⟨?_, by simp; omega, by simp; omega, T, c4, by omega, c6, c7⟩
          have := rebuild_pass Γ W _ c x A2 (Or.inr (Or.inr ⟨hid', a', v', b', open_, after, hf2, hRA, hne⟩)) q2 c1
          simpa using this
        · simp at hRA; obtain ⟨rfl, _⟩ := hRA; simp [hop'] at hne
    · rw [hf'] at hf; simp at hf
    · rw [hf'] at hf; simp only [Option.some.injEq, Def.fn.injEq] at hf
      obtain ⟨rfl, rfl, rfl⟩ := hf
      rcases hR with rfl | ⟨open', after0, rfl, hop', hc0⟩
      · -- R empty: the invocation is all in A2
        simp at hRA
        subst hRA
        have hlen : inner.length + rest.length + 1 ≤ w := by simp at hl; omega
        have hc' : closeAt 0 (([] ++ inner) ++ cl :: rest) [] = some ([] ++ inner, cl, rest) := by simpa using hc
        have hbd' : bind ar vr ([] ++ inner) = some (named, va) := by simpa using hbd
        have h := fn_round' Γ ρ w IH W p k c x open_ cl [] inner rest hid hf' hop hc' named va r b q2 hbd' hrs hb h2
          (by simpa using i) (by simp) (fun t ht => hA2 t (by simp [ht])) (hA2 cl (by simp))
          (fun t ht => hA2 t (by simp [ht])) (by simp) (by omega) (by omega)
        have := preBAt_mono h (show Kf Γ ρ w p + 4 ≤ Kf Γ ρ w p + 6 by omega)
        simpa using this
      · -- R opened the invocation; its closing parenthesis is in A2
        simp only [List.cons_append, List.cons.injEq] at hRA
        obtain ⟨rfl, hRA⟩ := hRA
        rw [← hRA] at hc
        obtain ⟨pre, hin, hA⟩ := closeAt_past after0 A2 0 [] inner cl rest hc0 hc
        simp only [List.reverse_nil, List.nil_append] at hin
        subst hin; subst hA
        have hlen : pre.length + rest.length + 1 ≤ w + 1 := by simp at hl; omega
        have hl0 : after0.length ≤ p := by simp at hlxR; omega
        have hc' : closeAt 0 ((after0 ++ pre) ++ cl :: rest) [] = some (after0 ++ pre, cl, rest) := by
          rw [show (after0 ++ pre) ++ cl :: rest = after0 ++ (pre ++ cl :: rest) by simp]; exact hc
        have h := fn_round' Γ ρ w IH W p k c x open' cl after0 pre rest hid hf' hop hc' named va r b q2 hbd hrs hb h2
          (by simpa using i) (fun t ht => hxR t (by simp [ht])) (fun t ht => hA2 t (by simp [ht])) (hA2 cl (by simp))
          (fun t ht => hA2 t (by simp [ht])) hl0 (by omega) (by omega)
        have := preBAt_mono h (show Kf Γ ρ w p + 4 ≤ Kf Γ ρ w p + 6 by omega)
        simpa using this
    · -- a stop of the whole
      refine ⟨?_, by simp, by simp, x :: (R ++ A2), by simp, by simp at hlxR hl ⊢; omega, by simpa using i, ?_⟩
      · have := rebuild_stop Γ W 0 c x (R ++ A2) hs2
        have := pscan_mono Γ W _ _ _ _ this (Kf Γ ρ w p + 6) (by omega)
        simpa using this
      · intro t ht
        simp only [List.mem_cons, List.mem_append] at ht
        rcases ht with rfl | ht | ht
        · have := hxR t (by simp); omega
        · have := hxR t (by simp [ht]); omega
        · exact hA2 t ht

end PP
