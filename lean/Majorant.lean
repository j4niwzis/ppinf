/-
  Theorem 9: a primitive recursive majorant of the fuel bound `B`. `G` calls itself at an
  argument computed from its own value, which no primitive recursion scheme takes as it is;
  but `G w x ≤ F^[t w] x` for `x ≥ w`, with `F x = (4·Lb + 14)·(Bρ x + x + 1)` and
  `t (w + 1) = 2·t w + 3` -- an iterate, a primitive recursive number of times.
-/
import Bound
import Phi

namespace PP

def tcount : Nat → Nat
  | 0 => 1
  | w + 1 => 2 * tcount w + 3

def Fm (Lb : Nat) (Bρ : Nat → Nat) (x : Nat) : Nat := (4 * Lb + 14) * (Bρ x + x + 1)

theorem Fm_mono (Lb : Nat) {Bρ : Nat → Nat} (hB : Mono Bρ) : ∀ a b, a ≤ b → Fm Lb Bρ a ≤ Fm Lb Bρ b := by
  intro a b h; unfold Fm; exact Nat.mul_le_mul_left _ (by have := hB a b h; omega)

theorem Fm_infl (Lb : Nat) (Bρ : Nat → Nat) : ∀ a, a ≤ Fm Lb Bρ a := by
  intro a; unfold Fm
  have : 1 * (Bρ a + a + 1) ≤ (4 * Lb + 14) * (Bρ a + a + 1) := Nat.mul_le_mul_right _ (by omega)
  omega

theorem iter_succ' (f : Nat → Nat) (t x : Nat) : iter f t (f x) = iter f (t + 1) x := by
  have := iter_add f 1 t x; simp only [iter] at this; rw [this, Nat.add_comm]

theorem G_le_iter (Lb : Nat) (hL : 1 ≤ Lb) (Bρ : Nat → Nat) (hB : Mono Bρ) :
    ∀ w x, w ≤ x → G Lb Bρ w x ≤ iter (Fm Lb Bρ) (tcount w) x := by
  have mono := Fm_mono Lb hB
  have infl := Fm_infl Lb Bρ
  intro w
  induction w with
  | zero =>
    intro x _
    show Bρ x + 2 ≤ Fm Lb Bρ x
    unfold Fm
    have : 14 * (Bρ x + x + 1) ≤ (4 * Lb + 14) * (Bρ x + x + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  | succ w ih =>
    intro x hx
    let F := Fm Lb Bρ
    let t := tcount w
    let p := Bρ x
    let S := iter F (t + 1) x
    let Y := iter F (2 * t + 2) x
    have hFx : p + w + 1 ≤ F x := by
      show Bρ x + w + 1 ≤ (4 * Lb + 14) * (Bρ x + x + 1)
      have : 1 * (Bρ x + x + 1) ≤ (4 * Lb + 14) * (Bρ x + x + 1) := Nat.mul_le_mul_right _ (by omega)
      omega
    -- the first call
    have h1 : G Lb Bρ w (p + w + 1) ≤ S := by
      calc G Lb Bρ w (p + w + 1) ≤ iter F t (p + w + 1) := ih _ (by omega)
        _ ≤ iter F t (F x) := iter_mono mono t _ _ hFx
        _ = S := iter_succ' F t x
    have hxS : x ≤ S := iter_infl infl _ x
    have hpS : p ≤ S := by
      have : F x ≤ S := by
        show F x ≤ F (iter F t x); exact mono _ _ (iter_infl infl t x)
      omega
    -- the second call's argument
    let s := G Lb Bρ w (p + w + 1) + 2
    let nl := Lb * (s + p + w + 2)
    have hnlw : w ≤ nl := by
      have : 1 * (s + p + w + 2) ≤ Lb * (s + p + w + 2) := Nat.mul_le_mul_right _ hL
      show w ≤ Lb * (s + p + w + 2); omega
    have hnl : nl ≤ F S := by
      show Lb * (s + p + w + 2) ≤ (4 * Lb + 14) * (Bρ S + S + 1)
      have a1 : Lb * (s + p + w + 2) ≤ Lb * (4 * (S + 1)) := Nat.mul_le_mul_left _ (by omega)
      have a2 : Lb * (4 * (S + 1)) = 4 * Lb * (S + 1) := by rw [← Nat.mul_assoc, Nat.mul_comm Lb 4]
      have a3 : 4 * Lb * (S + 1) ≤ (4 * Lb + 14) * (Bρ S + S + 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    have hFS : F S = iter F (t + 2) x := by show F (iter F (t + 1) x) = _; rfl
    have hNY : iter F (t + 2) x ≤ Y := iter_more infl x _ _ (by omega)
    have h2 : G Lb Bρ w nl ≤ Y := by
      calc G Lb Bρ w nl ≤ iter F t nl := ih _ hnlw
        _ ≤ iter F t (iter F (t + 2) x) := iter_mono mono t _ _ (by rw [← hFS]; exact hnl)
        _ = Y := by rw [iter_add]; show iter F (t + 2 + t) x = iter F (2 * t + 2) x; congr 1; omega
    have hSY : S ≤ Y := iter_more infl x _ _ (by omega)
    -- the total
    show p + 2 * (Lb * s + s + nl + G Lb Bρ w nl) + 10 ≤ iter F (2 * t + 3) x
    have hY : iter F (2 * t + 3) x = F Y := rfl
    rw [hY]
    show p + 2 * (Lb * s + s + nl + G Lb Bρ w nl) + 10 ≤ (4 * Lb + 14) * (Bρ Y + Y + 1)
    have b1 : Lb * s ≤ Lb * (Y + 2) := Nat.mul_le_mul_left _ (by omega)
    have b2 : Lb * (Y + 2) = Lb * Y + 2 * Lb := by rw [Nat.mul_add, Nat.mul_comm Lb 2]
    have b3 : (4 * Lb + 14) * (Y + 1) ≤ (4 * Lb + 14) * (Bρ Y + Y + 1) := Nat.mul_le_mul_left _ (by omega)
    have b4 : (4 * Lb + 14) * (Y + 1) = 4 * (Lb * Y) + 14 * Y + 4 * Lb + 14 := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.mul_assoc]; omega
    have hnlY : nl ≤ Y := by have := hnl; rw [hFS] at this; omega
    omega

/-- The majorant, rank by rank. -/
def Bm (Lb : Nat) : Nat → Nat → Nat
  | 0, a => a + 1
  | ρ + 1, a => iter (Fm Lb (Bm Lb ρ)) (tcount a) a

theorem iter_le_of_le {f g : Nat → Nat} (hfg : ∀ x, f x ≤ g x) (hg : ∀ a b, a ≤ b → g a ≤ g b) :
    ∀ n x, iter f n x ≤ iter g n x
  | 0, _ => Nat.le_refl _
  | n + 1, x => Nat.le_trans (hfg _) (hg _ _ (iter_le_of_le hfg hg n x))

theorem Bm_props (Lb : Nat) (hL : 1 ≤ Lb) : ∀ ρ, Mono (Bm Lb ρ) ∧ ∀ a, B Lb ρ a ≤ Bm Lb ρ a := by
  intro ρ
  induction ρ with
  | zero => exact ⟨fun a b h => by simp only [Bm]; omega, fun a => by simp [B, Bm]⟩
  | succ ρ ih =>
    obtain ⟨mono, le⟩ := ih
    have Fmono := Fm_mono Lb mono
    have Finfl := Fm_infl Lb (Bm Lb ρ)
    refine ⟨fun a b h => ?_, fun a => ?_⟩
    · simp only [Bm]
      have t_mono : tcount a ≤ tcount b := by
        induction h with
        | refl => exact Nat.le_refl _
        | step _ ih' => exact Nat.le_trans ih' (by simp only [tcount]; omega)
      exact Nat.le_trans (iter_mono Fmono _ a b h) (iter_more Finfl b _ _ t_mono)
    · simp only [B, Bm]
      calc G Lb (B Lb ρ) a a ≤ iter (Fm Lb (B Lb ρ)) (tcount a) a := G_le_iter Lb hL _ (B_mono Lb ρ) a a (Nat.le_refl _)
        _ ≤ iter (Fm Lb (Bm Lb ρ)) (tcount a) a :=
          iter_le_of_le (fun x => by unfold Fm; exact Nat.mul_le_mul_left _ (by have := le x; omega)) Fmono _ _

theorem B_le_Bm (Lb : Nat) (hL : 1 ≤ Lb) (ρ a : Nat) : B Lb ρ a ≤ Bm Lb ρ a := (Bm_props Lb hL ρ).2 a
theorem Bm_mono (Lb : Nat) (hL : 1 ≤ Lb) (ρ : Nat) : Mono (Bm Lb ρ) := (Bm_props Lb hL ρ).1

end PP
