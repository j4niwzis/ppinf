/-
  Encodings for Theorem 9: characters as valid code points, strings as their characters,
  and the machine's tokens, steps, frames and states as products and sums of these.
-/
import Mathlib.Computability.Primrec.List
import Machine

open Primrec

namespace PP

theorem valid_prim : PrimrecPred Nat.isValidChar := by
  unfold Nat.isValidChar
  exact PrimrecPred.or (PrimrecRel.comp nat_lt Primrec.id (const _))
    (PrimrecPred.and (PrimrecRel.comp nat_lt (const _) Primrec.id) (PrimrecRel.comp nat_lt Primrec.id (const _)))

instance validCode : Primcodable {n : ℕ // n.isValidChar} := Primcodable.subtype valid_prim

theorem toNat_ofNat_valid (n : ℕ) (h : n.isValidChar) : (Char.ofNat n).toNat = n := by
  simp [Char.ofNat, h, Char.ofNatAux, Char.toNat]

def charEquiv : Char ≃ {n : ℕ // n.isValidChar} where
  toFun c := ⟨c.toNat, c.valid⟩
  invFun n := Char.ofNat n.1
  left_inv c := Char.ofNat_toNat c
  right_inv n := Subtype.ext (toNat_ofNat_valid n.1 n.2)

instance : Primcodable Char := Primcodable.ofEquiv _ charEquiv

def stringEquiv : String ≃ List Char where
  toFun := String.toList
  invFun := String.ofList
  left_inv s := by simp
  right_inv l := by simp

instance : Primcodable String := Primcodable.ofEquiv _ stringEquiv

def tokEquiv : Tok ≃ String × List String × ℕ × List String where
  toFun t := (t.s, t.H, t.o, t.P)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv t := rfl
  right_inv p := rfl

instance : Primcodable Tok := Primcodable.ofEquiv _ tokEquiv

def stepEquiv : Step ≃ String × Tok × Option Tok × List String × ℕ where
  toFun t := (t.m, t.head, t.close, t.mark, t.id)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv t := rfl
  right_inv p := rfl

instance : Primcodable Step := Primcodable.ofEquiv _ stepEquiv

def btokEquiv : BTok ≃ String ⊕ ℕ ⊕ Bool where
  toFun
    | .tok s => .inl s
    | .param i => .inr (.inl i)
    | .va => .inr (.inr true)
    | .paste => .inr (.inr false)
  invFun
    | .inl s => .tok s
    | .inr (.inl i) => .param i
    | .inr (.inr true) => .va
    | .inr (.inr false) => .paste
  left_inv b := by cases b <;> rfl
  right_inv p := by rcases p with s | i | (_ | _) <;> rfl

instance : Primcodable BTok := Primcodable.ofEquiv _ btokEquiv

def defEquiv : Def ≃ List BTok ⊕ (ℕ × Bool × List BTok) where
  toFun
    | .obj b => .inl b
    | .fn a v b => .inr (a, v, b)
  invFun
    | .inl b => .obj b
    | .inr (a, v, b) => .fn a v b
  left_inv d := by cases d <;> rfl
  right_inv p := by rcases p with b | ⟨a, v, b⟩ <;> rfl

instance : Primcodable Def := Primcodable.ofEquiv _ defEquiv

def rtokEquiv : RTok ≃ Tok ⊕ Bool where
  toFun
    | .t x => .inl x
    | .pm => .inr true
    | .op => .inr false
  invFun
    | .inl x => .t x
    | .inr true => .pm
    | .inr false => .op
  left_inv r := by cases r <;> rfl
  right_inv p := by rcases p with x | (_ | _) <;> rfl

instance : Primcodable RTok := Primcodable.ofEquiv _ rtokEquiv

def levelEquiv : Level ≃ List Tok × List Tok where
  toFun l := (l.out, l.inp)
  invFun p := ⟨p.1, p.2⟩
  left_inv l := rfl
  right_inv p := rfl

instance : Primcodable Level := Primcodable.ofEquiv _ levelEquiv

def frameEquiv : Frame ≃ Level × Step × List BTok × List BTok × ℕ × List RTok × List (List Tok) × List Tok where
  toFun f := (f.lvl, f.step, f.whole, f.bs, f.i, f.acc, f.named, f.va)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2⟩
  left_inv f := rfl
  right_inv p := rfl

instance : Primcodable Frame := Primcodable.ofEquiv _ frameEquiv

def modeEquiv : Mode ≃ (Level × List Frame) ⊕ (Frame × List Frame) ⊕ Option (List Tok) where
  toFun
    | .scan l fs => .inl (l, fs)
    | .body f fs => .inr (.inl (f, fs))
    | .done out => .inr (.inr (some out))
    | .fail => .inr (.inr none)
  invFun
    | .inl (l, fs) => .scan l fs
    | .inr (.inl (f, fs)) => .body f fs
    | .inr (.inr (some out)) => .done out
    | .inr (.inr none) => .fail
  left_inv m := by cases m <;> rfl
  right_inv p := by rcases p with ⟨l, fs⟩ | ⟨f, fs⟩ | (_ | out) <;> rfl

instance : Primcodable Mode := Primcodable.ofEquiv _ modeEquiv

def mstateEquiv : MState ≃ Mode × List Step × ℕ where
  toFun s := (s.mode, s.steps, s.c)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv s := rfl
  right_inv p := rfl

instance : Primcodable MState := Primcodable.ofEquiv _ mstateEquiv

end PP
