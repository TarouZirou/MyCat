import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Data.Nat.Basic

#eval ((· + 3) ∘ (· + 5)) 0

def Nat_list : ℕ → List ℕ
  | 0        => [0]
  | Nat.succ k => Nat_list k ++ [k + 1]

def Nat_range (a b : Nat) : List Nat :=
  ite (a > b) [] (List.range (b - a + 1) |>.map (· + a))

def Nat_List_sum (i n : Nat) (f : Nat → Nat) : Nat :=
  ((Nat_range i n).map f).sum

notation:max "∑("i "~" n")" f => Nat_List_sum i n f

theorem index_shift (i n : Nat) (f : Nat → Nat)(a : Nat) :
  (∑(i ~ n) f) = (∑((i + a) ~ (n + a)) (f ∘ (· - a))) := by
  induction n with
  | zero =>
    simp [Nat_List_sum, Nat_range]
    split
    case zero.isTrue =>
      simp [List.map,List.sum]
    case zero.isFalse =>
      simp [List.range, List.range.loop]
  | succ k hk =>
    have h : (∑(i~k + 1)f) = (∑(i~k)f) + f (k + 1) := by
      simp [Nat_List_sum, Nat_range]
      split
      case _ =>
        simp [List.map]
      case _ =>

    rw [h]
    have h' :
      (∑(i + a~k + 1 + a)f ∘ fun x ↦ x - a) =
        (∑(i + a~k + a)f ∘ fun x ↦ x - a) + f (k + 1) := by
      sorry
    rw [h']
    rw [hk]

#eval Nat_list 10
#eval (Nat_list (10)).sum

theorem sum_eq (n : ℕ) :
  (Nat_list n).sum = (n * (n + 1)) / 2 := by
  induction n with
  | zero => simp [Nat_list]
  | succ k hk =>
    calc
      (Nat_list (k + 1)).sum
          = (Nat_list k ++ [k + 1]).sum           := rfl
      _ = (Nat_list k).sum + ([k + 1] : List ℕ).sum := by simp [List.sum_append]
      _ = (Nat_list k).sum + (k + 1)                 := by simp [List.sum_singleton]
      _ = (k * (k + 1) / 2) + (k + 1)               := by rw [hk]
      _ = (k + 1) * (k + 2) / 2 := by
        have h: k * (k + 1) + 2 * (k + 1) = (k + 1) * (k + 2) := by
          calc
            k * (k + 1) + 2 * (k + 1) = k * (k + 1) + (k + 1) + (k + 1) := by
              have h: 2 = 1 + 1 := by
                change 2 = 1 + 1
                rfl
              rw [h]
              rw [mul_add (1 + 1)]
              rw [add_mul 1 1 k, add_mul 1 1 1]
              rw [one_mul, one_mul]
              rw [add_assoc k k,← add_assoc k 1, add_comm k 1, add_comm k (1 + k + 1), add_assoc, ← add_assoc]
            _ = (k + 2) * (k + 1) := by
              rw [add_assoc]
              rw [←two_mul]
              rw [← add_mul]
            _ = (k + 1) * (k + 2) := by rw [mul_comm]
        rw [← Nat.add_mul_div_left]
        rw [h]
        decide

-- 階乗
def fact : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * fact k
notation:max n "!" => fact n
#eval 5! -- 120

-- 組み合わせの数
def combo (n r : Nat) : Nat := n ! / ((n - r)! * r !)
notation:max n "C" r => combo n r
#eval 6 C 3

#eval Nat_list 7

#eval (Nat_list 7).map (combo 7)
#eval (Nat_list 8).map (λ r ↦ combo 8 r * (1 ^ (8 - r)) * (2 ^ r))



/-
theorem add_pow_eq_sum (a b n : Nat) :
  (a + b) ^ n = ((Nat_list n).map (λ r ↦ (combo n r * a ^ (n - r) * b ^ r))).sum := by
  induction n with
  | zero =>
    rw [Nat_list]
    have h: List.map (fun r ↦ (0C r) * a ^ (0 - r) * b ^ r) [0] = [1] := by
      dsimp [List.map]
      rw [combo]
      simp [fact]
    rw [h, List.sum_singleton]
    rw [pow_zero]
  | succ n hn =>
    rw [Nat_list]
    rw [List.map_append]
    rw [List.sum_append]

    --have h : List.map
    --  (fun r ↦ ((n + 1)C r) * a ^ (n + 1 - r) * b ^ r)
    --  (Nat_list n ++ [n + 1])
    --  = List.map
-/
