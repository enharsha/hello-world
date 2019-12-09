namespace hidden
inductive nat : Type
| zero : nat
| succ : nat →  nat
namespace nat

def add (m n:nat):nat:=
nat.rec_on n m (λ a (add_m_n),succ (add_m_n))

def mult (m n:nat):nat:=
nat.rec_on n zero (λ a mult_m_n,add m mult_m_n)

def pred (m:nat):nat:=
nat.rec_on m zero (λ a pred_m,a)

def exp (m n:nat):nat:=
nat.rec_on n succ(zero)) (λ a exp_m_n,mult m exp_m_n) 

end nat

inductive list (α : Type u)
| nil {} : list
| cons : α → list → list

namespace list

variable {α : Type}
notation h :: t := cons h t

def append (s t : list α)  : list α  :=
list.rec t (λ x l u, x::u) s

def length (s:list α) :nat :=
list.rec s nat.zero (λ x l n,(nat.succ n) ) 

end list
end hidden

/-Question 3-/
inductive test : Type
|const: nat→ test
|var:nat→ test
|plus:nat→ nat→ test
|times:nat→ nat→ test

