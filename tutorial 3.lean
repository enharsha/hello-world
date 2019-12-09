variables (α:Type) (p q :α → Prop)
/-Question-/
example: (∀x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
iff.intro
(assume h: (∀ x,p x ∧ q x), and.intro (assume h1 : α, (h h1).left) (assume h2 : α, (h h2).right))
(assume h: (∀ x, p x) ∧ (∀ x, q x), assume h1 : α, and.intro (h.left h1) (h.right h1))

example: (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
assume h1: (∀ x, p x → q x), assume h2: (∀ x, p x),assume h3: α, (h1 h3) (h2 h3)

example: (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
assume h: (∀ x, p x) ∨ (∀ x, q x),assume x : α,
or.elim h (assume h1 : ∀ x, p x, or.inl (h1 x)) (assume h2 : ∀ x, q x, or.inr (h2 x))

/-Question-/
variables (men : Type) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false :=
have h1 : shaves barber barber ↔ ¬shaves barber barber, from (h barber),
have h2 : ¬shaves barber barber, from (assume h3 : shaves barber barber, absurd h3 (h1.mp h3)),
false.elim (h2 (h1.mpr h2))

/-Question-/
namespace hidden

def divides (m n : ℕ) : Prop := ∃ k, m * k = n
instance : has_dvd nat := ⟨divides⟩
def even (n : ℕ) : Prop := 2 ∣ n

def prime (n : ℕ) : Prop := ∀ m, (m ∣ n) → (m=1) ∨ (m=n) 
def infinitely_many_primes : Prop := ∀ n, ∃ m, (m > n) ∧ prime m
def Fermat_number (n : ℕ) : Prop := ∃ m:nat, n=2^(2^m) + 1
def Fermat_prime (n : ℕ) : Prop := prime n ∧ Fermat_number n
def infinitely_many_Fermat_primes : Prop := ∀ n, ∃ m,(m > n) ∧ Fermat_prime m
def goldbach_conjecture : Prop := ∀ n, (n > 2) → ∃ p q, (p + q = n) ∧ prime p ∧ prime q
def Goldbach's_weak_conjecture : Prop := ∀ n, ¬even n ∧ (n > 5) → ∃ p p1 p2, (p + p1 + p2 = n) ∧ prime p ∧ prime p1 ∧ prime p2
def Fermat's_last_theorem : Prop := ∀ n, (n > 2) → ¬∃ a b c, a^n + b^n = c^n ∧ (a > 0) ∧ (b > 0) ∧ (c > 0)

end hidden

