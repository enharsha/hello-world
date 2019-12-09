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