/- # LoVe Exercise 3: Forward Proofs -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe

/- ## Question 1: Connectives and Quantifiers
1.1. Supply structured proofs of the following lemmas. -/

lemma I (a : Prop) :
  a → a :=
assume ha,
ha

lemma K (a b : Prop) :
  a → b → b :=
assume ha,
assume hb,
hb

lemma C (a b c : Prop) :
  (a → b → c) → b → a → c :=
assume habc,
assume b,
assume a,
habc a b

lemma proj_1st (a : Prop) :
  a → a → a :=
assume ha,
assume ha2,
ha

/- Please give a different answer than for `proj_1st`. -/

lemma proj_2nd (a : Prop) :
  a → a → a :=
assume ha,
I (a)

lemma some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c :=
assume habc,
assume ha,
assume hac,
assume hb,
hac ha

/- 1.2. Supply a structured proof of the contraposition rule. -/

lemma contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a :=
assume hab,
assume hnob,
assume ha,
hnob (hab (ha))

/- 1.3. Supply a structured proof of the distributivity of `∀` over `∧`. -/

lemma forall_and {α : Type} (p q : α → Prop) :
  (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
iff.intro
(
  assume h1,
  and.intro 
  (
    assume x,
    and.elim_left (h1 x)
  )
  (
    assume x,
    and.elim_right (h1 x)
  )
)
(
  assume h1,
  assume x,
  and.intro 
  (
    and.elim_left h1 x
  ) 
  (
    and.elim_right h1 x
  )
)

/- 1.4. Reuse, if possible, the lemma `forall_and` you proved above to prove
the following instance of the lemma. -/

lemma forall_and_inst {α : Type} (r s : α → α → Prop) :
  (∀x, r x x ∧ s x x) ↔ (∀x, r x x) ∧ (∀x, s x x) :=
forall_and (λ x:α, r x x)(λ x:α, s x x)


/- ## Question 2: Chain of Equalities
2.1. Write the following proof using `calc`.
      `(a + b) * (a + b)`
    `= a * (a + b) + b * (a + b)`
    `= a * a + a * b + b * a + b * b`
    `= a * a + a * b + a * b + b * b`
    `= a * a + 2 * a * b + b * b`
Hint: You might need the tactics `simp` and `cc` and the lemmas `mul_add`,
`add_mul`, and `two_mul`. -/

lemma binomial_square (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
sorry

/- 2.2. Prove the same argument again, this time as a structured proof. Try to
reuse as much of the above proof idea as possible. -/

lemma binomial_square₂ (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
sorry

/- 2.3. Prove the same lemma again, this time using tactics. -/

lemma binomial_square₃ (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
begin
  sorry
end


/- ## Question 3 (**optional**): One-Point Rules
3.1 (**optional**). Prove that the following wrong formulation of the one-point
rule for `∀` is inconsistent, using a structured proof. -/

axiom forall.one_point_wrong {α : Type} {t : α} {p : α → Prop} :
  (∀x : α, x = t ∧ p x) ↔ p t

lemma proof_of_false :
  false :=
begin
  have wrong : (∀x, x = 0 ∧ true) ↔ true :=
    @forall.one_point_wrong ℕ 0 (λ_, true),
  simp at wrong,
  have one_eq_zero : 1 = 0 :=
    wrong 1,
  cc
end

/- 3.2 (**optional**). Prove that the following wrong formulation of the
one-point rule for `∃` is inconsistent, using a tactical or structured proof. -/

axiom exists.one_point_wrong {α : Type} {t : α} {p : α → Prop} :
  (∃x : α, x = t → p x) ↔ p t

lemma proof_of_false₂ :
  false :=
begin
  have wrong : (∃x, x ≠ 0) ↔ false :=
    @exists.one_point_wrong ℕ 0 (λ_, false),
  simp at wrong,
  have one_eq_zero : 1 = 0 :=
    wrong 1,
  cc
end

end LoVe