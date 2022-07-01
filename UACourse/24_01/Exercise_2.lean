/- # LoVe Exercise 2: Backward Proofs -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe

namespace backward_proofs


/- ## Question 1: Connectives and Quantifiers
1.1. Carry out the following proofs using basic tactics.
Hint: Some strategies for carrying out such proofs are described at the end of
Section 2.3 in the Hitchhiker's Guide. -/

lemma I (a : Prop) :
  a → a :=
begin
  intro h1,
  exact h1,
end

lemma K (a b : Prop) :
  a → b → b :=
begin
  assume ha,
  exact I(b),
end

lemma C (a b c : Prop) :
  (a → b → c) → b → a → c :=
begin
  assume h1,
  assume hb,
  assume ha,
  exact h1 ha hb,
end

lemma proj_1st (a : Prop) :
  a → a → a :=
begin
  assume h1,
  assume h2,
  exact h1,
end

/- Please give a different answer than for `proj_1st`: -/

lemma proj_2nd (a : Prop) :
  a → a → a :=
begin
  exact K a a,
end

lemma some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c :=
begin
  assume h1,
  assume ha,
  assume hac,
  assume hb,
  exact hac ha,
end

/- 1.2. Prove the contraposition rule using basic tactics. -/

lemma contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a :=
begin
  assume hab,
  assume nob,
  assume ha,
  exact nob (hab ha),
end

/- 1.3. Prove the distributivity of `∀` over `∧` using basic tactics.
Hint: This exercise is tricky, especially the right-to-left direction. Some
forward reasoning, like in the proof of `and_swap₂` in the lecture, might be
necessary. -/

lemma forall_and {α : Type} (p q : α → Prop) :
  (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
begin
  apply iff.intro,
  {
    assume h1,
    apply and.intro,
    {
      assume t,
      have h2 := h1 t,
      exact and.elim_left h2,
    },
    {
      assume t,
      have h2 := h1 t,
      exact and.elim_right h2,
    }
  },
  {
    assume h1,
    assume t,
    exact and.intro (and.elim_left h1 t) (and.elim_right h1 t)
    }
end


/- ## Question 2: Natural Numbers
2.1. Prove the following recursive equations on the first argument of the
`mul` operator defined in lecture 1. -/

#check mul

lemma mul_zero (n : ℕ) :
  mul 0 n = 0 :=
sorry

lemma mul_succ (m n : ℕ) :
  mul (nat.succ m) n = add (mul m n) n :=
sorry

/- 2.2. Prove commutativity and associativity of multiplication using the
`induction'` tactic. Choose the induction variable carefully. -/

lemma mul_comm (m n : ℕ) :
  mul m n = mul n m :=
sorry

lemma mul_assoc (l m n : ℕ) :
  mul (mul l m) n = mul l (mul m n) :=
sorry

/- 2.3. Prove the symmetric variant of `mul_add` using `rw`. To apply
commutativity at a specific position, instantiate the rule by passing some
arguments (e.g., `mul_comm _ l`). -/

lemma add_mul (l m n : ℕ) :
  mul (add l m) n = add (mul n l) (mul n m) :=
sorry


/- ## Question 3 (**optional**): Intuitionistic Logic
Intuitionistic logic is extended to classical logic by assuming a classical
axiom. There are several possibilities for the choice of axiom. In this
question, we are concerned with the logical equivalence of three different
axioms: -/

def excluded_middle :=
∀a : Prop, a ∨ ¬ a

def peirce :=
∀a b : Prop, ((a → b) → a) → a

def double_negation :=
∀a : Prop, (¬¬ a) → a

/- For the proofs below, please avoid using lemmas from Lean's `classical`
namespace, because this would defeat the purpose of the exercise.
3.1 (**optional**). Prove the following implication using tactics.
Hint: You will need `or.elim` and `false.elim`. You can use
`rw excluded_middle` to unfold the definition of `excluded_middle`,
and similarly for `peirce`. -/

lemma peirce_of_em :
  excluded_middle → peirce :=
begin
  rw excluded_middle,
  rw peirce,
  assume exc,
  assume ha hb,
  assume h1,
  apply or.elim (exc ha),
  {
    assume a,
    exact a,
  },
  {
    assume noa,
    apply h1,
    assume a,
    apply false.elim,
    exact noa a,
  }
end

/- 3.2 (**optional**). Prove the following implication using tactics. -/

lemma dn_of_peirce :
  peirce → double_negation :=
begin
  rw peirce,
  rw double_negation,
  assume hpeir,
  assume a,
  assume hnonoa,
  apply hpeir a false,
  assume hnoa,
  apply false.elim,
  apply hnonoa,
  exact hnoa,
end

/- We leave the missing implication for the homework: -/

namespace sorry_lemmas

lemma em_of_dn :
  double_negation → excluded_middle :=
sorry

end sorry_lemmas

end backward_proofs

end LoVe