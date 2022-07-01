/- # LoVe Homework 2: Backward Proofs
Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe

namespace backward_proofs


/- ## Question 1 (4 points): Connectives and Quantifiers
1.1 (3 points). Complete the following proofs using basic tactics such as
`intro`, `apply`, and `exact`.
Hint: Some strategies for carrying out such proofs are described at the end of
Section 2.3 in the Hitchhiker's Guide. -/

lemma B (a b c : Prop) :
  (a → b) → (c → a) → c → b :=
begin
  assume hab,
  assume hca,
  assume c,
  exact (hab (hca c)),
end

lemma S (a b c : Prop) :
  (a → b → c) → (a → b) → a → c :=
begin
  assume h1,
  assume hab,
  assume a,
  exact (h1 a (hab a)),
end

lemma more_nonsense (a b c : Prop) :
  (c → (a → b) → a) → c → b → a :=
begin
  assume h1,
  assume hc,
  assume hb,
  apply h1,
  {
    exact hc,
  },
  {
    assume ha,
    exact hb,
  }
end

lemma even_more_nonsense (a b c : Prop) :
  (a → a → b) → (b → c) → a → b → c :=
begin
  assume haab,
  assume hbc,
  assume ha,
  assume hb,
  exact (hbc hb),
end

/- 1.2 (1 point). Prove the following lemma using basic tactics. -/

lemma weak_peirce (a b : Prop) :
  ((((a → b) → a) → a) → b) → b :=
begin
  assume h1,
  apply h1,
  assume h2,
  apply h2,
  assume ha,
  apply h1,
  assume h3,
  exact ha,
end


/- ## Question 2 (5 points): Logical Connectives
2.1 (1 point). Prove the following property about implication using basic
tactics.
Hints:
* Keep in mind that `¬ a` is the same as `a → false`. You can start by invoking
  `rw not_def` if this helps you.
* You will need to apply the elimination rules for `∨` and `false` at some
  point. -/

lemma about_implication (a b : Prop) :
  ¬ a ∨ b → a → b :=
begin
  assume h1,
  assume ha,
  apply or.elim (h1),
  {
    assume hnoa,
    apply false.elim,
    exact hnoa ha,
  },
  {
    assume hb,
    exact hb,
  }
end

namespace sorry_lemmas
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

/- 2.2 (2 points). Prove the missing link in our chain of classical axiom
implications.
Hints:
* You can use `rw double_negation` to unfold the definition of
  `double_negation`, and similarly for the other definitions.
* You will need to apply the double negation hypothesis for `a ∨ ¬ a`. You will
  also need the left and right introduction rules for `∨` at some point. -/

#check excluded_middle
#check peirce
#check double_negation

lemma em_of_dn :
  double_negation → excluded_middle :=
begin
  rw double_negation,
  rw excluded_middle,
  assume hdn,
  assume a,
  apply hdn,
  assume hneg,
  apply hneg,
  apply or.intro_left,
  apply hdn,
  assume hna,
  apply hneg,
  apply or.intro_right,
  exact hna,
end


/- 2.3 (2 points). We have proved three of the six possible implications
between `excluded_middle`, `peirce`, and `double_negation`. State and prove the
three missing implications, exploiting the three theorems we already have. -/

#check peirce_of_em
#check dn_of_peirce
#check em_of_dn
.
lemma em_of_peirce:
  peirce → excluded_middle:=
begin
  assume hpeirce,
  exact (em_of_dn (dn_of_peirce (hpeirce))),
end

lemma peirce_of_dn:
  double_negation → peirce:=
begin
  assume hdn,
  exact (peirce_of_em (em_of_dn (hdn))),
end

lemma dn_of_em:
  excluded_middle → double_negation:=
begin
  assume hem,
  exact (dn_of_peirce (peirce_of_em (hem))),
end

end sorry_lemmas

end backward_proofs

end LoVe