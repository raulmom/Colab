set_option trace.simplify.rewrite true
open nat
open classical


lemma fst_of_two_props :
∀a b : Prop, a → b → a :=
assume a b : Prop,
assume ha : a,
assume hb : b,
show a, from
ha

lemma prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) :
a → c :=
begin
  assume ha : a,
  have hb : b :=
  hab ha,
  have hc : c :=
  hbc hb,
  show c, from
  hc
end


--------

--Prueba mixta
lemma forall.one_point {α : Type} (t : α) (p : α → Prop) :
(∀x, x = t → p x) ↔ p t :=
iff.intro
  (assume hall : ∀x, x = t → p x,
  show p t, from
    begin
    apply hall t,
    refl
    end)
  (assume hp : p t,
  assume x,
  assume heq : x = t,
  show p x, from
    begin
    rw heq,
    exact hp
    end
)

--Prueba by tactics
lemma forall.one_point2 {α : Type} (t : α) (p : α → Prop) :
(∀x, x = t → p x) ↔ p t :=
begin
  split,
  {assume h1,
  apply h1 t,
  refl},
  {assume h1,
  assume x,
  assume h2: x=t,
  rw h2,
  exact h1
  }
end

-- Prueba sin tactics
lemma forall.one_point3 {α : Type} (t : α) (p : α → Prop) :
(∀x, x = t → p x) ↔ p t :=
iff.intro 
(assume h1: ∀x, x = t → p x,
have h2 : t=t → p t, from
  h1 t,
show p t, from
 h2 (eq.refl t)
) 
(assume h1 : p t,
assume x : α,
assume h2 : x=t,
show p x, from
  eq.subst (eq.symm h2) h1
)


------------



lemma beast_666 (beast : ℕ) :
(∀n, n = 666 → beast ≥ n) ↔ beast ≥ 666 :=
forall.one_point 666 (λ n:ℕ, beast ≥ n)

lemma beast_666_2 (beast : ℕ) :
(∀n, n = 666 → beast ≥ n) ↔ beast ≥ 666 :=
forall.one_point 666 (λ n:ℕ, beast ≥ n)


lemma exists.one_point {α : Type} (t : α) (p : α → Prop) :
(∃x : α, x = t ∧ p x) ↔ p t :=
iff.intro
(assume hex : ∃x, x = t ∧ p x,
show p t, from
  exists.elim hex
  (assume x,
  assume hand : x = t ∧ p x,
  show p t, from
    by cc))
(assume hp : p t,
show ∃x : α, x = t ∧ p x, from
  exists.intro t
  (show t = t ∧ p t, from
    by cc))

lemma prop_comp₃ (a b c : Prop) (hab : a → b) (hbc : b → c) :
  a → c :=
begin
  intro ha,
  have hb : b :=
    hab ha,
  let c' := c,
  have hc : c' :=
    hbc hb,
  exact hc
end