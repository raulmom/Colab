set_option trace.simplify.rewrite true
open nat


-- 1.1.4
universe u
constants α β γ : Type 


def some_fun_of_type : (α → β → γ) → ((β → α) → β) → α → γ := 
λ f, λ g, λ a, f a (g(λ h, a))

/-
inductive type-name (params1 : type1) . . . (paramsk : typek) : Type
| constructor-name1 : constructor-type1
.
.
.
| constructor-namen : constructor-typen
-/

inductive aexp : Type
| num : ℤ → aexp
| var : string → aexp
| add : aexp → aexp → aexp
| sub : aexp → aexp → aexp
| mul : aexp → aexp → aexp
| div : aexp → aexp → aexp

def eval (env : string → ℤ) : aexp → ℤ 
| (aexp.num i) := i
| (aexp.var x) := env x
| (aexp.add e1 e2) := eval e1 + eval e2
| (aexp.sub e1 e2) := eval e1 - eval e2
| (aexp.mul e1 e2) := eval e1 * eval e2
| (aexp.div e1 e2) := eval e1 / eval e2

-- 2.1

lemma fst_of_two_props :
∀a b : Prop, a → b → a :=
begin
intros a b,
intros ha hb,
assumption,
end

lemma fst_of_two_props2 (a b : Prop) (ha : a) (hb : b) :
a :=
begin
exact ha,
end

lemma fst_of_two_props3 (a b : Prop) (ha : a) (hb : b) :
a :=
by apply ha

lemma prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) :
a → c :=
begin
intro ha,
apply hbc,
apply hab,
apply ha,
end

-- 2.3
lemma and_swap (a b : Prop) :
a ∧ b → b ∧ a :=
begin
intro hab,
apply and.intro,
apply and.elim_right,
exact hab,
apply and.elim_left,
exact hab,
end

lemma and_swap2 :
∀a b : Prop, a ∧ b → b ∧ a :=
begin
intros a b hab,
apply and.intro,
{ exact and.elim_right hab },
{ exact and.elim_left hab }
end

lemma nat_exists_double_iden :
∃n : ℕ, n = n :=
begin
apply exists.intro 0,
refl,
end

-- 2.4
lemma cong_fst_arg {α : Type} (a a' b : α)
(f : α → α → α) (ha : a = a') :
f a b = f a' b :=
begin
apply eq.subst ha,
apply eq.refl,
end

lemma cong_two_args {α : Type} (a a' b b' : α)
(f : α → α → α) (ha : a = a') (hb : b = b') :
f a b = f a' b' :=
begin
apply eq.subst ha,
apply eq.subst hb,
apply eq.refl
end

lemma cong_two_args2 {α : Type} (a a' b b' : α)
(f : α → α → α) (ha : a = a') (hb : b = b') :
f a b = f a' b' :=
begin
rw ha,
rw hb,
end

lemma cong_two_args3 {α : Type} (a a' b b' : α)
(f : α → α → α) (ha : a = a') (hb : b = b') :
f a b = f a' b' :=
begin
simp[*] at *,
end
 
-- 2.6
namespace myadd

def add : ℕ → ℕ → ℕ 
| m nat.zero := m
| m (nat.succ n) := nat.succ (add m n)

lemma add_zero (n : ℕ) :
add 0 n = n :=
begin
induction n,
{ refl },
{ simp [add, n_ih] }
end

lemma add_succ (m n : ℕ) :
add (nat.succ m) n = nat.succ (add m n) :=
begin
induction n,
{ refl },
{ simp [add, n_ih] }
end

lemma add_comm (m n : ℕ) :
add m n = add n m :=
begin
induction n,
{ simp [add, add_zero] },
{ simp [add, add_succ, n_ih] }
end

lemma add_assoc (l m n : ℕ) :
add (add l m) n = add l (add m n) :=
begin
induction n,
{ refl },
{ simp [add, n_ih] }
end

@[instance] def add.is_commutative : is_commutative ℕ add :=
{ comm := add_comm }
@[instance] def add.is_associative : is_associative ℕ add :=
{ assoc := add_assoc }


end myadd