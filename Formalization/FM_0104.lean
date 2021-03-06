import tactic data.set.basic data.rel data.list.basic group_theory.congruence
set_option trace.simplify.rewrite true

@[instance] def list_has_mul {Ω : Type _} : has_mul (list Ω) :=
{
  mul := λ (u v : list Ω), u ++ v
}

def tras_right {Ω : Type _} (w : list Ω) : list Ω → list Ω :=
  λ (u : list Ω), w ++ u
 
def tras_left {Ω : Type _} (w : list Ω) : list Ω → list Ω :=
  λ (u : list Ω), u ++ w

def is_closed_right {Ω : Type _} (w : list Ω) (r : setoid (list Ω)) : Prop :=
  ∀ (u v : list Ω), setoid.r u v → setoid.r (tras_right w u) (tras_right w v)

def is_closed_left {Ω : Type _} (w : list Ω) (r : setoid (list Ω)) : Prop :=
  ∀ (u v : list Ω), setoid.r u v → setoid.r (tras_left w u) (tras_left w v)

structure is_tras_closed {Ω : Type _} (r : setoid (list Ω)) : Prop :=
  (rc : ∀ (w : list Ω), is_closed_right w r)
  (lc : ∀ (w : list Ω), is_closed_left w r)

def is_con {Ω : Type _} (r : setoid Ω) [has_mul Ω] : Prop :=
  ∀ {w x y z : Ω}, setoid.r w x → setoid.r y z → setoid.r (w * y) (x * z)

#print setoid


--Proposition 2_72
lemma con_iff_tras_closed {Ω : Type _} (r : setoid (list Ω)) : 
  is_con r ↔ is_tras_closed r := 
begin
  split,
  {
    rw is_con,
    assume h1,
    split,
    {
      assume w,
      rw is_closed_right,
      assume u v,
      rw tras_right,
      simp,
      assume h2,
      apply h1,
      exact setoid.refl w,
      exact h2,
    },
    {
      assume w,
      rw is_closed_left,
      assume u v,
      rw tras_left,
      simp,
      assume h2,
      apply h1,
      exact h2,
      exact setoid.refl w,
    }
  },

  {
    rw is_con,
    assume h1,
    assume a b x y,
    assume h2,
    assume h3,
    have h4 : setoid.r (a*x) (a*y) :=
      begin
        apply h1.rc _,
        exact h3
      end,
    have h5 : setoid.r (a*y) (b*y) :=
      begin
        apply h1.lc _,
        exact h2
      end,
    exact setoid.trans h4 h5
  }
end


def is_recognizable {M : Type _} [monoid (M)] (L : set M) : Prop :=
 ∃ (N : Type _) [monoid N] [fintype N], ∃ (φ : @monoid_hom M N (monoid.to_mul_one_class M) (@monoid.to_mul_one_class N (_inst_2))), ∃ B : set N, L = φ ⁻¹' B