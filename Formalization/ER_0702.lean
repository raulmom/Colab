import tactic data.set.basic data.setoid.basic
set_option trace.simplify.rewrite true

#print partial_order
#print setoid
#print quotient
#print subtype
#print set


@[class] structure closure_op (Ω : Type _) (p : partial_order(Ω)):=
(co : Ω → Ω)
(co_extensive : ∀(X : Ω), X ≤ co(X))
(co_monotonic : ∀(X Y : Ω), (X ≤ Y) → (co(X) ≤ co(Y)))
(co_idempotent: ∀(X : Ω), co(co(X)) = co(X))

--Ejemplo: Saturación de una relación de equivalencia
@[instance] def set.partial_order (Ω : Type _): partial_order (set (Ω)) :=
{
  le := (⊆),
  lt := (⊂),
  le_refl := @set.subset.rfl (Ω),
  le_trans := @set.subset.trans (Ω),
  lt_iff_le_not_le :=
    begin
      assume A B,
      simp *,
      refl
    end, 
  le_antisymm := @set.subset.antisymm (Ω)
}

def sat_fun {Ω : Type _} {Φ : setoid (Ω)} : set (Ω) → set (Ω) :=
λ L, (λ y, ∃ ( x ∈ L ), x ≈ y)

namespace sat_fun

lemma is_extensive {Ω : Type _} {Φ : setoid (Ω)}:
 ∀(L : set Ω), L ⊆ @sat_fun (Ω) (Φ) (L) :=
begin
  assume L,
  assume x,
  assume x_in_L,
  fconstructor,
  {
    exact x
  },
  {
    tauto
  }
end

lemma is_monotonic {Ω : Type _} {Φ : setoid (Ω)}:
∀(L M : set(Ω)), (L ⊆ M) → (@sat_fun (Ω) (Φ) (L) ⊆ @sat_fun (Ω) (Φ) (M)) :=
begin
  assume L M,
  assume L_subset_M,
  assume y,
  assume h1,
  cases h1,
  fconstructor,
  {
    exact h1_w
  },
  {
    tauto
  }
end

lemma is_idempotent {Ω : Type _} {Φ : setoid (Ω)}:
∀(L : set Ω), @sat_fun (Ω) (Φ) (@sat_fun (Ω) (Φ) (L)) = @sat_fun (Ω) (Φ) (L) :=
begin
  assume L,
  ext1,
  split,
  {
    assume h1,
    cases h1,
    cases h1_h,
    cases h1_h_w,
    fconstructor,
    {
      exact h1_h_w_w
    },
    {
      simp at *,
      cases h1_h_w_h,
      apply and.intro,
      {
        exact h1_h_w_h_left
      },
      {
        exact setoid.trans h1_h_w_h_right h1_h_h
      }
    }
  },
  {
    have h1: sat_fun (L) ⊆ sat_fun (sat_fun (L)), from
    begin
      exact @sat_fun.is_extensive (Ω) (Φ) (sat_fun L),
      exact Φ
    end,
    tauto
  }
end

@[instance] def co {Ω : Type _} {Φ : setoid (Ω)} : closure_op (set(Ω)) (set.partial_order Ω):=
{
  co := @sat_fun (Ω) (Φ),
  co_extensive := sat_fun.is_extensive,
  co_monotonic := sat_fun.is_monotonic,
  co_idempotent := sat_fun.is_idempotent
}

end sat_fun

lemma remark_2_25 {Ω : Type _} {Φ : setoid (Ω)} {L: set (Ω)}: 
  @sat_fun (Ω) (Φ) (L) = quotient.mk ⁻¹' (quotient.mk '' (L)) :=
begin
  ext1,
  split,

-- (-->)
  {
    assume h1,
    cases h1 with x' h1,
    simp at *,
    fconstructor,
    {
      exact x'
    },
    {
      exact h1
    }
  },

-- (<--)
  {
    assume h1,
    cases h1 with x' h1,
    simp at *,
    fconstructor,
    {
      exact x'
    },
    {
      simp at *,
      exact h1
    }
  }
end                           

--Operador saturación y relaciones
lemma lemma_2_26 {Ω : Type _} (Φ Ψ : setoid (Ω)) :
Φ ≤ Ψ ↔ ∀ (L : set(Ω)), @sat_fun (Ω) (Φ) (@sat_fun (Ω) (Ψ) (L)) = @sat_fun (Ω) (Ψ) (L) :=
begin
  rw setoid.le_def,
  split,

-- (-->) 
  {
    assume h1,
    assume L,
    apply set.subset.antisymm,

    --(⊆)
    {
      assume z,
      assume h2,
      cases h2 with a h2,
      cases h2 with h2 h3,
      have h4 : Ψ.rel a z, by exact h1 h3,
      cases h2 with b h2,
      fconstructor,
      {
        exact b
      },
      {
        cases h2 with h5 h6,
        have h2 : Ψ.rel b z, by exact setoid.trans' Ψ h6 h4,
        fconstructor,
        {
          exact h5
        },
        {
          exact h2
        }
      }
    },

    --(⊇)
    {
      exact sat_fun.is_extensive (sat_fun L),
    }
  },
  {
    assume h1,
    assume x0 y0,
    assume h2,
    have h3 : sat_fun (sat_fun {x0}) = sat_fun {x0}, from
      begin
        exact h1 {x0}
      end,
    have h4 : {x0} ⊆ @sat_fun Ω Ψ {x0}, from 
      begin
        exact sat_fun.is_extensive {x0}
      end,
    have h5 : @sat_fun Ω Φ {x0} ⊆ @sat_fun Ω Φ (@sat_fun Ω Ψ {x0}), from
      begin
        exact sat_fun.is_monotonic {x0} (@sat_fun Ω Ψ {x0}) h4
      end,
    have h6 : @sat_fun Ω Φ {x0} ⊆ @sat_fun Ω Ψ {x0}, from
      begin
        rw (eq.symm h3),
        exact h5
      end,
    have h7 : y0 ∈ @sat_fun Ω Φ {x0}, from
      begin
        rw sat_fun,
        simp at *,
        exact h2
      end,
    have h8 : y0 ∈ @sat_fun Ω Ψ {x0}, from
      begin
        exact h6 h7
      end,
    rw sat_fun at h8,
    simp at h8,
    exact h8
  }
end