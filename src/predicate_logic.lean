import formal_system data.set.finite init.data.list
universe u

-- We introduce predicate logic.

namespace logic

open logic list tactic set

section basic
parameters {sort : Type u} [decidable_eq sort]

structure functional_symbol :=
    (name : string)
    (domain   : list sort)
    (codomain : sort)

instance deq_functional_symbol : decidable_eq functional_symbol :=
    begin
    intros f g,
    cases f with nf df cdf,
    cases g with ng dg cdg,
    simp,
    apply_instance
    end

def arity (f : functional_symbol) := length f.domain

def is_constant (f : functional_symbol) := arity f = 0

@[reducible]
def tail_symbol (f : functional_symbol) : functional_symbol :=
{ name := f.name ++ "tail",
  domain := tail f.domain,
  codomain := f.codomain}

structure relational_symbol :=
    (name : string)
    (sig : list sort)
    (sig_not_empty : sig ≠ [])

instance deq_relational_symbol : decidable_eq relational_symbol :=
    begin
    intros f g,
    cases f with nf df cdf,
    cases g with ng dg cdg,
    simp,
    apply_instance
    end

def rarity (r : relational_symbol) := length r.sig

structure signature :=
    (sf : set functional_symbol)
    (sr : set relational_symbol)
    (unique_name₁ : ∀ f₁ f₂ : functional_symbol, f₁ ∈ sf → f₂ ∈ sf → f₁.name ≠ f₂.name)
    (unique_name₂ : ∀ r₁ r₂ : relational_symbol, r₁ ∈ sr → r₂ ∈ sr → r₁.name ≠ r₂.name)
    (unique_name₃ : ∀ (r₁ : relational_symbol) (f₂ : functional_symbol), r₁ ∈ sr → f₂ ∈ sf → r₁.name ≠ f₂.name)
    -- support for partial application.
    (head_project : ∀ f ∈ sf, tail_symbol f ∈ sf)

parameter {σ : signature}

def in_use  (s : sort) := 
    (∃ f : functional_symbol, f ∈ σ.sf ∧ (s ∈ f.domain ∨ s = f.codomain))
    ∨ (∃ r : relational_symbol, r ∈ σ.sr ∧ s ∈ r.sig)

def nary (n : ℕ) := subtype {f : functional_symbol | f ∈ σ.sf ∧ arity f = n}
@[reducible]
def const := nary 0

def nrary (n : ℕ) := subtype {r : relational_symbol | r ∈ σ.sr ∧ rarity r = n}

instance deq_nary (n : ℕ) : decidable_eq (nary n) :=
begin 
    intros f g,
    rcases f with ⟨f, fleft, fright⟩,
    rcases g with ⟨g, gleft, gright⟩,
    simp, apply_instance
end

instance deq_nrary (n : ℕ) : decidable_eq (nrary n) :=
begin 
    intros f g,
    rcases f with ⟨f, fleft, fright⟩,
    rcases g with ⟨g, gleft, gright⟩,
    simp,
    apply_instance
end

inductive tvariable
| mk :  ∀ s : sort, in_use s → ℕ → tvariable

instance deq_tvariable : decidable_eq tvariable :=
begin
    intros x y,
    cases x; cases y; simp * at *,
    exact and.decidable
end

-- Note: for lack of support for nested inductive types, 
-- you can't switch (fin n → pre_term) for (vector pre_term n) in the definition.
-- See: https://leanprover-community.github.io/archive/113488general/48465nestedinductivetype.html
inductive pre_term
| var : tvariable → pre_term
| app  {n : ℕ} (f : nary n) (v : fin n → pre_term) :  pre_term

def pre_tem.const : const → pre_term
| c := pre_term.app c fin_zero_elim

#check nat.decidable_eq
#check cast

instance deq_pre_term : decidable_eq pre_term :=
begin
    intros x y,
    -- ⟨f_y, fy_in_σ, fy_arity⟩
    rcases x with x_var | ⟨n_x, f_x, x_v⟩;
    rcases y with y_var | ⟨n_y, f_y, y_v⟩;
    simp * at *;
    try{apply_instance},
    suffices h : decidable (f_x == f_y ∧ x_v == y_v),
        from @and.decidable _ _ _ h,
    tidy,
    admit,
    -- have c 
    --     := (@subtype.decidable_eq functional_symbol 
    --     (λ f, f ∈ σ.sf ∧ arity f = n_x) _),
    -- suffices h : decidable (x_v == y_v),
    --     from @and.decidable _ _ c h,

    -- have c : decidable (⟨f_x_val, _⟩ == ⟨f_y_val, _⟩),
    -- obtain c₁ | c₂ := nat.decidable_eq n_x n_y,
    --     -- left, rintro ⟨h₁, h₂⟩,
    --     suffices h : decidable (x_v == y_v),
    --         from @and.decidable _ _ _ h,
    --     have c : f_x.property.right == f_y.property.right
    --         := h₁,
            
            -- simp [h.left, eq.substr],
    --     refine @and.decidable _ _ _ _,
    -- have c₀ : decidable (f_x == f_y),
    --     cases h₀ : f_x with val prop,
    --     cases prop with p₁ p₂,
    --     cases nat.decidable_eq n_x n_y,
    --         work_on_goal 1 {rw h at p₂, apply_instance}
        
        -- exact (
        --     if hyp : n_x = n_y
        --     then by {
        --         rw hyp at p₂, 
        --         replace f_x : nary n_y
        --         exact logic.deq_nary n_x
        --     }
        --     else admit
        -- ),
    -- have c : decidable (f_x == f_y ∧ x_v == y_v),
    --     admit,
    -- assumption
end

-- My original inclination was to write:
-- | (pre_term.app f v) := pre_term.app f (pre_term.rewrite ∘ v)
-- But apparently lean doesn't reduce the ∘ that easily.

def pre_term.rewrite (x : tvariable) (t : pre_term) : pre_term → pre_term
| (pre_term.var a) := if x = a then t else pre_term.var a
| (pre_term.app f v) := 
    let v₂ := λ m, pre_term.rewrite (v m) in
    pre_term.app f v₂

def pre_term.variables : pre_term → set tvariable
| (pre_term.var a) := {a}
| (pre_term.app f v) :=
    let v₂ := λ m, pre_term.variables (v m) in
    ⋃ m, v₂ m

def pre_term.list_variables : list pre_term → set tvariable
| [] := ∅
| (hd :: tl) := pre_term.variables hd ∪ pre_term.list_variables tl

def pre_term.denotes (t : pre_term) :=
    pre_term.variables t = ∅

def typing : pre_term → sort
| (pre_term.var ⟨s, _, _⟩) := s
| (pre_term.app f _) := f.val.codomain

def type_check {n} (l : list sort) (v : fin n → pre_term) : Prop :=
map typing (of_fn v) = l

inductive consistently_typed : pre_term → Prop
| base {x : tvariable} : consistently_typed (pre_term.var x)
| app {n : ℕ} (f : nary n) (v : fin n → pre_term) 
    (h₀ : ∀ x, consistently_typed (v x)) (h₁ : type_check f.val.domain v) 
    : consistently_typed (pre_term.app f v) 

structure term :=
    (syntax : pre_term)
    (check : consistently_typed syntax)

def type_matches (x : tvariable) (t : term) :=
    typing (pre_term.var x) = typing (t.syntax)

-- typing (pre_term.var x) = typing t₁.syntax →
theorem rewrite_consistent : ∀ (x : tvariable) (t₁ t₂ : term) (h : type_matches x t₁), consistently_typed (pre_term.rewrite x t₁.syntax t₂.syntax) :=
begin
    intros x t₁ t₂ h,
    induction (t₁.syntax.rewrite x t₂.syntax),
        exact consistently_typed.base,
    simp at *,
    refine consistently_typed.app f v ih _,
    unfold type_check,
    induction c : (of_fn v),
        simp [c] at *,
        ext,
        admit,
    admit
end

def term.rewrite (x : tvariable) (t : term) (h : type_matches x t) : term → term :=
begin
    intro target,
    fsplit,
    exact t.syntax.rewrite x target.syntax,
    exact rewrite_consistent x t target h,
end

-- term typing
def ttyping : term → sort
| t := typing t.syntax

lemma term.rewrite_typing (x : tvariable) (t₁ : term) (h : type_matches x t₁)
                          (t₂ : term)
                          : ttyping (t₁.rewrite x h t₂) =  ttyping t₂ :=
sorry

-- term type_check
def ttc {n} (l : list sort) (v : fin n → term) : Prop :=
map ttyping (of_fn v) = l

structure name extends term :=
    (denotative : pre_term.denotes syntax)

structure expression extends term :=
    (has_var : ¬ pre_term.denotes syntax)

inductive atomic_formula
| relational {n : ℕ} (r : nrary n) (v : fin n → term)
    (h : ttc r.val.sig v) : atomic_formula
| equation (t₁ t₂ : term) : atomic_formula
| true : atomic_formula
| false : atomic_formula

def atomic_formula.variables : atomic_formula → set tvariable
| (atomic_formula.relational r v h) :=
    let  v₂ := term.syntax ∘ v
    in pre_term.list_variables (of_fn v₂)
| (atomic_formula.equation t₁ t₂) := 
    pre_term.variables t₁.syntax
    ∪ pre_term.variables t₂.syntax
| _ := ∅

open list

def atomic_formula.rewrite (x : tvariable) (t : term) (h₀ : type_matches x t) : atomic_formula → atomic_formula
| (@atomic_formula.relational _ _ _ n r v h) := 
    let v₂ := (term.rewrite x t h₀) ∘ v in
    begin
    refine atomic_formula.relational r v₂ _,
    simp [ttc] at *,
    cases c : of_fn v,
        rw c at h,
        simp at h,
        replace h := eq.symm h,
        have neq :=  r.val.sig_not_empty,
        contradiction,
    rw [←h],
    have conc := t.rewrite_typing x h₀,
    -- cases c₂ : of_fn v₂,
    -- simp, library_search,
    -- simp [v₂,  c, function.comp],
    ext, constructor; intro hyp;
    simp * at *,
    rcases hyp with ⟨y, hyp₁, hyp₂⟩,
        simp [v₂] at *,
    
        
        
    -- suffices c : 
    --     map ttyping (of_fn v₂)
    --     = map ttyping (of_fn v),
    --     dsimp [ttc] at *,
    --     rw c,
    --     exact h,
    -- dsimp [map],
    -- ext, constructor; intro hyp;
    -- simp * at *;
    -- rcases hyp with ⟨x, hyp₁, hyp₂⟩,
    --     existsi x,
    --     simp [v₂, hyp₂] at *,
    -- admit,
    end
| (atomic_formula.equation t₁ t₂) := 
    let t₁ := t.rewrite x h₀ t₁,
        t₂ := t.rewrite x h₀ t₂ 
    in atomic_formula.equation t₁ t₂
| φ := φ


inductive pre_formula
| atomic : atomic_formula → pre_formula 
| for_all :  tvariable → pre_formula → pre_formula
| exist   : tvariable → pre_formula → pre_formula
| and : pre_formula → pre_formula → pre_formula
| or : pre_formula → pre_formula → pre_formula
| if_then : pre_formula → pre_formula → pre_formula

def pre_formula.is_atomic : pre_formula → Prop
| (logic.pre_formula.atomic _) := true
| _ := false

def pre_formula.is_molecular : pre_formula → Prop
| (logic.pre_formula.atomic _) := true
| (logic.pre_formula.and φ ψ) :=
    pre_formula.is_molecular φ
    ∧ pre_formula.is_molecular ψ
| (logic.pre_formula.or φ ψ) :=
    pre_formula.is_molecular φ
    ∧ pre_formula.is_molecular ψ
| (logic.pre_formula.if_then φ ψ) :=
    pre_formula.is_molecular φ
    ∧ pre_formula.is_molecular ψ
| _ := false

def pre_formula.free_variables : pre_formula → set tvariable
| (logic.pre_formula.atomic φ) := atomic_formula.variables φ
| (logic.pre_formula.for_all x φ) := pre_formula.free_variables φ - {x}
| (logic.pre_formula.exist x φ) := pre_formula.free_variables φ - {x}
| (logic.pre_formula.and φ ψ) := 
    pre_formula.free_variables φ 
    ∪ pre_formula.free_variables ψ
| (logic.pre_formula.or φ ψ) :=
    pre_formula.free_variables φ 
    ∪ pre_formula.free_variables ψ
| (logic.pre_formula.if_then φ ψ) :=
    pre_formula.free_variables φ 
    ∪ pre_formula.free_variables ψ

def pre_formula.bound_variables : pre_formula → set tvariable
| (logic.pre_formula.atomic φ) := ∅
| (logic.pre_formula.for_all x φ) := pre_formula.bound_variables φ ∪ {x}
| (logic.pre_formula.exist x φ) := pre_formula.bound_variables φ ∪ {x}
| (logic.pre_formula.and φ ψ) := 
    pre_formula.bound_variables φ 
    ∩ pre_formula.bound_variables ψ
| (logic.pre_formula.or φ ψ) :=
    pre_formula.bound_variables φ 
    ∩ pre_formula.bound_variables ψ
| (logic.pre_formula.if_then φ ψ) :=
    pre_formula.bound_variables φ 
    ∩ pre_formula.bound_variables ψ

def pre_formula.rewrite (x : tvariable) (t : pre_term) : pre_formula → pre_formula
| (logic.pre_formula.atomic a) := _
| (logic.pre_formula.for_all a a_1) := _
| (logic.pre_formula.exist a a_1) := _
| (logic.pre_formula.and a a_1) := _
| (logic.pre_formula.or a a_1) := _
| (logic.pre_formula.if_then a a_1) := _


inductive well_formed : pre_formula → Prop
| atomic (φ : atomic_formula) : well_formed (pre_formula.atomic φ)
| for_all (x : tvariable) (φ : pre_formula)
          (h₁ : well_formed φ) (h₂ : x ∈ pre_formula.free_variables φ)
          : well_formed (pre_formula.for_all x φ)
| exist   (x : tvariable) (φ : pre_formula)
          (h₁ : well_formed φ) (h₂ : x ∈ pre_formula.free_variables φ)
          : well_formed (pre_formula.exist x φ)
| and (φ ψ : pre_formula)
      (h₁ : well_formed φ)
      (h₂ : well_formed ψ)
      : well_formed (pre_formula.and φ ψ)
| or (φ ψ : pre_formula)
     (h₁ : well_formed φ)
     (h₂ : well_formed ψ) 
     : well_formed (pre_formula.or φ ψ)
| if_then (φ ψ : pre_formula)
          (h₁ : well_formed φ)
          (h₂ : well_formed ψ) 
          : well_formed (pre_formula.if_then φ ψ)


structure wff :=
    (formula : pre_formula)
    (well_formed : well_formed formula)

def wff.and : wff → wff → wff
| ⟨φ, h₁⟩ ⟨ψ, h₂⟩ := ⟨pre_formula.and φ ψ,
                      well_formed.and φ ψ h₁ h₂⟩

def wff.or : wff → wff → wff
| ⟨φ, h₁⟩ ⟨ψ, h₂⟩ := ⟨pre_formula.or φ ψ,
                      well_formed.or φ ψ h₁ h₂⟩

def wff.if_then : wff → wff → wff
| ⟨φ, h₁⟩ ⟨ψ, h₂⟩ := ⟨pre_formula.if_then φ ψ,
                      well_formed.if_then φ ψ h₁ h₂⟩
def wff.true : wff :=
{ formula := pre_formula.atomic atomic_formula.true,
  well_formed := well_formed.atomic _ 
}

instance wff.has_exp : has_exp wff := ⟨wff.if_then⟩

def assertive (φ : pre_formula) := pre_formula.free_variables φ = ∅
def conotative (φ : pre_formula) := ¬ assertive φ

structure sentence extends wff :=
    (assertive : assertive formula)

structure predicate extends wff :=
    (conotative : conotative formula)

-- theorem finite_num_var : ∀ φ : pre_formula, finite (pre_formula.free_variables φ) := 
-- begin 
--     intros φ,
--     repeat {induction φ},
--     -- repeat {fsplit},
--     -- unfold multiset,
--     -- work_on_goal 2 { intros x,
--     -- cases x,
--     -- simp at * },
-- end

inductive wff.entails : set wff → wff → Prop
| reflexive (Γ : set wff) (φ : wff)(h : φ ∈ Γ) : wff.entails Γ φ
| transitivity (Γ Δ : set wff) (φ : wff)
               (h₁ : ∀ ψ ∈ Δ, wff.entails Γ ψ)
               (h₂ : wff.entails Δ φ) :  wff.entails Γ φ
| and_intro (φ ψ : wff) (Γ : set wff)
            (h₁ : wff.entails Γ φ)
            (h₂ : wff.entails Γ ψ)
             : wff.entails Γ (wff.and φ ψ)
| and_elim_left (φ ψ : wff) (Γ : set wff)
            (h : wff.entails Γ (wff.and φ ψ))
             : wff.entails Γ φ
| and_elim_right (φ ψ : wff) (Γ : set wff)
            (h : wff.entails Γ (wff.and φ ψ))
             : wff.entails Γ ψ
| or_intro_left 
            (φ ψ : wff) (Γ : set wff)
            (h : wff.entails Γ φ)
             : wff.entails Γ (wff.or φ ψ)
| or_intro_right 
            (φ ψ : wff) (Γ : set wff)
            (h : wff.entails Γ ψ)
             : wff.entails Γ (wff.or φ ψ)
| or_elim
            (φ ψ δ : wff) (Γ : set wff)
            (h₁ : wff.entails Γ (wff.or φ ψ))
            (h₂ : wff.entails (Γ ∪ {φ}) δ)
            (h₃ : wff.entails (Γ ∪ {ψ}) δ)
             : wff.entails Γ δ
| modus_ponens
            (φ ψ : wff) (Γ : set wff)
            (h₁ : wff.entails Γ (φ ⇒ ψ))
            (h₂ : wff.entails Γ φ)
             : wff.entails Γ ψ
| intro
            (φ ψ : wff) (Γ : set wff)
            (h : wff.entails (Γ ∪ {φ}) ψ)
             : wff.entails Γ (φ ⇒ ψ)
| true_intro
            (Γ : set wff)
             : wff.entails Γ wff.true
| true_intro
            (Γ : set wff) (φ : wff)
            (x : tvariable)
            (free : x ∈ pre_formula.free_variables φ.formula)
            (h : ∀ t : term wff.entails (Γ ∪ {φ}) ψ)
             : wff.entails Γ wff.true

-- let l := of_fn v in
-- map typing l = f.val.domain
-- ∧ ∀ x ∈ l, consistently_typed x

-- begin
--     cases h : f.val.domain, exact true,
--     cases hyp : n with n₀, exact true,
--     have wfr : n₀ < n, -- for proving well-founded recursion
--         rw hyp, 
--         exact nat.lt_succ_self n₀,
--     have c := nat.zero_lt_succ n₀,
--     have z : fin (nat.succ n₀) := ⟨0, c⟩,
--     refine typing _ = [hd] ∧ consistently_typed _,
--         rw hyp at v, exact (v z),
--     right, work_on_goal 2 {exact n₀},
--     constructor, 
--     work_on_goal 1{
--         constructor,
--         exact f.val.name ++ "tail",
--         exact tl,
--         exact f.val.codomain,
--     },
--         constructor,
--         have c₂ := (σ.head_project f.val f.property.left),
--         simp [tail_symbol] at c₂,
--         rwa h at c₂,
--         simp [arity],
--         replace c₂ : tl = tail f.val.domain,
--             simp [h],
--         simp [c₂],
--         replace c₂ : length f.val.domain = n := f.property.right,
--         rw [c₂, hyp],
--         refl,
--     rintros ⟨x, hx⟩,
--     refine v ⟨x+1, _⟩, rw hyp,
--     exact nat.lt_succ_iff.mpr hx
-- end
-- using_well_founded { rel_tac := _,
-- dec_tac := `[rw hyp, exact nat.lt_succ_self n₀] }

end basic
end logic