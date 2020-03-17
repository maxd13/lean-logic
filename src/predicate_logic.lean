import formal_system data.set.finite init.data.list tactic.find
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

def tail_symbol (f : functional_symbol) : functional_symbol :=
{ name := f.name ++ "tail_",
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
    -- (head_project : ∀ f ∈ sf, tail_symbol f ∈ sf)

section terms
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
-- you can't switch (fin n → uterm) for (vector uterm n) in the definition.
-- See: https://leanprover-community.github.io/archive/113488general/48465nestedinductivetype.html
-- This is the type of untyped terms of the signature, which is to say that they are terms but we don't
-- pay attention to their type, only the arity of the signature functions matters.
-- We can later introduce typed terms by type checking the untyped ones.
inductive uterm
| var : tvariable → uterm
| app  {n : ℕ} (f : nary n) (v : fin n → uterm) :  uterm

-- constant terms.
def const.uterm : const → uterm
| c := uterm.app c fin_zero_elim

def uterm.app_vector {n : ℕ} (f : nary n) (v : vector uterm n) : uterm :=
    uterm.app f (λ m, v.nth m)

-- syntatic equality between untyped terms.
instance deq_uterm : decidable_eq uterm :=
begin
    intros x y,
    -- ⟨f_y, fy_in_σ, fy_arity⟩
    rcases x with x_var | ⟨n_x, f_x, x_v⟩;
    rcases y with y_var | ⟨n_y, f_y, y_v⟩;
    simp * at *;
    try{apply_instance},
    suffices h : decidable (f_x == f_y ∧ x_v == y_v),
        from @and.decidable _ _ _ h,
    -- rcases f_x with ⟨f_x, _, _⟩,
    -- rcases f_y with ⟨f_y, _, _⟩,
    -- suffices h : decidable (x_v == y_v),
    --     from @and.decidable _ _ _ h,
    have h : decidable(f_x == f_y) := ( 
        if z : n_x = n_y 
        then by {
            have teq : nary n_x = nary n_y,
                rw z,
            let f := cast teq f_x,
            have h : f == f_x := cast_heq teq f_x,
            have deq : decidable (f == f_y),
                cases logic.deq_nary n_y f f_y with c₁ c₂,
                    left, intro hyp,
                    have c := eq_of_heq hyp,
                    contradiction,
                right,
                exact heq_of_eq c₂,
            cases deq,
                left, intro hyp,
                have c := heq.trans h hyp,
                contradiction,
            right,
            replace h := heq.symm h,
            exact heq.trans h deq
        }
            -- exact @and.decidable _ _ deq h}
        else by {
            left, intro h,
            let f := λ (n : ℕ) (x : nary n), (@arity sort _)(subtype.val x) = n_x,
                work_on_goal 1 {exact σ},
            -- have c := type_eq_of_heq h, 

            have c₁ : (f n_x f_x) := f_x.property.right,
            -- have c := heq.subst h c₁,
                -- @heq.elim (nary n_x) f_x f f_y h c₁,
            -- let f := cast c f_x,
            -- have z : f == f_x := cast_heq c f_x,
            -- apply heq.rec_on h,

            have c₂ := f_y.property.right,
            admit
        }
    ),
        
    -- have h : decidable(f_x == f_y),
        -- tidy,
        -- suffices h : decidable (x_v == y_v),
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
-- | (uterm.app f v) := uterm.app f (uterm.rewrite ∘ v)
-- But apparently lean doesn't reduce the ∘ that easily.

def uterm.rewrite : uterm → tvariable → uterm → uterm
| (uterm.var a) x t := if x = a then t else uterm.var a
| (uterm.app f v) x t := 
    let v₂ := λ m, uterm.rewrite (v m) x t in
    uterm.app f v₂

def uterm.variables : uterm → set tvariable
| (uterm.var a) := {a}
| (uterm.app f v) :=
    let v₂ := λ m, uterm.variables (v m) in
    ⋃ m, v₂ m

lemma uterm.nvar_rw (τ : uterm) (x : tvariable) (t : uterm) : x ∉ τ.variables → τ.rewrite x t = τ :=
begin
    intros h,
    induction τ;
    dunfold uterm.rewrite,
        have c : x ∉ {τ} := h,
        simp at c,
        simp [c],
    simp,
    ext m,
    apply τ_ih m,
    have c : x ∉ ⋃ m, (τ_v m).variables := h,
    simp at c,
    exact c m
 end


lemma uterm.nvar_rw₂ (τ : uterm) (x y : tvariable) (t : uterm) (h : y ∈ τ.variables) : x ≠ y → y ∈ (τ.rewrite x t).variables :=
begin
    intro hyp,
    induction τ;
    dunfold uterm.rewrite,
        replace h : y ∈ {τ} := h,
        simp at h,
        by_cases c : x = τ,
            rw ←h at c,
            contradiction,
        simp [c],
        dunfold uterm.variables,
        simp [h],
    dunfold uterm.variables,
    simp,
    have c : y ∈ ⋃ m, (τ_v m).variables := h,
    simp at c,
    cases c with i c,
    existsi i,
    apply τ_ih i,
    exact c
end

def list_variables : list uterm → set tvariable
| [] := ∅
| (hd :: tl) := hd.variables  ∪ list_variables tl

def list_rewrite : list uterm → tvariable → uterm → list uterm
| [] _ _:= ∅
| (hd :: tl) x t := (hd.rewrite x t) :: list_rewrite tl x t

def fn_rewrite {n : ℕ} (v : fin n → uterm) : tvariable → uterm → list uterm :=
    list_rewrite (of_fn v)

def vector_rewrite {n : ℕ} : vector uterm n → tvariable → uterm → vector uterm n
| v x t := ⟨list_rewrite v.val x t, by admit⟩

lemma list_variables_nvar_rw₂ (xs : list uterm) (x y : tvariable) (t : uterm) (h : y ∈ list_variables xs) : x ≠ y → y ∈ list_variables (list_rewrite xs x t) :=
begin
    intro hyp,
    induction xs with hd tl ih,
        replace h : false := h,
        contradiction,
    dunfold list_rewrite list_variables,
    cases h,
        left,
        exact hd.nvar_rw₂ x y t h hyp,
    right,
    exact ih h
end


def uterm.denotes (t : uterm) :=
    uterm.variables t = ∅

-- untyped atomic formulas.
inductive uatomic_formula
| relational {n : ℕ} (r : nrary n) (v : fin n → uterm) : uatomic_formula
| equation (t₁ t₂ : uterm) : uatomic_formula
| true : uatomic_formula
| false : uatomic_formula

def uatomic_formula.variables : uatomic_formula → set tvariable
| (uatomic_formula.relational r v) := list_variables (of_fn v)
| (uatomic_formula.equation t₁ t₂) := t₁.variables  ∪ t₂.variables
| _ := ∅

def uatomic_formula.rewrite : uatomic_formula → tvariable → uterm → uatomic_formula
| (uatomic_formula.relational r v) x t :=
    let v₂ := λ m, (v m).rewrite x t in
    uatomic_formula.relational r v₂
| (uatomic_formula.equation t₁ t₂) x t :=
    let t₃ := t₁.rewrite x t,
        t₄ := t₂.rewrite x t
    in uatomic_formula.equation t₃ t₄
| φ _ _ := φ

lemma uatomic_formula.nvar_rw₂ (φ : uatomic_formula) (x y : tvariable) (t : uterm) (h : y ∈ φ.variables) : x ≠ y → y ∈ (φ.rewrite x t).variables :=
begin
    intro hyp,
    induction φ;
    -- any_goals {
    --     replace h : y ∈ list_variables (of_fn φ_v) := h,
    --     have c := list_variables_nvar_rw₂ (of_fn φ_v) x y t h hyp,
    -- };
    dunfold uatomic_formula.rewrite;
    simp * at *,
        dunfold uatomic_formula.variables,
        replace h : y ∈ list_variables (of_fn φ_v) := h,
        have c := list_variables_nvar_rw₂ (of_fn φ_v) x y t h hyp,
        cases c₀ : (of_fn φ_v),
            rw c₀ at h,
            simp [list_variables] at h,
            contradiction,
    -- rw c₀ at c,
    -- revert c,
    -- dunfold list_rewrite list_variables,
    -- rintro (c₁ | c₂),
    convert c,
    ext m, constructor; intro h₂,

        
    

end

-- untyped formulas. 
-- Not requiring quantified variables to be free.
inductive uformula
| atomic : uatomic_formula → uformula 
| for_all :  tvariable → uformula → uformula
| exist   : tvariable → uformula → uformula
| and : uformula → uformula → uformula
| or : uformula → uformula → uformula
| if_then : uformula → uformula → uformula

def uformula.is_atomic : uformula → Prop
| (uformula.atomic _) := true
| _ := false

instance uformula.lift : has_lift uatomic_formula uformula := ⟨uformula.atomic⟩

def uformula.is_molecular : uformula → Prop
| (uformula.atomic _)    :=  true
| (uformula.and φ ψ)     :=  φ.is_molecular ∧ ψ.is_molecular
| (uformula.or φ ψ)      :=  φ.is_molecular ∧ ψ.is_molecular
| (uformula.if_then φ ψ) :=  φ.is_molecular ∧ ψ.is_molecular
| _ := false

-- free variables
def uformula.free : uformula → set tvariable
| (uformula.atomic φ)    := φ.variables 
| (uformula.for_all x φ) := φ.free - {x}
| (uformula.exist x φ)   := φ.free - {x}
| (uformula.and φ ψ)     := φ.free ∪ ψ.free
| (uformula.or φ ψ)      := φ.free ∪ ψ.free
| (uformula.if_then φ ψ) := φ.free ∪ ψ.free 

-- open and closed formulas.
def uformula.closed : uformula → Prop
| φ := φ.free = ∅

def uformula.open : uformula → Prop
| φ := ¬ φ.closed

-- instance dec_free (φ : uformula) : decidable_pred φ.free :=
-- begin 
--     intros x,
--     cases φ,
    
--     -- try{apply_instance},
-- end

def uformula.variables : uformula → set tvariable
| (uformula.atomic φ)    := φ.variables 
| (uformula.for_all x φ) := φ.free ∪ {x}
| (uformula.exist x φ)   := φ.free ∪ {x}
| (uformula.and φ ψ)     := φ.variables ∪ ψ.variables
| (uformula.or φ ψ)      := φ.variables ∪ ψ.variables
| (uformula.if_then φ ψ) := φ.variables ∪ ψ.variables

-- def uformula.bound_variables : uformula → set tvariable
-- | (logic.uformula.atomic φ) := ∅
-- | (logic.uformula.for_all x φ) := uformula.bound_variables φ ∪ {x}
-- | (logic.uformula.exist x φ) := uformula.bound_variables φ ∪ {x}
-- | (logic.uformula.and φ ψ) := 
--     uformula.bound_variables φ 
--     ∩ uformula.bound_variables ψ
-- | (logic.uformula.or φ ψ) :=
--     uformula.bound_variables φ 
--     ∩ uformula.bound_variables ψ
-- | (logic.uformula.if_then φ ψ) :=
--     uformula.bound_variables φ 
--     ∩ uformula.bound_variables ψ

def uformula.rewrite : uformula → tvariable → uterm → uformula
| (uformula.atomic φ) x t    := ↑(φ.rewrite x t)
| (uformula.for_all y φ) x t :=
    let ψ := if y = x then φ else φ.rewrite x t in
    uformula.for_all y ψ
| (uformula.exist y φ) x t := 
    let ψ := if y = x then φ else φ.rewrite x t in
    uformula.exist y ψ
| (uformula.and φ ψ) x t     := uformula.and (φ.rewrite x t) (ψ.rewrite x t)
| (uformula.or φ ψ)  x t     := uformula.or (φ.rewrite x t) (ψ.rewrite x t)
| (uformula.if_then φ ψ) x t := uformula.if_then (φ.rewrite x t) (ψ.rewrite x t)

-- lemma uformula.rw_free : ∀ (φ : uformula) (x : tvariable) (t : uterm), φ.free - {x} ⊆ (φ.rewrite x t).free :=
-- begin
--  intros φ x t y h,
--  cases h with h₁ h₂,
--  simp at *,
--  cases φ;
--  dunfold uformula.rewrite,
--  replace h₁ : y ∈ (uatomic_formula.relational φ_r φ_v).variables := h₁,

 
-- --  dunfold uformula.free at h₁,
-- --  dunfold uterm.rewrite,
 
-- --  dunfold ,
-- end

-- -- rewriting a bound variable is the same as keeping the formula as it is.
-- lemma uformula.rw_bnd (x : tvariable) (t : uterm) (φ : uformula) : x ∉ φ.free → φ.rewrite x t = φ :=
-- begin
--     intros h,
--     induction φ,
--     replace h : x ∉ φ.variables := h, 
-- end

lemma uformula.rw_bnd (x y : tvariable) (t : uterm) (φ : uformula) (h : y ∈ φ.free) : x ≠ y → y ∈ (φ.rewrite x t).free :=
begin
    intro hyp,
    induction φ;
    dunfold uformula.rewrite;
    simp * at *,
        focus {
            -- exact list_variables_nvar_rw₂,
            -- dunfold uformula.lift,
            -- admit
            -- dunfold uformula.free,
        },
    all_goals {cases h with h₁ h₂},
    any_goals {
        by_cases c : φ_a = x;
        simp [c];
        dunfold uformula.free,
        rw c at h₂,
        exact ⟨h₁, h₂⟩,
    simp [h₂],
    apply φ_ih,
    exact h₁,
    },
    all_goals {
        dunfold uformula.free,
        {left, apply φ_ih_a, assumption} <|>
        {right, apply φ_ih_a_1, assumption},
    }
end


-- checks whether variables bound by a quantifier are free in the rest of the expression.
def uformula.well_formed : uformula → Prop
| (uformula.atomic φ)    := true
| (uformula.for_all x φ) := x ∈ φ.free ∧ φ.well_formed
| (uformula.exist x φ)   := x ∈ φ.free ∧ φ.well_formed
| (uformula.and φ ψ)     := φ.well_formed ∧ ψ.well_formed
| (uformula.or φ ψ)      := φ.well_formed ∧ ψ.well_formed
| (uformula.if_then φ ψ) := φ.well_formed ∧ ψ.well_formed

-- The type of untyped well formed formulas.
def uwff := subtype uformula.well_formed

-- utilities
def uwff.and : uwff → uwff → uwff
| ⟨φ, h₁⟩ ⟨ψ, h₂⟩ := ⟨uformula.and φ ψ,
                      by constructor; assumption⟩

def uwff.or : uwff → uwff → uwff
| ⟨φ, h₁⟩ ⟨ψ, h₂⟩ := ⟨uformula.or φ ψ,
                      by constructor; assumption⟩

def uwff.if_then : uwff → uwff → uwff
| ⟨φ, h₁⟩ ⟨ψ, h₂⟩ := ⟨uformula.if_then φ ψ,
                      by constructor; assumption⟩

instance uwff.has_exp : has_exp uwff := ⟨uwff.if_then⟩

instance uwff.lift : has_lift uatomic_formula uwff := ⟨λ φ, ⟨↑φ, true.intro⟩⟩

def uwff.true : uwff := ↑uatomic_formula.true
def uwff.false : uwff := ↑uatomic_formula.false

def uwff.free (φ : uwff) := φ.val.free

def uwff.for_all (x : tvariable) (φ : uwff) (h : x ∈ φ.free) : uwff := 
    ⟨uformula.for_all x φ.val, ⟨h, φ.property⟩⟩

def uwff.exist (x : tvariable) (φ : uwff) (h : x ∈ φ.free) : uwff := 
    ⟨uformula.exist x φ.val, ⟨h, φ.property⟩⟩

def uwff.rewrite (x : tvariable) (t : uterm) : uwff → uwff
| ⟨φ, h⟩ := 
⟨φ.rewrite x t,
begin
    -- induction φ.rewrite x t,
    -- exact true.intro,
    induction φ,
    exact true.intro,
    all_goals {dunfold uformula.rewrite},
        by_cases c : φ_a = x;
        simp [c],
        rw ←c,
        exact h,
        refine and.intro _ (φ_ih h.2),
        cases φ_a_1,
        try{dunfold uformula.rewrite},
        
    
    
    -- cases h with h₁ h₂,
    -- have c := φ_ih h₂,
    -- obtain c₁ | c₂ : decidable (φ_a = x),
    --     by apply_instance,
    -- dunfold uformula.rewrite,
    -- -- constructor,
    -- simp [c₁],
    -- constructor,
    -- dunfold uformula.free,
    -- cases 
      --  logic.deq_tvariable,
    -- constructor;
    
    -- cases h₂ : ψ;
    -- constructor;
    
    -- any_goals {assumption},

end⟩

-- deductive consequence of uwffs: Γ ⊢ φ
inductive uwff.entails : set uwff → uwff → Prop
| reflexive (Γ : set uwff) (φ : uwff)(h : φ ∈ Γ) : uwff.entails Γ φ
| transitivity (Γ Δ : set uwff) (φ : uwff)
               (h₁ : ∀ ψ ∈ Δ, uwff.entails Γ ψ)
               (h₂ : uwff.entails Δ φ) :  uwff.entails Γ φ
| and_intro (φ ψ : uwff) (Γ : set uwff)
            (h₁ : uwff.entails Γ φ)
            (h₂ : uwff.entails Γ ψ)
             : uwff.entails Γ (uwff.and φ ψ)
| and_elim_left (φ ψ : uwff) (Γ : set uwff)
            (h : uwff.entails Γ (uwff.and φ ψ))
             : uwff.entails Γ φ
| and_elim_right (φ ψ : uwff) (Γ : set uwff)
            (h : uwff.entails Γ (uwff.and φ ψ))
             : uwff.entails Γ ψ
| or_intro_left 
            (φ ψ : uwff) (Γ : set uwff)
            (h : uwff.entails Γ φ)
             : uwff.entails Γ (uwff.or φ ψ)
| or_intro_right 
            (φ ψ : uwff) (Γ : set uwff)
            (h : uwff.entails Γ ψ)
             : uwff.entails Γ (uwff.or φ ψ)
| or_elim
            (φ ψ δ : uwff) (Γ : set uwff)
            (h₁ : uwff.entails Γ (uwff.or φ ψ))
            (h₂ : uwff.entails (Γ ∪ {φ}) δ)
            (h₃ : uwff.entails (Γ ∪ {ψ}) δ)
             : uwff.entails Γ δ
| modus_ponens
            (φ ψ : uwff) (Γ : set uwff)
            (h₁ : uwff.entails Γ (φ ⇒ ψ))
            (h₂ : uwff.entails Γ φ)
             : uwff.entails Γ ψ
| intro
            (φ ψ : uwff) (Γ : set uwff)
            (h : uwff.entails (Γ ∪ {φ}) ψ)
             : uwff.entails Γ (φ ⇒ ψ)
| true_intro
            (Γ : set uwff)
             : uwff.entails Γ uwff.true
| for_all_elim
            (Γ : set uwff) (φ : uwff)
            (x : tvariable)
            (free : x ∈ φ.free)
            (h : uwff.entails Γ (uwff.for_all x φ free))
            (t : uterm)
             : uwff.entails Γ uwff.true






end terms
end basic
end logic