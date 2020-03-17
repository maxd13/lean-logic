import formal_system tactic.find --init.data.list
universe u

-- We introduce a much simplified version of
-- untyped first order (minimal) predicate logic.

-- make all propositions decidable. 
-- Allows us to freely use ifs like in Haskell
-- but then we must add noncomputable to all functions
-- local attribute [instance] classical.prop_decidable


namespace logic

open logic list tactic set

section formulas
parameters {functional_symbol : Type u} [decidable_eq functional_symbol]
parameter {relational_symbol : Type u}
parameters {tvariable : Type u} [decidable_eq tvariable]
parameter {var_ne : nonempty tvariable}
-- parameters {var_index : ℕ → tvariable} {inj : function.injective var_index}
parameters {abstract_var : Type u} [decidable_eq abstract_var]
-- parameter {abs_ne : nonempty abstract_var}
parameter {arity : functional_symbol -> ℕ}
parameter {rarity : relational_symbol -> ℕ}

-- arity types
def is_constant (f : functional_symbol) := arity f = 0
def nary (n : ℕ) := subtype {f : functional_symbol | arity f = n}
def nrary (n : ℕ) := subtype {r : relational_symbol | rarity r = n}
@[reducible]
def const := nary 0

-- terms in the language
inductive term
| var : tvariable → term
| abs : abstract_var → term
| app  {n : ℕ} (f : nary n) (v : fin n → term) :  term

-- constant terms.
def const.term : const → term
| c := term.app c fin_zero_elim

@[reducible]
def term.rw : term → tvariable → term → term
| (term.var a) x t := if x = a then t else term.var a
| (term.app f v) x t := 
    let v₂ := λ m, term.rw (v m) x t in
    term.app f v₂
| t _ _ := t

-- abstract rewrite
def term.arw : term → abstract_var → term → term
| (term.abs a) x t := if x = a then t else term.abs a
| (term.app f v) x t := 
    let v₂ := λ m, term.arw (v m) x t in
    term.app f v₂
| t _ _ := t

-- Syntatical equality. 
-- This is a trick to bypass the need to prove decidable_eq term
-- for using ifs.
-- The linter is unable to prove this terminates,
-- so we have to declare it as meta, unfortunately.
-- meta def term_seq : term → term → bool
-- | (term.var x) (term.var y) := if x = y then tt else ff
-- | (term.app f v₁) (term.app g v₂) :=
--     if f.val ≠ g.val then ff else
--     let zs := zip (of_fn v₁) (of_fn v₂),
--         unc := function.uncurry term_seq
--     in all zs unc
-- | _ _ := ff

-- can't be finished without decidable_eq term
-- previous fix can work as well but introduces this
-- as a meta def
-- meta def term.rwt : term → term → term → term
-- | (term.var a) (term.var x) t := if x = a then t else term.var a
-- -- | (term.var a) _ _ := (term.var a)
-- | (term.app f v) x t := 
--     if term_seq (term.app f v) x then t else
--     let v₂ := λ m, term.rwt (v m) x t in
--     term.app f v₂

-- So far I haven't figured out a better way
-- to tell LEAN to unfold definitions other than to mark
-- them as reducible.
-- If they are not reducible it is always a headache to get
-- the elaborator to unfold a definition when it doesn't want to,
-- sometimes using the simplifier works, other times not.
@[reducible]
def term.vars : term → set tvariable
| (term.var a) := {a}
| (term.app f v) :=
    let v₂ := λ m, term.vars (v m) in
    ⋃ m, v₂ m
| _ := ∅

-- theorem hidden_variables : ∀ t : term, ∃ x : tvariable, x ∉ t.vars :=
-- let i := var_index,
--     inj := inj
-- in
-- begin
--     intro t,
--     induction t,
--     -- case t is a variable
--         let indexed := ∃ n : ℕ, i n = t,
--         classical,
--         by_cases indexed,
--             obtain ⟨n, np⟩ := h,
--             existsi i (n + 1),
--             simp,
--             intro h,
--             rw [←np] at h,
--             have c₁ := inj h,
--             have c₀ : n + 1 ≠ n := nat.succ_ne_self n,
--             contradiction,
--         existsi i 0,
--         simp,
--         intro h₂,
--         apply h,
--         exact ⟨0, h₂⟩,
--     -- case t is an abstract variable
--         simp,
--         exact ⟨i 0, true.intro⟩,
--     -- case t is a function application
--         simp,
--         classical,
--         by_contradiction h,
--         replace h := not_exists.mp h,
--         -- replace h := not_forall.mp h,
-- end

@[reducible]
def term.denotes (t : term) := t.vars = ∅
@[reducible]
def term.conotes (t : term) := ¬ t.denotes
def term.concrete : term → Prop
| (term.var a) := true
| (term.abs a) := false
| (term.app f v) := ∀ m, term.concrete (v m)

-- a term in the proper sense of the term (pun intended).
def pterm := subtype {t : term | t.denotes ∧ t.concrete}
def expression := subtype {t : term | t.conotes ∧ t.concrete}

theorem den_rw : ∀ (t₁ t₂ : term) (x : tvariable), t₁.denotes → t₁.rw x t₂ = t₁ :=
begin
    intros t₁ t₂ x den₁,
    induction t₁,
    -- case var
        replace den₁ : (term.var t₁).vars = ∅ := den₁,
        replace den₁ : {t₁} = ∅ := den₁,
        simp at den₁, 
        contradiction,
    -- case abs_var 
        simp,
    -- case app
        replace den₁ : (term.app t₁_f t₁_v).vars = ∅ := den₁,
        let v₂ := λ m, (t₁_v m).vars,
        replace den₁ : (⋃ m, v₂ m) = ∅ := den₁,
        have c₀ : ∀ m, (v₂ m) = ∅,
            intro m,
            ext, constructor, intro h,
                simp,
                have c : x_1 ∈ (⋃ m, v₂ m), 
                    simp,
                    existsi m,
                    exact h,
                rwa den₁ at c,
            intro insanity,
            simp at insanity,
            contradiction,
        have c₁ : ∀ m, (t₁_v m).denotes := c₀,
        have c₂ : ∀ m, (t₁_v m).rw x t₂ = (t₁_v m),
            intro m,
            exact t₁_ih m (c₁ m),
        dunfold term.rw, 
        simp[c₂],
end

def term.subterms : term → set term
| (term.app f v) := 
    let v₂ := λ m, term.subterms (v m) in
    (⋃ m, v₂ m) ∪ {(term.app f v)}
| t := {t}

def list.vars : list term → set tvariable
| [] := ∅
| (hd :: tl) := hd.vars ∪ tl.vars

def list.subterms : list term → set term
| [] := ∅
| (hd :: tl) := hd.subterms ∪ tl.subterms

def list.rw : list term → tvariable → term → list term
| [] _ _:= ∅
| (hd :: tl) x t := (hd.rw x t) :: tl.rw x t

-- meta def list.rwt : list term → term → term → list term
-- | [] _ _:= ∅
-- | (hd :: tl) x t := (hd.rwt x t) :: tl.rwt x t

def subterms : set term → set term
| S := ⋃ x ∈ S, term.subterms x

-- formulas
inductive uformula
| relational {n : ℕ} (r : nrary n) (v : fin n → term) : uformula
| equation (t₁ t₂ : term) : uformula
| true : uformula
| false : uformula
| for_all :  tvariable → uformula → uformula
| exist   : tvariable → uformula → uformula
| and : uformula → uformula → uformula
| or : uformula → uformula → uformula
| if_then : uformula → uformula → uformula

instance uformula.has_exp : has_exp uformula := ⟨uformula.if_then⟩
@[reducible]
def uformula.rw : uformula → tvariable → term → uformula
| (uformula.relational r v) x t :=
    let v₂ := λ m, (v m).rw x t in
    uformula.relational r v₂
| (uformula.equation t₁ t₂) x t :=
    let t₃ := t₁.rw x t,
        t₄ := t₂.rw x t
    in uformula.equation t₃ t₄
| (uformula.for_all y φ) x t :=
    let ψ := if y = x then φ else φ.rw x t in
    uformula.for_all y ψ
| (uformula.exist y φ) x t := 
    let ψ := if y = x then φ else φ.rw x t in
    uformula.exist y ψ
| (uformula.and φ ψ) x t     := uformula.and (φ.rw x t) (ψ.rw x t)
| (uformula.or φ ψ)  x t     := uformula.or (φ.rw x t) (ψ.rw x t)
| (uformula.if_then φ ψ) x t := uformula.if_then (φ.rw x t) (ψ.rw x t)
| φ _ _ := φ

def uformula.arw : uformula → abstract_var → term → uformula
| (uformula.relational r v) x t :=
    let v₂ := λ m, (v m).arw x t in
    uformula.relational r v₂
| (uformula.equation t₁ t₂) x t :=
    let t₃ := t₁.arw x t,
        t₄ := t₂.arw x t
    in uformula.equation t₃ t₄
| (uformula.for_all y φ) x t := uformula.for_all y (φ.arw x t)
| (uformula.exist y φ) x t   := uformula.exist y (φ.arw x t)
| (uformula.and φ ψ) x t     := uformula.and (φ.arw x t) (ψ.arw x t)
| (uformula.or φ ψ)  x t     := uformula.or (φ.arw x t) (ψ.arw x t)
| (uformula.if_then φ ψ) x t := uformula.if_then (φ.arw x t) (ψ.arw x t)
| φ _ _ := φ

-- def uformula.rwt : uformula → term → term → uformula
-- | (uformula.relational r v) x t :=
--     let v₂ := λ m, (v m).rwt x t in
--     uformula.relational r v₂
-- | (uformula.equation t₁ t₂) x t :=
--     let t₃ := t₁.rwt x t,
--         t₄ := t₂.rwt x t
--     in uformula.equation t₃ t₄
-- | (uformula.for_all y φ) x t :=
--     let ψ := if term_seq (term.var y) x then φ else φ.rwt x t in
--     uformula.for_all y ψ
-- | (uformula.exist y φ) x t := 
--     let ψ := if y = x then φ else φ.rwt x t in
--     uformula.exist y ψ
-- | (uformula.and φ ψ) x t     := uformula.and (φ.rwt x t) (ψ.rwt x t)
-- | (uformula.or φ ψ)  x t     := uformula.or (φ.rwt x t) (ψ.rwt x t)
-- | (uformula.if_then φ ψ) x t := uformula.if_then (φ.rwt x t) (ψ.rwt x t)
-- | φ _ _ := φ


-- free variables
@[reducible]
def uformula.free : uformula → set tvariable
| (uformula.relational r v) := list.vars (of_fn v)
| (uformula.equation t₁ t₂) := t₁.vars  ∪ t₂.vars
| (uformula.for_all x φ) := φ.free - {x}
| (uformula.exist x φ)   := φ.free - {x}
| (uformula.and φ ψ)     := φ.free ∪ ψ.free
| (uformula.or φ ψ)      := φ.free ∪ ψ.free
| (uformula.if_then φ ψ) := φ.free ∪ ψ.free
| _ := ∅

-- open and closed formulas.
def uformula.closed : uformula → Prop
| φ := φ.free = ∅

def uformula.open : uformula → Prop
| φ := ¬ φ.closed

def uformula.vars : uformula → set tvariable
| (uformula.for_all x φ) := φ.free ∪ {x}
| (uformula.exist x φ)   := φ.free ∪ {x}
| (uformula.and φ ψ)     := φ.vars ∪ ψ.vars
| (uformula.or φ ψ)      := φ.vars ∪ ψ.vars
| (uformula.if_then φ ψ) := φ.vars ∪ ψ.vars
| φ := φ.free

def uformula.terms : uformula → set term
| (uformula.relational r v) := list.subterms (of_fn v)
| (uformula.equation t₁ t₂) := t₁.subterms ∪ t₂.subterms
| (uformula.for_all x φ) := φ.terms ∪ {term.var x}
| (uformula.exist x φ)   := φ.terms ∪ {term.var x}
| (uformula.and φ ψ)     := φ.terms ∪ ψ.terms
| (uformula.or φ ψ)      := φ.terms ∪ ψ.terms
| (uformula.if_then φ ψ) := φ.terms ∪ ψ.terms
| _ := ∅

def term.abstract_in : term → set uformula → Prop
| t S := t ∉ (⋃ φ ∈ S, uformula.terms φ)

def tvariable.abstract_in : tvariable → set uformula → Prop
| x S := x ∉ (⋃ φ ∈ S, uformula.vars φ)

-- deductive consequence of uformulas: Γ ⊢ φ in minimal logic
inductive minimal.entails : set uformula → uformula → Prop
| reflexive (Γ : set uformula) (φ : uformula)(h : φ ∈ Γ) : minimal.entails Γ φ
| transitivity (Γ Δ : set uformula) (φ : uformula)
               (h₁ : ∀ ψ ∈ Δ, minimal.entails Γ ψ)
               (h₂ : minimal.entails Δ φ) :  minimal.entails Γ φ
| and_intro (φ ψ : uformula) (Γ : set uformula)
            (h₁ : minimal.entails Γ φ)
            (h₂ : minimal.entails Γ ψ)
             : minimal.entails Γ (uformula.and φ ψ)
| and_elim_left (φ ψ : uformula) (Γ : set uformula)
            (h : minimal.entails Γ (uformula.and φ ψ))
             : minimal.entails Γ φ
| and_elim_right (φ ψ : uformula) (Γ : set uformula)
            (h : minimal.entails Γ (uformula.and φ ψ))
             : minimal.entails Γ ψ
| or_intro_left 
            (φ ψ : uformula) (Γ : set uformula)
            (h : minimal.entails Γ φ)
             : minimal.entails Γ (uformula.or φ ψ)
| or_intro_right 
            (φ ψ : uformula) (Γ : set uformula)
            (h : minimal.entails Γ ψ)
             : minimal.entails Γ (uformula.or φ ψ)
| or_elim
            (φ ψ δ : uformula) (Γ : set uformula)
            (h₁ : minimal.entails Γ (uformula.or φ ψ))
            (h₂ : minimal.entails Γ (φ ⇒ δ))
            (h₃ : minimal.entails Γ (ψ ⇒ δ))
             : minimal.entails Γ δ
| modus_ponens
            (φ ψ : uformula) (Γ : set uformula)
            (h₁ : minimal.entails Γ (φ ⇒ ψ))
            (h₂ : minimal.entails Γ φ)
             : minimal.entails Γ ψ
| intro
            (φ ψ : uformula) (Γ : set uformula)
            (h : minimal.entails (Γ ∪ {φ}) ψ)
             : minimal.entails Γ (φ ⇒ ψ)
| true_intro
            (Γ : set uformula)
             : minimal.entails Γ uformula.true
| for_all_intro
            (Γ : set uformula) (φ : uformula)
            (x : tvariable) (xf : x ∈ φ.free)
            (c : abstract_var)
            (h : minimal.entails Γ (φ.rw x $ term.abs c))
             : minimal.entails Γ (uformula.for_all x φ)
| for_all_elim
            (Γ : set uformula) (φ : uformula)
            (x : tvariable) (xf : x ∈ φ.free)
            (t : term) (den : t.denotes)
            (h : minimal.entails Γ (uformula.for_all x φ))
             : minimal.entails Γ (φ.rw x t)
| exists_intro 
            (Γ : set uformula) (φ : uformula)
            (x : tvariable) (xf : x ∈ φ.free)
            (t : term) (den : t.denotes)
            (h : minimal.entails Γ (φ.rw x t))
             : minimal.entails Γ (uformula.exist x φ)
| exists_elim 
            (Γ : set uformula) (φ ψ : uformula)
            (x : tvariable) (xf : x ∈ φ.free)
            (c : abstract_var)
            (h₁ : minimal.entails Γ (uformula.exist x φ))
            (h₂ : minimal.entails Γ ((φ.rw x $ term.abs c) ⇒ ψ))
             : minimal.entails Γ ψ
| identity_intro
            (Γ : set uformula) (t : term)
             : minimal.entails Γ (uformula.equation t t)
| identity_elim 
            (Γ : set uformula) (φ : uformula)
            (x : tvariable) (xf : x ∈ φ.free)
            (t₁ t₂: term) (den₁ : t₁.denotes) (den₂ : t₂.denotes)
            (h : minimal.entails Γ (φ.rw x t₁))
            (eq : minimal.entails Γ (uformula.equation t₁ t₂))
             : minimal.entails Γ (φ.rw x t₂)

variables (Γ : set uformula) (φ : uformula)

theorem self_entailment : minimal.entails Γ (φ ⇒ φ) :=
begin
    apply minimal.entails.intro,
    apply minimal.entails.reflexive (Γ∪{φ}) φ,
    simp
end

theorem id_symm : ∀ (t₁ t₂ : pterm),
                  minimal.entails Γ (uformula.equation t₁.val t₂.val) →
                  minimal.entails Γ (uformula.equation t₂.val t₁.val)  :=
let ne := var_ne in
begin
    intros t₁ t₂ h,
    apply nonempty.elim ne, intro x,
    -- φ := "x = t₁"
    let φ := uformula.equation (term.var x) t₁.val,
    have den₁ := t₁.property.1,
    have den₂ := t₂.property.1,
    have c₀ : x ∈ φ.free, simp[φ],
    have c₁ : minimal.entails Γ (φ.rw x t₁.val),
        simp[φ],
        dunfold uformula.rw, simp,
        dunfold term.rw, simp,
        rw den_rw t₁.val t₁.val x t₁.property.1,
        apply minimal.entails.identity_intro Γ t₁.val,
    have c₂ : minimal.entails Γ (φ.rw x t₂.val),
        apply minimal.entails.identity_elim, --Γ φ x c₀ t₁ t₂ den₂ den₁,
        repeat {assumption <|> apply_assumption},
    simp[φ] at c₂,
    have c₃ : (uformula.equation (term.var x) (t₁.val)).rw x (t₂.val) = uformula.equation (t₂.val) (t₁.val),
        dunfold uformula.rw, simp,
        constructor,
            dunfold term.rw, simp,
        apply den_rw t₁.val t₂.val x den₁,
    rwa c₃ at c₂,
end

variables (Δ : set uformula) (ψ : uformula)

theorem monotonicity : Δ ⊆ Γ → minimal.entails Δ ψ → minimal.entails Γ ψ :=
begin
    intros H h,
    -- induction on the possible ways in which
    -- Δ could prove ψ
    induction h,
    -- case it was proven by reflection
        apply minimal.entails.reflexive Γ h_φ,
        exact H h_h,
    -- case it was proven by transitivity
        apply minimal.entails.transitivity Γ h_Δ h_φ,
        intros ψ₂ elem,
        repeat {assumption <|> apply_assumption},
    -- case it was proven by and_intro
        apply minimal.entails.and_intro,-- h_φ h_ψ Γ,
        repeat {assumption <|> apply_assumption},
    -- case it was proven by and_elim_left
        apply minimal.entails.and_elim_left h_φ h_ψ Γ,
        repeat {assumption <|> apply_assumption},
    -- case it was proven by and_elim_right
        apply minimal.entails.and_elim_right h_φ h_ψ Γ,
        repeat {assumption <|> apply_assumption},
    -- case it was proven by or_intro_left
        apply minimal.entails.or_intro_left h_φ h_ψ Γ,
        repeat {assumption <|> apply_assumption},
    -- case it was proven by or_intro_right
        apply minimal.entails.or_intro_right h_φ h_ψ Γ,
        repeat {assumption <|> apply_assumption},
    -- case it was proven by or_elim
        apply minimal.entails.or_elim,-- h_φ h_ψ h_δ Γ,
        repeat {assumption <|> apply_assumption},
    -- case it was proven by modus ponens
        apply minimal.entails.modus_ponens h_φ h_ψ Γ,
        repeat {assumption <|> apply_assumption},
    -- case it was proven by intro
        have c : minimal.entails h_Γ (h_φ ⇒ h_ψ),
            apply minimal.entails.intro h_φ h_ψ h_Γ,
            assumption,
        apply minimal.entails.transitivity Γ h_Γ (h_φ ⇒ h_ψ),
            intros ψ₂ elem,
            have c₂ := H elem,
            exact minimal.entails.reflexive Γ ψ₂ c₂,
        assumption,
    -- case it was proven by true_intro
        exact minimal.entails.true_intro Γ,
    -- case it was proven by for_all_intro
        apply minimal.entails.for_all_intro Γ h_φ h_x h_xf h_c,
        repeat {assumption <|> apply_assumption},
    -- case it was proven by for_all_elim
        apply minimal.entails.for_all_elim Γ h_φ h_x h_xf,
        repeat {assumption <|> apply_assumption},
    -- case it was proven by exists_intro
        apply minimal.entails.exists_intro Γ h_φ h_x h_xf h_t,
        repeat {assumption <|> apply_assumption},
    -- case it was proven by exists_elim
        apply minimal.entails.exists_elim Γ h_φ h_ψ h_x h_xf,
        repeat {assumption <|> apply_assumption},
    -- case it was proven by identity_intro
        apply minimal.entails.identity_intro Γ h_t,
    -- case it was proven by identity_elim
        apply minimal.entails.identity_elim Γ h_φ h_x h_xf h_t₁ h_t₂,
        repeat {assumption <|> apply_assumption},
end

-- theorem tarski_finitary : minimal.entails Γ φ → ∃ S ⊆ Γ, finite S ∧ minimal.entails S φ :=
-- begin
--     intro h,
--     -- induction on the possible ways in which
--     -- Γ could prove φ
--     induction h,
--     -- case it was proven by reflection
--         replace h_h : {h_φ} ⊆ h_Γ, 
--             intros x elem,
--             simp at elem,
--             rwa ←elem at h_h,
--         existsi {h_φ},
--         existsi h_h,
--         constructor, simp,
--         apply minimal.entails.reflexive {h_φ} h_φ,
--         simp,
--     -- case it was proven by transitivity
--         admit,
--     -- case it was proven by and_intro
--         admit,
--     -- case it was proven by and_elim_left
--         admit,
--     -- case it was proven by and_elim_right
--         admit,
--     -- case it was proven by or_intro_left
--         admit,
--     -- case it was proven by or_intro_right
--         admit,
--     -- case it was proven by or_elim
--         admit,
--     -- case it was proven by modus ponens
--         admit,
--     -- case it was proven by intro
--         admit,
--     -- case it was proven by true_intro
--         admit,
--     -- case it was proven by for_all_intro
--         admit,
--     -- case it was proven by for_all_elim
--         admit,
--     -- case it was proven by exists_intro
--         admit,
--     -- case it was proven by exists_elim
--         admit,
--     -- case it was proven by identity_intro
--         admit,
--     -- case it was proven by identity_elim
--         admit,
-- end

-- an attempt to prove transitivity from other rules.

-- theorem transitivity : ∀ (Δ : set uformula)
--                (h₁ : ∀ ψ ∈ Δ, minimal.entails Γ ψ)
--                (h₂ : minimal.entails Δ φ),  minimal.entails Γ φ :=
-- begin
--     intros,
--     -- induction on the possible ways in which
--     -- Δ could prove φ
--     induction h₂,
--     -- case it was proven by reflection
--         apply_assumption,
--         assumption,
--     -- case it was proven by and.intro
--         apply minimal.entails.and_intro,
--         repeat{apply_assumption, assumption},
--     -- case it was proven by and_elim_left
--         apply minimal.entails.and_elim_left h₂_φ h₂_ψ Γ,
--         exact h₂_ih h₁,
--     -- case it was proven by and_elim_right
--         apply minimal.entails.and_elim_right h₂_φ h₂_ψ Γ,
--         exact h₂_ih h₁,
--     -- case it was proven by or_intro_left
--         apply minimal.entails.or_intro_left h₂_φ h₂_ψ Γ,
--         exact h₂_ih h₁,
--     -- case it was proven by or_intro_right
--         apply minimal.entails.or_intro_right h₂_φ h₂_ψ Γ,
--         exact h₂_ih h₁,
--     -- case it was proven by or_elim
--         have c₁ := h₂_ih_h₁ h₁,
--         have c₂ := h₂_ih_h₂ h₁,
--         have c₃ := h₂_ih_h₃ h₁,
--         exact minimal.entails.or_elim h₂_φ h₂_ψ h₂_δ Γ c₁ c₂ c₃,
--     -- case it was proven by modus ponens
--         apply minimal.entails.modus_ponens h₂_φ h₂_ψ Γ,
--         repeat {apply_assumption, assumption},
--     -- case it was proven by intro
--         admit,
--     -- case it was proven by true_intro
--         exact minimal.entails.true_intro Γ,
--     -- case it was proven by for_all_intro
--         admit,
--     -- case it was proven by for_all_elim
--         admit,
--     -- case it was proven by exists_intro
--         admit,
--     -- case it was proven by exists_elim
--         admit,
--     -- case it was proven by identity_intro
--         admit,
--     -- case it was proven by identity_elim
--         admit,
-- end



end formulas
end logic