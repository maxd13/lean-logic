import data.set.countable tactic.find tactic.tidy tactic.ring
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
def pterm.mk (t) (h) : pterm := subtype.mk t h
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

reserve infixr ` ⇒ `:55
class has_exp (α : Type u) := (exp : α → α → α)
infixr ⇒ := has_exp.exp

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

-- def minimal.theorem (φ : uformula) := minimal.entails ∅ φ

inductive argument
| silence {} : argument -- empty argument
| node : uformula → argument → argument → argument → argument

def argument.assumes (φ : uformula) : argument → Prop
| argument.silence := false
| (argument.node ψ argument.silence argument.silence argument.silence) := φ = ψ
| (argument.node _ a₁ a₂ a₃) := a₁.assumes ∨ 
                                a₂.assumes ∨ 
                                a₃.assumes

@[reducible]
def argument.concludes (φ : uformula) : argument → Prop
| argument.silence := false
| (logic.argument.node ψ x y z) := ψ = φ

-- def silence := argument.silence
-- -- because I said so
-- def argument.return : uformula → argument
-- | φ := argument.node φ silence silence silence

-- tells whether an argument is a proof from Γ
-- TODO: CONVERT THIS TO INDUCTIVE DEFINITION !!!!
@[reducible]
def argument.proof_from (Γ : set uformula) : argument → Prop
| (argument.node φ argument.silence argument.silence argument.silence) := φ ∈ Γ ∨
                                                                          φ = uformula.true ∨
                                                                          ∃ t, φ = uformula.equation t t
-- introduction rules
| (argument.node (uformula.and φ ψ)
                       γ₁
                       γ₂
                       argument.silence) := γ₁.concludes φ ∧
                                            γ₂.concludes ψ ∧
                                            γ₁.proof_from ∧
                                            γ₂.proof_from
| (argument.node (uformula.or φ _)
                       γ₁
                       argument.silence
                       argument.silence) := γ₁.concludes φ ∧ γ₁.proof_from
| (argument.node (uformula.or _ ψ)
                       argument.silence
                       γ₂
                       argument.silence) := γ₂.concludes ψ ∧ γ₂.proof_from
| (argument.node (uformula.if_then φ ψ)
                       γ
                       argument.silence
                       argument.silence) := γ.concludes ψ ∧
                                            γ.assumes φ ∧
                                            γ.proof_from
| (argument.node (uformula.for_all x φ)
                       γ
                       argument.silence
                       argument.silence) := ∃ c, γ.concludes (φ.rw x $ term.abs c) ∧
                                            x ∈ φ.free ∧
                                            γ.proof_from
| (argument.node (uformula.exist x φ)
                       γ
                       argument.silence
                       argument.silence) := ∃ t, γ.concludes (φ.rw x t) ∧
                                            t.denotes ∧
                                            x ∈ φ.free ∧
                                            γ.proof_from
-- elimination rules
| (argument.node φ γ argument.silence argument.silence) := ((∃ ψ, γ.concludes $ uformula.and φ ψ) ∨
                                                            (∃ ψ, γ.concludes $ uformula.and ψ φ) ∨
                                                            (∃ x (ψ : uformula) (t : term), 
                                                             t.denotes ∧
                                                             x ∈ ψ.free ∧
                                                             γ.concludes (uformula.for_all x ψ) ∧
                                                             φ = ψ.rw x t)) ∧
                                                             γ.proof_from
| (argument.node φ γ₁ γ₂ argument.silence) := ((∃ ψ, γ₁.concludes (ψ ⇒ φ) ∧
                                               γ₂.concludes ψ) ∨
                                              (∃ x (ψ : uformula) c,
                                               x ∈ ψ.free ∧
                                               γ₁.concludes (uformula.exist x ψ) ∧
                                               γ₂.concludes ((ψ.rw x $ term.abs c) ⇒ φ)) ∨
                                              (∃ x (ψ : uformula) (t₁ t₂ : term), 
                                               t₁.denotes ∧
                                               t₂.denotes ∧
                                               x ∈ ψ.free ∧
                                               γ₁.concludes (ψ.rw x t₁) ∧
                                               γ₂.concludes (uformula.equation t₁ t₂) ∧
                                               φ = ψ.rw x t₂)) ∧
                                               γ₁.proof_from ∧
                                               γ₂.proof_from
| (argument.node φ γ₁ γ₂ γ₃) := ∃ ψ₁ ψ₂, γ₁.concludes (uformula.or ψ₁ ψ₂) ∧
                                         γ₂.concludes (ψ₁ ⇒ φ) ∧
                                         γ₃.concludes (ψ₂ ⇒ φ) ∧
                                         γ₁.proof_from ∧
                                         γ₂.proof_from ∧
                                         γ₃.proof_from
| _ := false


def argument.proof_of (φ : uformula) (Γ : set uformula) : argument → Prop
| γ := γ.proof_from Γ ∧ γ.concludes φ 

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


theorem proof_entails : (∃ p : argument, p.proof_of φ Γ) → minimal.entails Γ φ :=
begin
    intro h,
    obtain ⟨p, ph₁, ph₂⟩ := h,
    induction p,
        have c : false := ph₂,
        contradiction,
    have eq : φ = p_a := sorry, 
        -- impossible to unfold at ph₂ for some reason
        -- simp [argument.concludes] at ph₂,
    rw ←eq at ph₁,
    admit,
    -- induction φ,
    
    -- simp at ph₁,

    
end

section semantics

parameters {α : Type u} [nonempty α]

-- functional interpretation
def fint  {n : ℕ} := nary n → vector α n → α
-- relational interpretation
def rint {n : ℕ} := nrary n → vector α n → Prop
-- variable assignment
def vasgn := tvariable → α

structure model :=
    (I₁ : Π {n}, @fint n)
    (I₂ : Π {n}, @rint n)

def remove_none_list {α} : list (option α) → option (list α)
| [] := some []
| (some x::xs) := remove_none_list xs >>= λ ls, some $ x::ls
| (none::_) := none

private lemma remove_none_aux {α} : ∀ (ls : list $ option α) n, 
                                    ls.length = n →
                                    ∀ xs, remove_none_list ls = some xs →
                                    xs.length = n :=
begin
    intros ls n h₁ xs h₂,
    induction ls generalizing n xs,
        simp at h₁,
        simp [remove_none_list] at h₂,
        rw [←h₂, ←h₁],
        simp,
    induction ls_hd;
        simp [remove_none_list] at h₂,
        contradiction,
    obtain ⟨tl, c₁, c₂⟩ := h₂,
    rw ←c₂, simp,
    simp at h₁,
    ring at h₁,
    rw ←h₁,
    ring, simp,
    replace h₁ : length ls_tl = n - 1,
        rw ←h₁,
        simp,
    have c := ls_ih (n-1) tl h₁ c₁,
    rwa h₁,
end

def remove_none {α} {n} : vector (option α) n → option (vector α n)
| ⟨ls, p⟩ := begin
                cases h : remove_none_list ls with xs,
                    exact none,
                have c := remove_none_aux ls n p xs h,
                exact some ⟨xs, c⟩
            end
    
def model.reference (M : model) : term → option α
-- | ⟨(term.var x), p⟩ := begin
--                         have c : logic.term.vars (term.var x) = ∅ 
--                             := p.1,
--                         simp at c,
--                         contradiction,
--                         end
-- | ⟨(term.abs c), p⟩ := begin
--                         have c : false := p.2,
--                         contradiction,
--                         end
| (@term.app _ _ _ _ _ _ _ 0 f _) := some $ model.I₁ M f ⟨[], rfl⟩
| (@term.app _ _ _ _ _ _ _ (n+1) f v) := let v₂ := λ k, model.reference (v k),
                                             v₃ := remove_none $ vector.of_fn v₂
                                         in do 
                                         v₄ <- v₃,
                                         some $
                                         model.I₁ M f v₄
| _ := none

def model.reference' (M : model) : term → vasgn → option α
| (term.var x) asg := some $ asg x
| (@term.app _ _ _ _ _ _ _ 0 f _) _ := model.I₁ M f ⟨[], rfl⟩
| (@term.app _ _ _ _ _ _ _ (n+1) f v) asg := let v₂ := λ k, model.reference' (v k) asg,
                                                 v₃ := remove_none $ vector.of_fn v₂
                                             in do 
                                             v₄ <- v₃,
                                             some $
                                             model.I₁ M f v₄
| _ _ := none
                                         
                                                   

-- let v₂ := (λ k,
--             let den : term.denotes (v k) ∧ term.concrete (v k):=
--                 begin
--                     constructor,
--                         have c : logic.term.vars (term.app f v) = ∅ := p.1,
--                         replace c : (let v₂ := λ m, logic.term.vars (v m) in ⋃ m, v₂ m) = ∅ := c,
--                         simp at c,
--                         ext, constructor,
--                             intro h,
--                             have d : x ∈ (⋃ (m : fin (n + 1)), logic.term.vars (v m)),
--                                 simp,
--                                 exact ⟨k, h⟩,
--                             rwa c at d,
--                         simp,
--                     have c := p.2,
--                     exact c k,
--                 end
--             in pterm.mk (v k) den),

-- TODO prove that the reference is defined for pterms
-- use commented code above for help

-- for some reason I cant use do notation with
-- the option types, because lean is unable to
-- synthesize the types
def model.satisfies' : model → uformula → vasgn → option Prop
| M (uformula.relational r v) asg := 
    match remove_none $
          vector.map (flip M.reference' asg) 
          (vector.of_fn v)
          with
          | none := none
          | some xs := some $ M.I₂ r xs
    end                         
| M (uformula.equation t₁ t₂) asg :=
    -- got ugly because 
    -- both do and >>= are causing problems
    match model.reference' M t₁ asg with
    | none := none
    | some x := match model.reference' M t₂ asg with
                | none := none
                | some y := some (x = y)
                end
    end
| M uformula.true _ := some true
| M uformula.false _ := some false
| M (uformula.for_all x φ) asg := some
    (∀ (a : α) (ass : vasgn),
    ass x = a →
    (∀ y, y ≠ x → ass y = asg y) →
    ∃ p : Prop, p ∧
    M.satisfies' φ ass = some p)
| M (uformula.exist x φ) asg := some
    (∃ (a : α),
    ∀ (ass : vasgn),
    ass x = a →
    (∀ y, y ≠ x → ass y = asg y) →
    ∃ p : Prop, p ∧
    M.satisfies' φ ass = some p)
| M (uformula.and φ ψ) asg :=
    match model.satisfies' M φ asg with
    | none := none
    | some x := match model.satisfies' M ψ asg with
                | none := none
                | some y := some (x ∧ y)
                end
    end

| M (uformula.or φ ψ) asg := 
    match model.satisfies' M φ asg with
    | none := none
    | some x := match model.satisfies' M ψ asg with
                | none := none
                | some y := some (x ∨ y)
                end
    end
| M (uformula.if_then φ ψ) asg :=
    match model.satisfies' M φ asg with
    | none := none
    | some x := match model.satisfies' M ψ asg with
                | none := none
                | some y := some (x → y)
                end
    end
-- @[reducible]
def model.satisfies : model → uformula → Prop
| M φ := 
    ∀ (ass : vasgn),
    ∃ p : Prop, p ∧
    M.satisfies' φ ass = some p

local infixr `⊨₁`:55 := model.satisfies
local infixr `⊢`:55 := minimal.entails

lemma false_is_unsat : ¬∃ M : model, M ⊨₁ uformula.false :=
begin
    intro h,
    obtain ⟨M, h⟩ := h,
    apply nonempty.elim _inst_4, intro x,
    obtain ⟨p, hp, sat⟩ := h (λ y : tvariable, x),
    replace sat : some false = some p := sat,
    simp at sat,
    contradiction,
end

def model.for : model → set uformula → Prop
| M Γ := ∀ φ ∈ Γ, M ⊨₁ φ

-- semantic consequence
-- remember Γ and φ are already defined
def theory.follows : Prop :=
    ∀ M : model, M.for Γ → M ⊨₁ φ

local infixr `⊨`:55 := theory.follows

-- so pretty.
theorem soundness : Γ ⊢ φ → Γ ⊨ φ :=
begin
    intros entails M h ass,
    induction entails generalizing ass,
    -- case reflexive
    have c : M.satisfies entails_φ := h entails_φ entails_h,
    obtain ⟨p, hp, sat⟩ := c ass,
    existsi p,
    constructor,
        exact hp,
    assumption,
    -- case transitivity
    apply entails_ih_h₂,
    intros ψ H asg,
    have c := entails_ih_h₁ ψ H h,
    exact c asg,
    -- case and.intro
    obtain ⟨p₁, hp₁, sat₁⟩ := entails_ih_h₁ h ass,
    obtain ⟨p₂, hp₂, sat₂⟩ := entails_ih_h₂ h ass,
    existsi p₁ ∧ p₂,
    constructor,
        exact ⟨hp₁, hp₂⟩,
    dunfold model.satisfies',
    simp [sat₁, sat₂],
    dunfold model.satisfies'._match_4,
    dunfold model.satisfies'._match_5,
    refl,
    -- case and.elim_left
    obtain ⟨p, hp, sat⟩ := entails_ih h ass,
    revert sat,
    dunfold model.satisfies',
    intro sat,
    cases (M.satisfies' entails_ψ ass),
        cases (M.satisfies' entails_φ ass);
            replace sat : none = some p := sat;
            simp at sat;
            contradiction,
    cases (M.satisfies' entails_φ ass);
        revert sat;
        dunfold model.satisfies'._match_4,
        contradiction,
    dunfold model.satisfies'._match_5,
    intro sat,
    simp at sat,
    existsi val_1,
    constructor,
        exact (sat.2 hp).1,
    refl,
    -- case and.elim_right
    obtain ⟨p, hp, sat⟩ := entails_ih h ass,
    revert sat,
    dunfold model.satisfies',
    intro sat,
    cases (M.satisfies' entails_ψ ass),
        cases (M.satisfies' entails_φ ass);
            replace sat : none = some p := sat;
            simp at sat;
            contradiction,
    cases (M.satisfies' entails_φ ass);
        revert sat;
        dunfold model.satisfies'._match_4,
        contradiction,
    dunfold model.satisfies'._match_5,
    intro sat,
    simp at sat,
    existsi val,
    constructor,
        exact (sat.2 hp).2,
    refl,
    -- case or_intro_left
    obtain ⟨p, hp, sat⟩ := entails_ih h ass,
    dunfold model.satisfies',
    -- cases (M.satisfies' entails_ψ ass),
    cases (M.satisfies' entails_φ ass),
        simp at sat,
        contradiction,
    simp at sat,
    dunfold model.satisfies'._match_6,
    -- dunfold model.satisfies'._match_7,
    cases (M.satisfies' entails_φ ass);
        revert sat;
        dunfold model.satisfies'._match_6,
        contradiction,
    dunfold model.satisfies'._match_7,


end



end semantics

section consistency
end consistency

end formulas
end logic