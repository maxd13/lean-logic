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
| var : ℕ → term
| app  {n : ℕ} (f : nary n) (v : fin n → term) :  term

-- constant terms.
def const.term : const → term
| c := term.app c fin_zero_elim

@[reducible]
def term.rw : term → ℕ → term → term
| (term.var a) x t := if x = a then t else term.var a
| (term.app f v) x t := 
    let v₂ := λ m, term.rw (v m) x t in
    term.app f v₂

def term.vars : term → list ℕ
| (term.var a) := [a]
| (term.app  f v) :=
    let v₂ := λ m, term.vars (v m) in
    foldr (++) [] (of_fn v₂)

@[reducible]
def term.denotes (t : term) := t.vars = []
@[reducible]
def term.conotes (t : term) := ¬ t.denotes

-- a term in the proper sense of the term (pun intended).
def pterm := subtype {t : term | t.denotes}
def expression := subtype {t : term | t.conotes}

-- def term.subterms : term → set term
-- | (term.app f v) := 
--     let v₂ := λ m, term.subterms (v m) in
--     (⋃ m, v₂ m) ∪ {(term.app f v)}
-- | t := {t}

def list.vars : list term → list ℕ
| [] := ∅
| (hd :: tl) := hd.vars ++ tl.vars

-- def list.subterms : list term → list term
-- | [] := ∅
-- | (hd :: tl) := hd.subterms ++ tl.subterms

def list.rw : list term → ℕ → term → list term
| [] _ _:= ∅
| (hd :: tl) x t := (hd.rw x t) :: tl.rw x t

-- def subterms : set term → list term
-- | S := ⋃ x ∈ S, term.subterms x

-- formulas
inductive uformula
| relational {n : ℕ} (r : nrary n) (v : fin n → term) : uformula
| equation (t₁ t₂ : term) : uformula
| false : uformula
| for_all :  ℕ → uformula → uformula
| if_then : uformula → uformula → uformula

def uformula.not (φ) := uformula.if_then φ uformula.false

reserve infixr ` ⇒ `:55
class has_exp (α : Type u) := (exp : α → α → α)
infixr ⇒ := has_exp.exp
instance uformula.has_exp : has_exp uformula := ⟨uformula.if_then⟩

local notation `∼` := uformula.not

@[reducible]
def uformula.rw : uformula → ℕ → term → uformula
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
| (uformula.if_then φ ψ) x t := uformula.if_then (φ.rw x t) (ψ.rw x t)
| φ _ _ := φ

def list_sub_aux {α} [decidable_eq α] : list α → list α → list α
| [] _ := []
| (hd::tl) xs := 
begin
    cases list.decidable_mem hd xs,
        exact hd :: list_sub_aux tl xs,
    exact list_sub_aux tl xs,
end
                
instance list_sub {α} [decidable_eq α] : has_sub (list α) :=
⟨list_sub_aux⟩

-- free variables
@[reducible]
def uformula.free : uformula → list ℕ
| (uformula.relational r v) := list.vars (of_fn v)
| (uformula.equation t₁ t₂) := t₁.vars ++ t₂.vars
| (uformula.for_all x φ) := φ.free - [x]
| (uformula.if_then φ ψ) := φ.free ++ ψ.free
| _ := []

-- open and closed formulas.
def uformula.closed : uformula → Prop
| φ := φ.free = ∅

def uformula.open : uformula → Prop
| φ := ¬ φ.closed

def uformula.vars : uformula → list ℕ
| (uformula.for_all x φ) := x::φ.free
| (uformula.if_then φ ψ) := φ.vars ++ ψ.vars
| φ := φ.free

inductive uaxiom : uformula → Prop
| p₁ (φ ψ : uformula) : uaxiom (φ ⇒ ψ ⇒ φ)
| p₂ (φ ψ δ : uformula) : uaxiom ((φ ⇒ ψ ⇒ δ) ⇒ ((φ ⇒ ψ) ⇒ φ ⇒ δ))
| p₃ (φ ψ : uformula) : uaxiom ((∼φ ⇒ ∼ψ) ⇒ ψ ⇒ φ)
| q₅ (x : ℕ) (φ : uformula) (t : pterm) : uaxiom ((uformula.for_all x φ) ⇒ φ.rw x t.val)
| q₆ (x : ℕ) (φ ψ : uformula) : uaxiom ((uformula.for_all x φ ⇒ ψ) ⇒ (uformula.for_all x φ) ⇒ (uformula.for_all x ψ))
| q₇ (x : ℕ) (φ : uformula) (x ∉ φ.free) : uaxiom (φ ⇒ (uformula.for_all x φ))

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

parameters {α : Type u} [inhabited α]

-- functional interpretation
def fint  {n : ℕ} := nary n → (fin n → α) → α
-- relational interpretation
def rint {n : ℕ} := nrary n → (fin n → α) → Prop
-- variable assignment
def vasgn := ℕ → α

parameter exists_ass : nonempty vasgn

structure model :=
    (I₁ : Π {n}, @fint n)
    -- required because any constant that would map
    -- to the default value, would be a "generic point"
    -- of the type α, i.e. any of its properties would be
    -- true of any instance of α.
    (constant_no_default : ∀ f : nary 0, I₁ f fin_zero_elim ≠ default α)
    (I₂ : Π {n}, @rint n)

-- @[reducible]
def model.reference' (M : model) : term → vasgn → α
| (term.var x) asg := asg x
| (@term.app _ _ _ _ _ _ _ 0 f _) _ := model.I₁ M f fin_zero_elim
| (@term.app _ _ _ _ _ _ _ (n+1) f v) asg := let v₂ := λ k, model.reference' (v k) asg
                                             in model.I₁ M f v₂
-- An unavoidable trick.
-- It is just ridiculously hard to try any other
-- alternative. I gained A LOT of productivity
-- from this.
| _ _ := default α

-- If the default value is considered to be
-- a non-existent reference, like an option.none,
-- then this reference is only defined for pterms.
def model.reference (M : model) : pterm → α
| ⟨(@term.app _ _ _ _ _ _ _ 0 f _),_⟩ := model.I₁ M f fin_zero_elim
| ⟨(@term.app _ _ _ _ _ _ _ (n+1) f v),p⟩ := let v₂ := λ k, model.reference ⟨v k,
                                            begin
                                                admit,
                                            end⟩
                                             in model.I₁ M f v₂
| _ := sorry
-- | t := M.reference' t.val (λx, default α)
using_well_founded well_founded_tactics.default
-- begin
--     constructor,
--     intros x y,
--     exact `[exact well_founded_tactics.cancel_nat_add_lt],
--     exact assumption,
-- end


def model.satisfies' : model → uformula → vasgn → Prop
| M (uformula.relational r v) asg := 
          M.I₂ r $ λm,  M.reference' (v m) asg
| M (uformula.equation t₁ t₂) asg :=
    let x := model.reference' M t₁ asg,
        y := model.reference' M t₂ asg
    in x = y
| M uformula.true _ := true
| M uformula.false _ := false
| M (uformula.for_all x φ) asg :=
    ∀ (a : α) (ass : vasgn),
    ass x = a →
    (∀ y, y ≠ x → ass y = asg y) →
    M.satisfies' φ ass
| M (uformula.exist x φ) asg :=
    ∃ (a : α),
    ∀ (ass : vasgn),
    ass x = a →
    (∀ y, y ≠ x → ass y = asg y) →
    M.satisfies' φ ass
| M (uformula.and φ ψ) asg :=
    let x := model.satisfies' M φ asg,
        y := model.satisfies' M ψ asg
    in x ∧ y
| M (uformula.or φ ψ) asg := 
    let x := model.satisfies' M φ asg,
        y := model.satisfies' M ψ asg
    in x ∨ y
| M (uformula.if_then φ ψ) asg :=
    let x := model.satisfies' M φ asg,
        y := model.satisfies' M ψ asg
    in x → y


@[reducible]
def model.satisfies : model → uformula → Prop
| M φ := ∀ (ass : vasgn), M.satisfies' φ ass

local infixr `⊨₁`:55 := model.satisfies
local infixr `⊢`:55 := minimal.entails

include exists_ass
lemma false_is_unsat : ¬∃ M : model, M ⊨₁ uformula.false :=
begin
    intro h,
    obtain ⟨M, h⟩ := h,
    tactic.unfreeze_local_instances,
    obtain ⟨x⟩ := exists_ass,
    exact h x,
end
omit exists_ass

def model.for : model → set uformula → Prop
| M Γ := ∀ φ ∈ Γ, M ⊨₁ φ

-- semantic consequence
-- remember Γ and φ are already defined
def theory.follows : Prop :=
    ∀ (M : model) ass, (∀ ψ ∈ Γ, M.satisfies' ψ ass) → M.satisfies' φ ass

local infixr `⊨`:55 := theory.follows


def vasgn.bind (ass : vasgn) (x : ℕ) (val : α) : vasgn :=
    λy, if y = x then val else ass y

-- lemma uformula.rw.semantics (φ : uformula) 
--                             (x : ℕ)
--                             (h₀ : x ∈ φ.free)
--                             (ass : vasgn)
--                             (M : model)
--                             (t : pterm)
--                             : 
--                             M.satisfies' φ ass →
--                             M.satisfies' (φ.rw x t.val)
--                             (ass.bind x (M.reference' t.val ass))
--                             :=
-- begin
--     -- intro h,
--     induction φ;
--     dunfold uformula.rw; try{simp};
--     dunfold model.satisfies';
--     intro h,
--     -- have c₁ : (λ (m : fin φ_n), M.reference' (φ_v m) ass) = (flip M.reference' ass) ∘ φ_v,
--     --     dsimp [flip, function.comp],
--     --     refl,
--     have c : ∀ m, (M.reference' ((φ_v m).rw x t.val) (ass.bind x (M.reference' t.val ass))) = M.reference' (φ_v m) ass,
--         focus {
--             intro m,
--             induction (φ_v m);
--             dunfold term.rw;
--             dunfold vasgn.bind,
--             dunfold model.reference',
--             by_cases h₂ : x = a;
--                 simp [h₂],
--                 obtain ⟨t, pt₁, pt₂⟩ := t,
--                 induction t,
--                     dunfold model.reference',
--                     simp,
                
--                 revert pt₁,
--                 dunfold term.denotes,
--                 dunfold term.vars,
--                 simp,
--                     revert pt₂,
--                     dunfold term.concrete,
--                     contradiction,
--                 simp,
--                 induction t_n;
--                 dunfold model.reference',
                
--                     -- dunfold model.reference',

--         }

            

-- end

-- So pretty.
theorem soundness : Γ ⊢ φ → Γ ⊨ φ :=
begin
    intros entails M ass h,
    induction entails,
    -- case reflexive
    exact h entails_φ entails_h,
    -- case transitivity
    apply entails_ih_h₂,
    intros ψ H,
    exact entails_ih_h₁ ψ H h,
    -- case and.intro
    have c₁ := entails_ih_h₁ h,
    have c₂ := entails_ih_h₂ h,
    exact ⟨c₁, c₂⟩,
    -- case and.elim_left
    have sat := entails_ih h,
    revert sat,
    dunfold model.satisfies',
    simp,
    intros sat aux,
    exact sat,
    -- case and.elim_right
    have sat := entails_ih h,
    revert sat,
    repeat {dunfold model.satisfies', simp},
    left,
    exact entails_ih h,
    right,
    exact entails_ih h,
    -- case or_intro_left
    -- already solved
    -- case or_intro_right
    -- already solved
    -- case or_elim
    have c₁ := entails_ih_h₁ h,
    have c₂ := entails_ih_h₂ h,
    have c₃ := entails_ih_h₃ h,
    tactic.unfreeze_local_instances,
    dunfold model.satisfies' at *,
    simp at *,
    cases c₁,
        exact c₂ c₁,
    exact c₃ c₁,
    -- case modus ponens
    have c₁ := entails_ih_h₁ h,
    have c₂ := entails_ih_h₂ h,
    revert c₁,
    dunfold model.satisfies',
    simp,
    intro c₁,
    exact c₁ c₂,
    -- case intro
    intro h₂,
    have sat := entails_ih,
    apply sat,
    intros ψ H,
    cases H,
    exact h ψ H,
    simp at H,
    rwa H,
    -- case true.intro
    trivial,
    -- case universal intro
    -- intros x asg h₁ h₂,
    -- have sat := entails_ih h,
    -- focus {
    --     induction entails_φ;
    --     revert sat;
    --     dunfold uformula.rw;
    --     dunfold model.satisfies';
    --     try{dunfold flip};
    --     try{dunfold vector.of_fn};
    --     try{dunfold vector.map},
    --         intro sat,
    -- },
    admit,
    -- case universal elim
    -- focus {
    --     induction entails_φ;
    --     have sat := entails_ih h;
    --     revert sat;
    --     dunfold uformula.rw; try{simp},
    --     -- I cant go any further applying strategies to
    --     -- all goals because the linter gets very slow.
    --     dunfold model.satisfies', try{simp},
    --         intro sat,
    -- },
    admit,
    -- case exists intro
    have sat := entails_ih h,
    existsi M.reference' entails_t ass,
    intros asg h₁ h₂,
    admit,
    -- case exists elim
    admit,
    -- case identity intro
    -- already solved
    -- case identity elim
    admit,
end



end semantics

section consistency
end consistency

end formulas
end logic