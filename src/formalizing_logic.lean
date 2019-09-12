import data.set.finite data.set.countable order.bounded_lattice init.data.list
tactic computability.primrec -- tactic.tidy tactic.find
--.philosophy.Interpretation_PeterChen_ER

open set lattice
universe u
#check finite
--local attribute [instance] classical.prop_decidable

-- We formalize several logical systems.


class formal_system :=
    (formula : Type u)
    (entails : set formula → formula → Prop)

infixr `⊢`:50 := formal_system.entails

section basic_definitions
parameter {L : formal_system}

local notation `formula` := L.formula

-- consequence set.
def C (Δ : set formula) : set formula := {φ : formula | Δ ⊢ φ}

def istheory (Δ : set formula) : Prop := C Δ = Δ

def Theory := subtype istheory

def Theorem (φ : formula) : Prop := ∅ ⊢ φ

def weak_consistent (Δ : set formula) : Prop := C Δ ≠ univ

def weak_maximally_consistent (Γ : Theory) : Prop := 
    weak_consistent Γ.1 
    ∧ ∀ Δ : Theory, Γ.1 ⊆ Δ.1 → weak_consistent Δ.1 → Γ = Δ

def recursive (Δ : set formula) := countable Δ ∧ nonempty (decidable_pred Δ)

lemma finite_recursive [decidable_eq formula] : ∀ {Δ : set formula}, finite Δ → recursive Δ :=
    assume Δ : set formula,
    assume h : finite Δ,
    have c₀ : countable Δ, from countable_finite h,
    let (nonempty.intro x) := h in
    have dp : decidable_pred Δ, from @set.decidable_mem_of_fintype _ _ Δ x,
    ⟨c₀, nonempty.intro dp⟩

def axiomatizes (Δ: set formula) (Γ : Theory) : Prop := C Δ = Γ.1

def finitely_axiomatizable (Γ : Theory) : Prop := ∃ Δ, axiomatizes Δ Γ ∧ finite Δ

def recursively_axiomatizable (Γ : Theory) : Prop := ∃ Δ, axiomatizes Δ Γ ∧ recursive Δ


instance theoretic_entailment : has_le (set formula) := ⟨λ Γ Δ, ∀ ψ ∈ Δ, Γ ⊢ ψ⟩ 
--instance formula_entailment : has_le (formula) := ⟨λ φ ψ, {φ} ⊢ ψ⟩

end basic_definitions

section Tarski

class Tarski_system extends formal_system :=
    (reflexivity : ∀ (Γ : set formula) (φ : formula), φ ∈ Γ → Γ ⊢ φ)
    (transitivity : ∀ (Γ Δ : set formula) (φ : formula), Γ ≤ Δ → Δ ⊢ φ → Γ ⊢ φ)

parameter {L : Tarski_system}
local notation `formula` := L.formula

-- Proofs become more readable if we specify which axioms we are using from the definition of a structure
-- in the beggining of the proof. This way we know what to expect to be used, and it becomes easier to analyze
-- the dependencies of results on axioms.

-- The proofs of this section are supposed to be used to define a
-- closure algebra.

lemma subset_proof : ∀ {Γ Δ : set formula}, Γ ⊆ Δ → Δ ≤ Γ :=
    let rf := L.reflexivity in
    assume Γ Δ : set formula,
    assume h₀ : Γ ⊆ Δ,
    assume φ : formula,
    assume h₁ : φ ∈ Γ,
    have c₀ : φ ∈ Δ, from h₀ h₁,
    show Δ ⊢ φ, from rf Δ φ c₀

-- as we can see, for a non-monotonic logic we would have to drop
-- either the reflexivity or the transitivity axiom.
-- Fun fact: the Aristotelian name for "non-monotonic logic" is Rhetoric.
lemma C_monotone : ∀ {Γ Δ : set formula}, Γ ⊆ Δ → C Γ ⊆ C Δ :=
    let tr := L.transitivity in
    assume Γ Δ : set formula,
    assume h₀ : Γ ⊆ Δ,
    assume φ : formula,
    assume h₁ : φ ∈ C Γ,
    have c₀ : Γ ⊢ φ, from h₁,
    have c₁ : Δ ≤ Γ, from subset_proof h₀,
    show φ ∈ C Δ, from tr Δ Γ φ c₁ c₀

lemma C_increasing : ∀ {Γ : set formula}, Γ ⊆ C Γ := L.reflexivity

lemma C_idempotent : ∀ (Γ : set formula), C (C Γ) = C Γ :=
let tr := L.transitivity in
begin
    intro,
    ext φ,
    constructor; intro h₁,
        apply tr Γ (C (C Γ)) φ,
            intros ψ h₂,
            apply tr Γ (C Γ) ψ,
                intros x h, assumption,
                exact h₂,
        exact C_increasing h₁,
    exact C_increasing h₁
end

lemma C_top_fixed : C Theorem = @Theorem L.to_formal_system :=
    -- C (C ∅) = C ∅
    C_idempotent ∅


instance entailment_preorder : preorder (set formula) := 
let tr := L.transitivity in
{ le := λ Γ Δ, ∀ ψ ∈ Δ, Γ ⊢ ψ,
  lt := λ Γ Δ, (∀ ψ ∈ Δ, Γ ⊢ ψ) ∧ ¬ (∀ ψ ∈ Γ, Δ ⊢ ψ),
  le_refl := by intros S φ h; apply @subset_proof {φ}; simp; assumption,
  le_trans := 
    begin
    intros Γ Δ Ω h₁ h₂ φ h₃,
    dsimp at *,
    apply tr Γ Δ φ,
        exact h₁,
    apply h₂,
    exact h₃
    end,
  lt_iff_le_not_le := 
    begin 
    intros Γ Δ,
    fsplit; intro h;
    cases h with h₁ h₂;
    constructor; assumption,
    end 
}


instance entailment_order : partial_order (@Theory L.to_formal_system) := 
    begin 
    fsplit; intros Γ,
    intro Δ, exact Γ.1 ≤ Δ.1,
    intro Δ, exact Γ.1 < Δ.1,
    exact le_refl Γ.1,
    intros Δ Ω h₁ h₂, dsimp at *, exact le_trans h₁ h₂,
    all_goals {intros Δ; try{constructor}; intro h₁; try{exact h₁}},
    intro h₂, cases Γ, cases Δ, simp,
    ext φ, constructor; intro h,
        have c : Δ_val ⊢ φ, from h₂ φ h,
        unfold istheory at Δ_property,
        rewrite ←Δ_property, exact c,
    have c : Γ_val ⊢ φ, from h₁ φ h,
    unfold istheory at Γ_property,
    rewrite ←Γ_property, exact c,
    end

end Tarski

section logic

class deductive_system extends Tarski_system :=
    (finitary : ∀ (Γ) (φ : formula), Γ ⊢ φ → ∃ Δ ⊆ Γ, finite Δ ∧ Δ ⊢ φ)
    (encoding : encodable formula)
    (recursive : decidable_pred (range encoding.encode))

class logic extends deductive_system :=
    (connectives : distrib_lattice formula)
    (deduction_order : ∀ {φ ψ}, φ ≤ ψ ↔ {φ} ⊢ ψ)
    (and_intro : ∀ φ ψ, {φ, ψ} ⊢ φ ⊓ ψ)
    (or_elim : ∀ {Γ} (φ ψ γ: formula), Γ ⊢ φ ⊔ ψ → Γ ∪ {φ} ⊢ γ → Γ ∪ {φ} ⊢ γ → Γ ⊢ γ)
    (True : formula)
    (True_intro : Theorem True)
    (False : formula)

instance Lindenbaum_Tarski {L : logic} : distrib_lattice L.formula := L.connectives

@[simp]
def deduction_order {L : logic} := L.deduction_order


section propositional_logic

reserve infixr ` ⇒ `:55
class has_exp (α : Type u) := (exp : α → α → α)
infixr ⇒ := has_exp.exp

class minimal_logic extends logic :=
    (implication : has_exp formula)
    (implication_definition : ∀ φ ψ : formula, (φ ⇒ ψ) ⊓ φ ≤ ψ)
    (implication_universal_property : ∀ {φ ψ γ : formula}, γ ⊓ φ ≤ ψ → γ ≤ (φ ⇒ ψ))
    (deduction_theorem : ∀ {Γ} (φ ψ), Γ ∪ {φ} ⊢ ψ → Γ ⊢ φ ⇒ ψ)

parameter {L : minimal_logic}

instance implication_formula : has_exp L.formula := L.implication

instance minimal_negation : has_neg L.formula := ⟨λ φ, φ ⇒ L.False⟩

inductive proposition
| false : proposition
| true : proposition
| atomic : ℕ → proposition
| and : proposition → proposition → proposition
| or : proposition → proposition → proposition
| if_then : proposition → proposition → proposition

instance proposition_exp : has_exp proposition := ⟨proposition.if_then⟩

def proposition.iff : proposition → proposition → proposition := λ p q, proposition.and (p ⇒ q) (q ⇒ p) 

def proposition.not :  proposition → proposition := λ p, p ⇒ proposition.false

#check combinator.K
#check combinator.S

def hilbert_axioms : set proposition := 
    ⋃φ ψ γ,  
    {
     φ ⇒ ψ ⇒ φ, -- K combinator
     (φ ⇒ ψ ⇒ γ) ⇒ (φ ⇒ ψ) ⇒ (φ ⇒ γ), -- S combinator
     proposition.true
    }

noncomputable instance deq_proposition : decidable_eq proposition := 
        by intros φ ψ; exact classical.prop_decidable (φ = ψ)

        --this is an old failed attempt to remove the "noncomputable" above.
        -- It is surprisingly effective, until it isn't, i.e. it reduces 64 goals to 5, but then
        -- the and, or, and if_then make the proof of the remaining goals too hard or impossible. 

        --begin 
        --induction a; induction b; simp,
        --repeat {apply_instance};
        --admit
        --end

        -- TODO: show an isomorphism between propositions and naturals or strings,
        -- and then derive the equality from their respective equalities.


def proof_from (Γ : set proposition) (conclusion : proposition) : list proposition → Prop
| [] := false
| (φ :: xs) :=  
    let S := {x | x ∈ xs} ∪ Γ ∪ hilbert_axioms in
    φ = conclusion ∧
    (φ ∈ Γ ∪ hilbert_axioms ∨
    (∃ ψ, ψ ∈ S ∧ ψ ⇒ φ ∈ S))

def proof_of (conclusion : proposition) (Γ : set proposition) : list proposition → Prop := λ l, proof_from Γ conclusion l

instance minimal_Tarski : Tarski_system := 
{ formula := proposition,
  entails := λ Γ φ, ∃ l : list proposition, proof_from Γ φ l,
  reflexivity := 
    begin
        intros Γ φ h,
        dsimp at *,
        fsplit,
        exact [φ],
        constructor, refl,
        left, left,
        exact h
    end,
  transitivity := 
    begin
        intros Γ Δ φ h₁ h₂,
        cases h₂ with proof h₃,
        dsimp at *,
        cases proof with head tail,
            exact false.elim h₃,
        cases h₃ with c₁ c₂,
        rewrite c₁ at c₂,
        cases c₂ with easy hard,
            cases easy, exact h₁ φ easy,
            fsplit, exact [φ],
            constructor, refl,
            left, right, exact easy,
        cases hard with ψ h₂,
        fsplit,
            exact [φ, ψ, proposition.if_then ψ φ] ++ tail,
        constructor, refl,
        right, existsi ψ,
        constructor; left; simp,
        left, right, left, refl,
    end
}

-- We introduce quantifiers.
parameters (sort : Type u) [decidable_eq sort]

open list
-- inductive sort 
-- | empty {} : sort
-- | base (x : α) : sort
-- | prod  (s₁ : sort) (s₂ : sort) :  sort

-- def sort_card : sort → ℕ
-- | (sort.base _) := 1
-- | (sort.prod s₁ s₂) := (sort_card s₁) * (sort_card s₂)
-- | empty := 0


--set_option class.instance_max_depth 100
structure functional_symbol :=
    (name : string)
    (domain   : list sort)
    (codomain : sort)

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

def rarity (r : relational_symbol) := length r.sig

structure signature :=
    (sf : set functional_symbol)
    (sr : set relational_symbol)
    (unique_name₁ : ∀ f₁ f₂ : functional_symbol, f₁ ∈ sf → f₂ ∈ sf → f₁.name ≠ f₂.name)
    (unique_name₂ : ∀ r₁ r₂ : relational_symbol, r₁ ∈ sr → r₂ ∈ sr → r₁.name ≠ r₂.name)
    (unique_name₃ : ∀ (r₁ : relational_symbol) (f₂ : functional_symbol), r₁ ∈ sr → f₂ ∈ sf → r₁.name ≠ f₂.name)
    (head_project : ∀ f ∈ sf, tail_symbol f ∈ sf)

parameter (σ : signature)

def in_use  (s : sort) := 
    (∃ f : functional_symbol, f ∈ σ.sf ∧ (s ∈ f.domain ∨ s = f.codomain))
    ∨ (∃ r : relational_symbol, r ∈ σ.sr ∧ s ∈ r.sig)

def nary (n : ℕ) := subtype {f : functional_symbol | f ∈ σ.sf ∧ arity f = n}
@[reducible]
def const := nary 0

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

instance deq_pre_term : decidable_eq pre_term :=
begin
    intros x y,
    rcases x with x_var | ⟨n_x, ⟨f_x, fx_in_σ, fx_arity⟩, x_v⟩;
    rcases y with y_var | ⟨n_y, ⟨f_y, fy_in_σ, fy_arity⟩, y_v⟩;
    simp * at *;
    try{apply_instance},
    admit
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

def typing : pre_term → sort
| (pre_term.var ⟨s, _, _⟩) := s
| (pre_term.app f _) := f.val.codomain

def type_check_app {n} (f : nary n) (v : fin n → pre_term) : Prop :=
map typing (of_fn v) = f.val.domain

inductive consistently_typed : pre_term → Prop
| base {x : tvariable} : consistently_typed (pre_term.var x)
| app {n : ℕ} (f : nary n) (v : fin n → pre_term) 
    (h₀ : ∀ x, consistently_typed (v x)) (h₁ : type_check_app f v) 
    : consistently_typed (pre_term.app f v)

structure term :=
    (syntax : pre_term)
    (type_check : consistently_typed syntax)


inductive lambda.pre_term
| base : pre_term → lambda.pre_term
| lambda : tvariable → lambda.pre_term → lambda.pre_term
| app : lambda.pre_term → lambda.pre_term → lambda.pre_term

def free_variables : lambda.pre_term → set tvariable
| (lambda.pre_term.base t) := pre_term.variables t
| (lambda.pre_term.lambda x t) := free_variables t - {x} 
| (lambda.pre_term.app t₁ t₂) := free_variables t₁ ∪ free_variables t₂

def lambda.typing : lambda.pre_term → list sort
| (lambda.pre_term.base t) := [typing t]
| (lambda.pre_term.lambda ⟨s, _, _⟩ t) := s :: lambda.typing t
| (lambda.pre_term.app t₁ t₂) := tail (lambda.typing t₁)


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




--   finitary := 
--     begin 
--         intros Γ φ h,
--         cases h with proof is_proof,
--         dsimp at *,
--         simp at *,
--         existsi proof.to_finset.to_set ∩ Γ,
--         split, simp, split,
--             suffices h : finite (finset.to_set (list.to_finset proof)),
--             from ⟨@set.fintype_inter proposition
--                 (finset.to_set (list.to_finset proof)) Γ h.fintype (classical.dec_pred Γ)⟩,
--             apply finite_mem_finset,
--         existsi proof,
--         cases proof with head tail, 
--             exact false.elim is_proof,
--         cases is_proof with p₁ p₂,
--         split, assumption,
--         unfold finset.to_set, simp at *,
--         cases p₂ with c₁ c₂,
--             left, cases c₁,
--                 left, assumption,
--             right, assumption,
--         cases c₂ with ψ h,
--         cases h with h₁ h₂,
--         right, existsi ψ,
--         constructor,
--         cases h₁ with c₁ c₂,
--             left, exact c₁,
--         right,
--         cases c₂ with c₁ c₂, right,


        
        -- all_goals 
        --     {cases h₁ with c₁ c₂;
        --      try{cases c₂};
        --      cases h₂ with c₃ c₄;
        --      try{cases c₄}
        --     },
        -- repeat {left <|> right, assumption},
        -- any_goals {left, assumption},
        -- all_goals {right, try{cases c₂}},
        -- any_goals {right, assumption},
        -- all_goals {try{cases c₄}},
        -- any_goals {right, assumption},


        --dsimp at *, fsplit, work_on_goal 0 { fsplit, fsplit, work_on_goal 0 { fsplit }, work_on_goal 2 { intros x, cases x, simp at * } }, work_on_goal 3 { fsplit, work_on_goal 1 { assumption } } } 
    --end

-- instance minimal_propositional_logic : minimal_logic :=
-- {
--   encoding := _,
--   recursive := _,
--   connectives := _,
--   deduction_order := _,
--   and_intro := _,
--   or_elim := _,
--   True := proposition.true,
--   True_intro := _,
--   False := proposition.false,
--   implication := ⟨proposition.if_then⟩,
--   implication_definition := _,
--   implication_universal_property := _,
--   deduction_theorem := _,
--   ...}

def intuitionistic : Prop := ∀ {φ : L.formula}, L.False ≤ φ

def classical : Prop := intuitionistic ∧ ∀ {φ : L.formula}, Theorem (φ ⊔ -φ)

end propositional_logic

end logic