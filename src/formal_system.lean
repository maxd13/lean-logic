import tactic data.set.countable
open set lattice
universe u

-- Basic definitions of formal systems and logics.

namespace logic

class formal_system :=
    (formula : Type u)
    (entails : set formula → formula → Prop)

infixr `⊢`:50 := formal_system.entails

section basic_definitions
parameter {L : formal_system}

@[reducible]
def formula := L.formula

-- local notation `formula` := L.formula

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

-- Proofs become more readable if we specify which axioms we are using from the definition of a structure
-- in the beggining of the proof. This way we know what to expect to be used, and it becomes easier to analyze
-- the dependencies of results on axioms.

-- The proofs of this section are supposed to be used to define a
-- closure algebra.

lemma subset_proof : ∀ {Γ Δ : set L.formula}, Γ ⊆ Δ → Δ ≤ Γ :=
    let rf := L.reflexivity in
    assume Γ Δ : set L.formula,
    assume h₀ : Γ ⊆ Δ,
    assume φ : L.formula,
    assume h₁ : φ ∈ Γ,
    have c₀ : φ ∈ Δ, from h₀ h₁,
    show Δ ⊢ φ, from rf Δ φ c₀

-- as we can see, for a non-monotonic logic we would have to drop
-- either the reflexivity or the transitivity axiom.
-- Fun fact: the Aristotelian name for "non-monotonic logic" would be Rhetoric.
lemma C_monotone : ∀ {Γ Δ : set L.formula}, Γ ⊆ Δ → C Γ ⊆ C Δ :=
    let tr := L.transitivity in
    assume Γ Δ : set L.formula,
    assume h₀ : Γ ⊆ Δ,
    assume φ : L.formula,
    assume h₁ : φ ∈ C Γ,
    have c₀ : Γ ⊢ φ, from h₁,
    have c₁ : Δ ≤ Γ, from subset_proof h₀,
    show φ ∈ C Δ, from tr Δ Γ φ c₁ c₀

lemma C_increasing : ∀ {Γ : set L.formula}, Γ ⊆ C Γ := L.reflexivity

lemma C_idempotent : ∀ (Γ : set L.formula), C (C Γ) = C Γ :=
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


instance entailment_preorder : preorder (set L.formula) := 
let tr := L.transitivity in
{ le := λ Γ Δ, ∀ ψ ∈ Δ, Γ ⊢ ψ,
  lt := λ Γ Δ, (∀ ψ ∈ Δ, Γ ⊢ ψ) ∧ ¬ (∀ ψ ∈ Γ, Δ ⊢ ψ),
  le_refl := by intros S φ h; apply @subset_proof _ {φ} S; simp; assumption,
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

section deduction

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

def intuitionistic : Prop := ∀ {φ : L.formula}, L.False ≤ φ

def classical : Prop := intuitionistic ∧ ∀ {φ : L.formula}, Theorem (φ ⊔ -φ)

end deduction
end logic