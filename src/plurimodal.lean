import tactic
section modal
-- 2 modal logics: alethic, grounding

-- alethic logic
parameter {box₁ : Prop → Prop}
variable K : ∀ φ ψ : Prop, box₁ (φ → ψ) → box₁ φ → box₁ ψ
variable T : ∀ φ : Prop, box₁ φ → φ
-- also known as axiom 4, 
-- but lean doesnt let me use a number as an identifier
variable S4 : ∀ φ: Prop, box₁ φ → box₁ (box₁ φ)
-- variable S5 : 

-- let's assume in an ad hoc manner all instances
-- of the necessitation rule we will 
-- actually need for our proofs
variable n₁ : ∀ φ ψ : Prop, box₁ (φ ∧ ψ → φ)
variable n₂ : ∀ φ ψ : Prop, box₁ (φ ∧ ψ → ψ)
variable n₃ : ∀ φ ψ : Prop, box₁ (φ → ψ → φ ∧ ψ)

-- grounding logic
parameter {box₂ : Prop → Prop}
variable K₂ : ∀ φ ψ : Prop, box₂ (φ → ψ) → box₂ φ → box₂ ψ
variable T₂ : ∀ φ : Prop, box₂ φ → φ
-- also known as axiom 4, 
-- but lean doesnt let me use a number as an identifier
variable S4₂ : ∀ φ: Prop, box₂ φ → box₂ (box₂ φ)

-- let's assume in an ad hoc manner all instances
-- of the necessitation rule we will 
-- actually need for our proofs
variable n₁₂ : ∀ φ ψ : Prop, box₂ (φ ∧ ψ → φ)
variable n₂₂ : ∀ φ ψ : Prop, box₂ (φ ∧ ψ → ψ)
variable n₃₂ : ∀ φ ψ : Prop, box₂ (φ → ψ → φ ∧ ψ)

-- specific system axioms
variable a₁ : ∀ φ : Prop, box₁ (box₂ φ) → box₁ (φ → box₂ φ)
variable a₂ : ∀ φ : Prop, box₁ (box₂ ¬ (box₁ (¬ φ)))

variables φ ψ γ : Prop

local notation `□` := box₁
local notation `◾`:= box₂

def diamond (φ):= ¬ (box₁ (¬ φ))
def diamond₂ (φ):= ¬ (box₂ (¬ φ))

local notation `⋄` := diamond
local notation `✦` := diamond₂

-- lets prove that these operators are analogous
-- to topological kuratowski operators when defined
-- in an interior algebra. 
-- i.e. if the Lindenbaum-Tarski algebra 
-- of the propositional logic were complete and atomistic,
-- a "powerset", then they would give a definition of
-- a kuratowski interior/closure.
include K n₁ n₂ n₃
-- this here should be valid in minimal logic
theorem kuratowski : □ (φ ∧ ψ) ↔ (□ φ) ∧ (□ ψ) :=
begin
    constructor; intro h,
        constructor,
            apply K (φ ∧ ψ) φ,
            exact n₁ φ ψ,
            assumption,
        apply K (φ ∧ ψ) ψ,
        exact n₂ φ ψ,
        assumption,
    have c₀ := K φ (ψ → φ ∧ ψ),
    have c₁ := c₀ (n₃ φ ψ) h.1,
    apply K ψ (φ ∧ ψ) c₁,
    exact h.2
end
omit K n₁ n₂ n₃

-- to prove the analogous result for ⋄ we first
-- need to prove its derived S4 properties

theorem increasing : φ → ⋄ φ :=
    assume h₀ : φ,
    -- recall ⋄ φ = ¬ □ (¬ φ)
    assume h₁ : □ ¬ φ,
    have c : ¬ φ, from T (¬ φ) h₁,
    show false, from absurd h₀ c

-- notice the theorem obtained a dependency
-- from axiom T
#check increasing

-- theorem monotonicity : □ (φ → ψ) → ⋄ φ → ⋄ ψ :=
-- begin
--     intros h₁ h₂ h₃,
--     have c :
-- end

-- lets prove axiom D
theorem D : □ φ → ⋄ φ :=
    assume h : □ φ,
    have c : φ, from T φ h,
    increasing T φ c

end modal