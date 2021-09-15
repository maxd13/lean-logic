import tactic.tidy

universe u

section necessary

parameter entity : Type u
parameter situation : Type u
parameter exist : entity → Prop
parameter obtain : situation → Prop
parameter cause : entity → situation → Prop
parameter necessary : Prop → Prop

def possible (p : Prop) := ¬ necessary (¬ p)

local notation `⋄` := possible
local notation `□` := necessary

def necessary (e : entity) := □ (exist e)

-- #check ∃ e, ⋄ (necessary e)

def contingent₁ (e : entity) := 
    ¬ □ (exist e) ∧ ⋄ (exist e)

def contingent₂ (s : situation) := 
    ¬ □ (obtain s) ∧ ⋄ (obtain s)

def has_causal_powers (e : entity) :=
    ∃ s, ⋄ (cause e s)

def causable (s : situation) :=
    ∃ e, ⋄ (cause e s)

def necessary_being (e : entity) :=
    necessary e ∧ has_causal_powers e

def something_uncausable := 
    (∃ s, contingent₂ s ∧ obtain s) →
    (∃ s, contingent₂ s ∧ obtain s ∧ ¬ causable s)

parameter h₁ : ¬ □ something_uncausable

include h₁
lemma c₁ : ⋄ ¬ something_uncausable :=
    by simp [possible, classical.not_not]; exact h₁

-- lemma c₂ : ¬ something_uncausable →
--           ∀ s, contingent₂ s →
--           obtain s →
--           causable s :=
-- begin
--     intros h s con obt,
-- end




-- theorem God : 
-- ∃ (w : world) g : entity,
--  (necessary g)  ∧ (has_causal_powers g) :=



-- sorry



end necessary