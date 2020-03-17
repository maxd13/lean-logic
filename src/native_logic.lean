import tactic.find tactic.tidy data.set.basic
universe u

namespace metalogic

open tactic set

-- We wanted to define what a tautology is in order
-- to define a necessitation rule for normal modal logics
-- in terms of this notion of tautology. 
-- However our approach did not work.
-- For this approach to work the defined proof system
-- would have to be incomplete relative to provability
-- or "truth" in LEAN. However we were able to prove
-- that given a proof of proposition φ we can build
-- a proof of proposition provable.minimal Γ φ
-- for any set Γ of propositions.


inductive provable.minimal : set Prop → Prop → Prop
| reflexive (Γ : set Prop) (φ : Prop) (h : set.mem φ Γ) : provable.minimal Γ φ
| transitivity (Γ Δ : set Prop) (φ : Prop)
               (h₁ : ∀ ψ ∈ Δ, provable.minimal Γ ψ)
               (h₂ : provable.minimal Δ φ) 
                : provable.minimal Γ φ
| and_intro (φ ψ : Prop) (Γ : set Prop)
            (h₁ : provable.minimal Γ φ)
            (h₂ : provable.minimal Γ ψ)
             : provable.minimal Γ (φ ∧ ψ)
| and_elim_left (φ ψ : Prop) (Γ : set Prop)
            (h : provable.minimal Γ (φ ∧ ψ))
             : provable.minimal Γ φ
| and_elim_right (φ ψ : Prop) (Γ : set Prop)
            (h : provable.minimal Γ (φ ∧ ψ))
             : provable.minimal Γ ψ
| or_intro_left 
            (φ ψ : Prop) (Γ : set Prop)
            (h : provable.minimal Γ φ)
             : provable.minimal Γ (φ ∨ ψ)
| or_intro_right 
            (φ ψ : Prop) (Γ : set Prop)
            (h : provable.minimal Γ ψ)
             : provable.minimal Γ (φ ∨ ψ)
| or_elim
            (φ ψ δ : Prop) (Γ : set Prop)
            (h₁ : provable.minimal Γ (φ ∨ ψ))
            (h₂ : provable.minimal Γ (φ → δ))
            (h₃ : provable.minimal Γ (ψ → δ))
             : provable.minimal Γ δ
| modus_ponens
            (φ ψ : Prop) (Γ : set Prop)
            (h₁ : provable.minimal Γ (φ → ψ))
            (h₂ : provable.minimal Γ φ)
             : provable.minimal Γ ψ
| intro
            (φ ψ : Prop) (Γ : set Prop)
            (h : provable.minimal (Γ ∪ {φ}) ψ)
             : provable.minimal Γ (φ → ψ)
| true_intro
            (Γ : set Prop)
             : provable.minimal Γ true
| for_all_intro
            {α : Type u}
            (Γ : set Prop) (p : α → Prop)
            (h : ∀ x : α, provable.minimal Γ (p x))
             : provable.minimal Γ (∀ x:α, p x)
| for_all_elim
            {α : Type u}
            (Γ : set Prop) (p : α → Prop)
            (c : α)
            (h : provable.minimal Γ (∀ x : α, p x))
             : provable.minimal Γ (p c)
| exists_intro 
            {α : Type u}
            (Γ : set Prop) (p : α → Prop)
            (c : α)
            (h : provable.minimal Γ (p c))
             : provable.minimal Γ (∃x:α, p x)
| exists_elim 
            {α : Type u}
            (Γ : set Prop) (p : α → Prop)
            (ψ : Prop)
            (h₁ : provable.minimal Γ (∃x:α, p x))
            (h₂ : ∀ x:α, provable.minimal Γ (p x → ψ))
             : provable.minimal Γ ψ
| identity_intro
            {α : Type u}
            (Γ : set Prop) (c : α)
             : provable.minimal Γ (c = c)
| identity_elim
            {α : Type u}
            (Γ : set Prop) (p : α → Prop)
            (c₁ c₂: α)
            (h : provable.minimal Γ (p c₁))
            (eq : provable.minimal Γ (c₁ = c₂))
             : provable.minimal Γ (p c₂)

variables {Γ : set Prop} {φ : Prop}

example : provable.minimal.{u} Γ (φ → φ) :=
begin
    apply provable.minimal.intro,
    apply provable.minimal.reflexive (Γ∪{φ} : set Prop) φ,
    right, 
    -- this would be needed if we forgot the .{u}
    -- apply singleton_subset_iff.mp,
    simp,
end

-- here is the proof why this approach doesn't quite work:
theorem completeness.minimal : φ → minimal Γ φ :=
begin
    intro h₁,
    have c₁ := classical.eq_true_or_eq_false φ,
    cases c₁,
        rw c₁,
        apply provable.minimal.true_intro Γ,
    simp at c₁,
    contradiction,
end

-- it doesn't help to remove the true_intro rule
-- because it can be proven using the same logic:
-- (1) prove that Γ proves false → false, 
-- (2) simplify false → false to true,
-- (3) conclude that Γ proves true

-- and it gets worse than that:

def complete.minimal (Γ : set Prop) := ∀ φ : Prop, provable.minimal.{u} Γ φ ∨ provable.minimal.{u} Γ (¬φ)

theorem universal_decidibility.minimal : complete.minimal Γ :=
begin
    intro φ,
    classical,
    by_cases φ,
        left,
        apply completeness.minimal,
        assumption,
    right,
    apply completeness.minimal,
    assumption,
end

-- It might have worked out if we refrained
-- from using classical logic, but there isn't a 
-- clear requirement that we refrain from it.
-- Even if we do another user of this module might use it,
-- and he might prove the same result we did above.
-- There is no way to keep tabs on where classical
-- reasoning is being used.

-- It would be more useful if whenever we used
-- classical logic, we had to add a tag
-- to the theorem or definition name, like "meta"
-- or "noncomputable" are already in use.


-- Which is pretty sad because I made all these nice
-- other proofs:

theorem provable.minimal.monotonicity : ∀ (Δ ⊆ Γ) (ψ : Prop), provable.minimal.{u} Δ ψ → provable.minimal.{u} Γ ψ :=
begin
    intros Δ H ψ h,
    -- induction on the possible ways in which
    -- Δ could prove ψ
    induction h,
    -- case it was proven by reflection
        apply provable.minimal.reflexive Γ h_φ,
        exact H h_h,
    -- case it was proven by transitivity
        apply provable.minimal.transitivity Γ h_Δ h_φ,
        intros ψ₂ elem,
        repeat {assumption <|> apply_assumption},
    -- case it was proven by and_intro
        apply provable.minimal.and_intro,-- h_φ h_ψ Γ,
        repeat {assumption <|> apply_assumption},
    -- case it was proven by and_elim_left
        apply provable.minimal.and_elim_left h_φ h_ψ Γ,
        repeat {assumption <|> apply_assumption},
    -- case it was proven by and_elim_right
        apply provable.minimal.and_elim_right h_φ h_ψ Γ,
        repeat {assumption <|> apply_assumption},
    -- case it was proven by or_intro_left
        apply provable.minimal.or_intro_left h_φ h_ψ Γ,
        repeat {assumption <|> apply_assumption},
    -- case it was proven by or_intro_right
        apply provable.minimal.or_intro_right h_φ h_ψ Γ,
        repeat {assumption <|> apply_assumption},
    -- case it was proven by or_elim
        apply provable.minimal.or_elim,-- h_φ h_ψ h_δ Γ,
        repeat {assumption <|> apply_assumption},
    -- case it was proven by modus ponens
        apply provable.minimal.modus_ponens h_φ h_ψ Γ,
        repeat {assumption <|> apply_assumption},
    -- case it was proven by intro
        have c : provable.minimal h_Γ (h_φ → h_ψ),
            apply provable.minimal.intro h_φ h_ψ h_Γ,
            assumption,
        apply provable.minimal.transitivity Γ h_Γ (h_φ → h_ψ),
            intros ψ₂ elem,
            have c₂ := H elem,
            exact provable.minimal.reflexive Γ ψ₂ c₂,
        assumption,
    -- case it was proven by true_intro
        exact provable.minimal.true_intro Γ,
    -- case it was proven by for_all_intro
        apply provable.minimal.for_all_intro,
        intro x,
        have c := h_ih x,
        repeat {assumption <|> apply_assumption},
    -- case it was proven by for_all_elim
        apply provable.minimal.for_all_elim,
        repeat {assumption <|> apply_assumption},
    -- case it was proven by exists_intro
        apply provable.minimal.exists_intro,
        repeat {assumption <|> apply_assumption},
    -- case it was proven by exists_elim
        have c : minimal h_Γ h_ψ,
            apply provable.minimal.exists_elim h_Γ h_p h_ψ,
            repeat {assumption <|> apply_assumption},
        apply provable.minimal.exists_elim Γ h_p h_ψ,
        repeat {assumption <|> apply_assumption},
        intro x,
        repeat {assumption <|> apply_assumption},
    -- case it was proven by identity_intro
        apply provable.minimal.identity_intro,
    -- case it was proven by identity_elim
        apply provable.minimal.identity_elim,
        repeat {assumption <|> apply_assumption},
end

-- prove that minimal logic is sound relative to LEAN
-- semantics.
theorem provable.minimal.sound : provable.minimal Γ φ →
                                (∀ ψ ∈ Γ, ψ) →
                                 φ :=
begin
    intros h₀ h₁,
    induction h₀,
    -- case it was proven by reflection
    apply_assumption, assumption,
    -- case it was proven by transitivity
        apply h₀_ih_h₂,
        intros ψ elem,
        have c := h₀_ih_h₁ ψ elem,
        exact c h₁,
    -- case it was proven by and_intro
        constructor;
        apply_assumption; assumption,
    -- case it was proven by and_elim_left
        exact (h₀_ih h₁).1,
    -- case it was proven by and_elim_right
        exact (h₀_ih h₁).2,
    -- case it was proven by or_intro_left
        left,
        apply_assumption, assumption,
    -- case it was proven by or_intro_right
        right,
        apply_assumption, assumption,
    -- case it was proven by or_elim
        cases h₀_ih_h₁ h₁ with h,
            exact h₀_ih_h₂ h₁ h,
        exact h₀_ih_h₃ h₁ h,
    -- case it was proven by modus ponens
        apply h₀_ih_h₁ h₁,
        apply_assumption, assumption,
    -- case it was proven by intro
        have c : (∀ (ψ : Prop), ψ ∈ h₀_Γ ∪ {h₀_φ} → ψ),
            intros ψ elem,
            cases elem,
                exact h₀_h₁ ψ elem,
            simp at elem,
            exact elem.2 a,
        apply_assumption, assumption,
    -- case it was proven by true_intro
        exact true.intro,
    -- case it was proven by for_all_intro
        have c := h₀_ih x,
        apply_assumption, assumption,
    -- case it was proven by for_all_elim
        exact h₀_ih h₁ h₀_c,
    -- case it was proven by exists_intro
        existsi h₀_c,
        apply_assumption, assumption,
    -- case it was proven by exists_elim
        obtain ⟨x, p⟩ := h₀_ih_h₁ h₁,
        have c := h₀_ih_h₂ x,
        exact c h₁ p,
    -- case it was proven by identity_intro
        refl,
    -- case it was proven by identity_elim
        have c := h₀_ih_h h₁,
        rwa h₀_ih_eq h₁ at c,
end

lemma provable.minimal.cond : provable.minimal.{u} Γ φ → ∀ ψ : Prop, provable.minimal.{u} Γ (ψ → φ) :=
begin
    intros h ψ,
    apply provable.minimal.intro,
    apply provable.minimal.monotonicity Γ,
        simp,
    assumption,
end

def tautology.minimal (φ : Prop) : Prop := provable.minimal ∅ φ

def consistent.minimal (Γ : set Prop) := ¬ ∀ φ : Prop, provable.minimal.{u} Γ φ 

inductive provable.constructive : set Prop → Prop → Prop
| minimal (Γ : set Prop) (φ : Prop) 
          (h : provable.minimal Γ φ)
           : provable.constructive Γ φ
| quodlibet (Γ : set Prop) (φ : Prop)
           : provable.constructive Γ (false → φ)


theorem provable.constructive.sound : provable.constructive Γ φ →
                                (∀ ψ ∈ Γ, ψ) →
                                 φ :=
begin
    intros h₀ h₁,
    induction h₀,
        exact provable.minimal.sound h₀_h h₁,
    contradiction,
end

-- lemma provable.constructive.cond : provable.constructive.{u} Γ φ → ∀ ψ : Prop, provable.constructive.{u} Γ (ψ → φ) :=
-- begin
--     intros h ψ,
--     cases h,
-- end

-- lemma provable.constructive.intro : ∀ φ ψ : Prop, 
--                                 (provable.constructive.{u} (Γ ∪ {φ}) ψ)
--                                 → provable.constructive.{u} Γ (φ → ψ) :=
-- begin
--     intros φ ψ h,
--     rcases h with h₁| h₂,
--         apply provable.constructive.minimal,
--         apply provable.minimal.intro,
--         have c : ((Γ ∪ {φ}) : set Prop) = λ (a : Prop), a ∈ Γ ∨ a ∈ ({φ}:set Prop),
--             trivial,
--         rwa c,
--     simp,
        
        
-- end

def tautology.constructive (φ : Prop) : Prop := provable.constructive ∅ φ

inductive provable.classical : set Prop → Prop → Prop
| constructive (Γ : set Prop) (φ : Prop) 
               (h : provable.constructive Γ φ)
                : provable.classical Γ φ
| by_contradiction (Γ : set Prop) (φ : Prop)
                    (h : provable.classical Γ (¬φ → false))
                    : provable.classical Γ φ

theorem provable.classical.sound : provable.classical Γ φ →
                                (∀ ψ ∈ Γ, ψ) →
                                 φ :=
begin
    intros h₀ h₁,
    induction h₀,
        exact provable.constructive.sound h₀_h h₁,
    have c := h₀_ih h₁,
    classical,
    by_contradiction h,
    exact c h,
end

def tautology.classical (φ : Prop) : Prop := provable.classical ∅ φ

-- lemma provable.classical.intro : ∀ φ ψ : Prop, 
--                                 (provable.classical (Γ ∪ {φ}) ψ)
--                                 → provable.classical Γ (φ → ψ)
-- :=
-- begin
--     intros φ ψ h,
--     cases h,
--         apply provable.classical.constructive,
--     -- apply provable.constructive.minimal,
-- end

-- example : tautology.classical (φ ∨ ¬ φ) :=
-- begin
--     unfold tautology.classical,
--     apply provable.classical.by_contradiction ∅ (φ ∨ ¬ φ),
--     apply provable.classical.constructive ∅ (¬(φ ∨ ¬φ) → false),
--     apply provable.constructive.minimal ∅ (¬(φ ∨ ¬φ) → false),
--     apply provable.minimal.intro (¬(φ ∨ ¬φ)) false ∅, simp,
--     have c₀ : minimal ∅ (φ → φ ∨ ¬φ),
--         -- apply provable.classical.constructive ∅ (φ → φ ∨ ¬φ),
--         -- apply provable.constructive.minimal ∅ (φ → φ ∨ ¬φ),
--         apply provable.minimal.intro φ (φ ∨ ¬φ) ∅,
--         simp,
--         apply provable.minimal.or_intro_left φ (¬φ) {φ},
--         apply provable.minimal.reflexive {φ} φ,
--         -- again, what the hell???
--         apply singleton_subset_iff.mp,
--         simp,
--     have c₁ : minimal
    
        
-- end

end metalogic