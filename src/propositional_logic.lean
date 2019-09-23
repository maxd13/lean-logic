import formal_system

open logic

section propositional_logic

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


end propositional_logic