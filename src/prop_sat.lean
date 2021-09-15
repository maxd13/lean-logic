import tactic.tidy tactic.library_search


inductive proposition
| false : proposition
| true : proposition
| atomic : ℕ → proposition
-- | and : proposition → proposition → proposition
| or : proposition → proposition → proposition
| not : proposition → proposition
-- | if_then : proposition → proposition → proposition

-- def proposition.if_then : proposition → proposition → proposition
-- | φ ψ := proposition.or (proposition.not φ) ψ

-- notation p `⇒` q := proposition.if_then p q

-- def proposition.not :  proposition → proposition := λ p, p ⇒ proposition.false

def proposition.and : proposition → proposition → proposition
| φ ψ := proposition.not $ proposition.or (proposition.not φ) (proposition.not ψ)

-- def proposition.iff : proposition → proposition → proposition
-- | φ ψ := proposition.and (φ ⇒ ψ) (ψ ⇒ φ) 

def proposition.eval : proposition → (ℕ → bool) → bool
| proposition.false _ := ff
| proposition.true _ := tt
| (proposition.atomic n) f := if f n then tt else ff
-- | (proposition.and φ ψ) f := φ.eval f && ψ.eval f  
| (proposition.or φ ψ) f := φ.eval f || ψ.eval f
| (proposition.not φ) f := not (φ.eval f)
-- | (proposition.if_then φ ψ) f := not (φ.eval f) || ψ.eval f

def proposition.appears : proposition → ℕ → bool
| proposition.false _ := ff
| proposition.true  _ := ff
| (proposition.atomic m) n := if n = m then tt else ff
-- | (proposition.and φ ψ) n := φ.appears n || ψ.appears n
| (proposition.or φ ψ) n := φ.appears n || ψ.appears n
| (proposition.not φ) f := φ.appears f
-- | (proposition.if_then φ ψ) n := φ.appears n || ψ.appears n

def theory.appears : list proposition → ℕ → bool
| [] _ :=  ff
| (x::xs) n := x.appears n || theory.appears xs n

lemma theory.exists : ∀ (Γ : list proposition) n, 
                      theory.appears Γ n →
                      ∃ φ ∈ Γ, proposition.appears φ n
                      :=
begin
    intros Γ n h,
    induction Γ;
        simp [theory.appears] at h,
        contradiction,
    cases h,
        existsi Γ_hd,
        fsplit, simp,
        assumption,
    obtain ⟨φ, c₁, c₂⟩ := Γ_ih h,
    existsi φ,
    fsplit,
        simp [c₁],
    assumption,
end

def proposition.satisfiable (φ : proposition) :=
    ∃ I : ℕ → bool, φ.eval I 


-- This code here actually implements the sat solver...
-- FROM A TACTIC PROOF!!!
instance sat_solver (φ : proposition) : decidable φ.satisfiable :=
let I₁ := λn : ℕ, tt in
begin
    induction φ,
    -- case false
        left,
        intro h,
        obtain ⟨I, c⟩ := h,
        simp [proposition.eval] at c,
        contradiction,
    -- case true
        right,
        existsi I₁,
        simp [proposition.eval],
    -- case atomic
        right,
        existsi I₁,
        simp [proposition.eval],
    -- case and
        -- This is actually hard.
        -- We only managed to prove that if
        -- either side of the conjunction is
        -- unsat, then the conjunction is unsat.
        -- maybe that is why most algorithms assume
        -- that the proposition is on
        -- a particular normal form.
        -- So when we got to this point,
        -- we changed the definition of proposition
        -- to use only ∨ and ¬, which is 
        -- functionally complete.

        -- cases φ_ih_a,
        --     left,
        --     intro h,
        --     obtain ⟨I, c⟩ := h,
        --     simp [proposition.eval] at c,
        --     replace c : φ_a.satisfiable := ⟨I,c.1⟩,
        --     contradiction,
        -- cases φ_ih_a_1,
        --     left,
        --     intro h,
        --     obtain ⟨I, c⟩ := h,
        --     simp [proposition.eval] at c,
        --     replace c : φ_a_1.satisfiable := ⟨I,c.2⟩,
        --     contradiction,
    -- case or
        cases φ_ih_a,
            cases φ_ih_a_1,
                left,
                intro h,
                obtain ⟨I, c⟩ := h,
                simp [proposition.eval] at c,
                cases c,
                    replace c : φ_a.satisfiable := ⟨I,c⟩,
                    contradiction,
                replace c : φ_a_1.satisfiable := ⟨I,c⟩,
                contradiction,
            right,
            obtain ⟨I, c⟩ := φ_ih_a_1,
            existsi I,
            simp [proposition.eval],
            right,
            assumption,
        right,
        obtain ⟨I, c⟩ := φ_ih_a,
        existsi I,
        simp [proposition.eval],
        left,
        assumption,
    -- case not
        cases φ_ih,
            right,
            have c := not_exists.mp φ_ih I₁,
            existsi I₁,
            simp [proposition.eval],
            simp at c,
            rw c,
            simp,
        admit,
    -- case if_then
    -- cases φ_ih_a,
    --     right,
    --     existsi I₁,
    --     simp [proposition.eval],
    --     have c := not_exists.mp φ_ih_a I₁,
    --     simp at c,
    --     left,
    --     rw c,
    --     simp,
    -- cases φ_ih_a_1,
    --     left,
    --     intro h,
    --     obtain ⟨I, c⟩ := h,
    --     simp [proposition.eval] at c,
end

def proposition.sat : proposition → bool
| φ := if φ.satisfiable then tt else ff

#reduce proposition.false.sat
#reduce proposition.true.sat
#reduce λ n, (proposition.atomic n).sat
#reduce λ n, (proposition.or (proposition.atomic n) proposition.false).sat
#reduce λ n, (proposition.or (proposition.atomic n) (proposition.not $ proposition.atomic n)).sat
-- #reduce λ n, (proposition.and (proposition.atomic n) (proposition.not $ proposition.atomic n)).sat

def proposition.follows (Γ : list proposition) : proposition → Prop
| φ :=    ∀ (I : ℕ → bool), 
          (∀ ψ ∈ Γ, proposition.eval ψ I == tt) →
          φ.eval I == tt

-- instance proposition_decidable (Γ : list proposition) (φ : proposition) :decidable (φ.follows Γ) :=
-- begin
--     induction φ,
--         admit,
--     right,
--     intros I h,
--     refl,
--     by_cases (theory.appears Γ φ) = tt,
--         have c : Prop,
--             obtain ⟨ψ, c₀, c₁⟩ := theory.exists Γ φ h,
--         replace h₂ := h₂ ψ c₀,
--         right,
--         intros I h₂,
--         dsimp [proposition.eval],
--         simp,
--         -- let ψ := proposition.atomic φ,

--         -- induction Γ;
--         --     simp [theory.appears] at h,
--         --     contradiction,
        
--         -- have c := h ψ h₂,

-- end

-- def proposition.decide : proposition → set proposition → bool
-- | φ Γ := if φ.follows Γ then tt else ff

