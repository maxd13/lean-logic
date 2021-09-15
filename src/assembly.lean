import tactic.tidy

-- assembly verification

inductive assembly.expr
| cons : ℕ → assembly.expr
| register : fin 12 → assembly.expr

inductive assembly.cmd
| mov : assembly.expr → assembly.expr → assembly.cmd
| add : assembly.expr → assembly.expr → assembly.cmd

def assembly.program := list assembly.cmd

def assembly.state := fin 12 → ℕ

-- def assembly.run (state : assembly.state) :
--                   assembly.cmd → option assembly.state
-- | (cmd.mov (expr.cons n) (expr.register i)) := some $ λ r,
--                                                if r = i 
--                                                then n
--                                                else state r
-- | (cmd.mov (expr.register j) (expr.register i)) := some $ λ r,
--                                                    if r = i
--                                                    then state j
--                                                    else state r
-- | (cmd.add a a_1) := sorry
-- | _  := none

example : ∀ n : ℕ, ∃ m : ℕ, n + 1 = m  :=
begin
    intro n,
    existsi n+1,
    refl,
end



