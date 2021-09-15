import tactic init.meta.interactive_base

open tactic interactive interactive.types
#check tactic.induction
#check interactive.induction
#check mk_const
#check ``(1)
#check intro
#check exact

#check applyc
#check prod.fst
#check first
#check focus
#check try

meta def tactic.my_tac (e : expr) : tactic unit :=
    do cases ← induction e,
    focus (list.map (λx, try $ applyc (prod.fst x)) cases)

meta def my_tac (q : parse texpr) : tactic unit :=
    i_to_expr ``(%%q) >>= tactic.my_tac

inductive test
| a : test
| b : test

example : ∀ t : test, ∃ x, x = t := 
begin
    intro t,
    have h := true.intro,
    -- my_tac h,
    admit
end
