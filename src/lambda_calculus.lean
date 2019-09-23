import predicate_logic
universe u

open logic list

section lambda

parameters {sort : Type u} [decidable_eq sort]
parameter {σ : @signature sort _}

local notation `pre_term` := @pre_term sort _ σ
local notation `var` := @tvariable sort _ σ

inductive lambda_pre_term
| base : pre_term → lambda_pre_term
| lambda : var → lambda_pre_term → lambda_pre_term
| app : lambda_pre_term → lambda_pre_term → lambda_pre_term

def free_variables : lambda_pre_term → set var
| (lambda_pre_term.base t) := pre_term.variables t
| (lambda_pre_term.lambda x t) := free_variables t - {x} 
| (lambda_pre_term.app t₁ t₂) := free_variables t₁ ∪ free_variables t₂

def lambda.typing : lambda_pre_term → list sort
| (lambda_pre_term.base t) := [typing t]
| (lambda_pre_term.lambda ⟨s, _, _⟩ t) := s :: lambda.typing t
| (lambda_pre_term.app t₁ t₂) := tail (lambda.typing t₁)

end lambda