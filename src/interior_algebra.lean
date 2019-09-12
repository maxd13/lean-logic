import data.set.lattice topology.basic order.bounded_lattice
open set lattice
set_option old_structure_cmd true
universe u

class has_operator (α : Type u) :=
    (operator : α → α)

notation `#` := has_operator.operator

class order_retract (α : Type u) extends has_operator α, order_top α, order_bot α :=
    (monotone : ∀ x y : α, x ≤ y → # x ≤ # y) -- Axiom K
    (idempotent : ∀ x : α, (# ∘ #) x = # x) -- Axiom 4

class necessity (α : Type u) extends order_retract α :=
    (decreasing :  ∀ x : α, # x ≤ x) -- Axiom T
    (top_open : # top = top) -- Necessitation rule

class possibility (α : Type u) extends order_retract α :=
    (increasing :  ∀ x : α, x ≤ # x)
    (bot_closed : # bot = bot)

class interior_algebra (α : Type u) extends necessity α, boolean_algebra α
class closure_algebra (α : Type u) extends possibility α, boolean_algebra α

notation `□` := necessity.operator
notation `⋄` := possibility.operator

variable {α : Type u}

@[simp, reducible]
def pbot [c : closure_algebra α] :  ⋄ ⊥ = (⊥:α)  := c.bot_closed

lemma possibility_top_open [closure_algebra α] : -⋄(-⊤) = (⊤:α) := 
    by simp --rw [neg_top, pbot, neg_bot]
    

instance classical_possibility [necessity α] [Ω : boolean_algebra α] : possibility α := 
{ operator := - (□ ∘ has_neg.neg),
  monotone := sorry,
  idempotent := sorry,
  increasing := sorry,
  bot_closed := sorry,
  ..Ω }

instance classical_necessity [possibility α] [Ω : boolean_algebra α] : necessity α := 
{ operator := - (⋄ ∘ has_neg.neg),
  monotone := sorry,
  idempotent := sorry,
  decreasing := sorry,
  top_open := sorry,
  ..Ω }

instance set_dualize₁ [necessity (set α)] : possibility (set α) := by apply_instance 
instance set_dualize₂ [possibility (set α)] : necessity (set α) := by apply_instance

open topological_space
instance topological_interior [topological_space α ] : necessity (set α) := 
{
  operator := interior,
  monotone := @interior_mono α _ ,
  idempotent := @interior_interior α _,
  decreasing := @interior_subset α _,
  top_open := @interior_univ α _,
  ..set.lattice_set  }

instance topological_closure [topological_space α ] : possibility (set α) := by apply_instance

instance closure_from_possibility [p : possibility (set α)] : topological_space α := 
{ is_open := λ s, - ⋄(-s) = s,
  is_open_univ := by {!!),--by rwa p.bot_closed,
  is_open_inter := _,
  is_open_sUnion := _ }

-- instance topological_closure [topological_space α ] : possibility (set α) := 
-- {
--   operator := closure,
--   monotone := @closure_mono α _ ,
--   idempotent := @closure_closure α _,
--   increasing := @subset_closure α _,
--   bot_closed := @closure_empty α _,
--   ..set.lattice_set  }
