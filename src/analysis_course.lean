--Thu Aug 22 08:26:12 -03 2019
-- Luiz Carlos R. Viana

import data.set.basic algebra.big_operators
data.nat.basic data.real.basic 
tactic.tidy

-- We formalize the curriculum of a basic analysis course from scratch in Lean
-- (even though this is already part of the standard library).

-- The goal here however is the readability and simplicity of proofs, so that this material may
-- be used to teach undergraduate students about sets and proofs in the future. 
-- For details about the language itself, the reader should refer to the guide "Theorem Proving in Lean", which can be
-- found at https://Leanprover.github.io/theorem_proving_in_Lean/index.html (access date = date of this document).

-- On a more technical note, since interactive theorem provers use type theory instead of set theory as a foundation
-- for mathematics, in order to develop the usual (material, pure) set theoretic foundation of analysis within 
-- this type theory, we would need to consider an internal model of set theory within type theory. 
-- This was already accomplished in the standard library in the module set_theory.zfc, but the approach used there
-- is unnecessarily technical for our purposes, as it would be hard to teach using the foundations there outlined.

-- Instead the approach used here is simply to declare a type of base things a set can be composed of and then prove
-- results in a similar fashion as is done in the standard library, such as in data.set.basic. This gives us a more
-- canonical way of writing this material without having to concern ourselves all that much with complex constructions involving
-- types. As an inevitable result of this, when we go up the hierarchy of sets we will notice that ∈ is unavoidably 
-- type theoretical, since x ∈ y is not defined for arbitrary sets x and y.

-- We begin with the primitive notion of a Type. A Type is a kind of thing, and each thing has a single type.
-- For instance, there is a Type ℕ of numbers, and the things of Type ℕ are called natural numbers. We write n : ℕ
-- to indicate that n is an instance of Type ℕ, i.e. that n is a natural number.

-- One thing that is important to notice about the declaration "n : ℕ" is that it is not a proposition, as it
-- makes little sense to ask wether it is true or false. Rather the typing declaration of n is a presupposition of
-- any proposition we make involving n, without which it would not make sense. For instance, we can say 
-- "the number 2 is walking in the street", and one interpretation of this expression would say that it is a proposition
-- that is false; but certainly there is something else going on here. If the expression is false, it doesn't appear to be
-- false in the exact same sense in which we say that "2 = 3" is false, but rather it would appear to us that the expression
-- itself is nonsensical. "Walking in the street" simply is not an operation that is defined for natural numbers, so the
-- expression itself, though it may pose as a proposition, is ill-formed. Rather, we must presuppose that we know the types
-- of things that we are talking about so as to understand the possible ways we can form propositions involving them.
-- In type theory we consider that both propositions and typing declarations are different forms of judgement.
open set
namespace hidden

-- Where do Types live in? We can define an universe of discourse which will include all Types relevant to the development
-- of our theory, and this universe will be the collection of all our Types. 
universe u

-- All that is needed to develop set theory from type theory is a single Type of things we wish
-- to talk about, so let α be a Type in the universe u

variable α : Type u

-- A set X of α's can be identified with a function which takes x : α and constructs a proposition "x is an element of X".
-- This is already defined in Lean's standard library, so we simply reproduce that definition here.
-- def set (α : Type u) := α → Prop

-- We can give a few examples of sets of different Types, for instance instead of α we could use natural numbers:
example : set ℕ := {x : ℕ | x > 0} -- this is the set of all natural numbers greater than 0.
example : set ℕ := {1, 2, 3}

-- If X is a set, the symbol ∈ is used as notation for membership in X, so if x : α, the proposition x ∈ X is the
-- one we get by applying X over x as a function.

-- We now start to define important notions involving sets. The first of them is set inclusion:

-- This definition says that s₁ is a subset of s₂ if and only if every element of s₁ is an element of s₂
def subset (s₁ s₂ : set α) := ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂

-- in order to be able to use the notation ⊆ for sets we need to tell Lean's elaborator that the type set α is
-- one of those types for which this notation is defined. We do this with the following command.
instance : has_subset (set α) :=
⟨set.subset⟩

-- 2 sets X and Y are said to be equal if and only if they have exactly the same elements, i.e. X ⊆ Y and Y ⊆ X.
-- This is called the principle of extensionality for sets. Since Lean treats equality as a primitive concept,
-- we don't really have to define it, rather it is possible to prove from certain axioms within Lean that 2 sets
-- are equal if and only if they have the same elements. The important theorem of the standard library that does this
-- is declared as:
-- theorem ext {a b : set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b

-- We need to keep in mind only that to prove equality between 2 sets X and Y, all we need to do is take
-- an element of X and prove that it is in Y, and then take an element of Y and prove that it is in X.
-- This is equivalent to proving both X ⊆ Y and Y ⊆ X.
-- To aid such proofs there is also a theorem in the standard library:
-- theorem eq_of_subset_of_subset {a b : set α} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b

-- For instance, here is a proof that every set is equal to itself.  

--#check or.elim

example : ∀ s : set α, s = s :=
    assume s : set α,
    have s ⊆ s, from
        (assume x : α,
         assume h : x ∈ s,
         show x ∈ s, from h
        ),
    show s = s, from eq_of_subset_of_subset this this -- notice "this" refers to the last theorem proved using "have".

-- This proof, although very simple, is much more complicated than it needs to be.
-- We already have a standard method of proving equality for any given Type without the need to go
-- into details about the Type in question.

example : ∀ s : set α, s = s := assume s : set α, rfl

-- We can then define the notions of union and intersection of sets and their respective notations,
-- and prove theorems about them.

def union (s₁ s₂ : set α) : set α := {a | a ∈ s₁ ∨ a ∈ s₂}

-- We use ∪ for union.
instance : has_union (set α) := ⟨set.union⟩

def inter (s₁ s₂ : set α) : set α := {a | a ∈ s₁ ∧ a ∈ s₂}

-- We use ∩ for intersection.
instance : has_inter (set α) := ⟨set.inter⟩

-- here is a result a little bit harder than the previous one. 
lemma distributivity₁ : ∀ {A B C : set α}, (A ∩ B) ∪ C = (A ∪ C) ∩ (B ∪ C) :=
    assume A B C : set α, -- let A, B, C be sets.
    -- we prove the side (⊆) first.
    have c₀ : (A ∩ B) ∪ C ⊆ (A ∪ C) ∩ (B ∪ C), from
        (assume x : α, -- suppose x is an α.
         assume h : x ∈ (A ∩ B) ∪ C, -- suppose x is an element of the left hand side.
         have c₀ : x ∈ (A ∩ B) ∨ x ∈ C, from h, -- by the definition of ∪, obtain that x is in (A ∩ B) OR x is in C.
         -- lets prove that x ∈ A ∪ C.
         -- We give a proof by cases, assuming in one case that x ∈ (A ∩ B), and in the other that x ∈ C.
         -- The logical rule that allows us to do this is known as or-elimination.
         have c₁ : x ∈ (A ∪ C), from or.elim c₀ 
            (-- since we know c₀, assume in the fist case x ∈ (A ∩ B)
             assume h : x ∈ (A ∩ B),-- notice this replaces the 'h' defined above. 
             -- We won't need that 'h' anymore so we can reuse the name.
             -- the logical rule that allows us to infer that x ∈ A from the fact that both x ∈ A and x ∈ B is called
             -- and-elimination.
             have x ∈ A, from and.elim_left h,
             -- since x ∈ A, x ∈ (A ∪ C). The rule that allows us to infer this is called or-introduction.
             show x ∈ (A ∪ C), from or.inl this
             -- this concludes the proof for the case x ∈ (A ∩ B)
            )
            (-- We then need to show the this works out in the other case as well.
             assume h : x ∈ C,
             -- likewise, we prove the desired result using or-introduction. 
             -- Can you tell the difference between the rules or.inl and or.inr? Hint: (l)eft vs (r)ight.
             show x ∈ (A ∪ C), from or.inr h
            ),
        -- next we must prove x ∈ (B ∪ C). The proof is very similar to the previous one.
        have c₂ : x ∈ (B ∪ C), from or.elim c₀
            (assume h : x ∈ (A ∩ B),
             have x ∈ B, from and.elim_right h,
             show x ∈ (B ∪ C), from or.inl this
            )
            (assume h: x ∈ C,
             show x ∈ (B ∪ C), from or.inr h
            ),
        -- to conclude the proof we put both results together.
        show x ∈ (A ∪ C) ∩ (B ∪ C), from ⟨c₁, c₂⟩ -- the ⟨⟩ forms a notation for the rule of and-introduction.
        ),


    
    -- next we prove the other side.
    -- We we show here that we can write a proof of this sort more efficiently by using a few tricks.
    have c₁ : (A ∪ C) ∩ (B ∪ C) ⊆ (A ∩ B) ∪ C, from
        (assume x : α,
         assume h₀ : x ∈ (A ∪ C) ∩ (B ∪ C),
         match h₀.left with
        | (or.inl h₁) := 
            match h₀.right with
            | (or.inl h₂) := or.inl ⟨h₁, h₂⟩
            | (or.inr h₂) := or.inr h₂
            end
        | (or.inr h₁) := or.inr h₁
        end
        ),



    -- finally we put the 2 results together to prove the equality.
    show (A ∩ B) ∪ C = (A ∪ C) ∩ (B ∪ C), from eq_of_subset_of_subset c₀ c₁

-- When you learn to do these kinds of proof more or less in your head, 
-- this is good evidence that you have a decent proficiency with proofs.

-- There is an even shorter way of writing proofs in Lean using tactics. We will show this style
-- of writing in the next theorem.

lemma distributivity₂ : ∀ {A B C : set α}, (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) :=
begin
    intros A B C,
    apply eq_of_subset_of_subset,
        intros x h,
        cases h.left with c₁ c₂,
            exact or.inl ⟨c₁, h.right⟩,
            exact or.inr ⟨c₂, h.right⟩,
    intros x h,
    cases h with c₁ c₂,
        exact ⟨or.inl c₁.left, c₁.right⟩,
        exact ⟨or.inr c₂.left, c₂.right⟩,
end

-- By using tactics we tell Lean in a more abstract manner what to do to generate a proof of our theorem.
-- We can ask Lean to show the proof it generated using the print command

set_option pp.beta true
set_option pp.notation true
--#print distributivity₂


-- Here is the generated proof:

-- theorem hidden.distributivity₂ : ∀ (α : Type u) {A B C : set α}, (A ∪ B) ∩ C = A ∩ C ∪ B ∩ C :=
-- λ (α : Type u) (A B C : set α),
--   eq_of_subset_of_subset
--     (id
--        (λ (x : α) (h : x ∈ (A ∪ B) ∩ C),
--           or.dcases_on (h.left) (λ (c₁ : x ∈ A), or.inl ⟨c₁, h.right⟩)
--             (λ (c₂ : x ∈ B), or.inr ⟨c₂, h.right⟩)))
--     (id
--        (λ (x : α) (h : x ∈ A ∩ C ∪ B ∩ C),
--           or.dcases_on h (λ (c₁ : x ∈ A ∩ C), ⟨or.inl (c₁.left), c₁.right⟩)
--             (λ (c₂ : x ∈ B ∩ C), ⟨or.inr (c₂.left), c₂.right⟩)))

-- Moving on we prove other basic results:

lemma union_commutative : ∀ {A B : set α}, A ∪ B = B ∪ A :=
begin
    intros A B, -- let A, B be sets.
    apply eq_of_subset_of_subset, -- proceed to prove the equality by showing the inclusions on both sides.
        intros x h, -- to prove the first goal (⊆) assume x : α, h : x ∈ A ∪ B
        cases h, -- proceed to prove x ∈ B ∪ A by cases
            exact or.inr h, -- in case x ∈ A, we have x ∈ B ∪ A by applying or.inr
            exact or.inl h, -- in case x ∈ B, by or.inl
            -- Note: h was renamed to h : x ∈ A and h : x ∈ B, in each case respectively.
            -- this way it is unecessary to declare names c₁, c₂ with the "with" statement, as above.
    intros x h, -- now we prove the second goal, with h : x ∈ B ∪ A
    cases h, -- proceed to prove x ∈ A ∪ B by cases
            exact or.inr h, -- in case x ∈ B, we have x ∈ A ∪ B by applying or.inr
            exact or.inl h, -- in case x ∈ A, by or.inl
    -- Notice the proof of the second goal is symmetric to that of the first!!!
end

lemma union_associative : ∀ {A B C: set α}, (A ∪ B) ∪ C = A ∪ (B ∪ C) :=
begin
    intros A B C,
    apply eq_of_subset_of_subset,
        intros x h,
        cases h with c₁ c₂,
            cases c₁ with c₁₁ c₁₂, -- here we have to case c₁ : x ∈ A ∪ B
                exact or.inl c₁₁,
                exact or.inr (or.inl c₁₂),
            exact or.inr (or.inr c₂),
    intros x h,
    cases h with c₁ c₂,
        exact or.inl (or.inl c₁),
        cases c₂ with c₂₁ c₂₂,
            exact or.inl (or.inr c₂₁),
            exact or.inr c₂₂
end

lemma intersection_commutative : ∀ {A B : set α}, A ∩ B = B ∩ A :=
    by intros; apply eq_of_subset_of_subset; intros x h; exact ⟨h.2, h.1⟩
    -- This reads:
    -- 1. Introduce assumptions.
    -- 2. Prove the equality by eq_of_subset_of_subset.
    -- 3. Assume an x belonging to the respective left hand side of the inclusion.
    -- 4. If ⟨h₁, h₂⟩ is a proof of x ∈ X ∩ Y, with h₁ : x ∈ X and h₂ : x ∈ Y, then
    ---   the proof that x ∈ Y ∩ X is given exactly by ⟨h₂, h₁⟩

lemma intersection_associative : ∀ {A B C: set α}, (A ∩ B) ∩ C = A ∩ (B ∩ C) :=
begin
    intros,
    apply eq_of_subset_of_subset,
        intros x h,
        exact ⟨h.1.1, ⟨h.1.2, h.2⟩⟩, 
    intros x h,
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
end

def relative_complement {B : set α} (A : set α) := {x ∈ B | x ∉ A}

instance set_complement : has_neg (set α) := ⟨@relative_complement α univ⟩

lemma set_pnc : ∀ {A : set α}, A ∩ - A = ∅ := 
    by intros; tidy

#print set_pnc
#check ext

lemma complement_distrib : ∀ {A B : set α}, (A ∪ B) ∩ - A = B ∩ - A := 
    by intros A B; rw [@distributivity₂ α A B (-A), set_pnc]; simp

section induction

-- The natural numbers are defined as:
-- inductive nat
-- | zero : nat
-- | succ (n : nat) : nat

-- Inductive types have recursors, which allow us to perform induction in these types.
-- The principle of mathematical induction for natural numbers is stated as follows:
#check nat.rec

open finset

-- example : ∀ n : ℕ, n > 1 → (finset.range n).prod (λi, 1 - 1 / i) =  1 / n :=
-- begin
--     intro n,
--     induction n with n₀ ih,
--         exfalso,
--         exact nat.not_succ_le_zero 1 h,
--     unfold finset.prod at *,
--     simp at *,
--     by_cases n₀ > 1,
--         rewrite ih h,
--         dsimp,
    
    
-- end

open nat
#check nat.add_div_left
example : ∀ n : ℕ, sum (range n) (λk, (k+1) / 2^(k+1)) =  (2^(n+1) - n - 2) / 2^n :=
begin 
    intro n,
    induction n with n₀ ih,
        simp,
    simp [range_succ, ih, nat.pow_succ 2 n₀],
    admit
    
    --rewrite nat.pow_succ 2 n₀,
    
    -- induction n₀ with n₁ ih₂,
    --     simp,
    -- rewrite range_succ,
    -- simp,
    -- rewrite ih,
    -- have h : (n₀ + 1) / 2 ^ (n₀ + 1) + (2 ^ (n₀ + 1) - n₀ - 2) / 2 ^ n₀ 
    --     = ((n₀ + 1)  + 2*(2 ^ (n₀ + 1) - n₀ - 2) )/ 2 ^ (n₀ + 1), from rfl,
    
end

open real lattice

#check real.of_near --set.range of_rat
#check set.exists_mem_of_ne_empty

variables (A B : set real)
variables (bddA₁ : bdd_above A) (bddB₁ : bdd_above B)
variables (bddA₂ : bdd_below A) (bddB₂ : bdd_below B)
variables (ne₁ : A ≠ ∅) (ne₂ : B ≠ ∅)
variables (h₁ : A ⊆ set.range of_rat) (h₂ : B ⊆ set.range of_rat)

lemma aux : ∀ ε : ℝ, ε > 0 → ∃ a ∈ A, real.Sup A < a + ε :=
begin
 intros ε a,
 simp at *,
 fsplit;
 --work_on_goal 1 { simp at *, fsplit };
 admit
end

lemma aux₂ : ∀ ε : ℝ, ε > 0 → ∃ a ∈ B, real.Inf B > a - ε :=
sorry

include bddA₁ bddA₂ bddB₁ bddB₂ ne₁ ne₂ h₁ h₂
theorem ex3 : real.Sup A = real.Inf B ↔ (∀ (a ∈ A) (b ∈ B), a ≤ b) ∧ (∀ ε : ℝ, ε > 0 → ∃ (a ∈ A) (b ∈ B), a + ε > b) :=
begin
    constructor; intro h,
    -- ⟶ side
    constructor, -- prova o lado esquerdo do and.
        intros a a_in_A b b_in_B,
        have c₀ : a ≤ real.Sup A, from le_cSup bddA₁ a_in_A,
        have c₁ : real.Inf B ≤ b, from cInf_le bddB₂ b_in_B,
        rewrite h at c₀,
        exact le_trans c₀ c₁,
    intros ε ε_pos,
    obtain ⟨a, a_in_A, c₀⟩ := aux A (ε/2) (mul_pos ε_pos _),
        work_on_goal 1 {ring, exact one_half_pos},
    obtain ⟨b, b_in_B, c₁⟩ := aux₂ B (ε/2) (mul_pos ε_pos _),
        work_on_goal 1 {ring, exact one_half_pos},
    -- cases (aux A (ε/2) (mul_pos ε_pos sorry)) with a c₀,
    --     cases c₀ with a_in_A c₀,
    -- cases (aux₂ B (ε/2) (mul_pos ε_pos sorry)) with b c₁,
    --     cases c₁ with b_in_B c₁,
    suffices c : a + ε > b, from ⟨a, a_in_A, b, b_in_B, c⟩,
    rewrite ←h at *, simp * at *,
    have c, from lt_trans c₁ c₀,
    replace c, from add_lt_add_left c (ε/2),
    rw [add_comm, add_assoc, add_left_neg, add_zero] at c,
    simp at c, exact c,
    -- ⟵ side
    cases h with c₁ c₂,
    have c₀ : ∀ a ∈ A, a ≤ real.Sup A, 
        intros a a_in_A,
        exact le_cSup bddA₁ a_in_A,
    have c₃ : ∀ b ∈ B, ∀ a ∈ A, a ≤ b,
        intros b b_in_B x x_in_A, 
        exact c₁ x x_in_A b b_in_B,
    have c₄ : ∀ b ∈ B, real.Sup A ≤ b ,
        intros b b_in_B,
        exact cSup_le ne₁ (c₃ b b_in_B),
    have c₅ : real.Sup A ≤ real.Inf B, from le_cInf ne₂ c₄,
    have c₆ : ∀ a ∈ A, real.Inf A ≤ a, 
        intros a a_in_A,
        exact cInf_le bddA₂ a_in_A,
    have c₇ : real.Inf A ≤ real.Sup A,
        cases (set.exists_mem_of_ne_empty ne₁) with a a_in_A,
        apply le_trans,
            exact c₆ a a_in_A,
            exact c₀ a a_in_A,
    replace c₇ : real.Inf A + -real.Inf A ≤ real.Sup A - real.Inf A, 
        from add_le_add_right c₇ (-real.Inf A),
        simp at c₇,
    let ε := real.Sup A - real.Inf A,
    -- have c : 0 ≠ ε, from sorry,
    replace c₇, from lt_of_le_of_ne c₇ sorry,
    obtain ⟨a, a_in_A, b, b_in_B, c⟩ := (c₂ ε c₇),
    -- replace c, from (c₂ ε c₇),
    -- rcases c with ⟨a, a_in_A, b, b_in_B, c⟩,
    -- cases c with a c,
    -- cases c with a_in_A c,
    -- cases c with b c,
    -- cases c with b_in_B c,
    
    
    -- cases (set.exists_mem_of_ne_empty ne₁) with a a_in_A,
    -- cases (set.exists_mem_of_ne_empty ne₂) with b b_in_B,
    -- repeat{fsplit},
    --     exact a,
    --     exact a_in_A,
    --     exact b,
    --     exact b_in_B,
    -- clarify, simp at a_1,
    
    -- simp * at *,
    --cases (a (real.Sup A)),

    


end


-- example : ∀ n m : ℕ, m * n = n * m :=
-- begin 
--     intros n m,
--     induction m with m ihm,
--         simp,
--     induction n with l ihn,
--         simp,
--     rewrite nat.mul_succ (n + 1) m,
--     rewrite nat.mul_succ (m+1) n,
--     rewrite ←ihm,
--     rewrite nat.mul_succ,
--     rewrite nat.add_assoc,

-- end



end induction

end hidden




-- Instead the approach used here is to construct the von Neumann hierarchy from the unit type,
-- the type with a single instance which is here to be considered as the empty set,
-- and we will define that a set  we begin by considering the