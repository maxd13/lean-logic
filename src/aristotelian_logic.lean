import predicate_logic tactic.find
open logic
universe u

namespace syllogistic
section syllogism
parameters {sort : Type u} [decidable_eq sort]
parameter {σ : @signature sort _}

-- Aristotelian syllogistic calculus with individuals and conversions (including singular conversion).
-- "singular conversion" means we support the conception of treating individual/singular assertions
-- as categorical ones. 
-- We had been told this is a port royal idea, but maybe it is due to Aristotle as well.
-- must check.

-- individuals
-- Notice that "term" for Aristotle is, in the context of a categorical syllogism,
-- almost the opposite of what "term" in mathematical logic means.
def atomo := @term sort _ σ

-- Aristotelian terms.
-- Those will be monadic predicates in the signature,
-- and also the terms generated from equality

-- universals (καθόλου)
def katholou := @nrary sort _ σ 1

inductive horos
| universal : katholou → horos
-- In predicate logic this constructor would be equivalent to the language having equality.
| singular : atomo → horos

instance : has_lift katholou horos := ⟨horos.universal⟩

-- Apophansis (ἀπόφανσις)
-- i.e.  the type of assertions
inductive apophansis
-- universal affirmative individual/singular (καθόλου κατάφασις άτομο)
-- Socrates is human.
| AI : atomo → katholou → apophansis
-- universal negative individual/singular
-- Socrates is not human.
| EI : atomo → katholou → apophansis
-- undefined/indefinite affirmative.
-- Supposed to stand either for vague quantification, or the predication of a proper accident.
-- Rougly, a proper accident is a property that is not part of the definition of the term, 
-- but is either deducible from the definition or present almost universally in the instance of the universal term.
-- humans are mortal.
| UA : katholou → katholou → apophansis
-- undefined/indefinite negative.
-- humans are not mortal.
| UE : katholou → katholou → apophansis
-- universal affirmative
-- All men are mortal.
| A : horos → katholou → apophansis
-- universal negative
-- No man is mortal.
| E : horos → katholou → apophansis
-- particular affirmative
-- Some men are mortal.
| I : katholou → katholou → apophansis
-- particular negative
-- Some men are not mortal.
| O : katholou → katholou → apophansis
-- Existence claims, used for introducing existential import in Aristotelian logic.
-- e.g. "Some human exists".
| EXI : katholou → apophansis
-- e.g. "No human exists".
| EXE : katholou → apophansis
-- trivially true
-- Used as a default value in some functions
-- e.g. "All humans exist".
| EXA : katholou → apophansis
-- Always false.
-- Used as a default value in some functions
-- e.g. "Some humans do not exist".
| EXO : katholou → apophansis

def AI := apophansis.AI
def EI := apophansis.EI
def UA := apophansis.UA
def UE := apophansis.UE
def A := apophansis.A
def E := apophansis.E
def I := apophansis.I
def O := apophansis.O
def EXA := apophansis.EXA
def EXE := apophansis.EXE
def EXI := apophansis.EXI
def EXO := apophansis.EXO


--square of opposition (up to singular conversion).
def contradictory : apophansis → apophansis
| (apophansis.AI socrates mortal) := EI socrates mortal
| (apophansis.EI socrates mortal) := AI socrates mortal
| (apophansis.UA human mortal) := UE human mortal
| (apophansis.UE human mortal) := UA human mortal
| (apophansis.A (horos.universal human) mortal) := O human mortal
| (apophansis.A (horos.singular socrates) mortal) := EI socrates mortal
| (apophansis.E (horos.universal human) mortal) := I human mortal
| (apophansis.E (horos.singular socrates) mortal) := EI socrates mortal
| (apophansis.I human mortal) := E ↑human mortal
| (apophansis.O human mortal) := A ↑human mortal
| (apophansis.EXA human) := EXO human
| (apophansis.EXE human) := EXI human
| (apophansis.EXI human) := EXE human
| (apophansis.EXO human) := EXA human

-- EXO can be interpreted as "undefined".
-- But it is also logically true that it is contrary to everything.
def contrary : apophansis → apophansis
| (apophansis.AI socrates mortal) := EI socrates mortal
| (apophansis.EI socrates mortal) := AI socrates mortal
| (apophansis.UA human mortal) := EXO human
| (apophansis.UE human mortal) := EXO human
| (apophansis.A human mortal) := E human mortal
| (apophansis.E human mortal) := A human mortal
| (apophansis.I human mortal) := EXO human
| (apophansis.O human mortal) := EXO human
| (apophansis.EXA human) := EXO human
| (apophansis.EXE human) := EXO human
| (apophansis.EXI human) := EXO human
| (apophansis.EXO human) := EXO human

-- EXA is the "undefined".
-- It is logically true that it is compatible with everthing (except EXO).
-- def subalternate : apophansis → apophansis
-- | (apophansis.AI socrates mortal) := EI socrates mortal
-- | (apophansis.EI socrates mortal) := AI socrates mortal
-- | (apophansis.UA human mortal) := EXA human
-- | (apophansis.UE human mortal) := EXA human
-- | (apophansis.A (horos.universal human) mortal) := I human mortal
-- | (apophansis.A (horos.singular socrates) mortal) := I human mortal
-- | (apophansis.E human mortal) := A human mortal
-- | (apophansis.I human mortal) := EXO human
-- | (apophansis.O human mortal) := EXO human
-- | (apophansis.EXA human) := EXO human
-- | (apophansis.EXE human) := EXO human
-- | (apophansis.EXI human) := EXO human
-- | (apophansis.EXO human) := EXO human



-- convert singular assertions to categorical ones.
-- e.g. convert from "Socrates is human" to "All Socrates are human"
-- (meaning all entities equal to Socrates are human).
-- e.g. convert from "Socrates is not human" to "No Socrates is human".
def singular_conversion : apophansis → apophansis
| (apophansis.AI socrates human) := A (horos.singular socrates) human
| (apophansis.EI socrates human) := E (horos.singular socrates) human
| φ := φ

-- inverse function.
-- converts from "All Socrates are human" to "Socrates is human".
-- converts from "No Socrates is human" to "Socrates is not human".
def singular_reversion : apophansis → apophansis
| (apophansis.A (horos.singular socrates) human) := AI socrates human
| (apophansis.E (horos.singular socrates) human) := EI socrates human
| φ := φ

def categorical : apophansis → Prop
| (apophansis.AI _ _) := false
| (apophansis.EI _ _) := false
| _ := true

lemma singular_conversion_gives_categorical : ∀ φ : apophansis, categorical (singular_conversion φ) :=
    begin
    intros φ,
    cases φ;
    simp [singular_conversion]
    end

-- Eba→Eab
-- if no human is a donkey, no donkey is a human.
def disjoint_conversion : apophansis → apophansis
| (apophansis.E (horos.universal human) donkey) := E ↑donkey human
| φ := φ

-- Iba→Iab
-- If some humans are idiots, some idiots are human.
def conjoint_conversion : apophansis → apophansis
| (apophansis.I human idiot) := I idiot human
| φ := φ

-- Aba → Iab
-- If all men are mortal, some mortals are men.
-- requires existential import.
def existential_conversion : apophansis → apophansis
| (apophansis.A (horos.universal human) mortal) := I mortal human 
| φ := φ


-- All moods can be reduced to Barbara and Celarent,
-- although Darii and Ferio are also considered perfect.
inductive perfect_syllogism : apophansis → apophansis → apophansis → Prop
| Barbara (middle major : katholou) (minor : horos) : perfect_syllogism (A ↑middle major) (A minor middle) (A minor major)
| Celarent (major middle minor : katholou) : perfect_syllogism (E ↑middle major) (A ↑minor middle) (E ↑minor major)

inductive syllogism : apophansis → apophansis → apophansis → Prop
-- teleios syllogism
| perfect {p₁ p₂ c₁ : apophansis} (h : perfect_syllogism p₁ p₂ c₁) : syllogism p₁ p₂ c₁
-- singular_conversion
| SC {p₁ p₂ c₁ : apophansis} (h : syllogism p₁ p₂ c₁) 
    : syllogism (singular_conversion p₁) (singular_conversion p₂) (singular_conversion c₁)
-- singular_reversion
| SR {p₁ p₂ c₁ : apophansis} (h : syllogism p₁ p₂ c₁) 
    : syllogism (singular_reversion p₁) (singular_reversion p₂) (singular_reversion c₁)
-- disjoint_conversion
| DC {p₁ p₂ c₁ : apophansis} (h : syllogism p₁ p₂ c₁) 
    : syllogism (disjoint_conversion p₁) (disjoint_conversion p₂) (disjoint_conversion c₁)
-- conjoint_conversion
| CC {p₁ p₂ c₁ : apophansis} (h : syllogism p₁ p₂ c₁) 
    : syllogism (conjoint_conversion p₁) (conjoint_conversion p₂) (conjoint_conversion c₁)
-- existential_conversion
| EC {p₁ p₂ c₁ : apophansis} (h : syllogism p₁ p₂ c₁) 
    : syllogism (existential_conversion p₁) (existential_conversion p₂) (existential_conversion c₁)

-- parameters {p₁ p₂ c : apophansis}

lemma BarbaraI (middle major : katholou) (minor : atomo) 
        : syllogism (singular_conversion (A ↑middle major)) (singular_conversion (A (horos.singular minor) middle))
(singular_conversion (A (horos.singular minor) major)) := 
syllogism.SC (syllogism.perfect
(perfect_syllogism.Barbara middle major (horos.singular minor)))

-- | CelarentI (major middle : katholou) (minor : atomo) : syllogism (E ↑middle major) (AI minor middle) (EI minor major)
 
inductive deduction : apophansis → Type u
| immediate  (p₁ p₂ c : apophansis) (h : syllogism p₁ p₂ c) : deduction c
| first_recursive (p₂ c₀ c : apophansis) (proof : deduction c₀) 
                  (h : syllogism c₀ p₂ c)  
                  : deduction c
| second_recursive (p₁ c₀ c : apophansis) (proof : deduction c₀) 
                  (h : syllogism p₁ c₀ c)  
                  : deduction c
| birecursive (p₁ c₁ c₂ c : apophansis) (proof₁ : deduction c₁) 
                  (proof₂ : deduction c₂) (h : syllogism c₁ c₂ c)
                  : deduction c

-- | second_recursive (p₁ p₂ c₁ p₃ c₂ : apophansis) (h₀ : syllogism p₁ p₂ c₁) 
--                   (h₀ : syllogism p₃ c₁ c₂)  
--                   : deduction [p₁, p₂, c₁, p₃, c₂]
end syllogism
end syllogistic