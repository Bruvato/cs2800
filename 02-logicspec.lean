-- CS 2800 LOGIC AND COMPUTATION, FALL 2026
-- COPYRIGHT 2026 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

import mylibrary1
import Plausible

/- **Key concepts covered in this lecture code and associated slides _slides01-logic.pdf_:**
 - basic logic: Boolean operators, truth tables, Boolean functions, syntax vs semantics, equivalent formulas, satisfiability and validity, stronger and weaker formulas, necessary and sufficient conditions
 - basic set theory: element of, subset of, intersection, union, complement, correspondence between logic and set theory
 - Bool vs Prop
 - Boolean operators on Prop and Bool: conjunction, disjunction, negation, implication, Iff, XOR
 - Quantifiers, forall properties
 - Formal correctness specifications
 - Property-based testing (_plausible_)
-/



-----------------------------------------------------------------
-- **LOGIC and FORMAL SPECIFICATION**
-----------------------------------------------------------------
/-
In the first part of the course we learned how to write simple programs in Lean, and how to test these programs on certain inputs, with _example_. What we really want is to _prove correctness for all possible inputs_. To do that, we must first define rigorously what correctness means. This process is called **formal specification**: it consists in writing properties that we want our programs to have in a certain **logic**. In this part of the course we will learn how to do that, in the logic of Lean.

First, we will review some basic concepts in logic, contained in file: **slides01-logic.pdf** (posted on canvas). Hopefully this material is not all new to you. In any case, **you are expected to know it, and you will be tested on it**.
-/



/- **Bool vs Prop**

The Lean type Bool represents the set of Booleans, Bool.true and Bool.false. Bool is a finite type.

The Lean type Prop is an infinite type that represents _all possible propositions that we can write in Lean_. A _proposition_ is a claim that we are making: typically it is a Lean formula that we try to prove. But until it's proven, the proposition is just a claim. False claims (that cannot be proven) are also of type Prop.

In what follows we give many examples of objects of type Prop. **Make sure you understand what each Prop claims**. You should be able to explain it in English.

**It is important that you understand the difference between Bool and Prop**. For instance, you should understand why Bool is finite and why Prop is infinite. **Why?**
-/

#check Bool
#print Bool

#check Prop
#print Prop -- error

#check true -- Bool
#check True -- Prop
#check false -- Bool
#check False -- Prop
/- True is the proposition that can always be proven (because "it's true"). False is the proposition that cannot be proven (because "it's false"). -/

-- there are (infinitely) many more propositions that we can write in Lean, other than True and False:
#check (0 = 0) -- the claim that 0 is equal to 0
#check 0 = 0 -- we will drop parentheses when there's no ambiguity
#check 2*3 = 6
#check len [] = 0
#check len [1,2,3] = 3
#check plus 2 2 = 4


-- **False (unprovable) claims are also Props !! :**
#check 0 = 1    -- False (unprovable) claim, but still a well-typed Prop!
#check len [] = 42  -- False claim, but still a well-typed Prop!
#check plus 2 2 = 5 -- False claim, but still a well-typed Prop!

/- Syntax errors, type errors, semantic errors
The expression "3 = " is syntactically incorrect: it doesn't even parse. So are the expressions "p /\ -> q", "3 * ) + 2", etc.

The expression "3 = [1,2,3]" can be seen as syntactically OK (depending on the underlying grammar, which we won't worry about here) but is a type error in Lean, as we have seen.

The expression "3 = 2" is both syntactically correct and well-typed (no type error), but can be seen as _semantically incorrect_ in the sense that it is False.
-/


/- **Equality**

The (single) equals symbol "=" stands for the equality function Eq, a predefined function in Lean. We can check its type, which roughly speaking says that Eq takes two things of some type α and returns the claim (the Prop) that these two things are equal: -/

#check Eq
#check Eq 0 0
#check Eq (2*3) 4

#check 2 = 3            -- a Prop
#check true = false     -- a Prop
#check [1,2,3] = [1,2]  -- a Prop
#check 2 == 3            -- a Bool
#check true == false     -- a Bool
#check [1,2,3] == [1,2]  -- a Bool

#eval True = true

/- Logical operators on Prop vs on Bool: -/


-- **Conjunction ("logical and")**

#check And      -- conjunction on Props
#check And (0 = 0) (1 = 1)

#check Bool.and
#check Bool.and true false



-- **Disjunction ("logical or")**

#check Or     -- disjunction on Props
#check Or (0 = 0) (1 = 1)

#check Bool.or
#check Bool.or true false



-- **Negation ("logical not")**

#check Not    -- negation on Props
#check Not (0 = 0)

#check Bool.not
#check Bool.not true



/- **Implication**
In Lean, logical implication on Props is written -> (or →). If P and Q are Props, then (P -> Q) is also a Prop:
-/

#check (0 = 0) -> (1 = 2)

/- There is a reason why the implication symbol is the same as the symbol for function types like Nat -> Bool. We will discuss this fascinating aspect of Lean later. As it turns out, implication is the most important logical operator, in the sense that _every other logical operator can be derived from implication and "false"_. You will explore this in your homework, where you will also define implication on Bools.
-/

/- Lean 3 had an "implies" function on Props, which seems to have disappeared in Lean 4. We can easily define it, if we need it: -/
def Implies (p q : Prop) := p -> q
#check Implies

/- *Do not confuse implication with if-then-else!* _ite_ (if-then-else) is a function with type (roughly)
  Prop -> α -> α -> α
meaning that it takes as input a Prop c (the condition, which must be decidable), a then branch x of some type α, and an else branch y of the same type α, and returns either x or y, depending on whether c holds or not.
-/
#check ite




/- **Logical equivalence (Iff, if and only if)**

Logical equivalence claims that two Props P and Q are _equivalent_, meaning that P implies Q and also Q implies P.
-/

#check Iff
#check Iff (0 = 0) (1 = 1)
#check (0 = 0) <-> (1 = 1)
#check (0 = 0) ↔ (1 = 1)


/- ENGLISH AND IMPLICATION

"A only if B"    =     A -> B
"B if A"         =     A -> B
"A if B"         =     B -> A
"if A then B"    =     A -> B

"A if and only if B"    =   A <-> B  =  A -> B and B -> A
-/




/- **Exclusive or (XOR)** -/
/- Lean 3 had an "xor" function on Props, which seems to have disappeared in Lean 4, but which we can easily define: -/
def XOR (p q : Prop) := Not (p <-> q)
#check XOR

-- do not confuse XOR with Bool.xor:
#check Bool.xor





def app : List Nat -> List Nat -> List Nat
  | [], L => L
  | (x :: L1), L2 => x :: (app L1 L2)

def rev : List Nat -> List Nat
  | [] => []
  | (a :: L) => app (rev L) [a]


/- **Quantifiers**

Lean's logic goes beyond Boolean expressions: we can use the quantifiers _forall_ (∀) and _exists_ (∃), to write more general Props than simple _example_ tests:
-/

#check forall x : Nat, x = x
#check forall x : Nat, x < x+1
#check forall x : Nat, x > 0 -- this claim is false, but it's still a Prop
#check forall x y : Nat, plus x y = plus y x -- commutativity
#check forall x y z: Nat, plus x (plus y z) = plus (plus x y) z -- associativity
#check forall x y : Nat, (x ≠ 0 ∧ y ≠ 0) -> plus x y > 0
#check forall x : Nat, len [x] = 1
#check forall x : Nat, len [x,x] = 2
#check forall L1 L2 : List Nat, len (app L1 L2) = plus (len L1) (len L2)
#check forall L : List Nat, len (rev L) = (len L)



/- We won't deal much with "exists properties", but here's an example: -/
#check forall x : Nat, exists y : Nat, x < y

/- Lean's logic is very general, and Props cover pretty much every mathematical claim we might want to make. For example, Fermat's last theorem can be written as a Prop: -/

def exponent : Nat -> Nat -> Nat
  | _, 0 => 1
  | x, (e+1) => x * (exponent x e)

def fermats_last_theorem :=
    ∀ n : Nat, n > 2
    -> ¬ ∃ x y z : Nat, x > 0 ∧ y > 0 ∧ z > 0
                ∧ (exponent x n) + (exponent y n) = (exponent z n)
#check fermats_last_theorem -- **important:** this does not prove Fermat's last theorem! it only checks its type, which is Prop

/- Higher-order claims, where we quantify for instance over functions, or even over Props themselves, can be written as Props too: -/

#check forall p q : Prop, Iff (p ∧ q) (q ∧ p)
#check forall p q : Prop, (p ∧ q) <-> (q ∧ p)

def apply : List Nat -> (Nat -> Nat) -> List Nat
  | [], _ => []
  | (a :: L), f => (f a) :: (apply L f)

/- It's a good exercise to try to "read" the property below: how would you express it in English? -/
#check forall L, forall f, len (apply L f) = len L




/- **Formal correctness specifications**

The reason we care about Prop is that all our correctness specifications will be Props. That is, we will define what it means for our programs to be correct by writing formal claims about our programs. Each of these claims will be a Prop. Each such claim corresponds to a property that we think our program should have. We will first learn how to write down such properties. Later we will learn how to prove them.
-/


/- **Correctness specification by exhaustive testing**

We begin with specifying correctness of "easy" functions that only have finitely many inputs, say, Boolean functions. Let's consider the function _negb_ which implements negation on Bools. (This is essentially the same function as the predefined Lean function Bool.not, but we re-define it  so that we are independent of Lean's libraries, and we have control over our definitions.)
-/
def negb : Bool -> Bool
    | true  => false  -- if the input is true , return false
    | false  => true  -- if the input is false , return true

/- What does it mean for negb to be "correct"? In the case of a simple function like negb, we can specify correctness "exhaustively" by testing: since there's only two possible input values, we can specify what the output should be in each of these two cases:
-/

example: negb true  = false  := by {rfl}
example: negb false  = true  := by {rfl}

/- This is the case for all Boolean functions (functions on one or more Bools that return a Bool). In principle, we can formally specify correctness of any Boolean function by exhaustive testing. This amounts to writing down 2^n tests where n is the number of input arguments to the function, i.e., writing down its truth table. But the truth table grows exponentially with n, so this approach does not scale. A better approach is to write forall properties about these functions. Even simple functions like negb have interesting properties: -/

-- negb is _involutive_
theorem negb_involutive: forall x : Bool, negb (negb x) = x := sorry -- we wrote the theorem, but we didn't prove it

-- we could prove it by exhaustive testing:
example: negb (negb true) = true := by {rfl}
example: negb (negb false) = false := by {rfl}


/- Let's re-define Boolean functions AND and OR: (**Think about properties that these functions should have, and write them down formally in Lean**.)
-/

def andb_exhaustive : Bool -> Bool -> Bool
    | true, true  => true
    | true, false  => false
    | false, true  => false
    | false, false  => false

-- shorter way to write it:
def andb_shorter : Bool -> Bool -> Bool
    | false, _ => false  -- if the first input is false, output is false independently of the second input
    | true, true  => true
    | true, false  => false

-- even shorter:
def andb : Bool -> Bool -> Bool
    | false, _ => false
    | true, y  => y

def orb : Bool -> Bool -> Bool
    | true, _ => true
    | false, y => y

/- Some properties of andb and orb: -/
theorem andb_commutative: forall x y : Bool, andb x y = andb y x := sorry
theorem orb_commutative: forall x y : Bool, orb x y = orb y x := sorry
theorem andb_associative: forall x y z : Bool, andb (andb x y) z = andb x (andb y z) := sorry
theorem orb_associative: forall x y z : Bool, orb (orb x y) z = orb x (orb y z) := sorry
-- etc.


/- **Correctness specification with _forall properties_**

_forall properties_, that is, properties using the _forall_ quantifier (also written ∀) allow us to write correctness specifications for functions whose correctness _cannot be specified by exhaustive testing_, even in principle. _plus_ is such a function (**why?**). Here's some forall properties about _plus_: -/

#check plus

theorem plus_zero: forall x : Nat, plus x 0 = x := sorry
theorem plus_commutative: forall x y : Nat, plus x y = plus y x := sorry
theorem plus_associative: forall x y z : Nat, plus (plus x y) z = plus x (plus y z) := sorry
-- etc.



/- In general, you should be thinking about properties of the programs you write. Can you think of properties that the function *next_workday* has? Can you write them formally in Lean?
-/
#check next_workday

-- ANSWER:





























open weekday

-- one property is "for any weekday d, (next_workday d) is never a saturday nor a sunday".
theorem next_workday_not_saturday:  forall x : weekday, Not (next_workday x = saturday) := sorry
theorem next_workday_not_sunday:  forall x : weekday, next_workday x ≠ sunday := sorry
theorem next_workday_not_weekend:  forall x : weekday, (next_workday x ≠ saturday) ∧ (next_workday x ≠ sunday) := sorry


-- another property: for any input day x the output day should be different from x.
theorem next_workday_different:  forall x : weekday, next_workday x ≠ x := sorry



/- The properties about *next_workday* that we wrote above use the logical operators ∧ (And) and ¬ (Not) over Props (and not the ones over Bools). **It is important that you understand this distinction**. -/

#check And -- And on Props
#check Or -- Or on Props
#check Not -- Not on Props
#check and -- Bool.and
#check or -- Bool.or
#check not -- Bool.not

#check And (0 = 0) (1 = 1)
#check (0 = 0) /\ (1 = 1) -- ASCII way to write ∧
#check Or (0 = 0) (1 = 1)
#check (0 = 0) \/ (1 = 1) -- ASCII way to write ∨
#check Not (0 = 1)
#check 0 ≠ 1 -- same as Not (0 = 1)

#check and true true
#check and (0 = 0) (1 = 1) -- type coercion **BAD!!! don't do it**





-- **quiz**: what's another way to write *next_workday_not_weekend*, using Or instead of And ?

-- ANSWER:





























theorem next_workday_not_weekend_Not_Or:  forall x : weekday, Not (Or (next_workday x = saturday) (next_workday x = sunday)) := sorry

theorem next_workday_not_weekend_just_Or:  forall x : weekday,  (next_workday x = monday) ∨ (next_workday x = tuesday) ∨ (next_workday x = wednesday) ∨ (next_workday x = thursday) ∨ (next_workday x = friday) := sorry





/- **Property-based testing**

We have written tests by _example_, but it would be nice to be able to "test" more general claims, such as forall properties. "Testing" a forall property means attempting to find a counterexample to the property, _before_ attempting to prove it. This is useful in detecting bugs, either in our program, or in the property.

Methods that generate tests automatically from properties are called _property-based testing_ methods (PBT). _Plausible_ is a PBT method for Lean:
-/

#check plus -- correct _plus_
def buggyplus: Nat -> Nat -> Nat
  | 0, y => 0 -- bug1
--  | 0, y => y -- fixed bug 1
  | (Nat.succ x), y => plus x y -- bug 2
--  | (Nat.succ x), y => Nat.succ (plus x y) -- fixed bug 2

theorem plus_is_commutative: forall x y : Nat, plus x y = plus y x
:= by {
  plausible -- PBT doesn't find a counterexample
}

theorem buggyplus_is_commutative: forall x y : Nat, buggyplus x y = buggyplus y x
:= by {
  plausible -- PBT finds a counterexample: fix the bugs and see what happens
}

theorem correctplus_but_wrong_property: forall x : Nat, plus x 0 = 0 -- should be x
:= by {
  plausible
}



def elemOf : Nat -> List Nat -> Bool
 | _, [] => false
 | x, (y :: L) => Bool.or (x == y) (elemOf x L)

theorem list_conj: forall (x : Nat) (L1 L2 : List Nat),
  (L1 = L2 /\ L1 != [] /\ x > 0) -> ((elemOf x L1) && (elemOf x L2)) = true
:= by {
  plausible
}

/- The claim *list_conj* above does not hold in general. It holds when L1 ≠ L2 (**why?**). Still, if you comment out _plausible_ and add it back a few times, you will find that it sometimes finds a counterexample, and sometimes not.

Suppose L1 = L2. Then *list_conj* is equivalent to
  (L1 != [] /\ x > 0) -> elemOf x L1 = true       (1)
(**why?**).

So, if we falsify (1) by setting L1 := [0] and x := 1, we can falsify the original *list_conj* with L2 := L1 := [0] and x := 1.

Plausible has an easier time falsifying (1) than falsifying the original *list_conj*. The reason is that there is only L1 and x in (1), whereas *list_conj* has also L2. Because plausible "guesses" values for L1, L2, and x randomly, it will try many "useless" guesses where L1 != L2. Those cases cannot falsify the theorem. **Why?**
-/
