-- CS 2800 LOGIC AND COMPUTATION, FALL 2026
-- COPYRIGHT 2026 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

/-
**GENERAL NOTE: the lecture code that we post on canvas has content that we didn't get to cover during the lecture. you are supposed to read the ENTIRE lecture code files posted on canvas. if you don't understand something, ask us.**

Another general note: Lean seems to re-process the entire file every time you make a change. This wastes a lot of energy. We recommend that keep the files that we give you as mostly read-only: you can keep you own smaller tmpXY.lean files on the side for your experimentations.
-/

/- **Key concepts covered in this lecture code:**
 - function definition and application in Lean
 - testing as proving
 - types, contracts, type errors
 - partial evaluation and anonymous functions
 - pattern matching
 - recursion and termination
 - inductive data types
-/

-----------------------------------------------------------------
-- **FUNCTIONAL PROGRAMMING WITH TYPES, IN LEAN**
-----------------------------------------------------------------
/-
You may have already seen functional programming (in Racket, Scheme, Lisp, Haskell, ...) in your previous programming life. But you may have not seen functional programming with types. Types can be seen as "input-output contracts" between a program (a function f) and its environment (the functions that call f).  Types are useful because they allow the compiler to catch at compile-time many errors that would otherwise be caught at run-time.

Let's see a few examples of functional programs in LEAN, and how these use types.

First, we begin with some basic LEAN commands:
    #version
    #eval
    #reduce
    #check

-/


---------------------------------------------------
-- LOGISTICS: INSTALL **LEAN 4** ON YOUR MACHINE
---------------------------------------------------

#version -- Move your cursor here and look at the Lean InfoView window to the right: you should see something like "Lean 4.34.0-rc2" (this is the version specified in file _lean-toolchain_ available on canvas)




-------------------------------------------------------------------
-- BASIC EXPRESSIONS, PREDEFINED OPERATORS, #eval, #reduce, #check
-------------------------------------------------------------------

-- first let's see some basic expressions and predefined operations in LEAN:

-- addition:
#eval 2+3  -- #eval is a "compute" command
#reduce 2+3 -- #reduce is another compute command; we won't worry about the difference between #eval and #reduce for now
#eval Nat.add 2 3  -- Nat.add is a predefined function

-- subtraction:
#eval 3-2

#eval 2-3 -- weird! subtraction defined over Natural numbers
#eval 2-300
#check 2-3


#eval (2:Int)-(3:Int) -- by default, "2" is a Nat, but "(2:Int)" is an Int

-- how do we know? we can use #check, which gives the type of an expression:

#check 2
#check (2:Int)

#check (2+3)
#check (2-3)

#eval 2 - 3
#check 2 - 3

#eval Nat.sub 2 3

#check (2:Int) - 3
#check 3


#eval (2:Int) - (3 : Int)
#eval (2:Int) - 3
#eval 2 - (3 : Int)
#eval ((2-3):Int)


-- multiplication:
#eval 2*3


-- division:
#eval 4/2
#eval 4/3 -- Integer division!
#eval 2/3 -- Integer division!
#check 2/3



-- if-then-else
#eval ( if (1 = 1) then (10*2) else 1 )
#eval ite (0 = 1) (10*2) 1 -- if-then-else is actually the ternary function "ite"
#eval if (0 = 1) then (0+2) else (1+13)
#eval ite (0 = 1) 2 14
#check ite -- functions have types too, more later

#eval if (0 = 0) then 10 else 20
#eval ite (0 = 1) 10 (ite (0 = 10) 10 (20+10))


#eval bla -- bla is undefined, we get an error message
#check bla -- bla is undefined, we get an error message


----------------------
-- **FUNCTIONS**
----------------------

def f (x : Nat) : Nat := x + 1
-- function f takes x of type Nat and returns a result also of type Nat; the result is x + 1

#check f


-----------------------------------------------------------------
-- FUNCTION APPLICATION ("calling" functions)
-----------------------------------------------------------------

#eval (f 0)  -- (f 0) is function application (instead of f(0) we write (f 0))
#eval f 0  -- often parentheses are not needed, more later
#eval f (0) -- ok
#eval f(0) -- error

-- omitting parentheses is fine, except when they are needed to change the priority of operations:
def d (x : Nat) : Nat := 2*x
#eval (d 2)
#eval d 2 + 3  -- function application has higher priority than + so this is (d 2) + 3 instead of d (2+3)
#eval (d 2) + 3
#eval d (2+3)



-----------------------------------------------------------------
-- WHY FUNCTIONAL PROGRAMMING INSTEAD OF IMPERATIVE PROGRAMMING?
-----------------------------------------------------------------
/-
In the first part of this class we will be using Lean and its functional programming language. Later we will discuss formal verification for imperative code.
-/



---------------------------------------------------
-- **TESTING AS PROVING**
---------------------------------------------------
/-
There are two basic ways of checking the correctness of our programs: testing and proving. Proving is exhaustive, testing is not. This course focuses on proving, but testing is very important too. Moreover, simple testing can be seen as simple proving: testing that (f 42) is 0 is proving the equality (f 42) = 0. We will deal with proofs later. For now, you just have to get used to writing tests in Lean, as described below.
-/

-- consider the functions f and d that we defined earlier:
#check f
#check d

/- we want to test these functions, to make sure that they works as intended. one way to do that is simply to evaluate the functions on a bunch of inputs:
-/

#eval f 0
#eval f 1
#eval f 42
#eval d 0
#eval d (f 0)
#eval d 42

/- the problem with this testing approach is that it requires a human to check ("eyeball") the results. if we later change the code for some reason, we have to go over all our tests to make sure they are all still returning what they are supposed to return. a better way is to assert what we know the function _should_ return in each case. then, if later we change the function and introduce a bug, some of these assertions might fail automatically. in LEAN, we can use the "example" mechanism to do that. an "example" is actually a "mini-theorem" (in fact not so mini, since we can write arbitrary complicated logical statements inside an example), with a proof and all:
-/

example: f 0 = 1 := by {rfl}
example: f 1 = 2 := by {rfl}
example: f 42 = 43 := by {rfl}
example: d 0 = 0 := by {rfl}
example: d (f 0) = 2 := by {rfl}
example: d 42 = 84 := by {rfl}

/-
For now, you don't have to worry about the _:= by {rfl}_ part. You will include it in all your tests without knowing what it does. Just make sure that all your tests pass! So, from now on, for every function we define, instead of testing it with #eval, we will test it with _example_.
-/

/- If we claim something false, our proof doesn't go through (our test does not pass):
-/
example: d 42 = 4 := by {rfl} -- correct function, but buggy test (expected output is 84, not 4)

---------------------------------------------------
-- REGRESSION TESTING:
---------------------------------------------------

/- And if we modify the code and introduce a bug, some of our (correct) tests might fail:
-/

def d_bad (x : Nat) : Nat := 3*x -- bug, should be 2*x

example: d_bad 0 = 0 := by {rfl}  -- this test still passes
example: d_bad (f 0) = 2 := by {rfl}  -- this test now fails
example: d_bad 42 = 84 := by {rfl}  -- this fails too




-----------------------------------------------------------------
-- **TYPES**
-----------------------------------------------------------------

/- LEAN's programming language is "typed". we have already briefly talked about types and seen #check:
-/

#check 0 -- LEAN tells us (infoview) that 0 is of type Nat
    -- in general, the notation "x : T" means "x is of type T"

-- #check can be used to show the type of any expression
#check (3 + 2*7) -- this expression is also of type Nat

/- what exactly is a "type"? you can think of a type as a set of values. for example, you can think of Nat as the set of Natural numbers: {0, 1, 2, ...}. this is the mathematical / set-theory view, and it will be enough for now. later we will talk a bit more about type theory and we'll see how types can be "constructed". for now, you can think of "0 : Nat" (0 is of type Nat) as saying that "the value 0 belongs to the set Nat".

**In LEAN every correct expression has a type**. To be more precise, every syntactically correct expression is of some type, unless the expression has a type error. Types in LEAN are "first-class citizens", which means in particular that a type itself has a type:
-/

#check Nat  -- Nat is of type "Type"
#check Type -- "Type" is of type "Type 1"
#check Type 1 -- "Type 1" is of type "Type 2"
#check Type 2 -- etc
#check Type 100
/- The types of types (like Type, Type 1, Type 2, etc.) are sometimes called _sorts_. This type _hierarchy_ is important to the proper foundation of logic (and therefore everything else!). More on this later. -/

#eval Nat -- we cannot #eval Nat because it doesn't have a "representation" (essentially a pretty-printing)
#reduce Nat  -- but we can #reduce Nat: it reduces to itself.


-----------------------------------------------------------------
-- SOME BASIC TYPES IN LEAN
-----------------------------------------------------------------

/- we can (and later will) define our own types in LEAN. for now, let's go over LEAN's basic predefined types: -/

-- Natural numbers:
#check 0
#check 1
#check 22


-- we have negative Integers, but we will not deal with them too much:
#eval -1
#eval (-1:Int)
#check (-1:Int)
#check ((-1):Int)


#check 103.5 -- we will not deal much with non-Integers
#eval 103.5


-- we have booleans:
#check true -- boolean "true"
#check false -- boolean "false"

#check True -- not the same as the Bool true, we'll learn propositions (Prop) later

-- we have Strings:
#check "abc"
#check "hello i love you"



-- we have lists:

#check []
#check List.nil   -- [] and List.nil are equivalent notations for the empty List

#check [1]
#check List.cons 1 List.nil
#check 1 :: List.nil
#check 1 :: [] -- infix notation for List.cons
#check List.cons 1 1 -- cryptic message, but 2nd argument of cons must be a List!

#check 1 :: 2 :: 3 :: []
#check 1 :: (2 :: (3 :: []))

#eval List.cons 1 (List.cons 2 (List.cons 3 List.nil))
#eval [1,2,3]



#check [1,2,3]
#eval List.cons 0 [1,2,3]
#eval 0 :: [1,2,3]          -- infix notation for List.cons

#check [1,2,3]  -- LEAN infers that this is a List of Nats
#check ["hello","bye"] -- LEAN infers that this is a List of Strings
#check [ [1,2], [3,4,5], []  ]   -- a List of Lists of Nats

#check [1,"hello"] -- this is allowed in some languages, but not in LEAN (at least not directly, without defining some sort of union/sum type); we will not worry about this

#check [(-1:Int),2,3]




-----------------------------------------------------------------
-- **FUNCTION TYPES ARE _CONTRACTS_**
-----------------------------------------------------------------

-- function types are input-output contracts:

#check f

/- f is a function from Nat to Nat. We will also write
    f : Nat -> Nat     or       f : Nat → Nat     .
In other circles this is called the _signature_ of f. The signature defines an _input-output contract_: it is the responsibility of the caller to call f passing a Nat as input; it is the responsibility of f to return a Nat as output. If the contract is violated, we get a type error.
-/

-----------------------------------------------------------------
-- TYPE ERRORS
-----------------------------------------------------------------

#check 0
#eval f 0  -- all good

#check (-1:Int)  -- (-1:Int) is of type Int
#eval f (-1:Int) -- type error: f expects a Nat, but we give it an Int. the environment (the callers of f) has "broken" the contract.
#eval f [1,2] -- type error


#check (1:Int)
#eval f (1:Int) -- type error, again, the fault is with the environment


-- here function fg breaks the output contract, the fault is with fg
def fg (x:Nat) : Nat := x-(20:Int)   -- fg is not well-defined



#eval f (f 0)  -- all good, because (f 0) is guaranteed to be a Nat, because of f's type

#eval (f f) 0

#eval f f 0  -- type error: this is parsed as (f f) 0, because function application is _left associative_ ("stacks to the left")
#eval (f f)  -- type error: f is not of type Nat, so it cannot be passed to f which expects a Nat


/- type errors vs "well-typed" code

LEAN's programming language is "strongly" typed. when programming in LEAN, we must be careful about types, and we must resolve any typing errors. other languages are more flexible about types.  LEAN has strong typing, meaning that typing errors are not tolerated. we (in this class) will not accept programs with type errors (in homeworks, exams, etc).

when a LEAN expression does not give any type error, we will say that it is "well-typed". **we will ask you to recognize whether a given expression is well-typed or not**. you will be supposed to be able to do that on your own, without the help of LEAN.
-/

#check 2+3
#check Nat.add 2 3
#check + 2 3 -- we get an error: why?
#check (2 3) -- we get an error: why?

#check Nat -> Nat   -- "Nat -> Nat" is a well-typed LEAN expression, just like "2+3" is a well-typed LEAN expression

#check Nat Nat  -- we get an error: why?

#check Nat




-----------------------------------------------------------------
-- POLYMORPHISM
-----------------------------------------------------------------

-- LEAN has a "polymorphic" type system:
#check List.nil -- this is the empty List: its type can be read as "List of something / List of some type"
#check []   -- same as List.nil

-- we will not talk much about polymorphism, so you can ignore it for now
#eval 0 :: []
#check 0 :: []  -- [0] is a "List of Nats"
#check 0 :: 1 :: 2 :: []
#check [0,1,2]

#check List.cons



-----------------------------------------------------------------
-- TYPE INFERENCE
-----------------------------------------------------------------

-- LEAN can sometimes infer the types in function definitions too:
def f5 (x : Nat)    := x + 1  -- notice that we omitted the output type
#check f5  -- LEAN infers that the output type is Nat
#eval f5 10

-- we could also have omitted both:
def f6 (x) := x+1
#check f6  -- LEAN is still able to infer the types. how? not the topic of this course, but probably because 1 is by default a Nat.

def f7 (x) := x + (1:Int)
#check f7  -- now that we forced 1 to be an Int, the inferred type changes

/- type inference doesn't always work, and sometimes it might result in unexpected results that don't necessarily capture the intention of the programmer. _in this course, we will insist on specifying the type of every function, including input and output._
-/




-----------------------------------------------------------------
-- FUNCTIONS WITH MORE THAN ONE INPUTS
-----------------------------------------------------------------

/- _A function is an expression whose type is of the form (A -> B), for some (arbitrary) types A and B._ Note that A or B might themselves be function types, i.e., of the form C -> D, etc. -/

-- here's a function that takes as input two Nats, x and y, and returns a Nat:
def g (x y : Nat) : Nat := x+y

#eval g 2 3
#eval (g 2) 3
#check g

-- we could also have written g equivalently like this:
def gg (x : Nat) (y : Nat) : Nat  := x+y
#check gg

/- g and gg are **equivalent** functions. What this means is that (1) they have the same type/signature, and (2) they return the same output given the same input. We can actually prove that g and gg are equivalent formally, in Lean. We provide such a proof below but you can ignore it for now. Later you will learn to do such proofs yourself. -/

theorem g_equivalent_gg: forall x y : Nat, g x y = gg x y := by {
    intro x y
    rfl
}

/- The type of g (which is the same as the type of gg) is interesting:
    g : Nat → Nat → Nat
Adding the dropped parentheses, this is the same as:
    g : Nat → (Nat → Nat)
(It is unfortunate that Lean 4 does not show this as clearly as above and instead shows "g (x y : Nat) : Nat", but you can look at the "Expected type" section.)

What this type says is that "g is a function that takes as input a Nat, and returns a function that takes as input a Nat and returns a Nat". Although this is a mouthful and might not make sense the first time you see it, **you should understand it**. This will help you understand things like _partial evaluation_:
-/


-----------------------------------------------------------------
-- PARTIAL EVALUATION
-----------------------------------------------------------------

#check g
#check g 2
#eval g 2
#reduce g 2
#check (g 2)   /- Is (g 2) a well-typed expression? Yes it is! Hmm, that's strange. Doesn't g take TWO inputs? How come we are allowed to call it with just one input? If you understand the type of g, which is
    Nat → Nat → Nat   (which is the same as Nat → (Nat → Nat))
then (g 2) makes perfect sense: (g 2) has type Nat → Nat, so (g 2) is a function from Nat to Nat. We can call this function just like any other function: -/

#eval (g 2) 3  -- apply the function (g 2) to argument 3
#eval g 2 3 -- same as (g 2) 3, recall the function application rules
#eval g (3 4)    -- ERROR !  why?




-- what about the predefined operators like +, *, etc?
#check +    -- doesn't work: + is not really a function, but a generic infix notation for an "add" operation


#check Nat.add  -- Nat.add is the predefined addition function on Nats
-- NOTE: you might see a red squiggly line underlying the #check command above, indicating a possible error on that line. there is no error on the "#check Nat.add" line. the error message from the "#check +" line somehow propagates here. this is a bug. ignore it. the red line under "#check Nat.add" should disappear if you comment out the "#check +" line.

#eval Nat.add 2 3



#check Nat.sub -- subtraction
#check Nat.mul -- multiplication
#check Nat.div -- division

#eval Nat.sub 3 2
#eval Nat.sub 2 3
#eval Nat.mul 3 2
#eval Nat.div 3 2


/-
how can we know what functions +, *, etc correspond to?

we can't unless we start digging into the LEAN libraries, which we won't do. instead, we will re-define everything from scratch before proving things, so that we know exactly what functions we are proving things about.
-/



/- **PARENTHESES in types (and in function applications)**
all these expressions denote the same type:
-/
#check Nat -> Nat -> Nat
#check Nat -> (Nat -> Nat)
#check (Nat -> Nat -> Nat)
#check (Nat -> (Nat -> Nat))
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check (Nat → Nat → Nat)
#check (Nat → (Nat → Nat))

/- you can think of the type Nat → Nat as "the set of all functions from Nat to Nat", the type Nat → Nat → Nat as "the set of all functions from Nat to the set of all functions from Nat to Nat", etc.

type "\to" to get the Unicode arrow, you can also hover above the symbol and VScode tells you what you need to type.
-/


-- but this type is different from the ones above -- **why??**
#check (Nat -> Nat) -> Nat


/- **Remember**: arrow types "stack" to the right whereas function application stacks to the left! -/

#check Nat → (Nat → Nat)  -- Nat → Nat → Nat
#check (g 2) 3  -- g 2 3


-- how to define a function that has type (Nat -> Nat) -> Nat ?
def FF2 (f : Nat -> Nat) : Nat := f 42
#check FF2
#eval FF2 f
#eval FF2 (g 2)
#eval FF2 g 2    -- type error  --- **why?**

def MyFun (f : Nat -> Nat) : Nat := (f (f (f 0))  )


-- here's a function which mixes a few types:
def h (x : Nat) (b : Bool) : Int := if (b = true) then x else -x
#check h -- h : Nat → Bool → Int
#eval (h 3) true
#eval h 3 false

#reduce h 3
#check (h 3)

#check h 4

#check h 4 true
#eval h 4 false
#check h true -- type error, **why?**


-- these four types are identical:
#check (Nat -> (Bool -> Int))
#check Nat -> (Bool -> Int)
#check (Nat -> Bool -> Int)
#check Nat -> Bool -> Int

-- but this one is different:
#check (Nat -> Bool) -> Int


#check (Nat Bool -> Int) -- type error, **why?**


-- here's a function with 3 inputs:
def add3 (x : Nat) (y : Nat) (z : Nat) : Nat := x+y+z
#check add3

#check add3 3
#check add3 3 4
#check add3 3 4 5
#eval add3 3 4 5

-- another (equivalent) way to define add3:
def add3alt (x y z : Nat) : Nat := x+y+z
#check add3alt



-- here's a function with 3 inputs of different types:
def fgh (x : Nat) (y : Bool) (z : Int) : String := "hello"
#check fgh

-- the inputs are unused so they don't need a name:
def fgh_ (_ : Nat) (_ : Bool) (_ : Int) : String := "hello"
#check fgh_

#check List.cons
#check List.cons 1 (List.cons 2 [])


-- REMEMBER: in types, parentheses implicitly "stack" to the right:
#check Nat → (Nat → (Nat → Nat))
#check Nat → Nat → Nat → Nat
#check Nat → (Bool → (Int → String))
#check Nat → Bool → Int → String


-- **REMEMBER:** in function applications, parentheses implicitly "stack" to the left:
#eval fgh 34 true (-1)
#eval ((fgh 34) true) (-1)
#check add3 10 100 1000
#check ((add3 10) 100) 1000


/- Nat → Nat is a type. therefore we expect Nat → Nat to have itself a type: -/
#check Nat → Nat    -- Nat → Nat is of type Type
#check Nat -> Nat   -- Nat -> Nat is the same as Nat → Nat


/- A student asked: _how should I think about types like these?_

(Nat -> Int) -> (Nat -> Int)
Nat -> Int -> (Nat -> Int)
(Nat -> Int -> Nat -> Int)

The first thing to do is add the missing (implicit) parentheses (if any). Once you do that, the type becomes A -> B, for some A and B (which might contain arrows internally).

There's no missing parentheses in the first type above. So we can go ahead and read it:
(Nat -> Int) -> (Nat -> Int)
This type represents all functions from (Nat -> Int) to (Nat -> Int). That is, all functions that take as input a function from Nat to Int, and return as output a function from Nat to Int. But because to return a function from Nat to Int is the same as to take an additional Nat and return the Int, we can also think of the above type as representing functions that take two inputs: (1) a function from Nat to Int; and (2) a Nat; and return an Int.

The 2nd type above:
Nat -> Int -> (Nat -> Int)
is really the type below, once we add the implicit parentheses:
Nat -> (Int -> (Nat -> Int))
This type represents all functions from Nat to (Int -> (Nat -> Int)). That is, all functions that take as input a Nat, and return as output a function from Int to (Nat -> Int). But again, it's easier to think of this type as representing functions that take 2 inputs: (1) a Nat; (2) an Int; and return a function from Nat to Int. And it's even easier to think of this type as representing functions that take 3 inputs: (1) a Nat; (2) an Int; (3) a second Nat; and return an Int. And that's why in such cases we want to drop all parentheses and simply write the type as follows:
Nat -> Int -> Nat -> Int
which is exactly the 3rd type above!

-/


-----------------------------------------------------------------
-- **ANONYMOUS FUNCTIONS** - LAMBDAS
-----------------------------------------------------------------

-- in all the examples so far, every function that we defined has a name:
#check f
#check g
#check FF2

/- But it is often useful to also be able to define functions without names, "anonymous functions" so to speak. why would we ever want to do that? this is useful, for example, when treating functions as "first-class citizens". for example, we might want to pass a function as an argument to another function. or a function might return a function as a result. we will see several examples of this later in this course.

functions without names can be defined using "fun" or (unicode) λ (\lambda). you may encounter this under the term _lambda abstraction_:
-/

#check (fun x : Nat => x+1) -- an anonymous function with type Nat → Nat
#eval (fun x : Nat => x+1) 0 -- application of that anonymous function to 0

#check (fun x => x+1)  -- sometimes we can omit types but we don't want to do that in this course!

#check (fun (x:Nat) => (x+1 : Nat)) -- here we specify the types of both input and output, although the latter seems a bit redundant in this case, so we won't insist on specifying the types of the output in λ expressions

#check λ x:Nat => x+1   -- "fun" can be replaced by λ
#eval (λ x:Nat => (x+1 : Nat)) 17



-- anonymous functions can have multiple inputs:
#check  fun (x : Nat) (b : Bool) => (if (b=true) then x else 2*x)



-----------------------------------------------------------------
-- FUNCTIONS ARE FIRST-CLASS CITIZENS
-----------------------------------------------------------------

/- functions in LEAN are not different from other objects. just like we can pass to a function a number, say 0 or 1, or a bool, say true, we can also pass a function, provided that this is allowed by the input-output contract. let us illustrate this by example.

here's a function gg which takes as input a Nat x and a function f : Nat -> Nat and returns as output (f x):
-/

def ggg (x : Nat) (f : Nat → Nat) : Nat := f x

-- what is the type of gg? let's ask LEAN:
#check ggg -- LEAN says "gg : Nat → (Nat → Nat) → Nat", which means that ggg takes something of type Nat, and something of type "(Nat → Nat)", and returns something of type Nat. this is as we would expect. the second input to gg, of type "(Nat → Nat)", is a function that takes a Nat and returns a Nat. ggg can be called with any function that has this type, for example:

#eval ggg 10 f -- f is the function we defined earlier
#eval ggg 3 f
#eval ggg 3 (Nat.div 10)
#eval ggg 42 (g 2)

#eval ggg 10 (fun x : Nat => x+3)
#eval ggg 10 (λ x => x+3) -- here we pass an anonymous function as input to ggg

#eval ggg 10 f


-----------------------------------------------------------------
-- TYPES ARE FIRST-CLASS CITIZENS TOO
-----------------------------------------------------------------
#check Nat
#check Bool
#check Nat -> Nat

-- g is a function that takes as input some type x and returns as output the same type x
def tg (x : Type) : Type := x
#check tg
#check tg Nat
#check tg (Nat -> Nat)
#eval tg Nat  -- doesn't work, just like "#eval nat" doesn't work
#reduce tg Nat -- should be Nat; Lean 4 doesn't seem to reduce  it...
#reduce tg (List Nat)
#reduce tg (Nat -> Bool)


-- what is the type of this function?
def GH (x : Type) : Type := x → x
#check GH

-- what is the type of this function?
def GL (x : Type) : Type := List x
#check GL


-- what is the type of GH Nat?
#check GH Nat
-- what is the value of GH Nat?
#reduce GH Nat


#check GL Nat
#reduce GL Nat



/- Lean is founded on something called **dependent type theory**. We will not delve into type theory. For more info, see the lecture notes. -/




-----------------------------------------------------------------
-- **PATTERN MATCHING**
-----------------------------------------------------------------

/- In order to define recursive functions, we have to learn another way to define functions, by pattern matching. For example, the function f that we defined earlier can also be defined by pattern matching:
-/
#check f

-- here's another way to define f:
def fpat : Nat -> Nat -- we start by giving the type/contract
    | x => x + 1    -- then we define the function by "pattern matching"
-- in this case pattern matching is trivial: we basically say
-- "let the input be x" (| x), "then the output is x+1" (=> x+1)

#check fpat
#eval fpat 10

-- we can prove formally that f and fpat are equivalent (ignore the proof for now)
theorem f_equivalent_fpat: forall x : Nat, f x = fpat x := by {
    intro x
    rfl
}


-- pattern matching on two inputs:
def gpat : Nat -> Nat -> Nat
    | x, y => x+y

theorem g_equivalent_gpat: forall x : Nat, g x = gpat x := by {
    intro x
    rfl
}


def hpat : Nat -> Bool -> Int
    | x, y => if (y = true) then x else -x

theorem h_equivalent_hpat: forall x : Nat, h x = hpat x := by {
    intro x
    rfl
}


/-
the above pattern matching examples are silly because there's only one pattern so there's no real "matching" to be done. a slightly more interesting example is this:
-/

def hpatbis : Nat -> Bool -> Int
    | x, true => x
    | x, false => -x


theorem h_equivalent_hpatbis: forall (x : Nat) (y : Bool), h x y = hpatbis x y := by {
    intro x y
    cases y with
    | true =>
        rfl
    | false =>
        rfl
}

/- More interesting pattern matching happens when we define recursive functions: -/

-----------------------------------------------------------------
-- **RECURSION and TERMINATION**
-----------------------------------------------------------------

/- The most powerful mechanism in programming is repetition. In imperative programming (C, Java, etc) repetition is achieved using things like "while" and "for" loops. In functional programming, it is achieved by _recursion_: a function calling itself.

Here's a function that computes the sum 0+1+...+n for given Nat n:
-/

def sumall : Nat → Nat
    | 0 => 0
    | (n+1) => (n+1) + (sumall n) -- recursive call

/- This is a more interesting case of pattern matching, with a recursive 2nd case. what this is saying is the following:
  - if the input is 0 ("| 0") then output 0 ("=> 0")
  - otherwise, if the input is n+1, then output (n+1) + (sumall n)

Note that the two cases are both disjoint (non-overlapping) and exhaustive: the input is either 0 or n+1 (for some n), and it cannot be both.
-/

#eval sumall 0
#eval sumall 1
#eval sumall 2
#eval sumall 4
#check sumall


-- now, we could have defined the same function without pattern matching:
def sumallite (n : Nat) : Nat := if (n = 0) then 0 else n + (sumallite (n-1))

-- we can prove that the two definitions are equivalent (ignore the proof for now)
theorem sumall_equivalent_sumallite: forall x : Nat, sumall x = sumallite x := by {
    intro x
    induction x with
      | zero =>
        rw [sumall]
        rw [sumallite]; simp
      | succ z ih =>
        rw [sumall]
        rw [sumallite]; simp
        exact ih
}

/- But there are good reasons to define the function as sumall, and NOT as sumallite. One reason is termination analysis. **Lean only accepts functions that terminate** (we will discuss later why). In the definition of sumall termination is _obvious_ because the argument n to the recursive call is _obviously strictly smaller_ than the argument n+1 of the original call. Termination is less obvious in the case of sumallite because the argument (n-1) of the recursive call is not always strictly smaller than the argument n of the original call (**why?**). It is however strictly smaller when n>0, and we know that n>0 because we are in the else branch of the if-then-else. Indeed, Lean has to do this analysis internally in order to prove that sumallite terminates (in Lean 3 this function would not be accepted). As we will see later, checking termination is a hard problem (in fact it's _undecidable_; we will learn what that means later). So we should try to make termination as obvious to Lean as possible: using pattern matching is good for making termination obvious.

Another reason is to use pattern matching is that it makes proofs easier. We will see examples of this later, when we talk about proofs.
-/

/- Even though Lean 4 is better than Lean 3 at proving automatically that a function terminates, there are still relatively simple cases where it fails. For example, the definition of _sumallminus1_ below is accepted:
-/

def minus1 : Nat -> Nat
  | 0 => 0
  | (x+1) => x

def sumallminus1 : Nat -> Nat
  | 0 => 0
  | (x+1) => (x+1) + sumallminus1 (minus1 (x+1))

-- but the definition below is not accepted:
def sumallminus1ite (n : Nat) : Nat := if (n = 0) then 0 else n + (sumallminus1ite (minus1 n))


/-
Conclusion: **use pattern matching for all your recursive function definitions; make your recursions _obviously terminating_ so that Lean accepts them**. If you run into trouble ask us!
-/



---------------------------------------------------
-- MORE ON PATTERN MATCHING
---------------------------------------------------

-- sometimes LEAN doesn't complain about overlapping cases that give different results:
def badchoice : Nat → Nat
    | 0 => 0
    | 1 => 1
    | 2 => 2
    | (x+1) => badchoice x  -- this overlaps with case "1" if x=0 and with case "2" if x=1

#eval badchoice 0
#eval badchoice 1
#eval badchoice 2
#eval badchoice 3
#eval badchoice 4
-- in this class **we will insist on NOT having overlapping cases**. define your functions such as cases are mutually-exclusive (i.e., non-overlapping) and complete, in order to avoid any ambiguities. here's for example one way to fix the above:

def goodchoice : Nat → Nat
    | 0 => 0
    | 1 => 1
    | 2 => 2
    | (x+3) => goodchoice x  -- no overlap with any of the base cases



/-
note that there are limits to the pattern matching that LEAN allows.
for example, we might be tempted to try this:
-/

def evenbad : Nat → Bool    -- a function that checks whether a given Nat is even or odd
    | (2*n) => true       -- if the input is of the form 2*n then it's even
    | (2*n+1) => false     -- if the input is of the form 2*n+1 then it's odd

/- the reason why the above don't work will become more clear when we explain inductive data types.
-/



------------------------------------------------------------------------
-- **A PREVIEW OF INDUCTIVE DATA TYPES:** constructors of Nat and List
------------------------------------------------------------------------

#check Nat
#print Nat /- this says that natural numbers can be "constructed" in two ways:
- Nat.zero is a (_constructor_ that returns a) natural number
- Nat.succ is a constructor that takes a natural number, and returns a new natural number
-/
#check Nat.zero  -- 0 is shorthand notation for Nat.zero
#check Nat.succ Nat.zero -- 1 is shorthand for )Nat.succ Nat.zero)
#check Nat.succ (Nat.succ Nat.zero) -- and so on

#check Nat.succ (Nat.succ (Nat.succ (Nat.succ 0)))  -- x.succ is the same as (Nat.succ x)

-- "x+1" is the same as (Nat.succ x), so when we write (n+1) in our recursive case definitions, what we really mean is (Nat.succ n):


def sumallNat : Nat -> Nat
    | Nat.zero => Nat.zero
    | (Nat.succ n) => (Nat.succ n) + (sumallNat n)

-- sumallNat is equivalent to sumall (ignore the proof for now)
theorem sumall_equivalent_sumallNat: forall x : Nat, sumall x = sumallNat x
:= by {
    intro x
    induction x with
        | zero =>
            rfl
        | succ y ih =>
            rw [sumall]
            rw [sumallNat]
            rw [ih]
}

/- the definition of sumallNat also makes it clearer to see why this recursion is _obviously terminating_: the argument to recursive call, n, is _obviously_ smaller than the argument to the original call, (Nat.succ n), since (Nat.succ n) is constructed from n. -/

-- and what we really say when we define goodchoice is this:
def goodchoicebis : Nat → Nat
    | Nat.zero => 0
    | (Nat.succ Nat.zero) => 1
    | (Nat.succ (Nat.succ Nat.zero)) => 2
    | (Nat.succ (Nat.succ (Nat.succ x))) => goodchoicebis x


/-
The above hopefully also makes it clear why _(2*n)_ and _(2*n+1)_ are not acceptable patterns by LEAN. LEAN has no way to "deconstruct" a Nat m into _2*n_ or _2*n+1_, although it is easy to "deconstruct" m into either 0 (i.e., Nat.zero) or (n+1) (i.e., Nat.succ n).
-/

-- as should be expected, goodchoicebis is equivalent to goodchoice (ignore the proofs below)
theorem goodchoice_equivalent_goodchoicebis_funind: forall x : Nat, goodchoice x = goodchoicebis x
:= by {
    intro x
    induction x using goodchoice.induct with
    | case1 => rfl
    | case2 => rfl
    | case3 => rfl
    | case4 x ih =>
        rw [goodchoice]
        rw [goodchoicebis]
        exact ih
}

theorem goodchoice_equivalent_goodchoicebis_strongind: forall x : Nat, goodchoice x = goodchoicebis x
:= by {
    intro x
    induction x using Nat.strongRecOn with
    | ind n ih =>
        cases n with
        | zero =>
            rfl
        | succ z =>
            cases z with
            | zero =>
                rfl
            | succ w =>
                cases w with
                | zero => rfl
                | succ u =>
                    rw [goodchoice]
                    rw [goodchoicebis]
                    rw [ih]
                    omega
}



-----------------------------------------------------------------
-- **RECURSION ON LISTS**
-----------------------------------------------------------------

/- List is also an inductive data type, with two constructors, List.nil, and List.cons: -/
#check List
#print List -- you don't have to understand this type completely

def len : List Nat → Nat
    | [] => 0
    | (x :: L) => 1 + (len L)


#eval len []
#eval len [1,2,3]
#eval len [1,1,1]

-- since we are not using "x" in the pattern above, we can omit it and replace it with "_":
def len2 : List Nat → Nat
    | [] => 0
    | (_ :: L) => 1 + len2 L


-- we can also use the constructors explicitly:
def lenbis : List Nat → Nat
    | List.nil => 0
    | (List.cons _ L) => 1 + (lenbis L)


theorem len_equivalent_lenbis: forall L : List Nat, len L = lenbis L := by {
  intro L
  induction L with
    | nil =>
      rfl
    | cons x L1 ih =>
      rw [len]
      rw [lenbis]
      rw [ih]
}



/- ON THE MEANING OF CONSTRUCTORS:

Data type constructors like Nat.succ and List.cons are like functions, but they are not exactly the same thing: functions have a "body" definition, but constructors don't have that. So how do constructors work? What do they return exactly? Constructors don't "return" anything; the constructed expression _itself_ is the result. So (Nat.succ Nat.zero) "returns" itself. (Nat.succ Nat.zero) is a Nat, so it has the right type.

What is the meaning of things like (Nat.succ Nat.zero)? The meaning is what we (humans) assign it to be. We think of Nat.zero as the number 0. We think of (Nat.succ Nat.zero) as the number 1. And so on. That's the meaning of "formal" in "formal logic", "formal proofs", "formal methods", etc. The _form_ itself is the meaning.
-/





/- **helper** or **auxiliary** functions

HWK01b asks you to define many functions using pattern matching and recursion.

It is perfectly fine and often necessary (in the sense that it makes your life much easier) to use **helper** or **auxiliary** functions. What this means is that instead of defining the requested function in one monolithic definition, you first define one or more other functions, and then you call those other functions in the definition of the requested (main) function.

For example, you will probably want to call _app_ (the list append function which you are asked to define in one of the homework problems) in several of the other problems. This is perfectly fine.
-/



/- _Obviously terminating_

We request that you write functions that are **obviously terminating**. What this means is that Lean can prove termination. If Lean accepts your definition, you can assume that it was able to prove termination.

The way to make your functions "obviously terminating" is to guarantee the following property:

In every recursive call, at least one of the arguments to the recursive call is "obviously smaller" than the original argument.

"Obviously smaller" is defined as follows: x is obviously smaller than y, if y is constructed from x.

For example, for x : Nat, x is obviously smaller than (Nat.succ x), because (Nat.succ x) is constructed from x.

Another example: the list [1,2,3] is obviously smaller than [42,1,2,3] because [42,1,2,3] is constructed from [1,2,3].

Another example: the list L is obviously smaller than (x :: L) because (x :: L) is constructed from L.

Another example: the list L is obviously smaller than (x :: y :: L) because (x :: y :: L) is constructed from L.

def zip : List Nat -> List Nat -> List Nat
  | xs, [] => xs
  | [], ys => ys
  | x :: xs, ys => x :: zip ys xs

Does the above definition of _zip_ satisfy this property? No. Why not? The recursive call in the definition is

zip ys xs

The 1st argument to the recursive call is ys. Is ys obviously smaller than the original 1st argument? The original 1st argument is (x :: xs). ys is not obviously smaller than (x :: xs).

Similarly for the 2nd arguments, xs vs ys.

How to fix it? Non-overlapping cases, etc. Start with the 1st list: either it's empty, or non-empty. If the 1st list is non-empty, do cases on the second list: either that one is empty, or not.

_Is this definition obviously terminating? Isn't the 2nd list becoming longer and longer at each recursive call?_

def f : List Nat -> List Nat -> List Nat
  | [], L2 => L2
  | (x :: L1), L2 => f L1 (x :: L2)

_What about this one? Now the second list is growing even longer!_

def f : List Nat -> List Nat -> List Nat
  | [], L2 => L2
  | (x :: L1), L2 => f L1 (x :: x :: L2)

-/







---------------------------------------------------
-- **DEFINING OUR OWN (INDUCTIVE DATA) TYPES**
---------------------------------------------------

/-
"Algorithms + Data Structures = Programs" is a 1976 book written by Niklaus Wirth, a famous computer scientist who among other things created the Pascal programming language. we have already defined many programs, but have we defined any data structures? not really. we have been using the basic predefined data types of LEAN, like Nat, Bool, and list Nat. these can only take us so far. sometimes we need more elaborate data structures. sometimes we need more complex data types. although we will not focus on this topic in this course, let us still gain some basic understanding on how to define our own data types in LEAN.
-/

-- Defining our own types, and function definitions on those by case matching:

-- as an example, let's define a new type called "weekday":
inductive weekday : Type
    | sunday : weekday
    | monday : weekday
    | tuesday : weekday
    | wednesday : weekday
    | thursday : weekday
    | friday : weekday
    | saturday : weekday
    deriving DecidableEq -- you can ignore this. it can be omitted but then LEAN has problems with expressions like  ( ite (sunday = monday)  0  1 )

#check weekday -- weekday is indeed a type
#print weekday -- weekday has 7 "constructors"

-- recall the predefined type Bool:
#print Bool -- Bool has 2 constructors
#print Nat -- Nat also has 2 constructors

-- we can check the type of the new elements we just defined:
#check weekday.friday -- friday is the best day!
-- we cannot #eval them:
#eval weekday.friday
-- but we can #reduce them (in fact they don't reduce to anything else but themselves):
#reduce weekday.friday

#check weekday.monday
#check weekday.tuesday
#check weekday.wednesday
#check weekday.thursday
#check weekday.friday
#check weekday.saturday
#check weekday.sunday

open weekday

#check sunday

#check true
#check Bool.true

-- let's define a function on the newly defined type:
def next_workday_too_much_typing : weekday → weekday
    | weekday.sunday =>  weekday.monday
    | weekday.monday =>  weekday.tuesday
    | weekday.tuesday =>  weekday.wednesday
    | weekday.wednesday =>  weekday.thursday
    | weekday.thursday =>  weekday.friday
    | weekday.friday =>  weekday.monday
    | weekday.saturday =>  weekday.monday

open weekday -- so that we can write just "sunday" instead of "weekday.sunday"

def next_workday : weekday → weekday
    | sunday =>  monday
    | monday =>  tuesday
    | tuesday =>  wednesday
    | wednesday =>  thursday
    | thursday =>  friday
    | friday =>  monday
    | saturday =>  monday

example: next_workday friday = monday := by {rfl}
example: next_workday saturday = monday := by {rfl}
example: next_workday (next_workday monday) = wednesday := by {rfl}

#check monday
#check weekday.monday

#check if (monday = sunday) then 0 else 1   -- this doesn't type check unless we add the "deriving DecidableEq" in the type


/- **Constructors must return the defined type**
Note that the constructors of a newly defined data type must return that type:
-/

inductive bla : Type
    | bli : bla
    | blu : bla -> Nat   -- constructor blu is invalid, because it returns a Nat! it should return a bla

-- but this is ok:
inductive bla : Type
    | bli : bla
    | blu : bla -> bla

#check bla.bli
#check bla.blu bla.bli



---------------------------------------------------
-- RECURSIVELY DEFINED TYPES
---------------------------------------------------

-- We now look at a more interesting definition of an inductive data type which is defined recursively. (By the way, why are these called "inductive"? because they are strongly related to "induction", a fundamental proof technique that we will see later.) We will re-define the natural numbers. (For a similar treatment with Coq, see https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html#NatPlayground.)


inductive myNat : Type
  | Z : myNat
  | S : myNat -> myNat
  deriving DecidableEq

#check myNat.Z -- just Z here doesn't work

#check myNat.Z -- 0
#check myNat.S (myNat.Z) -- 1
#check myNat.S (myNat.S myNat.Z) -- 2

open myNat -- this allows us to omit "myNat."

#check Z -- zero
#check S Z -- one
#check S (S Z) -- two

#check S S Z -- type error
#check (S S) Z -- type error


---------------------------------------------------
-- DEFINING BASIC ARITHMETIC OPERATIONS ON mynats:
---------------------------------------------------

-- addition on myNat :
def myplus: myNat -> myNat -> myNat
  | myNat.Z, y => y
  | (S x), y => S (myplus x y)    -- (x+1) + y  =  (x+y) + 1
--  | (myNat.S x) y := (myplus x (S y))     -- (x+1) + y  =  x + (y+1)


#check myplus


#reduce myplus Z Z
#reduce myplus (S Z) (S Z)
#reduce myplus (S (S (S Z)))  (S (S (S (S Z))))

example: myplus Z Z = Z := by {rfl}
example: myplus Z (S Z) = S Z := by {rfl}
example: myplus (S Z) Z = S Z := by {rfl}
example: myplus (S Z) (S Z) = S (S Z) := by {rfl}
example: myplus (S (S (S Z)))  (S (S (S (S Z)))) = S (S (S (S (S (S (S Z)))))) := by {rfl}



---------------------------------------------------
-- A LEAN mystery
---------------------------------------------------

def myplusLEANcanTrefl: myNat -> myNat -> myNat
  | Z, Z => Z
  | Z, (S n) => S (myplusLEANcanTrefl Z n)
  | (S n), Z => S (myplusLEANcanTrefl n Z)
  | (S n1), (S n2) => S (S (myplusLEANcanTrefl n1 n2))

#reduce myplusLEANcanTrefl Z Z
#reduce myplusLEANcanTrefl (S Z) (S (S Z))

example: (myplusLEANcanTrefl Z Z) = Z := by {rfl} -- ???
example: (myplusLEANcanTrefl Z Z) = Z := by { rw [myplusLEANcanTrefl] } -- works, we will learn the rw tactic later
example: (myplusLEANcanTrefl Z (S Z)) = (S Z) := by { rw [myplusLEANcanTrefl]; rw [myplusLEANcanTrefl] }



def myplusLEANcanrefl: myNat -> myNat -> myNat
  | Z, Z => Z
  | (S x), Z => (S x)
  | Z, (S y) => (S y)
  | (S x), (S y) => S (S (myplusLEANcanrefl x y))

example: myplusLEANcanrefl Z Z = Z := by {rfl}
example: myplusLEANcanrefl Z (S Z) = S Z := by {rfl}
example: myplusLEANcanrefl (S Z) Z = S Z := by {rfl}
example: myplusLEANcanrefl (S Z) (S Z) = S (S Z) := by {rfl}


/- It's a mystery why LEAN "can't do rfl" on the claim "(myplusLEANcanTrefl Z Z) = Z" but can do rfl on "(myplusLEANcanrefl Z Z) = Z". We will not be concerned with such details, since our goal is not to learn the internal subtleties of LEAN, but to learn the fundamentals.

As far as we are concerned, (myplusLEANcanTrefl Z Z) = Z holds, because (myplusLEANcanTrefl Z Z) indeed reduces to Z, by the first line in the definition of myplusLEANcanTrefl. And the alternative proof of the examples with the _rw_ tactic shows that.

If you encounter problems like the above in your tests, talk to us.
-/


---------------------------------------------------
-- REDEFINING BASIC ARITHMETIC OPERATIONS ON Nats:
---------------------------------------------------

/- myNats are unreadable, so we won't use them much. Instead, we will re-define arithmetic operations like addition and multiplication on Lean's Nat type:
-/

#print Nat

example: 3 = Nat.succ (Nat.succ (Nat.succ Nat.zero)) := by {rfl}


-- addition:
def plus : Nat -> Nat -> Nat
  | Nat.zero, y => y
  | (Nat.succ x), y => Nat.succ (plus x y)
--  | x, (Nat.succ y) => (plus (Nat.succ x) y) -- makes life harder (later)

#check plus
example: plus 0 0 = 0 := by {rfl}
example: plus 0 1 = 1 := by {rfl}
example: plus 1 0 = 1 := by {rfl}
example: plus 1 1 = 2 := by {rfl}
example: plus 111 111 = 222 := by {rfl}

-- we could also have defined plus like this:
def plusbis : Nat -> Nat -> Nat
    | 0, y => y
    | (x+1), y => (plus x y) + 1

-- but we will avoid the above definition, because it's not immediate obvious that "x+1" is the same as "Nat.succ x". now that we know how nats are defined, we will use the constructors for nats.
