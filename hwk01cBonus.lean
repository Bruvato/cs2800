import mylibrary1
import DefaultScoring

/-
**INSTRUCTIONS:**
 - Enter your answers into the _Section Answer  end Answer_ part of the corresponding question. **Enter valid Lean code** otherwise your submission will be rejected.
 - **Do not modify in any way the rest of this file.** If you do, your submission will be rejected. Do not, for instance, add more tests (you can do that on your local copy, but not here.)
 - Submit this file, **and only this file**, as a single .lean file on Gradescope.
-/

question Question1
/-
Define the function skip which "skips" every other element in a list of Nats L. See examples below.
-/
section Answer
def skip:  List Nat -> List Nat
  | [] => []
  | h :: [] => [h]
  | h :: _ :: rest => h :: skip rest
end Answer

-- If your answer fails a Spec, you get 0 points for that question
section Spec
example: skip [] = [] := by {rfl}
example: skip [1] = [1] := by {rfl}
example: skip [1,2] = [1] := by {rfl}
example: skip [1,2,3] = [1,3] := by {rfl}
example: skip [1,2,3,4] = [1,3] := by {rfl}
example: skip [1,2,3,4,5] = [1,3,5] := by {rfl}
end Spec

end Question1

question Q7_3
-- max 2 Points

inductive ble : Type
    | bli : Nat -> Int -> Bool -> ble
deriving DecidableEq
/-
Is type _ble_ defined above finite or infinite? Answer by defining the variable below as the Bool "true" or "false":

def ble_is_finite := [true or false]
-/

section Answer
def ble_is_finite := false
end Answer

section Spec
#check (ble_is_finite : Bool)
-- Your answer must pass this type-checking Spec, but must also be correct.
end Spec


end Q7_3

question Q7_3bis
-- max 3 Points
/-
Define two distinct elements of type ble:

def x1 := ...
def x2 := ...
-/

section Answer
def x1 := ble.bli 0 1 true
def x2 := ble.bli 1 (-5) false
end Answer

section Spec1
#check (x1 : ble)
end Spec1

section Spec2
#check (x2 : ble)
end Spec2


end Q7_3bis


question Question3_3

/-
Define the function "all42" which takes as input a list of Nats L and turns all the elements of L into 42. Define all42 not by recursion, but by calling apply on L and the appropriate anonymous function, where apply takes a list of Nats [x1,x2,...] and a function f : Nat -> Nat, and returns [(f x1), (f x2), ...].
-/


section Answer
def apply : List Nat -> (Nat -> Nat) -> List Nat
  | [], _ => []
  | head :: tail, f => (f head) :: (apply tail f)

def all42 (L : List Nat) := apply L (fun _: Nat => 42)
end Answer

section Spec

example: all42 [] = [] := by {rfl}
example: all42 [1,2,3] = [42,42,42] := by {rfl}

end Spec

gradescope_defaults
#eval Score.score
#eval Message.message

end Question3_3

/-
PRODUCT TYPES AND CURRYING

In addition to "arrow types" like A -> B, in Lean we can have "product types" like A x B: the set of pairs of elements (x,y) such that x : A and y : B. Then we can define addition on pairs of Nats as follows:
-/

def addpair : (Nat × Nat) → Nat
  | (x,y) => x + y

example: addpair (2,3) = 5 := by {rfl}

-- Note that addpair 2 3 is a type error, why?

/-
Pairs are cumbersome to work with, because we have to "extract" from the pair the first and second elements. We can do that as follows:
-/

#eval (1,2).fst
#eval (1,2).snd
#eval (1, (2,3)).snd.fst
#eval (1,2,3).fst
#eval (1,2,3).snd
#eval (1,2,3).snd.fst
#eval (1,2,3).snd.snd

-- Using .fst and .snd, we can define addpair without pattern matching:

def addpairnopatt (x : Nat × Nat) : Nat := x.fst + x.snd

example: addpairnopatt (2,3) = 5 := by {rfl}

question Question4_1

/-
Define the function "curry" which takes as input a function f and returns as output a function g, such that:

- f takes as input a pair of Nats (x,y) and returns a Nat
- g takes as input two Nats x and y, and returns as output the Nat (f (x,y)).

https://en.wikipedia.org/wiki/Haskell_Curry
-/

section Answer
def curry (f: (Nat × Nat) -> Nat) : Nat -> Nat -> Nat := fun x y => f (x, y)
end Answer

section Spec

example: curry addpair 1 2 = 3 := by {rfl}
example: curry addpair = Nat.add := by {rfl}   -- wow! a powerful test!
example: curry addpairnopatt = Nat.add := by {rfl}    -- wow! powerful!

end Spec

gradescope_defaults

end Question4_1

#eval curry addpair 1 1

question Question4_2

/-
Define the function addprod3 which takes as input a triple of Nats and returns their sum, as in the examples that follow.
-/

section Answer
def addprod3 (x: Nat × Nat × Nat) : Nat := x.fst + x.snd.fst + x.snd.snd
end Answer

section Spec

example: addprod3 (0,0,0) = 0 := by {rfl}
example: addprod3 (1,1,1) = 3 := by {rfl}
example: addprod3 (1,2,3) = 6 := by {rfl}
example: addprod3 (10,2,3) = 15 := by {rfl}
example: addprod3 (1, (2, 3)) = 6 := by {rfl}

end Spec

gradescope_defaults

end Question4_2

/-
SERIAL COMPOSITION

The serial composition of two functions f : A -> B and g : B -> C, is the function f ∘ g : A -> C, such that (f ∘ g) x = g (f x).
-/

question Question5_1

/-
Define the function serialcompo which takes as input two functions f : Nat -> Bool and g : Bool -> String, and returns their serial composition f ∘ g : Nat -> String.
-/

section Answer
def serialcompo (f: Nat -> Bool) (g: Bool -> String) : Nat -> String := fun x => g (f x)
end Answer

section Spec

example: serialcompo (fun x : Nat => if x=0 then true else false)
  (fun b : Bool => if (b = true) then "zero!" else "nonzero!") 0
  = "zero!" := by {rfl}
example: serialcompo (fun x : Nat => if x=0 then true else false)
  (fun b : Bool => if (b = true) then "zero!" else "nonzero!") 42
  = "nonzero!" := by {rfl}

end Spec

gradescope_defaults

end Question5_1

question Question5_3

/-
Define the function serialcompolist which takes as input a list of functions L = [f1,f2,...], where each function fi is from Nat to Nat, and returns as output the serial composition f1 ∘ (f2 ∘ (f3 ∘ ...)).

If L is empty, then serialcompolist should return the identity function on Nats (see first example below). If L has only one element f, then serialcompolist should return f. If L = [f1,f2], then serialcompolist should return (f1 ∘ f2). If L = [f1,f2,f3], then should serialcompolist return (f1 ∘ (f2 ∘ f3)) or
((f1 ∘ f2) ∘ f3)? Are these two the same or different? In other words, is serial composition associative?
-/

section Answer
def serialcompolist : List (Nat -> Nat) -> (Nat -> Nat)
  | [] => fun x => x
  | f :: rest => fun x : Nat => serialcompolist rest (f x)
end Answer

section Spec

example: serialcompolist [] = fun x : Nat => x := by {rfl}
example: serialcompolist [plus 0] = fun x : Nat => x := by {rfl}
example: serialcompolist [plus 42] = plus 42 := by {rfl}
example: serialcompolist [plus 32, plus 10] = plus 42 := by {rfl}
example: serialcompolist [Nat.mul 2, Nat.add 1] = fun x : Nat => 1 + 2*x
  := by {rfl}
example: serialcompolist [Nat.add 1, Nat.mul 2] = fun x : Nat => 2*(1+x)
  := by {rfl}
example: serialcompolist [Nat.mul 42, Nat.add 3, Nat.mul 7]
  = fun x : Nat => 7*(3+42*x) := by {rfl}

end Spec

gradescope_defaults

end Question5_3

question Question6_1

/-
Define an inductive data type BTN which represents a binary tree of Nats. Every node of the tree (including both internal nodes and leaves) is labeled with a Nat. BTN has two constructors, BTN.leaf and BTN.node. Examples of objects of type BTN are given below.
-/

section Answer
inductive BTN : Type
  | leaf : Nat -> BTN
  | node : BTN -> Nat -> BTN -> BTN
end Answer

section Spec

-- a tree of just one node
#check (BTN.leaf 42 : BTN)
-- a tree with 3 nodes; the root label is 10, the left leaf label is 42 and the right leaf label is 0
#check (BTN.node (BTN.leaf 42) 10 (BTN.leaf 0) : BTN)
-- a tree with 5 nodes
#check (BTN.node (BTN.node (BTN.leaf 42) 10 (BTN.leaf 0)) 10 (BTN.leaf 0) : BTN)

end Spec

gradescope_defaults

end Question6_1

question Question6_3

/-
Define the function countBTNnodes : BTN -> Nat, which returns the total number of nodes in a given BTN (including leaves).
-/

section Answer
def countBTNnodes : BTN -> Nat
  | BTN.leaf _ => 1
  | BTN.node n1 _ n2 => (countBTNnodes n1) + (countBTNnodes n2) + 1
end Answer

section Spec

example: countBTNnodes (BTN.leaf 42) = 1 := by {rfl}
example: countBTNnodes (BTN.node (BTN.leaf 42) 10 (BTN.leaf 0)) = 3 := by {rfl}
example: countBTNnodes
  (BTN.node (BTN.node (BTN.leaf 42) 10 (BTN.leaf 0)) 10 (BTN.leaf 0))
  = 5 := by {rfl}

end Spec

gradescope_defaults

end Question6_3

question Question6_5

/-
Define the function inBTN : Nat -> BTN -> Bool, which checks whether the given Nat is one of the labels of the given BTN.
-/

section Answer
def inBTN : Nat -> BTN -> Bool
  | n, BTN.leaf val => n == val
  | n, BTN.node n1 val n2 => n == val || inBTN n n1 || inBTN n n2
end Answer

section Spec

example : inBTN 1 (BTN.leaf 1) = true := by { rfl }
example : inBTN 1 (BTN.node (BTN.leaf 2) 1 (BTN.leaf 3)) = true := by { rfl }
example : inBTN 2 (BTN.node (BTN.leaf 2) 1 (BTN.leaf 3)) = true := by { rfl }
example : inBTN 3 (BTN.node (BTN.leaf 2) 1 (BTN.leaf 3)) = true := by { rfl }
example : inBTN 67 (BTN.leaf 1) = false := by { rfl }
example : inBTN 67 (BTN.node (BTN.leaf 2) 1 (BTN.leaf 3)) = false := by { rfl }
example : inBTN 1 (BTN.node (BTN.leaf 4) 0 (BTN.node (BTN.leaf 2) 1 (BTN.leaf 3))) = true := by { rfl }

end Spec

gradescope_defaults

end Question6_5

question Question6_7

/-
Define the function BTNtoList : BTN -> List Nat, which returns the list of node labels in a given BTN. Note that depending on how you implement this function, the resulting list might be ordered differently. Find the implementation that passes all tests given below.
-/

section Answer
def app : List Nat -> List Nat -> List Nat
  | [], [] => []
  | l1, [] => l1
  | [], l2 => l2
  | h :: t, l2 => h :: (app t l2)

def BTNtoList : BTN -> List Nat
  | BTN.leaf val => [val]
  | BTN.node n1 val n2 => val :: (app (BTNtoList n1) (BTNtoList n2))
end Answer

section Spec

example: BTNtoList (BTN.leaf 42) = [42] := by {rfl}
example: BTNtoList (BTN.node (BTN.leaf 42) 10 (BTN.leaf 0)) = [10,42,0] := by {rfl}
example: BTNtoList (BTN.node (BTN.node (BTN.leaf 42) 10 (BTN.leaf 0)) 10 (BTN.leaf 0)) = [10,10,42,0,0] := by {rfl}

end Spec

gradescope_defaults

end Question6_7
