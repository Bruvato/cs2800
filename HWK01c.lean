def skip:  List Nat -> List Nat
  | [] => []
  | h :: [] => [h]
  | h :: _ :: rest => h :: skip rest

example: skip [] = [] := by {rfl}
example: skip [1] = [1] := by {rfl}
example: skip [1,2] = [1] := by {rfl}
example: skip [1,2,3] = [1,3] := by {rfl}
example: skip [1,2,3,4] = [1,3] := by {rfl}
example: skip [1,2,3,4,5] = [1,3,5] := by {rfl}

-------------------------------------------
-- Bool -> Nat -> (Bool -> Nat) -> String
def F (a : Bool) (x : Nat) := fun (f: (Bool -> Nat)) => ""

#check F



-----------------------------

-- Define the function "apply" which takes as input a list of Nats
-- L = [x1,x2,...] and a function f : Nat → Nat, and returns the list
-- L' = [(f x1), (f x2), ...], that is, it applies f to all the elements of L.

-- Test your apply function on examples using the empty list [] and the list [0,1,2,3], and passing as the second argument f the anonymous (lambda) functions that multiply their input by 3, and add 42 to their input. Also achieve the "add 42" effect by passing a partial evaluation of the plus function:

def plus : Nat -> Nat -> Nat
  | Nat.zero, y => y
  | (Nat.succ x), y => Nat.succ (plus x y)

def apply : List Nat -> (Nat -> Nat) -> List Nat
  | [], _ => []
  | head :: tail, f => (f head) :: (apply tail f)

example: apply [] (fun x: Nat => x + 1) = [] := by {rfl}
example: apply [] (fun x: Nat => x + 2) = [] := by {rfl}
example: apply [0,1,2,3] (fun x: Nat => x *3) = [0,3,6,9] := by {rfl}
example: apply [0,1,2,3] (fun x: Nat => x + 42) = [42,43,44,45] := by {rfl}
example: apply [0,1,2,3] (plus 42) = [42,43,44,45] := by {rfl}


-- --------------------------------------

-- Now define the function "all42" which takes as input a list of Nats L and turns all the elements of L into 42. Define all42 not by recursion, but by calling apply on L and the appropriate anonymous function.

def all42 (L : List Nat) := apply L (fun _: Nat => 42)
example: all42 [] = [] := by {rfl}
example: all42 [1,2,3] = [42,42,42] := by {rfl}

-- ----------------------------

/- PRODUCT TYPES AND CURRYING
-- In addition to "arrow types" like A → B, in Lean we can have "product types" like A × B: the set of pairs of elements (x,y) such that x : A and y : B. Then we can define addition on pairs of Nats as follows:
-- -/
def addpair : (Nat × Nat) → Nat
  | (x,y) => x + y
#check addpair
example: addpair (2,3) = 5 := by {rfl}

-- #check addpair 2 3 -- type error, why?

-- /- Pairs are cumbersome to work with, because we have to "extract" from the pair the first and second elements. We can do that as follows: -/
#eval (1,2).fst
#eval (1,2).snd
#eval (1, (2,3)).snd.fst
#eval (1,2,3).fst
#eval (1,2,3).snd
#eval (1,2,3).snd.fst
#eval (1,2,3).snd.snd

-- -- Using .fst and .snd, we can define addpair without pattern matching:
def addpairnopatt (x : Nat × Nat) : Nat := x.fst + x.snd
#check addpairnopatt
example: addpairnopatt (2,3) = 5 := by {rfl}
-- Question 4.1
-- Q4.1
-- 5 Points
-- Grading comment:

-- Define the function "curry" which takes as input a function f and returns as output a function g, such that:

--     f takes as input a pair of Nats (x,y) and returns a Nat

--     g takes as input two nats x and y, and returns as output the Nat (f (x,y)).
def curry (f: (Nat × Nat) -> Nat) : Nat -> Nat -> Nat := fun x y => f (x, y)

example: curry addpair 1 2 = 3 := by {rfl}
example: curry addpair = Nat.add := by {rfl}   -- wow! a powerful test!
example: curry addpairnopatt = Nat.add := by {rfl}    -- wow! powerful!



-- ----------------------------------------------------------------------------------

/- Define the function addprod3 which takes as input a triple of Nats and returns their sum, as in the examples that follow. -/
def addprod3 (x: Nat × Nat × Nat) : Nat := x.fst + x.snd.fst + x.snd.snd

example: addprod3 (0,0,0) = 0 := by {rfl}
example: addprod3 (1,1,1) = 3 := by {rfl}
example: addprod3 (1,2,3) = 6 := by {rfl}
example: addprod3 (10,2,3) = 15 := by {rfl}
example: addprod3 (1, (2, 3)) = 6 := by {rfl}


-- ----------------------------------------------------------------------------------

-- Define the function serialcompo which takes as input two functions f : Nat → Bool and g : Bool → String, and returns their serial composition f ∘ g : Nat → String.
def serialcompo (f: Nat -> Bool) (g: Bool -> String) : Nat -> String := fun x: Nat => g (f x)

example: serialcompo (fun x : Nat => if x=0 then true else false) (fun b : Bool => if (b = true) then "zero!" else "nonzero!") 0 = "zero!" := by {rfl}
example: serialcompo (fun x : Nat => if x=0 then true else false) (fun b : Bool => if (b = true) then "zero!" else "nonzero!") 42 = "nonzero!" := by {rfl}
-- ----------------------------------------------------------------------------------

-- Then define the function serialcompolist which takes as input a list of functions L = [f1,f2,...], where each function fi is from Nat to Nat, and returns as output the serial composition f1 ∘ (f2 ∘ (f3 ∘ ...)).

-- If L is empty, then serialcompolist should return the identity function on Nats (see first example below). If L has only one element f, then serialcompolist should return f. If L = [f1,f2], then serialcompolist should return (f1 ∘ f2). If L = [f1,f2,f3], then should serialcompolist return (f1 ∘ (f2 ∘ f3)) or ((f1 ∘ f2) ∘ f3)? Are these two the same or different? In other words, is serial composition associative?

def serialcompolist : List (Nat -> Nat) -> (Nat -> Nat)
  | [] => fun x : Nat => x
  | f :: rest => fun x : Nat => serialcompolist rest (f x)


example: serialcompolist [] = fun x : Nat => x := by {rfl}
example: serialcompolist [plus 0] = fun x : Nat => x := by {rfl}
example: serialcompolist [plus 42] = plus 42 := by {rfl}
example: serialcompolist [plus 32, plus 10] = plus 42 := by {rfl}
example: serialcompolist [Nat.mul 2, Nat.add 1] = fun x : Nat => 1 + 2*x := by {rfl}
example: serialcompolist [Nat.add 1, Nat.mul 2] = fun x : Nat => 2*(1+x) := by {rfl}
example: serialcompolist [Nat.mul 42, Nat.add 3, Nat.mul 7] = fun x : Nat => 7*(3+42*x) := by {rfl}

-- ----------------------------------------------------------------------------------

-- Define an inductive data type BTN which represents a binary tree of Nats. Every node of the tree (including both internal nodes and leaves) is labeled with a Nat. BTN has two constructors, BTN.leaf and BTN.node. Examples of objects of type BTN are given below:

-- examples of trees:
inductive BTN : Type
  | leaf : Nat -> BTN
  | node : BTN -> Nat -> BTN -> BTN

#check BTN.leaf 42   -- a tree of just one node
#check BTN.node (BTN.leaf 42) 10 (BTN.leaf 0) -- a tree with 3 nodes; the root label is 10, the left leaf label is 42 and the right leaf label is 0
#check BTN.node (BTN.node (BTN.leaf 42) 10 (BTN.leaf 0)) 10 (BTN.leaf 0) -- a tree with 5 nodes

-- ----------------------------------------------------------------------------------
-- Define the function countBTNnodes : BTN -> Nat, which returns the total number of nodes in a given BTN (including leaves). Test your function with example on at least the 3 example trees above.

def countBTNnodes : BTN -> Nat
  | BTN.leaf _ => 1
  | BTN.node n1 _ n2 => (countBTNnodes n1) + (countBTNnodes n2) + 1


example: countBTNnodes (BTN.leaf 42) = 1 := by {rfl}
example: countBTNnodes (BTN.node (BTN.leaf 42) 10 (BTN.leaf 0)) = 3 := by {rfl}
example: countBTNnodes (BTN.node (BTN.node (BTN.leaf 42) 10 (BTN.leaf 0)) 10 (BTN.leaf 0)) = 5 := by {rfl}
-- ----------------------------------------------------------------------------------
-- Define the function inBTN : Nat -> BTN -> Bool, which checks whether the given Nat is one of the labels of the given BTN.

def inBTN : Nat -> BTN -> Bool
  | n, BTN.leaf val => n == val
  | n, BTN.node n1 val n2 => n == val || inBTN n n1 || inBTN n n2

example : inBTN 1 (BTN.leaf 1) = true := by { rfl }
example : inBTN 1 (BTN.node (BTN.leaf 2) 1 (BTN.leaf 3)) = true := by { rfl }
example : inBTN 2 (BTN.node (BTN.leaf 2) 1 (BTN.leaf 3)) = true := by { rfl }
example : inBTN 3 (BTN.node (BTN.leaf 2) 1 (BTN.leaf 3)) = true := by { rfl }
example : inBTN 67 (BTN.leaf 1) = false := by { rfl }
example : inBTN 67 (BTN.node (BTN.leaf 2) 1 (BTN.leaf 3)) = false := by { rfl }
example : inBTN 1 (BTN.node (BTN.leaf 4) 0 (BTN.node (BTN.leaf 2) 1 (BTN.leaf 3))) = true := by { rfl }
-- ----------------------------------------------------------------------------------

-- Define the function BTNtoList : BTN -> List Nat, which returns the list of node labels in a given BTN. Note that depending on how you implement this function, the resulting list might be ordered differently. Find the implementation that passes all tests given below.
def app : List Nat -> List Nat -> List Nat
  | [], [] => []
  | l1, [] => l1
  | [], l2 => l2
  | h :: t, l2 => h :: (app t l2)

def BTNtoList : BTN -> List Nat
  | BTN.leaf val => [val]
  | BTN.node n1 val n2 => val :: (app (BTNtoList n1) (BTNtoList n2))

example: BTNtoList (BTN.leaf 42) = [42] := by {rfl}
example: BTNtoList (BTN.node (BTN.leaf 42) 10 (BTN.leaf 0)) = [10,42,0] := by {rfl}
example: BTNtoList (BTN.node (BTN.node (BTN.leaf 42) 10 (BTN.leaf 0)) 10 (BTN.leaf 0)) = [10,10,42,0,0] := by {rfl}
