import mylibrary1


/- Define the function evenb which checks whether a given Nat is even. -/
def evenb : Nat -> Bool
  | 0 => true
  | 1 => false
  | (n + 2) => evenb n

example: evenb 0 = true := by {rfl}
example: evenb 42 = true := by {rfl}
example: evenb 1 = false := by {rfl}
example: evenb 43 = false := by {rfl}

-- 42, 21, 20, 10, 5, 2,

-- Define the function ldupl which duplicates all elements in a list of Nats L. See examples below.
def ldupl : List Nat -> List Nat
  | [] => []
  | head :: rest => head :: head :: ldupl rest
example: ldupl [] = [] := by {rfl}
example: ldupl [1] = [1,1] := by {rfl}
example: ldupl [1,2] = [1,1,2,2] := by {rfl}
example: ldupl [1,2,3] = [1,1,2,2,3,3] := by {rfl}




def apply : List Nat -> (Nat -> Nat) -> List Nat
  | [], _ => []
  | (a :: L), f => (f a) :: (apply L f)

-- Fill-in the "___" below so that the test passes:

example : apply [42,43,44,45] (fun x => x) = [42,43,44,45] := by {rfl}





#check len

-- Fill-in the "___" below so that the test passes:

example: (fun (x : Nat) (L : List Nat) => len (x :: L)) 1 [1,2,3] = 4 := by {rfl}





def zip : List Nat -> List Nat -> List Nat
  | [], L2 => L2
  | L1, [] => L1
  | h1 :: t1, h2 :: t2 => h1 :: h2 :: zip t1 t2

#check zip





inductive foo : Type
  | bar : foo
  | ber : Nat -> foo
  | bor : foo -> Bool -> foo -> foo

#check (foo.bar : foo)
#check (foo.ber 0 : foo)
#check (foo.bor foo.bar true foo.bar : foo)
#check (foo.bor foo.bar true (foo.bor foo.bar true foo.bar) : foo)
#check (foo.bor foo.bar true (foo.ber 10) : foo)
#check (foo.bor (foo.ber 1) false (foo.ber 2) : foo)

#check foo.bor foo.bar
