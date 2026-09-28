def factorial : Nat -> Nat
  | 0 => 1
  | (n + 1) => (n + 1) * factorial (n)

example: factorial 0 = 1 := by {rfl}
example: factorial 1 = 1 := by {rfl}
example: factorial 2 = 2 := by {rfl}
example: factorial 3 = 6 := by {rfl}
example: factorial 4 = 24 := by {rfl}
example: factorial 5 = 120 := by {rfl}


def fib : Nat -> Nat
  | 0 => 0
  | 1 => 1
  | (n + 2) => fib (n + 1) + fib (n)

example: fib 0 = 0 := by {rfl}
example: fib 1 = 1 := by {rfl}
example: fib 2 = 1 := by {rfl}
example: fib 3 = 2 := by {rfl}
example: fib 4 = 3 := by {rfl}
example: fib 5 = 5 := by {rfl}
example: fib 6 = 8 := by {rfl}
example: fib 7 = 13 := by {rfl}
example: fib 10 = 55 := by {rfl}


def exponent : Nat -> Nat -> Nat
  | b, 0 => 1
  | b, (e + 1) => b * (exponent b e)

example: exponent 0 0 = 1 := by {rfl}
example: exponent 1 0 = 1 := by {rfl}
example: exponent 0 1 = 0 := by {rfl}
example: exponent 2 2 = 4 := by {rfl}
example: exponent 2 3 = 8 := by {rfl}
example: exponent 2 10 = 1024 := by {rfl}


-- Define the function minus which implements subtraction on Nats. See examples that follow.
def minus : Nat -> Nat -> Nat
  | 0, _ => 0
  | a, 0 => a
  | a + 1, b + 1 => minus a b

example: minus 0 1 = 0 := by {rfl}
example: minus 0 2 = 0 := by {rfl}
example: minus 0 10 = 0 := by {rfl}
example: minus 10 10 = 0 := by {rfl}
example: minus 10 0 = 10 := by {rfl}
example: minus 7 5 = 2 := by {rfl}

def app : List Nat -> List Nat -> List Nat
  | [], [] => []
  | l1, [] => l1
  | [], l2 => l2
  | h :: t, l2 => h :: (app t l2)

example: app List.nil [ ] = [ ] := by {rfl}
example: app [1,2,3] List.nil = [1,2,3] := by {rfl}
example: app List.nil [4,5,6] = [4,5,6] := by {rfl}
example: app [ 1,2,3 ] (6 :: []) = [ 1,2,3,6 ] := by {rfl}
example: app (1 :: []) [ 4,5,6 ] = [ 1,4,5,6 ] := by {rfl}


def revHelp : List Nat -> List Nat -> List Nat
  | [], acc => acc
  | h :: t, acc => revHelp t (h :: acc)

def rev : List Nat -> List Nat
  | l => revHelp l []


example: rev [] = [] := by {rfl}
example: rev [42] = [42] := by {rfl}
example: rev [1,2,3] = [3,2,1] := by {rfl}


-- Define the function "rl" which takes a list of nats L and a Nat n, and rotates L to the left n times. See examples below. You may use "app" as a helper function.
def rl : List Nat -> Nat -> List Nat
  | [], _ => []
  | l, 0 => l
  | h :: t, n + 1 => rl (app t ([h])) n

example : rl [1,2,3] 0 = [1,2,3] := by {rfl}
example : rl [1,2,3] 1 = [2,3,1] := by {rfl}
example : rl [1,2,3] 2 = [3,1,2] := by {rfl}
example : rl [1,2,3] 3 = [1,2,3] := by {rfl}
example : rl [1,2,3] 30 = [1,2,3] := by {rfl}
example : rl [] 13 = [] := by {rfl}
example : rl [1] 130 = [1] := by {rfl}



-- Define the function ith_elem which returns the ith element of a list of Nats (0 if the list is empty). See examples below for other corner cases.
def ith_elem : List Nat -> Nat -> Nat
  | [], _ => 0
  | h :: _, 0 => h
  | _ :: t, n + 1 => ith_elem t n

example: ith_elem [] 0 = 0 := by {rfl}
example: ith_elem [] 10 = 0 := by {rfl}
example: ith_elem [42] 0 = 42 := by {rfl}
example: ith_elem [42] 1 = 0 := by {rfl}
example: ith_elem [1,2,3] 0 = 1 := by {rfl}
example: ith_elem [1,2,3] 1 = 2 := by {rfl}
example: ith_elem [1,2,3] 2 = 3 := by {rfl}
example: ith_elem [1,2,3] 4 = 0 := by {rfl}
example: ith_elem [1,2,3] 14 = 0 := by {rfl}

-- Define the function list_delete which takes a list of Nats L, and an index i which is a Nat, and deletes the i-th element of L. See examples below.
def list_delete : List Nat -> Nat -> List Nat
  | [], _ => []
  | _ :: t, 0 => t
  | h :: t, n + 1 => h :: list_delete t n

example: list_delete [] 0 = [] := by {rfl}
example: list_delete [] 10 = [] := by {rfl}
example: list_delete [] 100 = [] := by {rfl}
example: list_delete [1,2,3] 0 = [2,3] := by {rfl}
example: list_delete [1,2,3] 1 = [1,3] := by {rfl}
example: list_delete [1,2,3] 2 = [1,2] := by {rfl}
example: list_delete [1,2,3] 3 = [1,2,3] := by {rfl}
example: list_delete [1,2,3] 3000 = [1,2,3] := by {rfl}


-- Define the function rr which takes a list of nats L and a Nat n, and rotates L to the right n times. See examples below.

def rr : List Nat -> Nat -> List Nat
  | [], _ => []
  | l, 0 => l
  | l, n => rev (rl (rev l) n)


example : rr [1,2,3] 0 = [1,2,3] := by {rfl}
example : rr [1,2,3] 1 = [3,1,2] := by {rfl}
example : rr [1,2,3] 2 = [2,3,1] := by {rfl}
example : rr [1,2,3] 3 = [1,2,3] := by {rfl}
example : rr [1,2,3] 30 = [1,2,3] := by {rfl}
example : rr [] 130 = [] := by {rfl}
example : rr [1] 45 = [1] := by {rfl}


-- Define the function "zip" which takes as input two lists of nats and "zips" or "merges" them, as in the examples provided below.
def zip : List Nat -> List Nat -> List Nat
  | l1, [] => l1
  | [], l2 => l2
  | h1 :: t1, h2 :: t2 => h1 :: h2 :: zip t1 t2

example: zip ([1,2,3]) ([4,5,6]) = [1,4,2,5,3,6] := by {rfl}
example: zip ([1,2,3,4]) ([5,6]) = [1,5,2,6,3,4] := by {rfl}
example: zip ([1,2,3]) ([]) = [1,2,3] := by {rfl}
example: zip ([]) ([1,2,3]) = [1,2,3] := by {rfl}


-- Define the function "list1toN" which takes a Nat n and returns the list [1,2,...,n] if n>0, an the empty list if n = 0.
def list1toNHelp : Nat -> List Nat -> List Nat
  | 0, acc => acc
  | n + 1, acc => list1toNHelp n ((n + 1) :: acc)

def list1toN : Nat -> List Nat
  | n => list1toNHelp n []

example: list1toN 0 = [] := by {rfl}
example: list1toN 1 = [1] := by {rfl}
example: list1toN 2 = [1,2] := by {rfl}
example: list1toN 10 = [1,2,3,4,5,6,7,8,9,10] := by {rfl}


-- Define a function lenmul3 which takes as input a list of Nats and returns Bool true if the list's length is a multiple of 3, and Bool false otherwise. An empty list has length 0, which is a multiple of 3: 0*3=3. Define the function directly using pattern matching and recursion, without using the "len" or "modulo" functions.

def lenmul3 : List Nat -> Bool
  | [] => true
  | _ :: [] => false
  | _ :: _ :: [] => false
  | _ :: _ :: _ :: rest => lenmul3 rest

example: lenmul3 [] = true := by {rfl}
example: lenmul3 [1] = false := by {rfl}
example: lenmul3 [1,2] = false := by {rfl}
example: lenmul3 [1,2,3] = true := by {rfl}
example: lenmul3 [1,2,3,4] = false := by {rfl}
example: lenmul3 [1,2,3,4,5,6,7,8,9] = true := by {rfl}

def F (f: Bool -> Nat) (n: Nat) : String := "asda"

#check F
#eval (F (fun _ : Bool => 42) 0) :: ["hello"]
