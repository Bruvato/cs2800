def thrice (x : Nat) : Nat := x * 3


example: thrice 0 = 0 := by {rfl}
example: thrice 1 = 3 := by {rfl}
example: thrice 2 = 6 := by {rfl}
example: thrice 3 = 9 := by {rfl}
example: thrice 9 = 27 := by {rfl}


#check 1



example: 1 = Nat.succ Nat.zero := by {rfl}
example: [1] = List.cons 1 List.nil := by {rfl}


#check Bool -> (Nat -> (Int -> Nat) -> Int)

#check Nat -> (Bool -> Int)
#check (Nat -> Bool) -> Int

#check Nat -> (Bool -> Int)
#check Nat -> Bool -> Int

#check Nat -> (Bool -> Int)
#check (Nat -> Bool -> Int)

def f42 (b : Bool) (x : Nat) := if (b = true) then (x:Int) else (-x:Int)

#check Int.toNat
example: Int.toNat 42 = 42 := by {rfl}
example: Int.toNat (-42) = 0 := by {rfl}




#check Nat -> Bool -> Nat
#check Nat -> (Bool -> Nat)
#check (Nat -> Bool) -> Nat


-- def f1 (x: Nat) (y: Bool) : Nat := ite (y = true) x x

-- #check f1

-- def f2 (x: Nat → Bool) : Nat := ite (x (0)) 0 0

-- #check f2


#check (Nat -> Int) -> (Nat -> Int)
def f1 (x: Nat → Int) (y: Nat) : Int := x (y)
#check f1

#check (Nat -> Int -> Nat -> Int)
def f2 (x: Nat) (y: Int) (z: Nat) : Int :=  x + y + z
#check f2

#check Nat -> Int -> (Nat -> Int)
def f3 (x: Nat) (y: Int) : (Nat → Int) := fun (z: Nat) => x + y + z
#check f3

#check Bool -> (Nat -> (Nat -> Nat) -> Nat)
def f4 (b: Bool) (n: Nat) (x: Nat → Nat) : Nat := ite (b = true) (x (n)) 0
#check f4


#check True :: []
