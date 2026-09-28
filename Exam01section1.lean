def h1 (x y : Nat) : Nat := x+y

example: h1 2 3 = 5 := by {rfl}
example: h1 21 21 = 42 := by {rfl}


def H (f : Nat -> Nat) (x : Nat) (h : Nat -> Nat) : Nat := 0

#check H



#check Bool -> Nat -> Bool -> Nat
#check Bool -> (Nat -> Bool) -> Nat
#check (Bool -> Nat) -> Bool -> Nat

def A (x: Bool) (y: Nat) (z: Bool) : Nat := 0
#check A

def B (x: Bool) (f: Nat -> Bool) : Nat := 0
#check B

def C (f: Bool -> Nat) (x: Bool) : Nat := 0
#check C
