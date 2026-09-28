-- CS 2800 LOGIC AND COMPUTATION, FALL 2026
-- COPYRIGHT 2026 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

def len : List Nat → Nat
    | [] => 0
    | (_ :: L) => Nat.succ (len L)

def plus : Nat -> Nat -> Nat
  | Nat.zero, y => y
  | (Nat.succ x), y => Nat.succ (plus x y)

inductive myNat : Type   -- we give it the name "mynat" because "nat" is taken
    | Z : myNat
    | S : myNat -> myNat
    deriving DecidableEq

inductive weekday : Type
    | sunday : weekday
    | monday : weekday
    | tuesday : weekday
    | wednesday : weekday
    | thursday : weekday
    | friday : weekday
    | saturday : weekday
    deriving DecidableEq

def next_workday : weekday → weekday
    | weekday.sunday =>  weekday.monday
    | weekday.monday =>  weekday.tuesday
    | weekday.tuesday =>  weekday.wednesday
    | weekday.wednesday =>  weekday.thursday
    | weekday.thursday =>  weekday.friday
    | weekday.friday =>  weekday.monday
    | weekday.saturday =>  weekday.monday

def leq : Nat -> Nat -> Bool
  | 0, _ => true
  | Nat.succ _, 0 => false
  | Nat.succ x, Nat.succ y => leq x y

def insrt : Nat -> List Nat -> List Nat
  | x, [] => [x]
  | x, (y :: L) =>  if (leq x y)
                    then x :: (y :: L)
                    else y :: (insrt x L)

def isort : List Nat -> List Nat
  | [] => []
  | (x :: L) => insrt x (isort L)
