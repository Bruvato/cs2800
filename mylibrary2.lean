-- CS 2800 LOGIC AND COMPUTATION, FALL 2026
-- COPYRIGHT 2026 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

import mylibrary1

-- Exclusive Or on Props:
def XOR : Prop -> Prop -> Prop := fun p q => Or (And p (Not q)) (And (Not p) q)

-- Exclusive or on Bools:
#check Bool.xor

def negb : Bool -> Bool
    | true  => false  -- if the input is true , return false
    | false  => true  -- if the input is false , return true

def andb : Bool -> Bool -> Bool
    | false, _ => false
    | true, y  => y

def orb : Bool -> Bool -> Bool
    | true, _ => true
    | false, y => y

def impliesb : Bool -> Bool -> Bool
  | false, _ => true
  | true, y => y


def app : List Nat -> List Nat -> List Nat
  | [], L => L
  | (x :: L1), L2 => x :: (app L1 L2)

def rev : List Nat -> List Nat
  | [] => []
  | (a :: L) => app (rev L) [a]

def mult : Nat -> Nat -> Nat
  | Nat.zero, _ => Nat.zero
  | (Nat.succ x), y => plus y (mult x y)

def exponent : Nat -> Nat -> Nat
  | _, 0 => 1
  | x, (e+1) => mult x (exponent x e)

def evenb : Nat -> Bool
    | 0 => true
    | 1 => false
    | (Nat.succ (Nat.succ x)) => evenb x
