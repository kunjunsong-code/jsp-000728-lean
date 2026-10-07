import Init.Data.List.Basic
import Init.Data.List.Lemmas

set_option maxRecDepth 1000000

/-!
# JSP-000728 - Lean 4.20.0, no Mathlib

## Question
How many inclusion-maximal sum-free subsets does a finite integer interval have?

## Answer (for {1,...,6})
A sum-free subset S of {1,...,6} is inclusion-maximal if no additional
element can be added while preserving the sum-free property.
There are exactly 6 such maximal sum-free subsets.

All proofs use decide. No sorry, no admit, no native_decide.
-/

def isSumFree (S : List Nat) : Bool :=
  ! (S.any fun a => S.any fun b => S.any fun c => a + b = c)

def powerSet {alpha : Type} : List alpha -> List (List alpha)
  | [] => [[]]
  | (x::xs) => (powerSet xs).map (fun s => x :: s) ++ powerSet xs

def isMaximalSumFree (n : Nat) (S : List Nat) : Bool :=
  isSumFree S &&
  (List.range' 1 n).all fun x =>
    S.contains x || ! isSumFree (x :: S)

def countMaximalSumFree (n : Nat) : Nat :=
  (powerSet (List.range' 1 n)).filter (isMaximalSumFree n) |>.length

theorem maximalSumFreeCount_6 : countMaximalSumFree 6 = 6 := by decide

#print axioms maximalSumFreeCount_6