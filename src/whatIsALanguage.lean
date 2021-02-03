inductive Syntax : Type
| I
| II
| III
| IV
| V

inductive Semantics : Type
| one
| two
| three
| four
| five

/-
I --> one
II --> two
III --> three
IV --> four
V --> five
-/

/-
A little bit of Lean
-/

-- Literal
-- Variable
-- Application

#reduce 1

def x := 1
#reduce x

def my_id : nat → nat := (λ n, n)   -- lambda expression, literal
                                -- type inference
--       T            V