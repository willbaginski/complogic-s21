/-
HIGHER-ORDER FUNCTION WARMUP
-/

/-
1. Write a function, double, that takes
a natural number and returns its double.
Write it using the following recursive
definition:
- double 0 = 0
- double (n' + 1) = double n' + 2
-/


-- ANSWER HERE
def double : ℕ → ℕ
| 0 := 0
| (n' + 1) := double n' + 2

#eval double 0
#eval double 3

/-
2. Write a function, map_list_nat, that 
takes as its arguments (1) a list, l, of 
natural numbers, and (2) a function, f, 
from nat to nat, and that returns a new 
list of natural numbers constructed by 
applying f to each element of l. Make f
the first argument and l the second. The
function will work by case analysis and
recursion on l.

-/

-- ANSWER HERE
def map_list_nat (f : ℕ → ℕ) : list ℕ → list ℕ
| list.nil := list.nil
| (list.cons h t) := list.cons (f h) (map_list_nat t)

/-
3. Test your map_list_nat function by
applying it to several lists, both empty
and not, passing double as the function
value. Include [], [2], and [1,2,3] in
your set of test inputs and use comments
to document the expected return values.
-/

/- this should return the same empty list -/
#eval map_list_nat double []
/- should return [4] -/
#eval map_list_nat double [2]
/- should return [2,4,6] -/
#eval map_list_nat double [1,2,3]

/-
4. In Lean, repr is an "overloaded"
function. When applied to a value of a
type for which it's defined (we'll see 
later  how that happens) it returns a
string representation of the value. It
is defined for the nat type, and so 
when applied to a nat value it returns
a corresponding string. It's "toString"
for Lean. Here's an example.
-/

#eval repr 5

/-
Write a function map_list_nat_string
that takes a list of nat values and
returns a list of strings in which
each nat in the given list has been
converted to a string using repr.
-/

-- ANSWER HERE
def map_list_nat_string : list ℕ → list string
| list.nil := list.nil
| (list.cons h t) := list.cons (repr h) (map_list_nat_string t)

#eval map_list_nat_string []
#eval map_list_nat_string [1, 2, 3, 4]

/-
5. Write a function, filterZeros,
that takes a list of natural numbers
and returns the same list but with any
and all zero values removed. Given
[0], for example, it should return
[]; given [1,2,0,3,4,0, 0, 5] it 
should return [1,2,3,4,5].
-/

-- ANSWER HERE
def filterZeros : list ℕ → list ℕ
| list.nil := list.nil
| (list.cons 0 t) := filterZeros t
| (list.cons h t) := list.cons h (filterZeros t)

#eval filterZeros [1, 0, 1, 0, 3, 0, 0, 5, 0]

/-
6. Write a function, isEqN, that
takes a natural number, n, and returns
a function that takes a natural number,
m, and returns true (tt) if m = n and
that returns false (ff) otherwise. Be
sure to test your function.
-/

-- ANSWER HERE
def isEqn (n : ℕ) : (ℕ → bool) :=
λ m, m = n


#eval isEqn 1 1
#eval isEqn 0 1

/-
7.
Write a function filterNs that takes
a function, pred, from nat to bool 
and a list, l, of natural numbers, and
that returns a list like l but with all
the numbers that satisfy the predicate
function removed. Test your function
using isEqN to produce a few predicate
functions (functions that for a given
argument return true or false).
-/

-- ANSWER HERE
def filterNs (pred : ℕ → bool) : list ℕ → list ℕ
| list.nil := list.nil
| (list.cons h t) := if pred h then filterNs t else list.cons h (filterNs t)

#eval filterNs (isEqn 0) []
#eval filterNs (isEqn 0) [0, 0, 0]
#eval filterNs (isEqn 0) [1, 2, 3, 4]
#eval filterNs (isEqn 0) [1, 2, 0, 3, 4]

/-
8. Write a function, iterate, that 
takes as its arguments (1) a function, 
f, of type nat → nat, and (2) a natural
number, n, and that returns a function 
that takes an argument, (m : nat), and
that returns the result of applying f 
to m n times. For example, if n = 3, it
should return f (f (f m)). The result
of applying f zero times is just m.
Hint: use case analysis on n, and 
recursion. Test your function using 
nat.succ, your double function, and
(nat.add 4) as function arguments. 
-/

-- ANSWER HERE
def iterate (f : ℕ → ℕ) : ℕ → (ℕ → ℕ)
| 0 := λ m, m
| (n' + 1) := λ m, iterate n' (f m)


#eval iterate double 3 5  -- should be 40 (5*2*2*2)
#eval iterate nat.succ 10 0  -- should be 10
#eval iterate (nat.add 4) 0 1  -- should be 1
#eval iterate (nat.add 3) 5 12  -- should be 27

/-
9. Write a function, list_add, that takes
a list of natural numbers and returns the
sum of all the numbers in the list.
-/

-- ANSWER HERE
def list_add : list ℕ → ℕ
| list.nil := 0
| (list.cons h t) := h + list_add t

#eval list_add [1, 2, 3]

/-
10. Write a function, list_mul, that takes
a list of natural numbers and returns the
product of all the numbers in the list.
-/

-- ANSWER HERE
def list_mul : list ℕ → ℕ
| list.nil := 1
| (list.cons h t) := if h = 0 then 0 else h * list_mul t

#eval list_mul [1, 2, 4]
#eval list_mul [1, 2, 3, 0]

/-
11. Write a function, list_has_zero, that
takes a list of natural numbers and returns
tt if the list contains any zero values and
that returns false otherwise. Use isEqN in
your solution. Test your solution on both
empty and non-empty lists including lists
that both have and don't have zero values.
-/

-- ANSWER HERE
def list_has_zero : list ℕ → bool
| list.nil := ff
| (list.cons h t) := if isEqn 0 h then tt else list_has_zero t

#eval list_has_zero [1, 2, 3]
#eval list_has_zero [0, 1, 2]

/-
12. Write a function, compose_nat_nat,
that takes two functions, f : ℕ → ℕ,
and g : ℕ → ℕ, and that returns a
function that takes a nat, n, and that
returns g (f n). Test your function 
using at least nat.succ and double as
argument values.
-/

-- ANSWER HERE
def compose_nat_nat (f g : ℕ → ℕ) : (ℕ → ℕ) :=
λ n, g (f n)

#eval compose_nat_nat nat.succ nat.succ 2 --should be 4
#eval compose_nat_nat double nat.succ 2 --should be 5
#eval compose_nat_nat nat.succ double 2 --should be 6
#eval compose_nat_nat double double 2 --should be 8

/-
13. Write a polymorphic map_box function
of type 

Π (α β : Type u), 
  (α → β) → box α → box β  
  
that takes a function, f, of type 
(α → β), and a box, b, containing a 
value of type α and that returns a 
box containing that value transformed
by the application of f.  
-/

-- ANSWER HERE
universe u

-- copied box from class library
structure box (α : Type u) : Type u :=
(val : α)

def map_box : Π (α β : Type u),
  (α → β) → box α → box β :=
  λ _ _ f b, box.mk (f (box.val b))

#eval (map_box ℕ ℕ double (box.mk 10)).val  --should be 20


/-
14. 
Write a function, map_option, that
takes a function, f, of type α → β
and an option α and that transforms
it into an option β, where none goes
to none, and some (a : α) goes to
some b, where b is a transformed by 
f.
-/

-- ANSWER HERE
def map_option (α β : Type u) (f : α → β) : option α → option β
| none := none
| (some (a : α)) := f a  -- don't need to write "some (f a)" bc some is inferred

-- test, should return some "3"
#eval map_option nat string repr (some 3)

/-
15. Write three functions, default_nat,
default_bool, and default_list α, each
taking no arguments (other than a type,
argument, α, in the third case), and 
each returning a default value of the
given type: a nat, a bool, and a list.
Don't overthink this: Yes, a function
that takes no arguments is basically 
a constant. You'll need to declare a
universe variable for the list problem.
-/

-- ANSWER HERE
def default_nat := default ℕ
def default_bool := default bool
def default_list (α : Type u) := default (list α)

#eval default_nat
#eval default_bool
#eval default_list string