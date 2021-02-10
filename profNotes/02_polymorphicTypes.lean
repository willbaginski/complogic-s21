namespace hidden

/-
Types Part I: Sum types, product types, inference rules
-/

/-
SOME SUM TYPES (variant, or, tagged union)

A value of such a type is "one of these OR
one of those OR one of something else." SUM
means OR in this sense.
-/

inductive romanNumeral : Type
| I     : romanNumeral
| II    : romanNumeral
| III   : romanNumeral
| IV    : romanNumeral
| V     : romanNumeral


/-
Some more simple sum types
-/

inductive empty : Type  -- Look Ma, no values!

inductive unit : Type   -- A type with one value (void)
| star : unit

inductive bool : Type   -- Two values
| tt : bool
| ff                    -- leave type to be inferred

inductive day : Type    -- code easy to read
| sun
| mon
| tue
| wed
| thu
| fri
| sat

open day

/-
We generally define functions that consume
values of sum types by case analysis. Which
constructor was used to construct the value
of the argument? The left side of a case is 
a pattern. Argument values are matched in the
order in which patterns are given. The result
is the value of the right hand side of the 
first pattern that matches.
-/

def next_day : day → day
-- if the argument value is sun, reduce to mon
| sun := mon
-- etc
| mon := tue
| tue := wed
| wed := thu
| thu := fri
| fri := sat
| sat := sun

#reduce next_day sun
#reduce next_day sat


/-
PRODUCT TYPES (records, structures)
-/

/-
A product type has one constructor
that takes/combines values of zero
or more other types into records, or 
structures. In a value of a product 
type there a value for the first field
AND a value for the secon AND a value 
for the third, etc. PRODUCT in this
sense means AND.
-/

/-
We define a product type with one 
field. A value of this type can be
visualized as a box with a single 
value inside. We start with a type
of box that "contains" a single nat
value. We present the same type in
four ways to illustrate syntax you
can use.
-/

inductive box_nat' : Type
| mk (val : ℕ) : box_nat'

inductive box_nat'' : Type
| mk : ℕ → box_nat''

structure box_nat''' : Type :=   
mk :: (val : ℕ)

structure box_nat := 
(val : ℕ) 

def aBox := box_nat.mk 3 

#check aBox
#reduce aBox


/- 
Given a box, we "destructure" it using 
"pattern matching" to get at the values
that were used in its construction: in
this case to access the ℕ inside a box.
-/

def unbox_nat : box_nat → ℕ 
| (box_nat.mk n) := n

#eval unbox_nat aBox

/-
When you use the "structure" syntax, Lean
generates a projection (accessor) function
for each field automatically.
-/

#eval box_nat.val aBox
#eval aBox.val     -- Preferred notation




/-
Polymorphic types
-/

/-
We immediately see the same problem 
as with functions: the need for a many 
variants varying only in the type of
value "contained in the box".

The solution is analogous: make our
type polymorphic by having it take a
type-valued parameter and by making
the value it contains of the type 
that is the value of that parameter.
-/

structure box (α : Type) : Type :=
(val : α)

def nat_box := box.mk 3
def str_box := box.mk "Hello, Lean!"
def bool_box := box.mk tt

#eval nat_box.val
#eval str_box.val
#eval bool_box.val


/-
Polymorphic product types with two 
fields -- the type of ordered pairs --
and two type parameters accordingly. 
-/

namespace hidden  -- Lean defined prod

structure prod (α β : Type) : Type :=
(fst : α) 
(snd : β)

-- Self-test: What's the type of prod?

-- "Introduce" some pairs
def pair1 := prod.mk 4 "Hi"
def pair2 := prod.mk "Bye" tt

-- "Eliminate" some pairs
#eval pair1.fst
#eval pair1.snd
#eval pair2.fst
#eval pair2.snd


#check prod

/-
Note: In contrast to arrays, in which 
all values are of the same type, records
can have fields of different types, as 
we see in the following example. You
should have strong intuition for product
types, as they crop up all the time in
imperative programming: as struct in C;
as multiple data fields of classes in OO
languages, such as C++, Java, Python; 
and as fields of records in relational
databases.
-/

/-
Think about a Java class: it basically
defines a record/structure/product type 
then gathers around it a set of operations
on instances of such structures. (There's
more to OOP than that, namely dynamic types
and dispatch, but that's another matter).
-/

/-
Let's start with an example. The prod_nat_string.mk
constructor takes a ℕ value, n, and a string value,
s, and puts them together into a pair, (n, s). The
mk function can thus be viewed as a prod_nat_string
introduction rule.

Now suppose we're given such a pair, (n, s), and 
we want to consume/use it to obtain a value of type
string (namely the string value that constitutes the
second element of the pair). 

To get at the elements of pair, (mk n s), constructed 
from some ℕ, n, and some string, s, we *destructure*
the pair by "pattern matching" on its constructor name
and by giving names to the values from which it was
constructed. This is like "breaking open the box and
giving names to the contents." Once we've done that we
can used the named contents in computing and returning
a desired value.

Here we use destructuring to define "field accessor"
functions for nat-string pairs. We refer to the first
field of a pair as "fst" and the second as "snd". We
also call such accessors "projection functions."
-/

def fst_nat_string : prod_nat_string → nat
| (prod_nat_string.mk n s) := n

def snd_nat_string : prod_nat_string → string
| (prod_nat_string.mk x y) := y

#eval fst_nat_string (prod_nat_string.mk 1 "Hello")
#eval snd_nat_string (prod_nat_string.mk 1 "Hello")

-- structures auto-generate projection functions

/-
Recall

structure prod_nat_string''' := 
(fst : ℕ) (snd : string)

-/
def p := prod_nat_string'''.mk 1 "Hello"
#eval (prod_nat_string'''.fst p)
#eval (p.fst)     -- dot notation for projection
#eval (p.snd)     -- aka accessor functions



/-
Polymorphic Types!
-/

universe u

structure box (α : Type u) : Type u :=
(val : α)

-- test 
def boxed_nat := box.mk 3
def boxed_string := box.mk "Hello"
#eval boxed_nat.val
#eval boxed_string.val


structure prod (α β : Type u) : Type u :=
(fst : α) (snd : β)

-- test

def ns_pair := prod.mk 1 "Hi, Lean!"
#eval ns_pair.fst
#eval ns_pair.snd


structure phythagorean_triple : Type :=
(a b c : ℕ)
(cert: a*a + b*b = c*c)

def py_tri : phythagorean_triple :=
phythagorean_triple.mk
3 4 5
rfl


#reduce py_tri.cert   -- construct proof that 25 = 25


def py_tri_bad : phythagorean_triple :=
phythagorean_triple.mk
3 4 6
rfl           -- can't construct proof that 25 = 36


-- Try that in mere Haskell. No way!

