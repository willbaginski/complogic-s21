/-
Identity functions for types nat, string, and bool.
An identity function takes and argument and returns
it unchanged.
-/


def id_nat : nat → nat :=
  λ n, n 

-- quick reminder on alternative syntax

-- cases
def id_nat' : nat → nat 
| n := n

-- c-style
def id_nat'' (n : nat) : nat := n

-- back to main point
def x : nat := 5
def id_string : string → string :=
  fun (s : string), s 
  
def id_bool : bool → bool :=
  λ n, n 

/-
Parametric polymorphism: types are
terms (values), too, and so can be
given as arguments to functions.
-/

-- Use #check to see the type of any term

#check 1
#check "Hello"
#check tt

/- 
Types are terms, too. As such, every type
has a type. All of the usual computational
types, and any additional ones you might
define, are of type, Type. It's important
to understand this now.
-/

#check nat 
#check string
#check bool

/-
Here's a polymorphic identity function. The
"Π (α : Type), α → α" is the type of this
function. You can read it like this: Given
any type, α (such as nat or bool or string),
the function is of type α → α. So if the value
of the first argument, α, is bool, for example,
then the the rest of the type is bool → bool.
-/

def id1 : Π (α : Type), α → α := 
  λ α,
    λ a,
      a

-- Alternative syntax

def id2 (α : Type) (a : α) := a

def id3 : Π (α : Type), α → α 
| α a := a

-- tests
#eval id1 bool tt               -- expect tt
#eval id1 string "Hello, Lean!" -- expect "Hello..."
#eval id1 nat 5                 -- expect 5


/-
Type inference
-/

-- Lean can infer the value of α from the second argument
#eval id1 _ tt                -- α must be bool
#eval id1 _ "Hello, Lean!"    -- α must be string
#eval id1 _ 5                 -- α must be nat

-- Exercise: Become fluent quickly with these notations

/-
Implicit type inference

You can ask Lean to infer values automatically. To do this
put curly braces rather than parentheses around an argument.
-/

def id4 : Π { α : Type }, α → α := 
  λ α,
    λ a,
      a

def id5 { α : Type } (a : α) : α := a

def id6 : Π { α : Type }, α → α
| α a := a

-- Compare with preceding examples
#eval id4 tt                -- α must be bool
#eval id5 "Hello, Lean!"    -- α must be string
#eval id6 5                 -- α must be nat

-- You can turn off implicit arguments with @

#eval @id4 bool tt                  
#eval @id5 string "Hello, Lean!"    
#eval @id6 nat 5                    


/-
We've defined our identity functions to take
(1) any type, α, of type Type, and (2) any 
value, a, of the type give as the value of α,
and to return that same value, a. 

Knowing that types are terms, too, the clever
student will try to apply our id functions to
type-valued terms, such as nat or bool. Alas,
that won't work. 
-/

#eval id6 nat       -- Nope!

/-
Why? Let's analyze it. That's easier if we make
the implicit type argument explicit using an _.
We'll use our id2 version, which requires that
the first, type, argument (a value of type, Type)
be given explicitly. Let's start with an example
that works.  
-/

#eval id2 nat 5

/-
Here 5 is value of type nat, and nat is a value
of type Type. 

              Type         -- Type is Type 0
             /  |  \
          bool nat string  (α : Type) 
          / \   |    |
         tt ff  5   "Hi!"  (a : α)

What does the picture look like with a = nat?


              Type 1
                |
              Type         (α : Type 1)
             /  |  \
          bool nat string  (a : α)
          / \   |    |
         tt ff  5   "Hi!"  

-/

-- A "sad" solution is to change to (α : Type 1)

def id7 {α : Type 1} (a : α) : α := a


-- Okay, it works when applied to types in Type 0
#reduce id7 nat   -- careful: nat is second argument!
#eval id bool
#eval id string

-- But now it's broken for *values* of these types

#eval id7 nat 5     -- hope for 5

-- And for values in the next "type universe" up

#eval id7 Type      -- hope for Type

/-
Here's the general picture.

               ... ad inf.      -- Type 2 is type of Type 1, etc
                |
             Type 1             -- Type of Type 0
                |
              Type 0            -- Type of usual types
             /  |  \
      ... bool nat string ...   -- usual types
          / \   |    |
         tt ff  5   "Hi!"  ...  -- values of these types
-/ 

/-
Solution is to make definition "polymorphic" in 
type universes.
-/

namespace right_solution

universe u   -- let u be an arbitrary universe level (0, 1, 2, etc)

-- And let Lean infer u from context

def id {α : Type u} (a : α) : α := a

#reduce id 5      -- 5    belongs to nat,     nat     belongs to Type
#reduce id nat    -- nat  belongs to Type,    Type    belongs to Type 1
#reduce id Type   -- Type belongs to Type 1,  Type 1  belongs to Type 2
#reduce id (Type 10)  -- etc, ad infinitum

-- Yay!

/-
Why such complexity? It avoids certain inconsistencies.

Russell's Paradox.

Consider the set of all sets that do not contain themselves.

Does it contain itself?
If it doesn't contain itself then it must contain itself.
If it does contain itself then it mustn't contain itself.
Either assumption leads to a contradiction, and inconsistency.
Russell introduced stratified types to avoid this problem in set theory.
The hierarchy prevents any type from containing itself as a value.

The very concept of sets containing or not containing themselves
has to be excluded from consideration. Types that contain only 
"lower" types and never themselves solves the problem. Bertrand
Russell is thus a great-great-granddaddy of this aspect of type
theory.

What belongs in higher type universes in practice? It's pretty
straightforward. If an object *contains a value* of type, Type u, 
then that object lives in (at least) Type u+1. Details later on.
-/

/-
This material about type universes is quite abstract, so please
don't worry if it's going over your head at this point. Graduate
students should work hard to grasp it. For the most part I will
avoid defining types in full generality w.r.t. universe levels.
-/

end right_solution