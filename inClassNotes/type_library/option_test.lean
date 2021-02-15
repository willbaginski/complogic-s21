import .option

namespace hidden 

/-
Every function in Lean must be total.
That is, there has to be an answer for
*all* values of the argument type. We
will discuss the reason later in the
course, but for now you can believe
there's a good reason.

This constraint presents a problem if
we want to represent *partial* functions
in constructive logic, i.e., functions
that are not defined for all values of 
its argument type(s).

Examples: 

    Total function from bool to bool
    tt --> 1
    ff --> 0

    Partial function from bool to bool
    tt --> 1
    ff ---> 

Indeed, Π means "for *every* value" of
one type there is *some* corresponding
value of another type. Check it out.
-/

#check ℕ → ℕ 
#check Π (n : nat), nat
#check ∀ (n : nat), nat

def id_nat'' : Π (n : nat), nat := 
  λ n, n
#check id_nat''

def id_nat' : ∀ (n : nat), nat := 
  λ n, n
#check id_nat'

def id_nat : nat → nat := 
  λ n, n

/-

All three expresions express the
type of *total* functions from ℕ
to ℕ. The arrow notation is just 
a nice, conventional, shorthand.

You can think of the function type, 
*Π (n : nat), nat,* as a proposition
that asserts that, given *any* value 
of type n, it's possible to construct
and return a value of the return type,
also nat in this case. That is, it 
can be read as asserting that there
is at some total function that takes
*any* nat values as an argument and
that given any such value constructs
and returns a value of type nat. The 
λ expressions are basically proofs 
that this is true, in the sense that 
type check as *values* of the Π type.
-/


/-
Now suppose for example we want to 
represent a partial function, f, 
from bool to nat, where (f b) is
defined to be zero if b is ff and
that is *undefined* otherwise.

You know lots of partial functions.
Another one is square root where
both the domain of definition and
the co-domain are taken to be the
real numbers, ℝ. Here the function
is partial because the real-valued
square root function is not defined
for every value in the domain of
definition. In particular, it's not
defined for any of the negative 
real numbers.

Note that if we defined the domain
of definition of a similar square
root function to be the non-negative
real numbers, ℝ⁺, that function is
total, because it's defined on 
every value of its domain. These
two square root functions have
exactly the same values on the 
same *domains*, where a domain
is the subset of a given domain
of definition on which a given
function is defined.

EXERCISE: Come up with a function
that takes and returns real numbers
but that isn't defined at zero.

A function is thus total iff it's
defined for every value in its 
domain of definition, and in this
case its domain is equal to its
domain of definition. A function
is partial if the domain on which
it's defined is a strict subset 
of its domain of definition.

How can we represent a partial
function in Lean (or in another
constructive logic proof assistant)
when all functions must be total?

Take our partial function from
bool to nat as an example. We
represent the domain of definition
of the function as the type bool.
We need to return some value for
each value of this type: here, a
value for tt and a value for ff, 
but where the form of value we
return indicates whether we got
a return value for an argument
on which the function is defined,
or a kind of "no value" result
for an argument on which it isn't.

Conceptually our function will have
to return *some natural number* for
any argument where the function is
defined (namely for the value, ff, 
in our example), other it will have
to return *none*. It will be as if
we've added a single new value,
none, to the natural numbers, to
serve as an "error" return value.

The trick is to define a new type,
*option nat*, a value of which is
either *none* or *some (n : nat)*,
and then to represent our partial
function, f, as a total function,
f', from bool to *option nat*: one 
that returns *none* when applied 
to a value, b, on which f is not
defined, and that otherwise returns
*some n*, where n is the value of 
(f b), where, again, b is a value 
on which the partial function, f,
that we're representing is defined.

An option type is a simple "sum of 
products" type, with two variants:
two constructors. The first, *none*,
represents the "not defined" return
value. The second, some (b : β),
is used to return b as the correct
value of a function, f', applied, 
to an (a : α) on which f is defined. 
-/

/-
Here it is, as defined in Lean.

universe u 

inductive option (α : Type u) : Type u
| none : option
| some (a : α) : option
-/

def pFun : bool → option ℕ 
| tt := option.none
| ff := option.some 0

#reduce pFun tt
#reduce pFun ff

/-
Here's another example: a partial
function from nat → ℕ that's like
the identity function but defined
only on even numbers.
-/

def evenId : ℕ → option ℕ :=
λ n, 
  if (n%2=0) 
  then (option.some n) 
  else option.none

#reduce evenId 0
#reduce evenId 1
#reduce evenId 2
#reduce evenId 3
#reduce evenId 4
#reduce evenId 5


end hidden

