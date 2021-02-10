namespace hidden

/-
The "either" type is used to hold either
a value, the "left" value, of one type,
α, or a value, the right value, of another
type, β. It's typically used to represent
either a correct value (e.g., a correct
value returned by a function) or an error 
value (perhaps an error string in a case
where the function was unable to construct
a correct value).
-/

inductive either (α β : Type) : Type
| (left : α)
| (right : β) 

/-
Exercise: define a function that takes a
natural number. If the number is even, it
returns the same number, but if the number
is odd, it returns an error string, "Oops."
-/

end hidden