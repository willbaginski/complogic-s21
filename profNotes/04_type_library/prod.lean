namespace hidden

/-
The polymorphic type, prod α β, is 
the type whose values are ordered
pairs the first elements of which 
are of type α and the second elements
of which are of type β.
-/

structure prod (α β : Type) : Type :=
(fst : α) (snd : β)

/-
The names of the field are also used
for generated projection functions for
the corresponding fields.
-/

end hidden