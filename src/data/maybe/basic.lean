import ...category.monad

namespace maybe

inductive maybe (α : Type) : Type
| nothing {} : maybe
| just (a : α) : maybe
export maybe.maybe (nothing just)

@[simp] protected def map {α β : Type} (f : α → β) : maybe α → maybe β 
| nothing := nothing 
| (just a) := just $ f a 

@[simp] protected def unit {α : Type} : α → maybe α := just

@[simp] protected def join {α : Type} : maybe (maybe α) → maybe α
| nothing := nothing
| (just m) := m

instance : category.functor maybe :=
{ map := @maybe.map, }

instance : category.premonad maybe :=
{ unit := @maybe.unit, }

instance : category.monad maybe := 
{ join := @maybe.join, }

end maybe