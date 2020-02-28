import ..category.monad
open category (renaming functor → my_functor)

namespace composed

@[simp] def compose : (Type → Type) → (Type → Type) → Type → Type :=
function.comp

protected def map {m n : Type → Type} [my_functor m] [my_functor n] 
  (α β : Type) : (α → β) → compose m n α → compose m n β :=
(map : (n α → n β) → compose m n α → (compose m n) β) ∘ map

protected def unit {m n : Type → Type} [premonad m] [premonad n] (α : Type)
  : α → compose m n α :=
(unit : n α → compose m n α) ∘ unit

instance {m n : Type → Type} [my_functor m] [my_functor n]
  : my_functor (compose m n) := 
{ map := composed.map, } 

instance {m n : Type → Type} [premonad m] [premonad n]
  : premonad (compose m n) := 
{ unit := composed.unit, }

end composed