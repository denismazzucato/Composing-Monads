import ..dorp
open category (renaming monad → my_monad) 
open composed (renaming dorp_constructor.dorp → dorp)

namespace composed 

class is_lawful_dorp (m n : Type → Type) [premonad m] [my_monad n]
  [dorp_constructor m n] :=
(dorp_map_map : ∀{α β : Type} (f : α → β), 
  dorp ∘ map (map f) = map f ∘ (dorp : _ → compose m n α))
(dorp_unit : ∀{α : Type}, dorp ∘ unit = (map unit : m α → compose m n α))
(dorp_map_unit : ∀{α : Type}, dorp ∘ map unit = (id : _ → compose m n α))
(dorp_map_join : ∀{α : Type},
  dorp ∘ join = (join ∘ map dorp : _ → compose m n α))

protected def dorp_from_monad {m n : Type → Type} [my_monad m] [my_monad n] 
  [my_monad (compose m n)] (α : Type) : compose m n (m α) → compose m n α :=
join ∘ map (map.fixed m (unit.fixed n))

instance {m n : Type → Type} [my_monad m] [my_monad n] [my_monad (compose m n)] 
  : dorp_constructor m n := { dorp := composed.dorp_from_monad, }

end composed