import ..swap
import ..dorp
import ..prod
open category (renaming monad → my_monad) 
open composed (renaming swap_constructor.swap → swap)
open composed (renaming dorp_constructor.dorp → dorp)
open composed (renaming prod_constructor.prod → my_prod)

namespace composed 

class is_lawful_swap (m n : Type → Type) [my_monad m] [my_monad n]
  [swap_constructor m n] [prod_constructor m n] [dorp_constructor m n] :=
(swap_map_map : ∀{α β : Type} (f : α → β), 
  swap ∘ map (map f) = (map (map f) ∘ swap : _ → compose m n (compose m n β)))
(swap_unit : ∀{α : Type}, (swap ∘ unit : m α → compose m n α) = map unit)
(swap_map_unit : ∀{α : Type}, (swap ∘ map unit : n α → compose m n α) = unit)
(prod_map_dorp : ∀{α : Type},
  my_prod ∘ map dorp = (dorp ∘ my_prod : _ → compose m n α))

protected def swap_from_monad {m n : Type → Type} [my_monad m] [my_monad n] 
  [my_monad (compose m n)] (α : Type) : compose n m α → compose m n α :=
join
∘ (unit.fixed m : n (compose m n α) → compose m n (compose m n α))
∘ (map.fixed n (map.fixed m (unit.fixed n)) : n (m α) → n (compose m n α))

instance {m n : Type → Type} [my_monad m] [my_monad n] [my_monad (compose m n)] 
  : swap_constructor m n := { swap := composed.swap_from_monad, }

end composed